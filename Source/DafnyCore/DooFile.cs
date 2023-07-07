using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Binding;
using System.Configuration;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Text;
using System.Threading;
using Microsoft.Dafny;
using Microsoft.Dafny.Auditor;
using Tomlyn;
using Tomlyn.Model;
using Type = System.Type;

namespace DafnyCore; 

// Model class for the .doo file format for Dafny libraries.
// Contains the validation logic for safely consuming libraries as well.
public class DooFile {

  private const string ProgramFileEntry = "program";

  private const string ManifestFileEntry = "manifest.toml";

  public class ManifestData {
    public const string CurrentDooFileVersion = "1.0";
    public string DooFileVersion { get; set; }

    public string DafnyVersion { get; set; }

    public string SolverIdentifier { get; set; }
    public string SolverVersion { get; set; }

    public Dictionary<string, object> Options { get; set; }

    public ManifestData() {
      // Only for TOML deserialization!
    }

    public ManifestData(DafnyOptions options) {
      DooFileVersion = CurrentDooFileVersion;
      DafnyVersion = options.VersionNumber;

      SolverIdentifier = options.SolverIdentifier;
      SolverVersion = options.SolverVersion.ToString();

      Options = new Dictionary<string, object>();
      foreach (var (option, _) in OptionChecks) {
        var optionValue = GetOptionValue(options, option);
        Options.Add(option.Name, optionValue);
      }
    }

    public static ManifestData Read(TextReader reader) {
      return Toml.ToModel<ManifestData>(reader.ReadToEnd(), null, new TomlModelOptions());
    }

    public void Write(TextWriter writer) {
      writer.Write(Toml.FromModel(this, new TomlModelOptions()));
    }
  }

  public ManifestData Manifest { get; set; }

  public string ProgramText { get; set; }

  // This must be independent from any user-provided options,
  // and remain fixed over the lifetime of a single .doo file format version.
  // We don't want to attempt to read the program text using --function-syntax:3 for example.
  // If we change default option values in future Dafny major version bumps,
  // this must be configured to stay the same.
  private static DafnyOptions ProgramSerializationOptions => DafnyOptions.Default;

  public static DooFile Read(string path) {
    var result = new DooFile();

    using var archive = ZipFile.Open(path, ZipArchiveMode.Read);
    var manifestEntry = archive.GetEntry(ManifestFileEntry);
    if (manifestEntry == null) {
      throw new ArgumentException(".doo file missing manifest entry");
    }
    using (var manifestStream = manifestEntry.Open()) {
      result.Manifest = ManifestData.Read(new StreamReader(manifestStream, Encoding.UTF8));
    }

    var programTextEntry = archive.GetEntry(ProgramFileEntry);
    if (programTextEntry == null) {
      throw new ArgumentException(".doo file missing program text entry");
    }
    using (var programTextStream = programTextEntry.Open()) {
      var reader = new StreamReader(programTextStream, Encoding.UTF8);
      result.ProgramText = reader.ReadToEnd();
    }

    return result;
  }

  public DooFile(Program dafnyProgram) {
    var tw = new StringWriter();
    var pr = new Printer(tw, ProgramSerializationOptions, PrintModes.Serialization);
    // afterResolver is false because we don't yet have a way to safely skip resolution
    // when reading the program back into memory.
    // It's probably worth serializing a program in a more efficient way first
    // before adding that feature.
    pr.PrintProgram(dafnyProgram, false);
    ProgramText = tw.ToString();
    Manifest = new ManifestData(dafnyProgram.Options);
  }

  private DooFile() {
  }

  public bool Validate(string filePath, DafnyOptions options, Command currentCommand) {
    if (currentCommand == null) {
      options.Printer.ErrorWriteLine(Console.Out, $"Cannot load {filePath}: .doo files cannot be used with the legacy CLI");
      return false;
    }

    if (options.VersionNumber != Manifest.DafnyVersion) {
      options.Printer.ErrorWriteLine(Console.Out, $"Cannot load {filePath}: it was built with Dafny {Manifest.DafnyVersion}, which cannot be used by Dafny {options.VersionNumber}");
      return false;
    }

    var success = true;
    var revelantOptions = currentCommand.Options.ToHashSet();
    foreach (var (option, check) in OptionChecks) {
      // It's important to only look at the options the current command uses,
      // because other options won't be initialized to the correct default value.
      // See CommandRegistry.Create().
      if (!revelantOptions.Contains(option)) {
        continue;
      }

      var localValue = options.Get(option);

      object libraryValue = null;
      if (Manifest.Options.TryGetValue(option.Name, out var manifestValue)) {
        if (!DafnyProject.TryGetValueFromToml(Console.Out, null,
              option.Name, option.ValueType, manifestValue, out libraryValue)) {
          return false;
        }
      } else if (option.ValueType == typeof(IEnumerable<string>)) {
        // This can happen because Tomlyn will drop aggregate properties with no values.
        libraryValue = Array.Empty<string>();
      }
      success = success && check(options, option, localValue, filePath, libraryValue);
    }
    return success;
  }

  private static object GetOptionValue(DafnyOptions options, Option option) {
    // This is annoyingly necessary because only DafnyOptions.Get<T>(Option<T> option)
    // handles falling back to the configured default option value,
    // whereas the non-generic DafnyOptions.Get(Option option) doesn't.
    // TODO: Move somewhere more generic if this is useful in other cases?
    var optionType = option.ValueType;
    if (optionType == typeof(bool)) {
      return options.Get((Option<bool>)option);
    }
    if (optionType == typeof(string)) {
      return options.Get((Option<string>)option);
    }
    if (optionType == typeof(IEnumerable<string>)) {
      return options.Get((Option<IEnumerable<string>>)option);
    }

    throw new ArgumentException();
  }

  public void Write(ConcreteSyntaxTree wr) {
    var manifestWr = wr.NewFile(ManifestFileEntry);
    using var manifestWriter = new StringWriter();
    Manifest.Write(manifestWriter);
    manifestWr.Write(manifestWriter.ToString());

    var programTextWr = wr.NewFile(ProgramFileEntry);
    programTextWr.Write(ProgramText);
  }

  public void Write(string path) {
    // Delete first, we don't want to merge with existing zips
    File.Delete(path);

    using var archive = ZipFile.Open(path, ZipArchiveMode.Create);

    var manifest = archive.CreateEntry(ManifestFileEntry);
    using (var manifestStream = manifest.Open()) {
      using var manifestWriter = new StreamWriter(manifestStream, Encoding.UTF8);
      Manifest.Write(manifestWriter);
    }

    var programText = archive.CreateEntry(ProgramFileEntry);
    using (var programTextStream = programText.Open()) {
      using var programTextWriter = new StreamWriter(programTextStream, Encoding.UTF8);
      programTextWriter.Write(ProgramText);
    }
  }

  // Partitioning of all options into subsets that must be recorded in a .doo file
  // to guard against unsafe usage.
  // Note that legacy CLI options are not as cleanly enumerated and therefore
  // more difficult to completely categorize, which is the main reason the LibraryBackend
  // is restricted to only the new CLI.

  public delegate bool OptionCheck(DafnyOptions options, Option option, object localValue, string libraryFile, object libraryValue);
  private static readonly Dictionary<Option, OptionCheck> OptionChecks = new();
  private static readonly HashSet<Option> NoChecksNeeded = new();

  public static bool CheckOptionMatches(DafnyOptions options, Option option, object localValue, string libraryFile, object libraryValue) {
    if (OptionValuesEqual(option, localValue, libraryValue)) {
      return true;
    }

    options.Printer.ErrorWriteLine(Console.Out, $"*** Error: Cannot load {libraryFile}: --{option.Name} is set locally to {OptionValueToString(option, localValue)}, but the library was built with {OptionValueToString(option, libraryValue)}");
    return false;
  }

  private static bool OptionValuesEqual(Option option, object first, object second) {
    if (first.Equals(second)) {
      return true;
    }

    if (option.ValueType == typeof(IEnumerable<string>)) {
      return ((IEnumerable<string>)first).SequenceEqual((IEnumerable<string>)second);
    }

    return false;
  }

  private static string OptionValueToString(Option option, object value) {
    if (option.ValueType == typeof(IEnumerable<string>)) {
      var values = (IEnumerable<string>)value;
      return $"[{string.Join(',', values)}]";
    }

    return value.ToString();
  }

  public static void RegisterLibraryChecks(IDictionary<Option, OptionCheck> checks) {
    foreach (var (option, check) in checks) {
      if (NoChecksNeeded.Contains(option)) {
        throw new ArgumentException($"Option already registered as not needing a library check: {option.Name}");
      }
      OptionChecks.Add(option, check);
    }
  }

  public static void RegisterNoChecksNeeded(params Option[] options) {
    foreach (var option in options) {
      if (OptionChecks.ContainsKey(option)) {
        throw new ArgumentException($"Option already registered as needing a library check: {option.Name}");
      }
      NoChecksNeeded.Add(option);
    }
  }

  public static void CheckOptions(IEnumerable<Option> allOptions) {
    var unsupportedOptions = allOptions.ToHashSet()
      .Where(o =>
        !OptionChecks.ContainsKey(o) && !NoChecksNeeded.Contains(o))
      .ToList();
    if (unsupportedOptions.Any()) {
      throw new Exception($"Internal error - unsupported options registered: {{\n{string.Join(",\n", unsupportedOptions)}\n}}");
    }
  }
}
