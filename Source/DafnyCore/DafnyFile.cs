using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using DafnyCore;

namespace Microsoft.Dafny;

public class DafnyFile {
  public string FilePath { get; private set; }
  public string CanonicalPath { get; private set; }
  public string BaseName { get; private set; }
  public bool IsPreverified { get; set; }
  public bool IsPrecompiled { get; set; }
  public TextReader Content { get; set; }
  public Uri Uri { get; }

  public DafnyFile(DafnyOptions options, Uri uri, TextReader contentOverride = null) {
    Uri = uri;
    var filePath = uri.LocalPath;

    var extension = ".dfy";
    if (uri.IsFile) {
      extension = Path.GetExtension(uri.LocalPath).ToLower();
      BaseName = Path.GetFileName(uri.LocalPath);
    }
    if (uri.Scheme == "stdin") {
      contentOverride = options.Input;
      BaseName = "<stdin>";
    }

    // Normalizing symbolic links appears to be not
    // supported in .Net APIs, because it is very difficult in general
    // So we will just use the absolute path, lowercased for all file systems.
    // cf. IncludeComparer.CompareTo
    CanonicalPath = contentOverride == null ? Canonicalize(filePath).LocalPath : "<stdin>";
    FilePath = CanonicalPath;

    var filePathForErrors = options.UseBaseNameForFileName ? Path.GetFileName(filePath) : filePath;
    if (contentOverride != null) {
      IsPreverified = false;
      IsPrecompiled = false;
      Content = contentOverride;
    } else if (extension == ".dfy" || extension == ".dfyi") {
      IsPreverified = false;
      IsPrecompiled = false;
      if (!File.Exists(filePath)) {
        if (0 < options.VerifySnapshots) {
          // For snapshots, we first create broken DafnyFile without content,
          // then look for the real files and create DafnuFiles for them.
          // TODO prevent creating the broken DafnyFiles for snapshots
          return;
        }

        options.Printer.ErrorWriteLine(options.OutputWriter, $"*** Error: file {filePathForErrors} not found");
        throw new IllegalDafnyFile(true);
      } else {
        Content = new StreamReader(filePath);
      }
    } else if (extension == ".doo") {
      IsPreverified = true;
      IsPrecompiled = false;

      if (!File.Exists(filePath)) {
        options.Printer.ErrorWriteLine(options.OutputWriter, $"*** Error: file {filePathForErrors} not found");
        throw new IllegalDafnyFile(true);
      }
      var dooFile = DooFile.Read(filePath);
      if (!dooFile.Validate(filePathForErrors, options, options.CurrentCommand)) {
        throw new IllegalDafnyFile(true);
      }

      // For now it's simpler to let the rest of the pipeline parse the
      // program text back into the AST representation.
      // At some point we'll likely want to serialize a program
      // more efficiently inside a .doo file, at which point
      // the DooFile class should encapsulate the serialization logic better
      // and expose a Program instead of the program text.
      Content = new StringReader(dooFile.ProgramText);
    } else if (extension == ".dll") {
      IsPreverified = true;
      // Technically only for C#, this is for backwards compatability
      IsPrecompiled = true;

      var sourceText = GetDafnySourceAttributeText(filePath);
      if (sourceText == null) { throw new IllegalDafnyFile(); }
      Content = new StringReader(sourceText);
    } else {
      throw new IllegalDafnyFile();
    }
  }

  // Returns a canonical string for the given file path, namely one which is the same
  // for all paths to a given file and different otherwise. The best we can do is to
  // make the path absolute -- detecting case and canonicalizing symbolic and hard
  // links are difficult across file systems (which may mount parts of other filesystems,
  // with different characteristics) and is not supported by .Net libraries
  public static Uri Canonicalize(string filePath) {
    if (filePath == null || !filePath.StartsWith("file:")) {
      return new Uri(Path.GetFullPath(filePath));
    }

    if (Uri.IsWellFormedUriString(filePath, UriKind.RelativeOrAbsolute)) {
      return new Uri(filePath);
    }

    var potentialPrefixes = new List<string>() { "file:\\", "file:/", "file:" };
    foreach (var potentialPrefix in potentialPrefixes) {
      if (filePath.StartsWith(potentialPrefix)) {
        var withoutPrefix = filePath.Substring(potentialPrefix.Length);
        var tentativeURI = "file:///" + withoutPrefix.Replace("\\", "/");
        if (Uri.IsWellFormedUriString(tentativeURI, UriKind.RelativeOrAbsolute)) {
          return new Uri(tentativeURI);
        }
        // Recovery mechanisms for the language server
        return new Uri(filePath.Substring(potentialPrefix.Length));
      }
    }
    return new Uri(filePath.Substring("file:".Length));
  }
  public static List<string> FileNames(IReadOnlyList<DafnyFile> dafnyFiles) {
    var sourceFiles = new List<string>();
    foreach (DafnyFile f in dafnyFiles) {
      sourceFiles.Add(f.FilePath);
    }
    return sourceFiles;
  }

  private static string GetDafnySourceAttributeText(string dllPath) {
    if (!File.Exists(dllPath)) {
      throw new IllegalDafnyFile();
    }
    using var dllFs = new FileStream(dllPath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
    using var dllPeReader = new PEReader(dllFs);
    var dllMetadataReader = dllPeReader.GetMetadataReader();

    foreach (var attrHandle in dllMetadataReader.CustomAttributes) {
      var attr = dllMetadataReader.GetCustomAttribute(attrHandle);
      try {
        /* The cast from EntityHandle to MemberReferenceHandle is overriden, uses private members, and throws
         * an InvalidCastException if it fails. We have no other option than to use it and catch the exception.
         */
        var constructor = dllMetadataReader.GetMemberReference((MemberReferenceHandle)attr.Constructor);
        var attrType = dllMetadataReader.GetTypeReference((TypeReferenceHandle)constructor.Parent);
        if (dllMetadataReader.GetString(attrType.Name) == "DafnySourceAttribute") {
          var decoded = attr.DecodeValue(new StringOnlyCustomAttributeTypeProvider());
          return (string)decoded.FixedArguments[0].Value;
        }
      } catch (InvalidCastException) {
        // Ignore - the Handle casts are handled as custom explicit operators,
        // and there's no way I can see to test if the cases will succeed ahead of time.
      }
    }

    return null;
  }

  // Dummy implementation of ICustomAttributeTypeProvider, providing just enough
  // functionality to successfully decode a DafnySourceAttribute value.
  private class StringOnlyCustomAttributeTypeProvider : ICustomAttributeTypeProvider<System.Type> {
    public System.Type GetPrimitiveType(PrimitiveTypeCode typeCode) {
      if (typeCode == PrimitiveTypeCode.String) {
        return typeof(string);
      }
      throw new NotImplementedException();
    }

    public System.Type GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle handle, byte rawTypeKind) {
      throw new NotImplementedException();
    }

    public System.Type GetTypeFromReference(MetadataReader reader, TypeReferenceHandle handle, byte rawTypeKind) {
      throw new NotImplementedException();
    }

    public System.Type GetSZArrayType(System.Type elementType) {
      throw new NotImplementedException();
    }

    public System.Type GetSystemType() {
      throw new NotImplementedException();
    }

    public System.Type GetTypeFromSerializedName(string name) {
      throw new NotImplementedException();
    }

    public PrimitiveTypeCode GetUnderlyingEnumType(System.Type type) {
      throw new NotImplementedException();
    }

    public bool IsSystemType(System.Type type) {
      throw new NotImplementedException();
    }
  }
}