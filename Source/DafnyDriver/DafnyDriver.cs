//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// DafnyDriver
//       - main program for taking a Dafny program and verifying it
//---------------------------------------------------------------------------------------------

using System.Collections.Concurrent;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using System.Diagnostics;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny {

  public class DafnyDriver {
    public DafnyOptions Options { get; }


    private readonly ExecutionEngine engine;

    private DafnyDriver(DafnyOptions dafnyOptions) {
      Options = dafnyOptions;
      engine = ExecutionEngine.CreateWithoutSharedCache(dafnyOptions);
    }

    // TODO: Refactor so that non-errors (NOT_VERIFIED, DONT_PROCESS_FILES) don't result in non-zero exit codes
    public enum ExitValue { SUCCESS = 0, PREPROCESSING_ERROR, DAFNY_ERROR, COMPILE_ERROR, VERIFICATION_ERROR, FORMAT_ERROR }

    // Environment variables that the CLI directly or indirectly (through target language tools) reads.
    // This is defined for the benefit of testing infrastructure to ensure that they are maintained
    // through separate processes.
    public static readonly string[] ReferencedEnvironmentVariables = { "PATH", "HOME", "DOTNET_NOLOGO" };

    static DafnyDriver() {
      if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
        ReferencedEnvironmentVariables = ReferencedEnvironmentVariables
          .Concat(new[] { // Careful: Keep this list in sync with the one in lit.site.cfg
            "APPDATA",
            "HOMEDRIVE",
            "HOMEPATH",
            "INCLUDE",
            "LIB",
            "LOCALAPPDATA",
            "NODE_PATH",
            "ProgramFiles",
            "ProgramFiles(x86)",
            "SystemRoot",
            "SystemDrive",
            "TEMP",
            "TMP",
            "USERPROFILE"
          }).ToArray();
      }
    }

    public static readonly string[] DefaultArgumentsForTesting = new[] {
      // Try to verify 2 verification conditions at once
      "/vcsCores:2",

      // We do not want absolute or relative paths in error messages, just the basename of the file
      "/useBaseNameForFileName",

      // We do not want output such as "Compiled program written to Foo.cs"
      // from the compilers, since that changes with the target language
      "/compileVerbose:0",
      
      // Set a default time limit, to catch cases where verification time runs off the rails
      "/timeLimit:300",

      // test results do not include source code snippets
      "/showSnippets:0"
    };

    public static readonly string[] NewDefaultArgumentsForTesting = new[] {
      // Try to verify 2 verification conditions at once
      "--cores=2",

      // We do not want absolute or relative paths in error messages, just the basename of the file
      "--use-basename-for-filename",

      // Set a default time limit, to catch cases where verification time runs off the rails
      "--verification-time-limit=300",

      // test results do not include source code snippets
      "--show-snippets:false"
    };

    public static int Main(string[] args) {
      return MainWithWriters(Console.Out, Console.Error, Console.In, args);
    }

    public static int MainWithWriters(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader,
      string[] args) {

      // Code that shouldn't be needed, but prevents some exceptions when running the integration tests in parallel
      // outputWriter = new UndisposableTextWriter(outputWriter);
      // errorWriter = new UndisposableTextWriter(errorWriter);
      // outputWriter = TextWriter.Synchronized(outputWriter);
      // errorWriter = TextWriter.Synchronized(errorWriter);

#pragma warning disable VSTHRD002
      return Task.Run(() => ThreadMain(outputWriter, errorWriter, inputReader, args)).Result;
#pragma warning restore VSTHRD002
    }

    private static int ThreadMain(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader, string[] args) {
      Contract.Requires(cce.NonNullElements(args));

      var cliArgumentsResult = ProcessCommandLineArguments(outputWriter, errorWriter, inputReader,
        args, out var dafnyOptions, out var dafnyFiles, out var otherFiles);
      ExitValue exitValue;

      switch (cliArgumentsResult) {
        case CommandLineArgumentsResult.OK:

          if (dafnyOptions.RunLanguageServer) {
#pragma warning disable VSTHRD002
            LanguageServer.Server.Start(dafnyOptions).Wait();
#pragma warning restore VSTHRD002
            return 0;
          }

          var driver = new DafnyDriver(dafnyOptions);
#pragma warning disable VSTHRD002
          exitValue = driver.ProcessFilesAsync(dafnyFiles, otherFiles.AsReadOnly(), dafnyOptions).Result;
#pragma warning restore VSTHRD002
          break;
        case CommandLineArgumentsResult.PREPROCESSING_ERROR:
          return (int)ExitValue.PREPROCESSING_ERROR;
        case CommandLineArgumentsResult.OK_EXIT_EARLY:
          return (int)ExitValue.SUCCESS;
        default:
          throw new ArgumentOutOfRangeException();
      }

      dafnyOptions.XmlSink?.Close();

      if (dafnyOptions.VerificationLoggerConfigs.Any()) {
        try {
          VerificationResultLogger.RaiseTestLoggerEvents(dafnyOptions);
        } catch (ArgumentException ae) {
          dafnyOptions.Printer.ErrorWriteLine(dafnyOptions.OutputWriter, $"*** Error: {ae.Message}");
          exitValue = ExitValue.PREPROCESSING_ERROR;
        }
      }
      if (dafnyOptions.Wait) {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }

      //Console.ReadKey();
      return (int)exitValue;
    }

    public enum CommandLineArgumentsResult {
      /// Indicates that arguments were parsed successfully.
      OK,
      /// Indicates that arguments were not parsed successfully.
      PREPROCESSING_ERROR,
      /// Indicates that arguments were parsed successfully, but the program should exit without processing files.
      OK_EXIT_EARLY
    }

    static HashSet<string> SplitOptionValueIntoFiles(HashSet<string> inputs) {
      var result = new HashSet<string>();
      foreach (var input in inputs) {
        var values = input.Split(',');
        foreach (var slice in values) {
          var name = slice.Trim();
          if (Directory.Exists(name)) {
            var files = Directory.GetFiles(name, "*.dfy", SearchOption.AllDirectories);
            foreach (var file in files) { result.Add(file); }
          } else {
            result.Add(name);
          }
        }
      }
      return result;
    }

    public static CommandLineArgumentsResult ProcessCommandLineArguments(TextWriter outputWriter,
      TextWriter errorWriter,
      TextReader inputReader,
      string[] args, out DafnyOptions options, out List<DafnyFile> dafnyFiles, out List<string> otherFiles) {
      dafnyFiles = new List<DafnyFile>();
      otherFiles = new List<string>();

      try {
        switch (CommandRegistry.Create(outputWriter, errorWriter, inputReader, args)) {
          case ParseArgumentSuccess success:
            options = success.DafnyOptions;
            break;
          case ParseArgumentFailure failure:
            options = null;
            return failure.ExitResult;
          default: throw new Exception("unreachable");
        }

        options.RunningBoogieFromCommandLine = true;
      } catch (ProverException pe) {
        new DafnyConsolePrinter(DafnyOptions.Create(outputWriter)).ErrorWriteLine(outputWriter, "*** ProverException: {0}", pe.Message);
        options = null;
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }

      if (options.RunLanguageServer) {
        return CommandLineArgumentsResult.OK;
      }

      var nonOutOptions = options;
      var compilers = options.Plugins.SelectMany(p => p.GetCompilers(nonOutOptions)).ToList();
      var compiler = compilers.LastOrDefault(c => c.TargetId == nonOutOptions.CompilerName);
      if (compiler == null) {
        if (nonOutOptions.CompilerName != null) {
          var known = String.Join(", ", compilers.Select(c => $"'{c.TargetId}' ({c.TargetName})"));
          options.Printer.ErrorWriteLine(options.ErrorWriter, $"*** Error: No compiler found for target \"{options.CompilerName}\"{(options.CompilerName.StartsWith("-t") || options.CompilerName.StartsWith("--") ? " (use just a target name, not a -t or --target option)" : "")}; expecting one of {known}");
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        }

        options.Backend = new NoExecutableBackend();
      } else {
        options.Backend = compiler;
      }

      // If requested, print version number, help, attribute help, etc. and exit.
      if (options.ProcessInfoFlags()) {
        return CommandLineArgumentsResult.OK_EXIT_EARLY;
      }

      if (options.UseStdin) {
        var uri = new Uri("stdin:///");
        options.CliRootSourceUris.Add(uri);
        dafnyFiles.Add(new DafnyFile(options, uri));
      } else if (options.CliRootSourceUris.Count == 0 && !options.Format) {
        options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: No input files were specified in command-line " + string.Join("|", args) + ".");
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }
      if (options.XmlSink != null) {
        string errMsg = options.XmlSink.Open();
        if (errMsg != null) {
          options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: " + errMsg);
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        }
      }
      if (options.ShowEnv == ExecutionEngineOptions.ShowEnvironment.Always) {
        outputWriter.WriteLine("---Command arguments");
        foreach (string arg in args) {
          Contract.Assert(arg != null);
          outputWriter.WriteLine(arg);
        }
        outputWriter.WriteLine("--------------------");
      }

      ISet<String> filesSeen = new HashSet<string>();
      foreach (var file in options.CliRootSourceUris.Where(u => u.IsFile).Select(u => u.LocalPath).
                 Concat(SplitOptionValueIntoFiles(options.LibraryFiles))) {
        Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null) { extension = extension.ToLower(); }

        bool isDafnyFile = false;
        var relative = Path.GetFileName(file);
        bool useRelative = options.UseBaseNameForFileName || relative.StartsWith("-");
        var nameToShow = useRelative ? relative
          : Path.GetRelativePath(Directory.GetCurrentDirectory(), file);
        try {
          var df = new DafnyFile(options, new Uri(Path.GetFullPath(file)));
          if (options.LibraryFiles.Contains(file)) {
            df.IsPreverified = true;
            df.IsPrecompiled = true;
          }
          if (!filesSeen.Add(df.CanonicalPath)) {
            continue; // silently ignore duplicate
          }
          dafnyFiles.Add(df);
          isDafnyFile = true;
        } catch (ArgumentException e) {
          options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: {0}: ", nameToShow, e.Message);
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        } catch (IllegalDafnyFile e) {
          if (e.ProcessingError) {
            return CommandLineArgumentsResult.PREPROCESSING_ERROR;
          }
          // Fall through and try to handle the file as an "other file"
        } catch (Exception e) {
          options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: {0}: {1}", nameToShow, e.Message);
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        }

        var supportedExtensions = options.Backend.SupportedExtensions;
        if (supportedExtensions.Contains(extension)) {
          // .h files are not part of the build, they are just emitted as includes
          // TODO: This should be delegated to the backend instead (i.e. the CppCompilerBackend)
          if (File.Exists(file) || extension == ".h") {
            otherFiles.Add(file);
          } else {
            options.Printer.ErrorWriteLine(options.OutputWriter, $"*** Error: file {nameToShow} not found");
            return CommandLineArgumentsResult.PREPROCESSING_ERROR;
          }
        } else if (options.AllowSourceFolders && Directory.Exists(file)) {
          options.SourceFolders.Add(file);
        } else if (!isDafnyFile) {
          if (options.UsingNewCli && string.IsNullOrEmpty(extension) && file.Length > 0) {
            options.Printer.ErrorWriteLine(options.OutputWriter,
              "*** Error: Command-line argument '{0}' is neither a recognized option nor a filename with a supported extension ({1}).",
              nameToShow,
              string.Join(", ", Enumerable.Repeat(".dfy", 1).Concat(supportedExtensions)));
          } else if (string.IsNullOrEmpty(extension) && file.Length > 0 && (file[0] == '/' || file[0] == '-')) {
            options.Printer.ErrorWriteLine(options.OutputWriter,
              "*** Error: Command-line argument '{0}' is neither a recognized option nor a filename with a supported extension ({1}).",
              nameToShow, string.Join(", ", Enumerable.Repeat(".dfy", 1).Concat(supportedExtensions)));
          } else {
            options.Printer.ErrorWriteLine(options.OutputWriter,
              "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or supported auxiliary files ({2})",
              nameToShow, extension, string.Join(", ", supportedExtensions));
          }
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        }
      }

      if (dafnyFiles.Count == 0 && options.SourceFolders.Count == 0) {
        if (!options.AllowSourceFolders) {
          options.Printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files");
          // TODO: With the test on CliRootUris.Count above, this code is no longer reachable
          options.Printer.ErrorWriteLine(options.OutputWriter, "*** Error: The command-line contains no .dfy files");
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        } else {
          options.Printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files or folders");
          //options.Printer.ErrorWriteLine(Console.Out,
          //  "Usage:\ndafny format [--check] [--print] <file/folder> <file/folder>...\nYou can use '.' for the current directory");
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        }
      }

      if (dafnyFiles.Count > 1 &&
          options.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
        options.Printer.ErrorWriteLine(options.OutputWriter,
          "*** Error: Only one .dfy file can be specified for testing");
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }

      if (options.ExtractCounterexample && options.ModelViewFile == null) {
        options.Printer.ErrorWriteLine(options.OutputWriter,
          "*** Error: ModelView file must be specified when attempting counterexample extraction");
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }
      return CommandLineArgumentsResult.OK;
    }

    private async Task<ExitValue> ProcessFilesAsync(IReadOnlyList<DafnyFile/*!*/>/*!*/ dafnyFiles,
      ReadOnlyCollection<string> otherFileNames,
      DafnyOptions options, bool lookForSnapshots = true, string programId = null) {
      Contract.Requires(cce.NonNullElements(dafnyFiles));
      var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);

      ExitValue exitValue = ExitValue.SUCCESS;
      if (options.TestGenOptions.WarnDeadCode) {
        await foreach (var line in DafnyTestGeneration.Main.GetDeadCodeStatistics(dafnyFileNames[0], options)) {
          await options.OutputWriter.WriteLineAsync(line);
        }
        if (DafnyTestGeneration.Main.setNonZeroExitCode) {
          exitValue = ExitValue.DAFNY_ERROR;
        }
        return exitValue;
      }
      if (options.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
        await foreach (var line in DafnyTestGeneration.Main.GetTestClassForProgram(dafnyFileNames[0], options)) {
          await options.OutputWriter.WriteLineAsync(line);
        }
        if (DafnyTestGeneration.Main.setNonZeroExitCode) {
          exitValue = ExitValue.DAFNY_ERROR;
        }
        return exitValue;
      }

      if (options.VerifySeparately && 1 < dafnyFiles.Count) {
        foreach (var f in dafnyFiles) {
          await options.OutputWriter.WriteLineAsync();
          await options.OutputWriter.WriteLineAsync($"-------------------- {f} --------------------");
          var ev = await ProcessFilesAsync(new List<DafnyFile> { f }, new List<string>().AsReadOnly(), options, lookForSnapshots, f.FilePath);
          if (exitValue != ev && ev != ExitValue.SUCCESS) {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      if (0 < options.VerifySnapshots && lookForSnapshots) {
        var snapshotsByVersion = ExecutionEngine.LookForSnapshots(dafnyFileNames);
        foreach (var s in snapshotsByVersion) {
          var snapshots = new List<DafnyFile>();
          foreach (var f in s) {
            var uri = new Uri(Path.GetFullPath(f));
            snapshots.Add(new DafnyFile(options, uri));
            options.CliRootSourceUris.Add(uri);
          }
          var ev = await ProcessFilesAsync(snapshots, new List<string>().AsReadOnly(), options, false, programId);
          if (exitValue != ev && ev != ExitValue.SUCCESS) {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      string programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the_program";
      string err;
      if (options.Format) {
        return DoFormatting(dafnyFiles, options, programName, options.ErrorWriter);
      }
      if (options.Command?.Name == "doc") {
        // dafny doc accepts folders as well as files, so it handles 'dafnyFiles' a bit differently than ParseCheck below
        return DafnyDoc.DoDocumenting(dafnyFiles, options.SourceFolders, programName, options);
      }

      err = DafnyMain.ParseCheck(options.Input, dafnyFiles, programName, options, out var dafnyProgram);
      if (err != null) {
        exitValue = ExitValue.DAFNY_ERROR;
        options.Printer.ErrorWriteLine(options.OutputWriter, err);
      } else if (dafnyProgram != null && !options.NoResolve && !options.NoTypecheck
          && options.DafnyVerify) {

        var boogiePrograms =
          await DafnyMain.LargeStackFactory.StartNew(() => Translate(engine.Options, dafnyProgram).ToList());

        string baseName = cce.NonNull(Path.GetFileName(dafnyFileNames[^1]));
        var (verified, outcome, moduleStats) = await BoogieAsync(options, baseName, boogiePrograms, programId);

        bool compiled;
        try {
          compiled = await Compile(dafnyFileNames[0], otherFileNames, dafnyProgram, outcome, moduleStats, verified);
        } catch (UnsupportedFeatureException e) {
          if (!options.Backend.UnsupportedFeatures.Contains(e.Feature)) {
            throw new Exception($"'{e.Feature}' is not an element of the {options.Backend.TargetId} compiler's UnsupportedFeatures set");
          }
          dafnyProgram.Reporter.Error(MessageSource.Compiler, Compilers.CompilerErrors.ErrorId.f_unsupported_feature, e.Token, e.Message);
          compiled = false;
        }

        exitValue = verified && compiled ? ExitValue.SUCCESS : !verified ? ExitValue.VERIFICATION_ERROR : ExitValue.COMPILE_ERROR;
      }

      if (err == null && dafnyProgram != null && options.PrintStats) {
        Util.PrintStats(dafnyProgram);
      }
      if (err == null && dafnyProgram != null && options.PrintFunctionCallGraph) {
        Util.PrintFunctionCallGraph(dafnyProgram);
      }
      if (dafnyProgram != null && options.ExtractCounterexample && exitValue == ExitValue.VERIFICATION_ERROR) {
        PrintCounterexample(options, options.ModelViewFile);
      }
      return exitValue;
    }

    private static ExitValue DoFormatting(IReadOnlyList<DafnyFile> dafnyFiles, DafnyOptions options, string programName, TextWriter errorWriter) {
      var exitValue = ExitValue.SUCCESS;
      Contract.Assert(dafnyFiles.Count > 0 || options.SourceFolders.Count > 0);
      dafnyFiles = dafnyFiles.Concat(options.SourceFolders.SelectMany(folderPath => {
        return Directory.GetFiles(folderPath, "*.dfy", SearchOption.AllDirectories)
            .Select(name => new DafnyFile(options, new Uri(name))).ToList();
      })).ToList();

      var failedToParseFiles = new List<string>();
      var emptyFiles = new List<string>();
      var doCheck = options.FormatCheck;
      var doPrint = options.DafnyPrintFile == "-";
      options.DafnyPrintFile = null;
      var neededFormatting = 0;
      foreach (var file in dafnyFiles) {
        var dafnyFile = file;
        if (!dafnyFile.Uri.IsFile && !doCheck && !doPrint) {
          errorWriter.WriteLine("Please use the '--check' and/or '--print' option as stdin cannot be formatted in place.");
          exitValue = ExitValue.PREPROCESSING_ERROR;
          continue;
        }

        string tempFileName = null;
        if (!dafnyFile.Uri.IsFile) {
          tempFileName = Path.GetTempFileName() + ".dfy";
          WriteFile(tempFileName, Console.In.ReadToEnd());
          dafnyFile = new DafnyFile(options, new Uri(tempFileName));
        }

        var originalText = dafnyFile.Content.ReadToEnd();
        dafnyFile.Content = new StringReader(originalText);
        // Might not be totally optimized but let's do that for now
        var err = DafnyMain.Parse(new List<DafnyFile> { dafnyFile }, programName, options, out var dafnyProgram);
        if (err != null) {
          exitValue = ExitValue.DAFNY_ERROR;
          errorWriter.WriteLine(err);
          failedToParseFiles.Add(dafnyFile.BaseName);
        } else {
          var firstToken = dafnyProgram.GetFirstTopLevelToken();
          var result = originalText;
          if (firstToken != null) {
            result = Formatting.__default.ReindentProgramFromFirstToken(firstToken,
              IndentationFormatter.ForProgram(dafnyProgram));
            if (result != originalText) {
              neededFormatting += 1;
              if (doCheck) {
                exitValue = exitValue != ExitValue.DAFNY_ERROR ? ExitValue.FORMAT_ERROR : exitValue;
              }

              if (doCheck && (!doPrint || options.Verbose)) {
                options.OutputWriter.WriteLine("The file " +
                                               (options.UseBaseNameForFileName
                                                 ? Path.GetFileName(dafnyFile.FilePath)
                                                 : dafnyFile.FilePath) + " needs to be formatted");
              }

              if (!doCheck && !doPrint) {
                WriteFile(dafnyFile.FilePath, result);
              }
            }
          } else {
            // TODO: is this necessary? there already is a warning about files containing no code
            if (options.Verbose) {
              options.ErrorWriter.WriteLine(dafnyFile.BaseName + " was empty.");
            }

            emptyFiles.Add((options.UseBaseNameForFileName
              ? Path.GetFileName(dafnyFile.FilePath)
              : dafnyFile.FilePath));
          }
          if (doPrint) {
            options.OutputWriter.Write(result);
          }
        }

        if (tempFileName != null) {
          File.Delete(tempFileName);
        }
      }

      string Files(int num) {
        return num + (num != 1 ? " files" : " file");
      }

      // Report any errors
      var reportMsg = "";
      if (failedToParseFiles.Count > 0) {
        reportMsg += $"\n{Files(failedToParseFiles.Count)} failed to parse:\n  " + string.Join("\n  ", failedToParseFiles);
      }
      if (emptyFiles.Count > 0) {
        reportMsg += $"\n{Files(emptyFiles.Count)} {(emptyFiles.Count > 1 ? "were" : "was")} empty:\n  " + string.Join("\n  ", emptyFiles);
      }

      var unchanged = dafnyFiles.Count - failedToParseFiles.Count - emptyFiles.Count - neededFormatting;
      reportMsg += unchanged > 0 && (failedToParseFiles.Count > 0 || emptyFiles.Count > 0) ? $"\n{Files(unchanged)} {(unchanged > 1 ? "were" : "was")} already formatted." : "";
      var filesNeedFormatting = neededFormatting == 0 ? "" : $"{Files(neededFormatting)} need{(neededFormatting > 1 ? "" : "s")} formatting.";
      reportMsg = filesNeedFormatting + reportMsg;

      if (doCheck) {
        options.OutputWriter.WriteLine(neededFormatting > 0
          ? $"Error: {reportMsg}"
          : "All files are correctly formatted");
      } else if (failedToParseFiles.Count > 0 || options.Verbose) {
        // We don't display anything if we just format files without verbosity and there was no parse error
        options.OutputWriter.WriteLine($"{reportMsg}");
      }

      return exitValue;
    }

    /// <summary>
    /// Extract the counterexample corresponding to the first failing
    /// assertion and print it to the console
    /// </summary>
    /// <param name="modelViewFile"> Name of the file from which to read
    /// the counterexample </param> 
    private static void PrintCounterexample(DafnyOptions options, string modelViewFile) {
      var model = DafnyModel.ExtractModel(options, File.ReadAllText(modelViewFile));
      options.OutputWriter.WriteLine("Counterexample for first failing assertion: ");
      foreach (var state in model.States.Where(state => !state.IsInitialState)) {
        options.OutputWriter.WriteLine(state.FullStateName + ":");
        var vars = state.ExpandedVariableSet(-1);
        foreach (var variable in vars) {
          options.OutputWriter.WriteLine($"\t{variable.ShortName} : " +
                                   $"{DafnyModelTypeUtils.GetInDafnyFormat(variable.Type)} = " +
                                   $"{variable.Value}");
        }
      }
    }

    private static string BoogieProgramSuffix(string printFile, string suffix) {
      var baseName = Path.GetFileNameWithoutExtension(printFile);
      var dirName = Path.GetDirectoryName(printFile);

      return Path.Combine(dirName, baseName + "_" + suffix + Path.GetExtension(printFile));
    }

    public static IEnumerable<Tuple<string, Bpl.Program>> Translate(ExecutionEngineOptions options, Program dafnyProgram) {
      var nmodules = Translator.VerifiableModules(dafnyProgram).Count();


      foreach (var prog in Translator.Translate(dafnyProgram, dafnyProgram.Reporter)) {

        if (options.PrintFile != null) {

          var nm = nmodules > 1 ? Dafny.DafnyMain.BoogieProgramSuffix(options.PrintFile, prog.Item1) : options.PrintFile;

          ExecutionEngine.PrintBplFile(options, nm, prog.Item2, false, false, options.PrettyPrint);
        }

        yield return prog;

      }
    }

    public async Task<(bool IsVerified, PipelineOutcome Outcome, IDictionary<string, PipelineStatistics> ModuleStats)>
      BoogieAsync(DafnyOptions options,
        string baseName,
        IEnumerable<Tuple<string, Bpl.Program>> boogiePrograms, string programId) {

      var concurrentModuleStats = new ConcurrentDictionary<string, PipelineStatistics>();
      var writerManager = new ConcurrentToSequentialWriteManager(options.OutputWriter);

      var moduleTasks = boogiePrograms.Select(async program => {
        await using var moduleWriter = writerManager.AppendWriter();
        // ReSharper disable once AccessToDisposedClosure
        var result = await Task.Run(() =>
          BoogieOnceWithTimerAsync(moduleWriter, options, baseName, programId, program.Item1, program.Item2));
        concurrentModuleStats.TryAdd(program.Item1, result.Stats);
        return result;
      }).ToList();

      await Task.WhenAll(moduleTasks);
      await options.OutputWriter.FlushAsync();
      var outcome = moduleTasks.Select(t => t.Result.Outcome)
        .Aggregate(PipelineOutcome.VerificationCompleted, MergeOutcomes);

      var isVerified = moduleTasks.Select(t =>
        Dafny.DafnyMain.IsBoogieVerified(t.Result.Outcome, t.Result.Stats)).All(x => x);
      return (isVerified, outcome, concurrentModuleStats);
    }

    private async Task<(PipelineOutcome Outcome, PipelineStatistics Stats)> BoogieOnceWithTimerAsync(
      TextWriter output,
      DafnyOptions options,
      string baseName, string programId,
      string moduleName,
      Bpl.Program program) {
      Stopwatch watch = new Stopwatch();
      watch.Start();
      if (options.SeparateModuleOutput) {
        options.Printer.AdvisoryWriteLine(output, "For module: {0}", moduleName);
      }

      var result =
        await Dafny.DafnyMain.BoogieOnce(options, output, engine, baseName, moduleName, program, programId);

      watch.Stop();

      if (options.SeparateModuleOutput) {
        TimeSpan ts = watch.Elapsed;
        string elapsedTime = $"{ts.Hours:00}:{ts.Minutes:00}:{ts.Seconds:00}";
        options.Printer.AdvisoryWriteLine(output, "Elapsed time: {0}", elapsedTime);
        WriteTrailer(options, output, result.Statistics);
      }

      return result;
    }

    private static PipelineOutcome MergeOutcomes(PipelineOutcome first, PipelineOutcome second) {

      if ((first == PipelineOutcome.VerificationCompleted || first == PipelineOutcome.Done) &&
          second != PipelineOutcome.VerificationCompleted) {
        return second;
      }

      return first;
    }

    private static void WriteTrailer(DafnyOptions options, TextWriter output, PipelineStatistics stats) {
      if (!options.Verify && stats.ErrorCount == 0) {
        output.WriteLine();
        output.Write("{0} did not attempt verification", options.DescriptiveToolName);
        if (stats.InconclusiveCount != 0) {
          output.Write(", {0} inconclusive{1}", stats.InconclusiveCount, Util.Plural(stats.InconclusiveCount));
        }
        if (stats.TimeoutCount != 0) {
          output.Write(", {0} time out{1}", stats.TimeoutCount, Util.Plural(stats.TimeoutCount));
        }
        if (stats.OutOfMemoryCount != 0) {
          output.Write(", {0} out of memory", stats.OutOfMemoryCount);
        }
        if (stats.OutOfResourceCount != 0) {
          output.Write(", {0} out of resource", stats.OutOfResourceCount);
        }
        if (stats.SolverExceptionCount != 0) {
          output.Write(", {0} solver exceptions", stats.SolverExceptionCount);
        }

        output.WriteLine();
        output.Flush();
      } else {
        // This calls a routine within Boogie
        options.Printer.WriteTrailer(output, stats);
      }
    }

    private static void WriteModuleStats(DafnyOptions options, TextWriter output, IDictionary<string, PipelineStatistics> moduleStats) {
      var statSum = new PipelineStatistics();
      foreach (var stats in moduleStats) {
        statSum.VerifiedCount += stats.Value.VerifiedCount;
        statSum.ErrorCount += stats.Value.ErrorCount;
        statSum.TimeoutCount += stats.Value.TimeoutCount;
        statSum.OutOfResourceCount += stats.Value.OutOfResourceCount;
        statSum.OutOfMemoryCount += stats.Value.OutOfMemoryCount;
        statSum.SolverExceptionCount += stats.Value.SolverExceptionCount;
        statSum.CachedErrorCount += stats.Value.CachedErrorCount;
        statSum.CachedInconclusiveCount += stats.Value.CachedInconclusiveCount;
        statSum.CachedOutOfMemoryCount += stats.Value.CachedOutOfMemoryCount;
        statSum.CachedTimeoutCount += stats.Value.CachedTimeoutCount;
        statSum.CachedOutOfResourceCount += stats.Value.CachedOutOfResourceCount;
        statSum.CachedSolverExceptionCount += stats.Value.CachedSolverExceptionCount;
        statSum.CachedVerifiedCount += stats.Value.CachedVerifiedCount;
        statSum.InconclusiveCount += stats.Value.InconclusiveCount;
      }
      WriteTrailer(options, output, statSum);
    }


    public static async Task<bool> Compile(string fileName, ReadOnlyCollection<string> otherFileNames, Program dafnyProgram,
                               PipelineOutcome oc, IDictionary<string, PipelineStatistics> moduleStats, bool verified) {
      var options = dafnyProgram.Options;
      var resultFileName = options.DafnyPrintCompiledFile ?? fileName;
      bool compiled = true;
      switch (oc) {
        case PipelineOutcome.VerificationCompleted:
          WriteModuleStats(options, options.OutputWriter, moduleStats);
          if ((options.Compile && verified && !options.UserConstrainedProcsToCheck) || options.ForceCompile) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, true);
          } else if ((2 <= options.SpillTargetCode && verified && !options.UserConstrainedProcsToCheck) || 3 <= options.SpillTargetCode) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, false);
          }
          break;
        case PipelineOutcome.Done:
          WriteModuleStats(options, options.OutputWriter, moduleStats);
          if (options.ForceCompile || 3 <= options.SpillTargetCode) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, options.ForceCompile);
          }
          break;
        default:
          // error has already been reported to user
          break;
      }
      return compiled;
    }

    #region Compilation

    private record TargetPaths(string Directory, string Filename) {
      private static Func<string, string> DeleteDot = p => p == "." ? "" : p;
      private static Func<string, string> AddDot = p => p == "" ? "." : p;
      private Func<string, string> RelativeToDirectory =
        path => DeleteDot(Path.GetRelativePath(AddDot(Directory), path));

      public string RelativeDirectory => RelativeToDirectory(AddDot(Path.GetDirectoryName(Filename)));
      public string RelativeFilename => RelativeToDirectory(Filename);
      public string SourceDirectory => Path.GetDirectoryName(Filename);
    }

    private static TargetPaths GenerateTargetPaths(DafnyOptions options, string dafnyProgramName) {
      string targetBaseDir = options.Backend.TargetBaseDir(dafnyProgramName);
      string targetExtension = options.Backend.TargetExtension;

      // Note that using Path.ChangeExtension here does the wrong thing when dafnyProgramName has multiple periods (e.g., a.b.dfy)
      string targetBaseName = options.Backend.TargetBasename(dafnyProgramName) + "." + targetExtension;
      string targetDir = Path.Combine(Path.GetDirectoryName(dafnyProgramName), targetBaseDir);

      string targetFilename = Path.Combine(targetDir, targetBaseName);

      return new TargetPaths(Directory: Path.GetDirectoryName(dafnyProgramName), Filename: targetFilename);
    }

    static void WriteDafnyProgramToFiles(DafnyOptions options, TargetPaths paths, bool targetProgramHasErrors, string targetProgramText,
      string/*?*/ callToMain, Dictionary<string, string> otherFiles, TextWriter outputWriter) {
      if (targetProgramText.Length != 0) {
        WriteFile(paths.Filename, targetProgramText, callToMain);
      }

      string NormalizeRelativeFilename(string fileName) {
        return RuntimeInformation.IsOSPlatform(OSPlatform.Windows)
          ? fileName.Replace(@"\", "/")
          : fileName;
      }

      var relativeTarget = NormalizeRelativeFilename(paths.RelativeFilename);
      if (targetProgramHasErrors) {
        // Something went wrong during compilation (e.g., the compiler may have found an "assume" statement).
        // As a courtesy, we're still printing the text of the generated target program. We print a message regardless
        // of the Verbose settings.
        outputWriter.WriteLine("Wrote textual form of partial target program to {0}", relativeTarget);
      } else if (options.Verbose) {
        outputWriter.WriteLine("Wrote textual form of target program to {0}", relativeTarget);
      }

      foreach (var entry in otherFiles) {
        var filename = entry.Key;
        WriteFile(Path.Join(paths.SourceDirectory, filename), entry.Value);
        if (options.Verbose) {
          outputWriter.WriteLine("Additional target code written to {0}", NormalizeRelativeFilename(Path.Join(paths.RelativeDirectory, filename)));
        }
      }
    }

    static void WriteFile(string filename, string text, string moreText = null) {
      var dir = Path.GetDirectoryName(filename);
      if (dir != "") {
        Directory.CreateDirectory(dir);
      }

      CheckFilenameIsLegal(filename);
      using TextWriter target = new StreamWriter(new FileStream(filename, FileMode.Create));
      target.Write(text);
      if (moreText != null) {
        target.Write(moreText);
      }
    }

    private static void CheckFilenameIsLegal(string filename) {
      // We cannot get the full path correctly on Windows if the file name uses some reserved words
      // For example, Path.GetFullPath("con.txt") will return "//./con" which is incorrect.
      // https://docs.microsoft.com/en-us/windows/win32/fileio/naming-a-file?redirectedfrom=MSDN
      if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
        var problematicNames =
          "CON, PRN, AUX, NUL, COM1, COM2, COM3, COM4, COM5, COM6, COM7, COM8, COM9, LPT1, LPT2, LPT3, LPT4, LPT5, LPT6, LPT7, LPT8, LPT9";
        var problematicRegex =
          new Regex(@"^(.*[/\\]|^)(" +
                    string.Join("|", problematicNames.Split(", ")) + @")(\.[^/\\]*)?$", RegexOptions.IgnoreCase);
        var match = problematicRegex.Match(filename);
        if (match.Success) {
          throw new Exception($"Cannot create a file with the name {filename}." +
                              $" Windows reserves the following file names: {problematicNames}");
        }
      }
    }

    /// <summary>
    /// Generate a C# program from the Dafny program and, if "invokeCompiler" is "true", invoke
    /// the C# compiler to compile it.
    /// </summary>
    public static async Task<bool> CompileDafnyProgram(Program dafnyProgram, string dafnyProgramName,
                                           ReadOnlyCollection<string> otherFileNames, bool invokeCompiler) {

      foreach (var rewriter in dafnyProgram.Compilation.Rewriters) {
        rewriter.PostVerification(dafnyProgram);
      }

      Contract.Requires(dafnyProgram != null);
      Contract.Assert(dafnyProgramName != null);

      var outputWriter = dafnyProgram.Options.OutputWriter;
      var errorWriter = dafnyProgram.Options.ErrorWriter;

      // Compile the Dafny program into a string that contains the target program
      var oldErrorCount = dafnyProgram.Reporter.Count(ErrorLevel.Error);
      var options = dafnyProgram.Options;
      options.Backend.OnPreCompile(dafnyProgram.Reporter, otherFileNames);
      var compiler = options.Backend;

      var hasMain = Compilers.SinglePassCompiler.HasMain(dafnyProgram, out var mainMethod);
      if (hasMain) {
        mainMethod.IsEntryPoint = true;
        dafnyProgram.MainMethod = mainMethod;
      }
      string targetProgramText;
      var otherFiles = new Dictionary<string, string>();
      {
        var output = new ConcreteSyntaxTree();
        await DafnyMain.LargeStackFactory.StartNew(() => compiler.Compile(dafnyProgram, output));
        var writerOptions = new WriterState();
        var targetProgramTextWriter = new StringWriter();
        var files = new Queue<FileSyntax>();
        output.Render(targetProgramTextWriter, 0, writerOptions, files, compiler.TargetIndentSize);
        targetProgramText = targetProgramTextWriter.ToString();

        while (files.Count > 0) {
          var file = files.Dequeue();
          var otherFileWriter = new StringWriter();
          writerOptions.HasNewLine = false;
          file.Tree.Render(otherFileWriter, 0, writerOptions, files, compiler.TargetIndentSize);
          otherFiles.Add(file.Filename, otherFileWriter.ToString());
        }
      }
      string callToMain = null;
      if (hasMain) {
        var callToMainTree = new ConcreteSyntaxTree();
        string baseName = Path.GetFileNameWithoutExtension(dafnyProgramName);
        compiler.EmitCallToMain(mainMethod, baseName, callToMainTree);
        callToMain = callToMainTree.MakeString(compiler.TargetIndentSize); // assume there aren't multiple files just to call main
      }
      Contract.Assert(hasMain == (callToMain != null));
      bool targetProgramHasErrors = dafnyProgram.Reporter.Count(ErrorLevel.Error) != oldErrorCount;

      compiler.OnPostCompile();

      // blurt out the code to a file, if requested, or if other target-language files were specified on the command line.
      var paths = GenerateTargetPaths(options, dafnyProgramName);
      if (options.SpillTargetCode > 0 || otherFileNames.Count > 0 || (invokeCompiler && !compiler.SupportsInMemoryCompilation) ||
          (invokeCompiler && compiler.TextualTargetIsExecutable && !options.RunAfterCompile)) {
        compiler.CleanSourceDirectory(paths.SourceDirectory);
        WriteDafnyProgramToFiles(options, paths, targetProgramHasErrors, targetProgramText, callToMain, otherFiles, outputWriter);
      }

      if (targetProgramHasErrors) {
        return false;
      }
      // If we got here, compilation succeeded
      if (!invokeCompiler) {
        return true; // If we're not asked to invoke the target compiler, we can report success
      }

      // compile the program into an assembly
      var compiledCorrectly = compiler.CompileTargetProgram(dafnyProgramName, targetProgramText, callToMain, paths.Filename, otherFileNames,
        hasMain && options.RunAfterCompile, outputWriter, out var compilationResult);
      if (compiledCorrectly && options.RunAfterCompile) {
        if (hasMain) {
          if (options.Verbose) {
            await outputWriter.WriteLineAsync("Running...");
            await outputWriter.WriteLineAsync();
          }

          compiledCorrectly = compiler.RunTargetProgram(dafnyProgramName, targetProgramText, callToMain,
            paths.Filename, otherFileNames, compilationResult, outputWriter, errorWriter);
        } else {
          // make sure to give some feedback to the user
          if (options.Verbose) {
            await outputWriter.WriteLineAsync("Program compiled successfully");
          }
        }
      }
      return compiledCorrectly;
    }

    #endregion

  }

  class NoExecutableBackend : IExecutableBackend {
    public override IReadOnlySet<string> SupportedExtensions => new HashSet<string>();
    public override string TargetName => throw new NotSupportedException();
    public override string TargetExtension => throw new NotSupportedException();
    public override string PublicIdProtect(string name) {
      throw new NotSupportedException();
    }

    public override bool TextualTargetIsExecutable => throw new NotSupportedException();

    public override bool SupportsInMemoryCompilation => throw new NotSupportedException();
    public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
      throw new NotSupportedException();
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
      throw new NotSupportedException();
    }

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string pathsFilename,
      ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      throw new NotSupportedException();
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
      string pathsFilename,
      ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter,
      TextWriter errorWriter) {
      throw new NotSupportedException();
    }
  }
}
