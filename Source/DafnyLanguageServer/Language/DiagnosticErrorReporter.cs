using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol;
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Threading;
using VCGeneration;

namespace Microsoft.Dafny.LanguageServer.Language {
  public class DiagnosticErrorReporter : ErrorReporter {
    private const MessageSource VerifierMessageSource = MessageSource.Verifier;
    private const string RelatedLocationCategory = "Related location";
    private const string RelatedLocationMessage = RelatedLocationCategory;

    private readonly DocumentUri entryDocumentUri;
    private readonly Dictionary<DocumentUri, List<DafnyDiagnostic>> diagnostics = new();
    private readonly Dictionary<ErrorLevel, int> counts = new();
    private readonly Dictionary<ErrorLevel, int> countsNotVerificationOrCompiler = new();
    private readonly ReaderWriterLockSlim rwLock = new();

    /// <summary>
    /// Creates a new instance with the given uri of the entry document.
    /// </summary>
    /// <param name="entryDocumentUri">The entry document's uri.</param>
    /// <remarks>
    /// The uri of the entry document is necessary to report general compiler errors as part of this document.
    /// </remarks>
    public DiagnosticErrorReporter(DafnyOptions options, DocumentUri entryDocumentUri) : base(options) {
      this.entryDocumentUri = entryDocumentUri;
    }

    public IReadOnlyDictionary<DocumentUri, List<DafnyDiagnostic>> AllDiagnosticsCopy => diagnostics.ToImmutableDictionary();

    public IReadOnlyList<DafnyDiagnostic> GetDiagnostics(DocumentUri documentUri) {
      rwLock.EnterReadLock();
      try {
        // Concurrency: Return a copy of the list not to expose a reference to an object that requires synchronization.
        // LATER: Make the Diagnostic type immutable, since we're not protecting it from concurrent accesses
        return new List<DafnyDiagnostic>(
          diagnostics.GetValueOrDefault(documentUri) ??
          Enumerable.Empty<DafnyDiagnostic>());
      }
      finally {
        rwLock.ExitReadLock();
      }
    }

    public void ReportBoogieError(ErrorInformation error) {
      var relatedInformation = new List<DafnyRelatedInformation>();
      foreach (var auxiliaryInformation in error.Aux) {
        if (auxiliaryInformation.Category == RelatedLocationCategory) {
          relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(Translator.ToDafnyToken(auxiliaryInformation.Tok), auxiliaryInformation.Msg));
        } else {
          // The execution trace is an additional auxiliary which identifies itself with
          // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
          // the execution trace message appears to not have any interesting information.
          if (auxiliaryInformation.Tok.line > 0) {
            Info(VerifierMessageSource, Translator.ToDafnyToken(auxiliaryInformation.Tok), auxiliaryInformation.Msg);
          }
        }
      }

      if (error.Tok is NestedToken { Inner: var innerToken }) {
        relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(innerToken, "Related location"));
      }

      var dafnyToken = Translator.ToDafnyToken(error.Tok);
      var uri = GetDocumentUriOrDefault(dafnyToken);
      var dafnyDiagnostic = new DafnyDiagnostic(null, dafnyToken, error.Msg,
        VerifierMessageSource, ErrorLevel.Error, relatedInformation);
      AddDiagnosticForFile(
        dafnyDiagnostic,
        VerifierMessageSource,
        uri
      );
    }

    public static readonly string PostConditionFailingMessage = new ProofObligationDescription.EnsuresDescription(null, null).FailureDescription;

    public static string FormatRelated(string related) {
      return $"Could not prove: {related}";
    }

    private IEnumerable<DafnyRelatedInformation> CreateDiagnosticRelatedInformationFor(IToken token, string message) {
      var (tokenForMessage, inner) = token is NestedToken nestedToken ? (nestedToken.Outer, nestedToken.Inner) : (token, null);
      if (tokenForMessage is BoogieRangeToken range) {
        if (message == PostConditionFailingMessage) {
          var postcondition = range.PrintOriginal();
          message = $"This postcondition might not hold: {postcondition}";
        } else if (message == "Related location") {
          message = FormatRelated(range.PrintOriginal());
        }
      }

      yield return new DafnyRelatedInformation(token, message);
      if (inner != null) {
        foreach (var nestedInformation in CreateDiagnosticRelatedInformationFor(inner, RelatedLocationMessage)) {
          yield return nestedInformation;
        }
      }
    }

    public override bool Message(MessageSource source, ErrorLevel level, string? errorId, IToken rootTok, string msg) {
      if (ErrorsOnly && level != ErrorLevel.Error) {
        return false;
      }
      var relatedInformation = new List<DafnyRelatedInformation>();
      var tok = rootTok;
      while (tok is NestedToken nestedToken) {
        tok = nestedToken.Inner;
        if (!(tok is RangeToken)) {
          relatedInformation.AddRange(
            CreateDiagnosticRelatedInformationFor(
              tok, nestedToken.Message ?? "Related location")
          );
          break;
        }
      }

      var dafnyDiagnostic = new DafnyDiagnostic(errorId, rootTok, msg, source, level, relatedInformation);
      AddDiagnosticForFile(dafnyDiagnostic, source, GetDocumentUriOrDefault(rootTok));
      return true;
    }

    public override int Count(ErrorLevel level) {
      rwLock.EnterReadLock();
      try {
        return counts.GetValueOrDefault(level, 0);
      }
      finally {
        rwLock.ExitReadLock();
      }
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      rwLock.EnterReadLock();
      try {
        return countsNotVerificationOrCompiler.GetValueOrDefault(level, 0);
      }
      finally {
        rwLock.ExitReadLock();
      }
    }

    private void AddDiagnosticForFile(DafnyDiagnostic dafnyDiagnostic, MessageSource messageSource, DocumentUri documentUri) {
      rwLock.EnterWriteLock();
      try {
        counts[dafnyDiagnostic.Level] = counts.GetValueOrDefault(dafnyDiagnostic.Level, 0) + 1;
        if (messageSource != MessageSource.Verifier && messageSource != MessageSource.Compiler) {
          countsNotVerificationOrCompiler[dafnyDiagnostic.Level] =
            countsNotVerificationOrCompiler.GetValueOrDefault(dafnyDiagnostic.Level, 0) + 1;
        }
        diagnostics.GetOrCreate(documentUri, () => new List<DafnyDiagnostic>()).Add(dafnyDiagnostic);
      }
      finally {
        rwLock.ExitWriteLock();
      }
    }

    private DocumentUri GetDocumentUriOrDefault(IToken token) {
      return token.Filepath == null
        ? entryDocumentUri
        : token.GetDocumentUri();
    }
  }
}
