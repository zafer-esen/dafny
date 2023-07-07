using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit.Abstractions;
using Xunit;
using XunitAssertMessages;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class ClientBasedLanguageServerTest : DafnyLanguageServerTestBase, IAsyncLifetime {
  protected ILanguageClient client;
  protected TestNotificationReceiver<FileVerificationStatus> verificationStatusReceiver;
  protected DiagnosticsReceiver diagnosticsReceiver;
  protected TestNotificationReceiver<GhostDiagnosticsParams> ghostnessReceiver;

  private const int MaxRequestExecutionTimeMs = 180_000;

  // We do not use the LanguageServerTestBase.cancellationToken here because it has a timeout.
  // Since these tests are slow, we do not use the timeout here.
  private CancellationTokenSource cancellationSource;

  protected CancellationToken CancellationTokenWithHighTimeout => cancellationSource.Token;

  public async Task<NamedVerifiableStatus> WaitForStatus(Range nameRange, PublishedVerificationStatus statusToFind,
    CancellationToken cancellationToken) {
    while (true) {
      var foundStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
      var namedVerifiableStatus = foundStatus.NamedVerifiables.FirstOrDefault(n => n.NameRange == nameRange);
      if (namedVerifiableStatus?.Status == statusToFind) {
        return namedVerifiableStatus;
      }
    }
  }

  public async Task<IEnumerable<DocumentSymbol>> RequestDocumentSymbol(TextDocumentItem documentItem) {
    var things = await client.RequestDocumentSymbol(
      new DocumentSymbolParams {
        TextDocument = documentItem.Uri,
      },
      CancellationToken
    ).ToTask();

    return things.Select(t => t.DocumentSymbol!);
  }

  public async Task<Diagnostic[]> GetLastDiagnostics(TextDocumentItem documentItem, CancellationToken cancellationToken) {
    await client.WaitForNotificationCompletionAsync(documentItem.Uri, cancellationToken);
    var document = (await Projects.GetLastDocumentAsync(documentItem))!;
    Assert.NotNull(document);
    Assert.Equal(documentItem.Version, document.Version);
    Diagnostic[] result;
    do {
      result = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(cancellationToken);
    } while (!document!.AllFileDiagnostics.Select(d => d.ToLspDiagnostic()).SequenceEqual(result));

    return result;
  }

  public virtual Task InitializeAsync() {
    return SetUp(null);
  }

  public Task DisposeAsync() {
    return Task.CompletedTask;
  }

  protected virtual async Task SetUp(Action<DafnyOptions> modifyOptions) {

    // We use a custom cancellation token with a higher timeout to clearly identify where the request got stuck.
    cancellationSource = new();
    cancellationSource.CancelAfter(MaxRequestExecutionTimeMs);

    diagnosticsReceiver = new();
    verificationStatusReceiver = new();
    ghostnessReceiver = new();
    client = await InitializeClient(InitialiseClientHandler, modifyOptions);
  }

  protected virtual void InitialiseClientHandler(LanguageClientOptions options) {
    options.OnPublishDiagnostics(diagnosticsReceiver.NotificationReceived);
    options.AddHandler(DafnyRequestNames.GhostDiagnostics,
      NotificationHandler.For<GhostDiagnosticsParams>(ghostnessReceiver.NotificationReceived));
    options.AddHandler(DafnyRequestNames.VerificationSymbolStatus,
      NotificationHandler.For<FileVerificationStatus>(verificationStatusReceiver.NotificationReceived));
  }

  protected void ApplyChange(ref TextDocumentItem documentItem, Range range, string text) {
    documentItem = documentItem with { Version = documentItem.Version + 1 };
    client.DidChangeTextDocument(new DidChangeTextDocumentParams {
      TextDocument = new OptionalVersionedTextDocumentIdentifier {
        Uri = documentItem.Uri,
        Version = documentItem.Version
      },
      ContentChanges = new[] {
        new TextDocumentContentChangeEvent {
          Range = range,
          Text = text
        }
      }
    });
  }

  public async Task AssertNoVerificationStatusIsComing(TextDocumentItem documentItem, CancellationToken cancellationToken) {
    foreach (var entry in Projects.Managers) {
      try {
        await entry.GetLastDocumentAsync();
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument("method Foo() { assert false; }", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    var statusReport = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.Equal(verificationDocumentItem.Uri, statusReport.Uri);
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
  }

  public async Task AssertNoGhostnessIsComing(CancellationToken cancellationToken) {
    foreach (var entry in Projects.Managers) {
      try {
        await entry.GetLastDocumentAsync();
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument(@"class X {does not parse", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    AssertM.Equal(verificationDocumentItem.Uri, resolutionReport.Uri,
      "Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", resolutionReport.Diagnostics.Select(diagnostic =>
        diagnostic.ToString())));
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.Equal(verificationDocumentItem.Uri, hideReport.Uri);
  }

  public async Task AssertNoDiagnosticsAreComing(CancellationToken cancellationToken) {
    foreach (var entry in Projects.Managers) {
      try {
        await entry.GetLastDocumentAsync();
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument("class X {does not parse", $"AssertNoDiagnosticsAreComing{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    AssertM.Equal(verificationDocumentItem.Uri, resolutionReport.Uri,
      "1) Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", resolutionReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    AssertM.Equal(verificationDocumentItem.Uri, hideReport.Uri,
      "2) Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", hideReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
  }

  protected async Task AssertNoResolutionErrors(TextDocumentItem documentItem) {
    var resolutionDiagnostics = (await Projects.GetResolvedDocumentAsync(documentItem))!.Diagnostics.ToList();
    var resolutionErrors = resolutionDiagnostics.Count(d => d.Severity == DiagnosticSeverity.Error);
    if (0 != resolutionErrors) {
      await Console.Out.WriteAsync(string.Join("\n", resolutionDiagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.ToString())));
      Assert.Equal(0, resolutionErrors);
    }
  }

  public async Task<PublishedVerificationStatus> PopNextStatus() {
    var nextNotification = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.NotNull(nextNotification);
    Assert.Equal(1, nextNotification.NamedVerifiables.Count);
    return nextNotification.NamedVerifiables.Single().Status;
  }

  public ClientBasedLanguageServerTest(ITestOutputHelper output) : base(output) {
  }
}
