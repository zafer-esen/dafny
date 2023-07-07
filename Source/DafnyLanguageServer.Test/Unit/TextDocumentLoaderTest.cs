﻿using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Moq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {
  public class TextDocumentLoaderTest {
    private readonly TextWriter output;

    private Mock<IFileSystem> fileSystem;
    private Mock<IDafnyParser> parser;
    private Mock<ISymbolResolver> symbolResolver;
    private Mock<ISymbolTableFactory> symbolTableFactory;
    private Mock<IGhostStateDiagnosticCollector> ghostStateDiagnosticCollector;
    private Mock<ICompilationStatusNotificationPublisher> notificationPublisher;
    private TextDocumentLoader textDocumentLoader;
    private Mock<ILoggerFactory> logger;
    private Mock<INotificationPublisher> diagnosticPublisher;

    public TextDocumentLoaderTest(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
      parser = new();
      symbolResolver = new();
      symbolTableFactory = new();
      ghostStateDiagnosticCollector = new();
      notificationPublisher = new();
      fileSystem = new();
      logger = new Mock<ILoggerFactory>();
      diagnosticPublisher = new Mock<INotificationPublisher>();
      textDocumentLoader = TextDocumentLoader.Create(
        DafnyOptions.Create(this.output, TextReader.Null),
        parser.Object,
        symbolResolver.Object,
        symbolTableFactory.Object,
        ghostStateDiagnosticCollector.Object,
        notificationPublisher.Object,
        logger.Object,
        diagnosticPublisher.Object
      );
    }

    private static VersionedTextDocumentIdentifier CreateTestDocumentId() {
      return new VersionedTextDocumentIdentifier() {
        Uri = DocumentUri.Parse("untitled:untitled1"),
        Version = 1,
      };
    }

    private static DocumentTextBuffer CreateTestDocument() {
      return new DocumentTextBuffer(new TextDocumentItem() {
        Uri = DocumentUri.Parse("untitled:untitled1"),
        LanguageId = "dafny",
        Version = 1,
        Text = ""
      });
    }

    [Fact]
    public async Task LoadReturnsCanceledTaskIfOperationIsCanceled() {
      var source = new CancellationTokenSource();
      parser.Setup(p => p.Parse(
          It.IsAny<VersionedTextDocumentIdentifier>(),
          It.IsAny<IFileSystem>(),
          It.IsAny<ErrorReporter>(),
          It.IsAny<CancellationToken>())).Callback(() => source.Cancel())
        .Throws<TaskCanceledException>();
      var task = textDocumentLoader.LoadAsync(DafnyOptions.Default, CreateTestDocumentId(), fileSystem.Object, source.Token);
      try {
        await task;
        Assert.Fail("document load was not cancelled");
      } catch (Exception e) {
        Assert.IsType<TaskCanceledException>(e);
        Assert.True(task.IsCanceled);
        Assert.False(task.IsFaulted);
      }
    }

    [Fact]
    public async Task LoadReturnsFaultedTaskIfAnyExceptionOccured() {
      parser.Setup(p => p.Parse(It.IsAny<VersionedTextDocumentIdentifier>(),
          It.IsAny<IFileSystem>(),
          It.IsAny<ErrorReporter>(),
          It.IsAny<CancellationToken>()))
        .Throws<InvalidOperationException>();
      var task = textDocumentLoader.LoadAsync(DafnyOptions.Default, CreateTestDocumentId(), fileSystem.Object, default);
      try {
        await task;
        Assert.Fail("document load did not fail");
      } catch (Exception e) {
        Assert.IsType<InvalidOperationException>(e);
        Assert.False(task.IsCanceled);
        Assert.True(task.IsFaulted);
      }
    }
  }
}
