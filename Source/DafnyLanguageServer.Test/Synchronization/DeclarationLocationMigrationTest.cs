﻿using System.IO;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class DeclarationLocationMigrationTest : SynchronizationTestBase {
    // The assertion Assert.False(document.SymbolTable.Resolved) is used to ensure that
    // we're working on a migrated symbol table. If that's not the case, the test case has
    // to be adapted.

    // TODO The Declaration Range currently does not incorporate keywords such as "class" and "var".
    // TODO The "BodyEndToken" used by the CreateDeclarationDictionary.CreateDeclarationDictionary()
    //      does not incorporate the closing braces.

    private bool TryFindSymbolDeclarationByName(IdeState state, string symbolName, out SymbolLocation location) {
      location = state.SignatureAndCompletionTable.Locations
        .WithCancellation(CancellationToken)
        .Where(entry => entry.Key.Name == symbolName)
        .Select(entry => entry.Value)
        .SingleOrDefault();
      return location != null;
    }

    [Fact]
    public async Task MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenChangingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = @"
class B {
  var x: int;

  function GetX()
}";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 0), (4, 1)),
        change
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.Equal(new Range((0, 6), (0, 7)), location.Name);
      Assert.Equal(new Range((0, 0), (1, 0)), location.Declaration);
    }

    [Fact]
    public async Task MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenRemovingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = "";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 0), (4, 0)),
        change
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.Equal(new Range((0, 6), (0, 7)), location.Name);
      Assert.Equal(new Range((0, 0), (1, 0)), location.Declaration);
    }

    [Fact]
    public async Task MigrationMovesLinesOfSymbolsAfterWhenChangingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = @"
class B {
  var x: int;

  function GetX()
}";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 0), (4, 1)),
        change
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "C", out var location));
      Assert.Equal(new Range((10, 6), (10, 7)), location.Name);
      Assert.Equal(new Range((10, 0), (11, 0)), location.Declaration);
    }

    [Fact]
    public async Task MigrationMovesLinesOfSymbolsAfterWhenRemovingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = "";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 0), (4, 0)),
        change
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "C", out var location));
      Assert.Equal(new Range((5, 6), (5, 7)), location.Name);
      Assert.Equal(new Range((5, 0), (6, 0)), location.Declaration);
    }

    [Fact]
    public async Task MigrationLeavesLocationUnchangedWhenChangingAtTheEndOfTheSignature() {
      var source = @"
class A {
  var x: int;

  function GetX(): int {
    x
  }
}".TrimStart();

      var change = "string reads thi";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 19), (3, 22)),
        change
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "GetX", out var location));
      Assert.Equal(new Range((3, 11), (3, 15)), location.Name);
      Assert.Equal(new Range((3, 2), (5, 2)), location.Declaration);
    }

    [Fact]
    public async Task MigrationExpandsDeclarationRangeWhenChangingTheContents() {
      var source = @"
class A {
  var x: int;
}".TrimStart();

      var change = @"var y: int;

  function GetY()";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((1, 2), (1, 13)),
        change
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.Equal(new Range((0, 6), (0, 7)), location.Name);
      Assert.Equal(new Range((0, 0), (4, 0)), location.Declaration);
    }

    [Fact]
    public async Task MigrationExpandsDeclarationRangeWhenChangingTheContentsOnTheSameLine() {
      var source = "class A { var x: int; }";
      var change = "var y: int; function GetY()";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 10), (0, 21)),
        change
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.Equal(new Range((0, 6), (0, 7)), location.Name);
      Assert.Equal(new Range((0, 0), (0, 38)), location.Declaration);
    }

    [Fact]
    public async Task MigrationRemovesLocationsWithinTheChangedRange() {
      var source = @"
class A {
  var x: int;
}".TrimStart();

      var change = @"var y: int;

  function GetY()";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((1, 2), (1, 13)),
        change
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.False(TryFindSymbolDeclarationByName(document, "x", out var _));
    }

    [Fact]
    public async Task MigrationMovesDeclarationWhenApplyingMultipleChangesAtOnce() {
      var source = @"
class X {
}

class B {
  var y: int;
}".TrimStart();

      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangesAndWaitCompletionAsync(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((3, 9), (3, 9)),
          Text = @"
  var x: int"
        },
        new TextDocumentContentChangeEvent {
          Range = new Range((0, 0), (1, 1)),
          Text = @"
class A {
  var a
}".TrimStart()
        }
      );
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "B", out var bLocation));
      Assert.Equal(new Range((4, 6), (4, 7)), bLocation.Name);
      Assert.Equal(new Range((4, 0), (7, 0)), bLocation.Declaration);
      Assert.True(TryFindSymbolDeclarationByName(document, "y", out var yLocation));
      Assert.Equal(new Range((6, 6), (6, 7)), yLocation.Name);
      Assert.Equal(new Range((6, 6), (6, 7)), yLocation.Declaration);
    }

    [Fact]
    public async Task PassingANullChangeRangeClearsSymbolsTable() {
      var source = "class X {}";
      var documentItem = CreateTestDocument(source);

      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "X", out var _));

      // First try a change that doesn't break resolution.
      // In this case all information is recomputed and no relocation happens.
      await ApplyChangeAndWaitCompletionAsync(document.DocumentIdentifier, null, "class Y {}");
      document = await Projects.GetResolvedDocumentAsync(document.DocumentIdentifier.Uri);
      Assert.NotNull(document); // No relocation, since no resolution errors, so Y can be found
      Assert.False(TryFindSymbolDeclarationByName(document, "X", out var _));
      Assert.True(TryFindSymbolDeclarationByName(document, "Y", out var _));

      // Next try a change that breaks resolution.
      // In this case symbols are relocated.  Since the change range is `null` all symbols for "test.dfy" are lost.
      await ApplyChangeAndWaitCompletionAsync(document.DocumentIdentifier, null, "; class Y {}");
      document = await Projects.GetResolvedDocumentAsync(document.DocumentIdentifier.Uri);
      Assert.NotNull(document);
      // Relocation happens due to the syntax error; range is null so table is cleared
      Assert.False(TryFindSymbolDeclarationByName(document, "X", out var _));
      Assert.False(TryFindSymbolDeclarationByName(document, "Y", out var _));
    }


    [Fact]
    public async Task PassingANullChangeRangePreservesForeignSymbols() {
      var source = "include \"foreign.dfy\"\nclass X {}";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));

      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var _));

      // Try a change that breaks resolution.  Symbols for `foreign.dfy` are kept.
      await ApplyChangeAndWaitCompletionAsync(document.DocumentIdentifier, null, "; include \"foreign.dfy\"\nclass Y {}");
      document = await Projects.GetResolvedDocumentAsync(document.DocumentIdentifier.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var _));

      // Finally we drop the reference to `foreign.dfy` and confirm that `A` is not accessible any more.
      await ApplyChangeAndWaitCompletionAsync(document.DocumentIdentifier, null, "class Y {}");
      document = await Projects.GetResolvedDocumentAsync(document.DocumentIdentifier.Uri);
      Assert.NotNull(document);
      Assert.False(TryFindSymbolDeclarationByName(document, "A", out var _));
    }

    public DeclarationLocationMigrationTest(ITestOutputHelper output) : base(output) {
    }
  }
}
