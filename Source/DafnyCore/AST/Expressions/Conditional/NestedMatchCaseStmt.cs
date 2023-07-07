using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchCaseStmt : NestedMatchCase, IAttributeBearingDeclaration, ICloneable<NestedMatchCaseStmt> {
  public readonly List<Statement> Body;
  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;
  public NestedMatchCaseStmt(RangeToken rangeToken, ExtendedPattern pat, List<Statement> body) : base(rangeToken.StartToken, pat) {
    RangeToken = rangeToken;
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = null;
  }
  public NestedMatchCaseStmt(IToken tok, ExtendedPattern pat, List<Statement> body, Attributes attrs) : base(tok, pat) {
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = attrs;
  }

  private NestedMatchCaseStmt(Cloner cloner, NestedMatchCaseStmt original) : base(original.tok, original.Pat) {
    this.Body = original.Body.Select(cloner.CloneStmt).ToList();
    this.Attributes = cloner.CloneAttributes(original.Attributes);
  }

  public NestedMatchCaseStmt Clone(Cloner cloner) {
    return new NestedMatchCaseStmt(cloner, this);
  }
  public override IEnumerable<Node> Children => new[] { Pat }.Concat<Node>(Body).Concat(Attributes?.Args ?? Enumerable.Empty<Node>());
  public override IEnumerable<Node> PreResolveChildren => Children;

  public void Resolve(
    ModuleResolver resolver,
    ResolutionContext resolutionContext,
    Dictionary<TypeParameter, Type> subst,
    Type sourceType) {
    var beforeResolveErrorCount = resolver.reporter.ErrorCount;

    Pat.Resolve(resolver, resolutionContext, sourceType, resolutionContext.IsGhost, true, false, false);

    // In Dafny, any bound variables introduced in a pattern are in scope throughout the case body, and cannot be shadowed at the top-level
    // of the case body. Because the machinery above creates, for each bound variable, a local variable with the same name and declares that
    // local variable in the case body, we introduce a new scope boundary around the body.
    resolver.scope.PushMarker();
    resolver.ResolveAttributes(this, resolutionContext);
    var afterResolveErrorCount = resolver.reporter.ErrorCount;
    if (beforeResolveErrorCount == afterResolveErrorCount) {
      resolver.DominatingStatementLabels.PushMarker();
      foreach (Statement ss in Body) {
        resolver.ResolveStatementWithLabels(ss, resolutionContext);
      }
      resolver.DominatingStatementLabels.PopMarker();
    }
    resolver.scope.PopMarker();
  }
}
