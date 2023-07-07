using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchCaseExpr : NestedMatchCase, IAttributeBearingDeclaration {
  public Expression Body;
  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;

  public NestedMatchCaseExpr(IToken tok, ExtendedPattern pat, Expression body, Attributes attrs) : base(tok, pat) {
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = attrs;
  }

  public override IEnumerable<Node> Children =>
    (Attributes != null ? new Node[] { Attributes } : Enumerable.Empty<Node>()).Concat(new Node[] { Body, Pat });

  public override IEnumerable<Node> PreResolveChildren => Children;

  public void Resolve(ModuleResolver resolver,
    ResolutionContext resolutionContext,
    Type resultType,
    Type sourceType) {
    var beforeResolveErrorCount = resolver.reporter.ErrorCount;

    Pat.Resolve(resolver, resolutionContext, sourceType, resolutionContext.IsGhost, false, false, false);

    resolver.ResolveAttributes(this, resolutionContext);
    var afterResolveErrorCount = resolver.reporter.ErrorCount;
    if (beforeResolveErrorCount == afterResolveErrorCount) {
      resolver.ResolveExpression(Body, resolutionContext);
      resolver.ConstrainSubtypeRelation(resultType, Body.Type, Body.tok, "type of case bodies do not agree (found {0}, previous types {1})", Body.Type, resultType);
    }
  }
}
