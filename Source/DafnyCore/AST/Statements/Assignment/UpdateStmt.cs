using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class UpdateStmt : ConcreteUpdateStatement, ICloneable<UpdateStmt>, ICanResolve {
  public readonly List<AssignmentRhs> Rhss;
  public readonly bool CanMutateKnownState;
  public Expression OriginalInitialLhs = null;

  public override IToken Tok {
    get {
      var firstRhs = Rhss.First();
      if (firstRhs.StartToken != StartToken) {
        // If there is an operator, use it as a token
        return firstRhs.StartToken.Prev;
      }

      return firstRhs.Tok;
    }
  }

  [FilledInDuringResolution] public List<Statement> ResolvedStatements;
  public override IEnumerable<Statement> SubStatements => Children.OfType<Statement>();

  public override IEnumerable<Node> Children => ResolvedStatements ?? Lhss.Concat<Node>(Rhss);
  public override IEnumerable<Node> PreResolveChildren => Lhss.Concat<Node>(Rhss);

  public override IEnumerable<Statement> PreResolveSubStatements => Enumerable.Empty<Statement>();

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Lhss));
    Contract.Invariant(cce.NonNullElements(Rhss));
  }

  public UpdateStmt Clone(Cloner cloner) {
    return new UpdateStmt(cloner, this);
  }

  public UpdateStmt(Cloner cloner, UpdateStmt original) : base(cloner, original) {
    Rhss = original.Rhss.Select(cloner.CloneRHS).ToList();
    CanMutateKnownState = original.CanMutateKnownState;
    if (cloner.CloneResolvedFields) {
      ResolvedStatements = original.ResolvedStatements.Select(cloner.CloneStmt).ToList();
    }
  }

  public UpdateStmt(RangeToken rangeToken, List<Expression> lhss, List<AssignmentRhs> rhss)
    : base(rangeToken, lhss) {
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(cce.NonNullElements(rhss));
    Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
    Rhss = rhss;
    CanMutateKnownState = false;
  }
  public UpdateStmt(RangeToken rangeToken, List<Expression> lhss, List<AssignmentRhs> rhss, bool mutate)
    : base(rangeToken, lhss) {
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(cce.NonNullElements(rhss));
    Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
    Rhss = rhss;
    CanMutateKnownState = mutate;
  }
  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var e in base.PreResolveSubExpressions) {
        yield return e;
      }
      foreach (var rhs in Rhss) {
        foreach (var e in rhs.PreResolveSubExpressions) {
          yield return e;
        }
      }
    }
  }

  /// <summary>
  /// Resolve the RHSs and entire UpdateStmt (LHSs should already have been checked by the caller).
  /// errorCountBeforeCheckingLhs is passed in so that this method can determined if any resolution errors were found during
  /// LHS or RHS checking, because only if no errors were found is update.ResolvedStmt changed.
  /// </summary>
  public override void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext) {
    Contract.Requires(this != null);
    Contract.Requires(resolutionContext != null);

    int errorCountBeforeCheckingLhs = resolver.Reporter.Count(ErrorLevel.Error);

    base.Resolve(resolver, resolutionContext);

    IToken firstEffectfulRhs = null;
    ModuleResolver.MethodCallInformation methodCallInfo = null;
    ResolvedStatements = new();
    foreach (var rhs in Rhss) {
      bool isEffectful;
      if (rhs is TypeRhs) {
        var tr = (TypeRhs)rhs;
        resolver.ResolveTypeRhs(tr, this, resolutionContext);
        isEffectful = tr.InitCall != null;
      } else if (rhs is HavocRhs) {
        isEffectful = false;
      } else {
        var er = (ExprRhs)rhs;
        if (er.Expr is ApplySuffix) {
          var a = (ApplySuffix)er.Expr;
          var cRhs = resolver.ResolveApplySuffix(a, resolutionContext, true);
          isEffectful = cRhs != null;
          methodCallInfo = methodCallInfo ?? cRhs;
        } else {
          resolver.ResolveExpression(er.Expr, resolutionContext);
          isEffectful = false;
        }
      }
      if (isEffectful && firstEffectfulRhs == null) {
        firstEffectfulRhs = rhs.Tok;
      }

      resolver.ResolveAttributes(rhs, resolutionContext);
    }

    // figure out what kind of UpdateStmt this is
    if (firstEffectfulRhs == null) {
      if (Lhss.Count == 0) {
        Contract.Assert(Rhss.Count == 1);  // guaranteed by the parser
        resolver.reporter.Error(MessageSource.Resolver, this, "expected method call, found expression");
      } else if (Lhss.Count != Rhss.Count) {
        resolver.reporter.Error(MessageSource.Resolver, this, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", Lhss.Count, Rhss.Count);
      } else if (resolver.reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
        // add the statements here in a sequence, but don't use that sequence later for translation (instead, should translate properly as multi-assignment)
        for (int i = 0; i < Lhss.Count; i++) {
          var a = new AssignStmt(RangeToken, Lhss[i].Resolved, Rhss[i]);
          ResolvedStatements.Add(a);
        }
      }

    } else if (CanMutateKnownState) {
      if (1 < Rhss.Count) {
        resolver.reporter.Error(MessageSource.Resolver, firstEffectfulRhs, "cannot have effectful parameter in multi-return statement.");
      } else { // it might be ok, if it is a TypeRhs
        Contract.Assert(Rhss.Count == 1);
        if (methodCallInfo != null) {
          resolver.reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "cannot have method call in return statement.");
        } else {
          // we have a TypeRhs
          Contract.Assert(Rhss[0] is TypeRhs);
          var tr = (TypeRhs)Rhss[0];
          Contract.Assert(tr.InitCall != null); // there were effects, so this must have been a call.
          if (tr.CanAffectPreviouslyKnownExpressions) {
            resolver.reporter.Error(MessageSource.Resolver, tr.Tok, "can only have initialization methods which modify at most 'this'.");
          } else if (resolver.reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
            var a = new AssignStmt(RangeToken, Lhss[0].Resolved, tr);
            ResolvedStatements.Add(a);
          }
        }
      }

    } else {
      // if there was an effectful RHS, that must be the only RHS
      if (Rhss.Count != 1) {
        resolver.reporter.Error(MessageSource.Resolver, firstEffectfulRhs, "an update statement is allowed an effectful RHS only if there is just one RHS");
      } else if (methodCallInfo == null) {
        // must be a single TypeRhs
        if (Lhss.Count != 1) {
          Contract.Assert(2 <= Lhss.Count);  // the parser allows 0 Lhss only if the whole statement looks like an expression (not a TypeRhs)
          resolver.reporter.Error(MessageSource.Resolver, Lhss[1].tok, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment", Lhss.Count, Rhss.Count);
        } else if (resolver.reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
          var a = new AssignStmt(RangeToken, Lhss[0].Resolved, Rhss[0]);
          ResolvedStatements.Add(a);
        }
      } else if (resolver.reporter.Count(ErrorLevel.Error) == errorCountBeforeCheckingLhs) {
        // a call statement
        var resolvedLhss = new List<Expression>();
        foreach (var ll in Lhss) {
          resolvedLhss.Add(ll.Resolved);
        }
        CallStmt a = new CallStmt(RangeToken, resolvedLhss, methodCallInfo.Callee, methodCallInfo.ActualParameters, methodCallInfo.Tok);
        a.OriginalInitialLhs = OriginalInitialLhs;
        ResolvedStatements.Add(a);
      }
    }

    foreach (var a in ResolvedStatements) {
      resolver.ResolveStatement(a, resolutionContext);
    }
  }
}