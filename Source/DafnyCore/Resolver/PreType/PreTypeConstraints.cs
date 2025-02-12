//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  /// <summary>
  /// This class holds the state of the pre-type inference. The state consists of a set of constraints; more precisely,
  /// it consists of lists of constraints, advice, and conditions to be confirmed.
  /// The class also contains methods for solving or partially solving these constraints.
  /// </summary>
  public class PreTypeConstraints {
    public readonly PreTypeResolver PreTypeResolver;
    private readonly DafnyOptions options;

    private List<SubtypeConstraint> unnormalizedSubtypeConstraints = new();
    private List<EqualityConstraint> equalityConstraints = new();
    private List<Func<bool>> guardedConstraints = new();
    private readonly List<Advice> defaultAdvice = new();
    private List<System.Action> confirmations = new();

    public PreTypeConstraints(PreTypeResolver preTypeResolver) {
      this.PreTypeResolver = preTypeResolver;
      this.options = preTypeResolver.resolver.Options;
    }

    /// <summary>
    /// Solves or simplifies as many type constraints as possible.
    /// If "allowDecisions" is "false", then no decisions, only determined inferences, are made; this mode is
    /// appropriate for the partial solving that's done before a member lookup.
    /// Returns "true" if anything changed (that is, if any of the constraints in the type-inference state
    /// caused a change some pre-type proxy).
    /// </summary>
    public void PartiallySolveTypeConstraints(string printableContext = null, bool makeDecisions = false) {
      if (printableContext != null) {
        PrintTypeInferenceState("(partial) " + printableContext);
      }

      // Note, the various constraints that have been recorded may contain pre-types that refer to symbols that
      // are not in scope. Therefore, it is important that, at the onset processing any of these constraints,
      // each pre-type is normalized with respect to scope.
      bool anythingChanged;
      do {
        anythingChanged = makeDecisions && TryMakeDecisions();
        anythingChanged |= ApplySubtypeConstraints();
        anythingChanged |= ApplyEqualityConstraints();
        anythingChanged |= ApplyGuardedConstraints();
      } while (anythingChanged);
    }

    private bool TryMakeDecisions() {
      if (TryResolveTypeProxiesUsingKnownBounds(true)) {
        return true;
      } else if (TryResolveTypeProxiesUsingKnownBounds(false)) {
        return true;
      } else if (TryApplyDefaultAdvice()) {
        return true;
      }
      return false;
    }

    public void SolveAllTypeConstraints(string printableContext) {
      PrintTypeInferenceState(printableContext);
      PartiallySolveTypeConstraints(null);

      PartiallySolveTypeConstraints(null, true);

      PrintLegend();
      ConfirmTypeConstraints();
      ClearState();
    }

    void ClearState() {
      unnormalizedSubtypeConstraints.Clear();
      equalityConstraints.Clear();
      guardedConstraints.Clear();
      defaultAdvice.Clear();
      confirmations.Clear();
      PreTypeResolver.allPreTypeProxies.Clear();
    }

    public void PrintTypeInferenceState(string/*?*/ header = null) {
      if (!options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }
      options.OutputWriter.WriteLine("*** Type inference state ***{0}", header == null ? "" : $" {header} ");
      PrintList("Subtype constraints", unnormalizedSubtypeConstraints, stc => {
        return $"{stc.Super} :> {stc.Sub}";
      });
      PrintList("Equality constraints", equalityConstraints, eqc => {
        return $"{eqc.A} == {eqc.B}";
      });
#if IS_THERE_A_GOOD_WAY_TO_PRINT_GUARDED_CONSTRAINTS
      PrintList("Guarded constraints", guardedConstraints, gc => {
        return gc.Kind + Util.Comma("", gc.Arguments, arg => $" {arg}");
      });
#endif
      PrintList("Default-type advice", defaultAdvice, advice => {
        return $"{advice.PreType} ~-~-> {advice.WhatString}";
      });
#if IS_THERE_A_GOOD_WAY_TO_PRINT_CONFIRMATIONS
      PrintList("Post-inference confirmations", confirmations, c => {
        return $"{TokToShortLocation(c.tok)}: {c.Check} {c.PreType}: {c.ErrorMessage()}";
      });
#endif
    }

    void PrintLegend() {
      PrintList("Legend", PreTypeResolver.allPreTypeProxies, pair => {
        var s = Pad($"?{pair.Item1.UniqueId}", 4) + pair.Item1;
        return pair.Item2 == null ? s : $"{Pad(s, 20)}  {pair.Item2}";
      });
    }

    void PrintList<T>(string rubric, List<T> list, Func<T, string> formatter) {
      if (!options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return;
      }
      options.OutputWriter.WriteLine($"    {rubric}:");
      foreach (var t in list) {
        var info = $"        {formatter(t)}";
        if (t is PreTypeConstraint preTypeConstraint) {
          info = $"{Pad(info, 30)}  {TokToShortLocation(preTypeConstraint.tok)}: {preTypeConstraint.ErrorMessage()}";
        }
        options.OutputWriter.WriteLine(info);
      }
    }

    public void AddEqualityConstraint(PreType a, PreType b, IToken tok, string msgFormat, PreTypeConstraint baseError = null) {
      equalityConstraints.Add(new EqualityConstraint(a, b, tok, msgFormat, baseError));
    }

    private bool ApplyEqualityConstraints() {
      if (equalityConstraints.Count == 0) {
        return false;
      }
      var constraints = equalityConstraints;
      equalityConstraints = new();
      foreach (var constraint in constraints) {
        equalityConstraints.AddRange(constraint.Apply(this));
      }
      return true;
    }

    public void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString, PreTypeConstraint baseError = null) {
      unnormalizedSubtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatString, baseError));
    }

    public void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, Func<string> errorFormatStringProducer) {
      unnormalizedSubtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatStringProducer));
    }

    bool ApplySubtypeConstraints() {
      if (unnormalizedSubtypeConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = unnormalizedSubtypeConstraints;
      unnormalizedSubtypeConstraints = new();
      var anythingChanged = false;
      foreach (var constraint in constraints) {
        if (constraint.Apply(this)) {
          anythingChanged = true;
        } else {
          unnormalizedSubtypeConstraints.Add(constraint.Normalize());
        }
      }
      return anythingChanged;
    }

    /// <summary>
    /// Try to resolve each proxy using its sub-bound constraints (if "fromSubBounds" is "true") or
    /// its super-bound constraints (if "fromSubBounds" is "false"). Add an equality constraint for
    /// any proxy whose head can be determined.
    /// Return "true" if any such equality constraint was added.
    /// </summary>
    bool TryResolveTypeProxiesUsingKnownBounds(bool fromSubBounds) {
      // First, compute the join/meet of the sub/super-bound heads of each proxy
      Dictionary<PreTypeProxy, TopLevelDecl> candidateHeads = new();
      Dictionary<PreTypeProxy, SubtypeConstraint> constraintOrigins = new();
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        var proxy = (fromSubBounds ? constraint.Super : constraint.Sub).Normalize() as PreTypeProxy;
        var bound = (fromSubBounds ? constraint.Sub : constraint.Super).Normalize() as DPreType;
        if (proxy != null && bound != null) {
          if (!candidateHeads.TryGetValue(proxy, out var previousBest)) {
            candidateHeads.Add(proxy, bound.Decl);
            constraintOrigins.Add(proxy, constraint);
          } else {
            var combined = fromSubBounds
              ? JoinHeads(previousBest, bound.Decl, PreTypeResolver.resolver.SystemModuleManager)
              : MeetHeads(previousBest, bound.Decl);
            if (combined == null) {
              // the two joins/meets were in conflict with each other; ignore the new one
            } else {
              candidateHeads[proxy] = combined;
            }
          }
        }
      }

      // Record equality constraints for each proxy that was determined
      var anythingChanged = false;
      foreach (var (proxy, best) in candidateHeads) {
        var pt = new DPreType(best, best.TypeArgs.ConvertAll(_ => PreTypeResolver.CreatePreTypeProxy()));
        var constraint = constraintOrigins[proxy];
        DebugPrint($"    DEBUG: head decision {proxy} := {pt}");
        AddEqualityConstraint(proxy, pt, constraint.tok, constraint.ErrorFormatString); // TODO: the message could be made more specific now (perhaps)
        anythingChanged = true;
      }
      return anythingChanged;
    }

    public static TopLevelDecl/*?*/ JoinHeads(TopLevelDecl a, TopLevelDecl b, SystemModuleManager systemModuleManager) {
      var aAncestors = new HashSet<TopLevelDecl>();
      var bAncestors = new HashSet<TopLevelDecl>();
      PreTypeResolver.ComputeAncestors(a, aAncestors, systemModuleManager);
      PreTypeResolver.ComputeAncestors(b, bAncestors, systemModuleManager);
      var ancestors = aAncestors.Intersect(bAncestors).ToList();
      // Unless ancestors.Count == 1, there is no unique answer, and not necessary any way to determine the best
      // answer. As a heuristic, pick the element with the highest unique Height number. If there is no such
      // element, return null.
      while (ancestors.Count != 0) {
        var maxAmongAncestors = ancestors.Max(Height);
        var highestAncestors = ancestors.Where(ancestor => Height(ancestor) == maxAmongAncestors).ToList();
        if (highestAncestors.Count == 1) {
          return highestAncestors.ElementAt(0);
        }
        ancestors.RemoveAll(ancestor => Height(ancestor) == maxAmongAncestors);
      }
      return null;
    }

    TopLevelDecl/*?*/ MeetHeads(TopLevelDecl a, TopLevelDecl b) {
      var aAncestors = new HashSet<TopLevelDecl>();
      if (aAncestors.Contains(b)) {
        // that's good enough; let's pick a
        return a;
      }
      var bAncestors = new HashSet<TopLevelDecl>();
      if (bAncestors.Contains(a)) {
        // that's good enough; let's pick b
        return b;
      }
      // give up
      return null;
    }

    /// <summary>
    /// Return the trait height of "decl". The height is the smallest natural number that satisfies:
    ///   - The built-in trait "object" is strictly lower than anything else
    ///   - A declaration is strictly taller than any of its (explicit or implicit) parents
    ///
    /// The purpose of the "height" is to sort parent traits during type inference. For this purpose,
    /// it seems less surprising to have (the possibly implicit) "object" have a lower height than
    /// anything else. Here's an example:
    ///     trait Trait { } // note, this trait is not a reference type
    ///     class A extends Trait { }
    ///     class B extends Trait { }
    ///     method M(a: A, b: B) {
    ///       var z;
    ///       z := a;
    ///       z := b;
    ///     }
    /// What type do you expect z to have? Looking at the program text suggests z's type to be Trait,
    /// since Trait is a common parent of both A and B. But "object" is also a common parent of A and
    /// B, since A and B are classes. It seems more surprising to report "z has no best type" than
    /// to make "object" a "last resort" during type inference.
    /// </summary>
    public static int Height(TopLevelDecl decl) {
      if (decl is TraitDecl { IsObjectTrait: true }) {
        // object is at height 0
        return 0;
      }
      if (decl is TopLevelDeclWithMembers { ParentTraitHeads: { Count: > 0 } } topLevelDeclWithMembers) {
        // Note, if "decl" is a reference type, then its parents include "object", whether or not "object" is explicitly
        // included in "ParentTraitHeads". Since the "Max" in the following line will return a number 0 or
        // higher, the "Max" would be the same whether or not "object" is in the "ParentTraitHeads" list.
        return topLevelDeclWithMembers.ParentTraitHeads.Max(Height) + 1;
      } else {
        // Other other declarations have height 1.
        // Note, an ostensibly parent-less reference type still has the implicit "object" as a parent trait, but
        // that still makes its height 1.
        return 1;
      }
    }

    public IEnumerable<DPreType> AllSubBounds(PreTypeProxy proxy, ISet<PreTypeProxy> visited) {
      Contract.Requires(proxy.PT == null);
      if (visited.Contains(proxy)) {
        yield break;
      }
      visited.Add(proxy);
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        if (constraint.Super.Normalize() == proxy) {
          var sub = constraint.Sub.Normalize();
          if (sub is PreTypeProxy subProxy) {
            foreach (var pt in AllSubBounds(subProxy, visited)) {
              yield return pt;
            }
          } else {
            yield return (DPreType)sub;
          }
        }
      }
    }

    public IEnumerable<DPreType> AllSuperBounds(PreTypeProxy proxy, ISet<PreTypeProxy> visited) {
      Contract.Requires(proxy.PT == null);
      if (visited.Contains(proxy)) {
        yield break;
      }
      visited.Add(proxy);
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        if (constraint.Sub.Normalize() == proxy) {
          var super = constraint.Super.Normalize();
          if (super is PreTypeProxy superProxy) {
            foreach (var pt in AllSuperBounds(superProxy, visited)) {
              yield return pt;
            }
          } else {
            yield return (DPreType)super;
          }
        }
      }
    }

    public IEnumerable<PreType> DirectionalBounds(PreTypeProxy tproxy, int direction) {
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        if (0 <= direction && constraint.Super.Normalize() == tproxy) {
          yield return constraint.Sub;
        }
        if (direction <= 0 && constraint.Sub.Normalize() == tproxy) {
          yield return constraint.Super;
        }
      }
    }

    public void AddGuardedConstraint(Func<bool> predicate) {
      guardedConstraints.Add(predicate);
    }

    bool ApplyGuardedConstraints() {
      if (guardedConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = guardedConstraints;
      guardedConstraints = new();
      var anythingChanged = false;
      foreach (var constraint in constraints) {
        if (constraint()) {
          anythingChanged = true;
        } else {
          guardedConstraints.Add(constraint);
        }
      }
      return anythingChanged;
    }

    public void AddDefaultAdvice(PreType preType, Advice.Target advice) {
      defaultAdvice.Add(new Advice(preType, advice));
    }

    bool TryApplyDefaultAdvice() {
      bool anythingChanged = false;
      foreach (var advice in defaultAdvice) {
        anythingChanged |= advice.Apply(PreTypeResolver);
      }
      return anythingChanged;
    }

    public void AddConfirmation(CommonConfirmationBag check, PreType preType, IToken tok, string errorFormatString) {
      confirmations.Add(() => {
        if (!ConfirmConstraint(check, preType, null)) {
          PreTypeResolver.ReportError(tok, errorFormatString, preType);
        }
      });
    }

    public void AddConfirmation(CommonConfirmationBag check, PreType preType, Type toType, IToken tok, string errorFormatString) {
      Contract.Requires(toType is NonProxyType);
      var toPreType = (DPreType)PreTypeResolver.Type2PreType(toType);
      confirmations.Add(() => {
        if (!ConfirmConstraint(check, preType, toPreType)) {
          PreTypeResolver.ReportError(tok, errorFormatString, preType);
        }
      });
    }

    public void AddConfirmation(System.Action confirm) {
      confirmations.Add(confirm);
    }

    void ConfirmTypeConstraints() {
      foreach (var confirmation in confirmations) {
        confirmation();
      }
    }

    public enum CommonConfirmationBag {
      InIntFamily,
      InRealFamily,
      InBoolFamily,
      InCharFamily,
      InSeqFamily,
      IsNullableRefType,
      IsBitvector,
      IntLikeOrBitvector,
      NumericOrBitvector,
      NumericOrBitvectorOrCharOrORDINALOrSuchTrait,
      BooleanBits,
      IntOrORDINAL,
      IntOrBitvectorOrORDINAL,
      Plussable,
      Mullable,
      Disjointable,
      OrderableLess,
      OrderableGreater,
      RankOrderable,
      RankOrderableOrTypeParameter,
      Sizeable,
      Freshable,
      IsCoDatatype,
    };

    private bool ConfirmConstraint(CommonConfirmationBag check, PreType preType, DPreType auxPreType) {
      preType = preType.Normalize();
      if (preType is PreTypeProxy) {
        return false;
      }

      var pt = (DPreType)preType;
      var ancestorPt = PreTypeResolver.NewTypeAncestor(pt);
      var ancestorDecl = ancestorPt.Decl;
      var familyDeclName = ancestorDecl.Name;
      switch (check) {
        case CommonConfirmationBag.InIntFamily:
          return familyDeclName == "int";
        case CommonConfirmationBag.InRealFamily:
          return familyDeclName == "real";
        case CommonConfirmationBag.InBoolFamily:
          return familyDeclName == "bool";
        case CommonConfirmationBag.InCharFamily:
          return familyDeclName == "char";
        case CommonConfirmationBag.InSeqFamily:
          return familyDeclName == "seq";
        case CommonConfirmationBag.IsNullableRefType:
          return DPreType.IsReferenceTypeDecl(pt.Decl);
        case CommonConfirmationBag.IsBitvector:
          return PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.IntLikeOrBitvector:
          return familyDeclName == "int" || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.NumericOrBitvector:
          return familyDeclName is "int" or "real" || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.NumericOrBitvectorOrCharOrORDINALOrSuchTrait:
          if (familyDeclName is "int" or "real" or "char" or "ORDINAL" || PreTypeResolver.IsBitvectorName(familyDeclName)) {
            return true;
          }
          return PreTypeResolver.IsSuperPreTypeOf(pt, auxPreType);
        case CommonConfirmationBag.BooleanBits:
          return familyDeclName == "bool" || PreTypeResolver.IsBitvectorName(familyDeclName);
        case CommonConfirmationBag.IntOrORDINAL:
          return familyDeclName == "int" || familyDeclName == "ORDINAL";
        case CommonConfirmationBag.IntOrBitvectorOrORDINAL:
          return familyDeclName == "int" || PreTypeResolver.IsBitvectorName(familyDeclName) || familyDeclName == "ORDINAL";
        case CommonConfirmationBag.Plussable:
          switch (familyDeclName) {
            case "int":
            case "real":
            case "ORDINAL":
            case "char":
            case "seq":
            case "set":
            case "iset":
            case "multiset":
            case "map":
            case "imap":
              return true;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.Mullable:
          switch (familyDeclName) {
            case "int":
            case "real":
            case "set":
            case "iset":
            case "multiset":
              return true;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.Disjointable:
          return familyDeclName == "set" || familyDeclName == "iset" || familyDeclName == "multiset";
        case CommonConfirmationBag.OrderableLess:
        case CommonConfirmationBag.OrderableGreater:
          switch (familyDeclName) {
            case "int":
            case "real":
            case "ORDINAL":
            case "char":
            case "set":
            case "iset":
            case "multiset":
              return true;
            case "seq":
              return check == CommonConfirmationBag.OrderableLess;
            default:
              return PreTypeResolver.IsBitvectorName(familyDeclName);
          }
        case CommonConfirmationBag.RankOrderable:
          return ancestorDecl is IndDatatypeDecl;
        case CommonConfirmationBag.RankOrderableOrTypeParameter:
          return ancestorDecl is IndDatatypeDecl || ancestorDecl is TypeParameter;
        case CommonConfirmationBag.Sizeable:
          switch (familyDeclName) {
            case "set": // but not "iset"
            case "multiset":
            case "seq":
            case "map": // but not "imap"
              return true;
            default:
              return false;
          }
        case CommonConfirmationBag.Freshable: {
            var t = familyDeclName == "set" || familyDeclName == "iset" || familyDeclName == "seq"
              ? ancestorPt.Arguments[0].Normalize() as DPreType
              : ancestorPt;
            return t != null && DPreType.IsReferenceTypeDecl(t.Decl);
          }
        case CommonConfirmationBag.IsCoDatatype:
          return ancestorDecl is CoDatatypeDecl;

        default:
          Contract.Assert(false); // unexpected case
          throw new cce.UnreachableException();
      }
    }

    /// <summary>
    /// If "super" is an ancestor of "sub", then return a list "L" of arguments for "super" such that
    /// "super<L>" is a supertype of "sub<subArguments>".
    /// Otherwise, return "null".
    /// </summary>
    public List<PreType> /*?*/ GetTypeArgumentsForSuperType(TopLevelDecl super, TopLevelDecl sub, List<PreType> subArguments) {
      Contract.Requires(sub.TypeArgs.Count == subArguments.Count);

      if (super == sub) {
        return subArguments;
      } else if (sub is TopLevelDeclWithMembers md) {
        var subst = PreType.PreTypeSubstMap(md.TypeArgs, subArguments);
        foreach (var parentType in AllParentTraits(md)) {
          var parentPreType = (DPreType)PreTypeResolver.Type2PreType(parentType).Substitute(subst);
          var arguments = GetTypeArgumentsForSuperType(super, parentPreType.Decl, parentPreType.Arguments);
          if (arguments != null) {
            return arguments;
          }
        }
      }
      return null;
    }

    /// <summary>
    /// AllParentTraits(decl) is like decl.ParentTraits, but also returns "object" if "decl" is a reference type.
    /// </summary>
    public IEnumerable<Type> AllParentTraits(TopLevelDeclWithMembers decl) {
      foreach (var parentType in decl.ParentTraits) {
        yield return parentType;
      }
      if (DPreType.IsReferenceTypeDecl(decl)) {
        if (decl is TraitDecl { IsObjectTrait: true }) {
          // don't return object itself
        } else {
          yield return PreTypeResolver.resolver.SystemModuleManager.ObjectQ();
        }
      }
    }

    public static string TokToShortLocation(IToken tok) {
      return $"{System.IO.Path.GetFileName(tok.filename)}({tok.line},{tok.col - 1})";
    }

    public static string Pad(string s, int minWidth) {
      return s + new string(' ', Math.Max(minWidth - s.Length, 0));
    }

    public void DebugPrint(string format, params object[] args) {
      if (options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        options.OutputWriter.WriteLine(format, args);
      }
    }

  }
}