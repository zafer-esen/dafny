using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class NonNullTypeDecl : SubsetTypeDecl {
  public override string WhatKind { get { return "non-null type"; } }
  public readonly ClassLikeDecl Class;

  /// <summary>
  /// The public constructor is NonNullTypeDecl(ClassDecl cl). The rest is pretty crazy: There are stages of "this"-constructor calls
  /// in order to build values that depend on previously computed parameters.
  /// </summary>
  public NonNullTypeDecl(ClassLikeDecl cl)
    : this(cl, cl.TypeArgs.ConvertAll(tp => new TypeParameter(tp.RangeToken, tp.NameNode, tp.VarianceSyntax, tp.Characteristics))) {
    Contract.Requires(cl != null);
  }

  private NonNullTypeDecl(ClassLikeDecl cl, List<TypeParameter> tps)
    : this(cl, tps,
      new BoundVar(cl.Tok, "c", new UserDefinedType(cl.Tok, cl.Name + "?", tps.Count == 0 ? null : tps.ConvertAll(tp => (Type)new UserDefinedType(tp))))) {
    Contract.Requires(cl != null);
    Contract.Requires(tps != null);
  }

  private NonNullTypeDecl(ClassLikeDecl cl, List<TypeParameter> tps, BoundVar id)
    : base(cl.RangeToken, cl.NameNode, new TypeParameter.TypeParameterCharacteristics(), tps, cl.EnclosingModuleDefinition, id,
      new BinaryExpr(cl.Tok, BinaryExpr.Opcode.Neq, new IdentifierExpr(cl.Tok, id), new LiteralExpr(cl.Tok)),
      SubsetTypeDecl.WKind.Special, null, SystemModuleManager.AxiomAttribute()) {
    Contract.Requires(cl != null);
    Contract.Requires(tps != null);
    Contract.Requires(id != null);
    Class = cl;
  }

  public override List<Type> ParentTypes(List<Type> typeArgs) {
    List<Type> result = new List<Type>(base.ParentTypes(typeArgs));

    foreach (var rhsParentType in Class.ParentTypes(typeArgs)) {
      var rhsParentUdt = (UserDefinedType)rhsParentType; // all parent types of .Class are expected to be possibly-null class types
      Contract.Assert(rhsParentUdt.ResolvedClass is TraitDecl);
      result.Add(UserDefinedType.CreateNonNullTypeIfReferenceType(rhsParentUdt));
    }

    return result;
  }
}