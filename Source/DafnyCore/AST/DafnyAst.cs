//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Text;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using System.Diagnostics;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.Auditor;
using Microsoft.Dafny.Plugins;
using Action = System.Action;

namespace Microsoft.Dafny {
  [System.AttributeUsage(System.AttributeTargets.Field | System.AttributeTargets.Property)]
  public class FilledInDuringTranslationAttribute : System.Attribute { }
  [System.AttributeUsage(System.AttributeTargets.Field | System.AttributeTargets.Property)]
  public class FilledInDuringResolutionAttribute : System.Attribute { }

  public interface IDeclarationOrUsage : INode {
    IToken NameToken { get; }
  }

  public class Program : TokenNode {
    public CompilationData Compilation { get; }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FullName != null);
      Contract.Invariant(DefaultModule != null);
    }

    public readonly string FullName;

    // Resolution essentially flattens the module hierarchy, for
    // purposes of translation and compilation.
    [FilledInDuringResolution] public Dictionary<ModuleDefinition, ModuleSignature> ModuleSigs;
    [FilledInDuringResolution] public IEnumerable<ModuleDefinition> CompileModules => new[] { SystemModuleManager.SystemModule }.Concat(Modules());
    // Contains the definitions to be used for compilation.

    public Method MainMethod; // Method to be used as main if compiled
    public LiteralModuleDecl DefaultModule;
    public IList<FileModuleDefinition> Files { get; } = new List<FileModuleDefinition>();
    public DefaultModuleDefinition DefaultModuleDef => (DefaultModuleDefinition)DefaultModule.ModuleDef;
    public SystemModuleManager SystemModuleManager;
    public DafnyOptions Options => Reporter.Options;
    public ErrorReporter Reporter { get; set; }

    public Program(string name, [Captured] LiteralModuleDecl module, [Captured] SystemModuleManager systemModuleManager, ErrorReporter reporter,
      CompilationData compilation) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(reporter != null);
      FullName = name;
      DefaultModule = module;
      SystemModuleManager = systemModuleManager;
      this.Reporter = reporter;
      Compilation = compilation;
    }

    //Set appropriate visibilty before presenting module
    public IEnumerable<ModuleDefinition> Modules() {

      foreach (var msig in ModuleSigs) {
        Type.PushScope(msig.Value.VisibilityScope);
        yield return msig.Key;
        Type.PopScope(msig.Value.VisibilityScope);
      }

    }

    public IEnumerable<ModuleDefinition> RawModules() {
      return ModuleSigs.Keys;
    }

    public string Name {
      get {
        try {
          return System.IO.Path.GetFileName(FullName);
        } catch (ArgumentException) {
          return FullName;
        }
      }
    }

    /// Get the first token that is in the same file as the DefaultModule.RootToken.FileName
    /// (skips included tokens)
    public IToken GetFirstTopLevelToken() {
      var rootToken = DefaultModuleDef.RangeToken.StartToken;
      if (rootToken.Next == null) {
        return null;
      }

      var firstToken = rootToken;
      // We skip all included files
      while (firstToken is { Next: { } } && firstToken.Next.Filepath != rootToken.Filepath) {
        firstToken = firstToken.Next;
      }

      if (firstToken == null || firstToken.kind == 0) {
        return null;
      }

      return firstToken;
    }

    public override IEnumerable<Node> Children => new[] { DefaultModule };

    public override IEnumerable<Node> PreResolveChildren => Children;

    public override IEnumerable<Assumption> Assumptions(Declaration decl) {
      return Modules().SelectMany(m => m.Assumptions(decl));
    }
  }

  /// <summary>
  /// An expression introducting bound variables
  /// </summary>
  public interface IBoundVarsBearingExpression {
    public IEnumerable<BoundVar> AllBoundVars {
      get;
    }
  }

  /// <summary>
  /// A class implementing this interface is one that can carry attributes.
  /// </summary>
  public interface IAttributeBearingDeclaration {
    Attributes Attributes { get; }
  }

  public static class IAttributeBearingDeclarationExtensions {
    public static bool HasUserAttribute(this IAttributeBearingDeclaration decl, string name, out Attributes attribute) {
      if (Attributes.Find(decl.Attributes, name) is UserSuppliedAttributes attr) {
        attribute = attr;
        return true;
      }

      attribute = null;
      return false;
    }
  }

  public class Attributes : TokenNode {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public static string AxiomAttributeName = "axiom";
    public static string ConcurrentAttributeName = "concurrent";
    public static string ExternAttributeName = "extern";
    public static string VerifyAttributeName = "verify";
    public static string AutoGeneratedAttributeName = "auto_generated";
    public static string TypeEncodingAttributeName = "typeEncoding";
    public static string PruneAttributeName = "prune";

    public string Name;
    /*Frozen*/
    public readonly List<Expression> Args;

    public readonly Attributes Prev;
    public Attributes(string name, [Captured] List<Expression> args, Attributes prev) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(args));
      Name = name;
      Args = args;
      Prev = prev;
    }

    public override string ToString() {
      string result = Prev?.ToString() + "{:" + Name;
      if (Args == null || Args.Count() == 0) {
        return result + "}";
      } else {
        var exprs = String.Join(", ", Args.Select(e => e.ToString()));
        return result + " " + exprs + "}";
      }
    }

    public static IEnumerable<Expression> SubExpressions(Attributes attrs) {
      return attrs.AsEnumerable().SelectMany(aa => aa.Args);
    }

    public static bool Contains(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      return attrs.AsEnumerable().Any(aa => aa.Name == nm);
    }

    /// <summary>
    /// Returns first occurrence of an attribute named <c>nm</c>, or <c>null</c> if there is no such
    /// attribute.
    /// </summary>
    [Pure]
    public static Attributes/*?*/ Find(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      return attrs.AsEnumerable().FirstOrDefault(attr => attr.Name == nm);
    }

    /// <summary>
    /// Returns true if "nm" is a specified attribute.  If it is, then:
    /// - if the attribute is {:nm true}, then value==true
    /// - if the attribute is {:nm false}, then value==false
    /// - if the attribute is anything else, then value returns as whatever it was passed in as.
    /// This method does NOT use type information of the attribute arguments, so it can safely
    /// be called very early during resolution before types are available and names have been resolved.
    /// </summary>
    [Pure]
    public static bool ContainsBool(Attributes attrs, string nm, ref bool value) {
      Contract.Requires(nm != null);
      var attr = attrs.AsEnumerable().FirstOrDefault(attr => attr.Name == nm);
      if (attr == null) {
        return false;
      }

      if (attr.Args.Count == 1 && attr.Args[0] is LiteralExpr { Value: bool v }) {
        value = v;
      }
      return true;
    }

    /// <summary>
    /// Checks whether a Boolean attribute has been set on the declaration itself,
    /// the enclosing class, or any enclosing module.  Settings closer to the declaration
    /// override those further away.
    /// </summary>
    public static bool ContainsBoolAtAnyLevel(MemberDecl decl, string attribName) {
      bool setting = true;
      if (Attributes.ContainsBool(decl.Attributes, attribName, ref setting)) {
        return setting;
      }

      if (Attributes.ContainsBool(decl.EnclosingClass.Attributes, attribName, ref setting)) {
        return setting;
      }

      // Check the entire stack of modules
      var mod = decl.EnclosingClass.EnclosingModuleDefinition;
      while (mod != null) {
        if (Attributes.ContainsBool(mod.Attributes, attribName, ref setting)) {
          return setting;
        }
        mod = mod.EnclosingModule;
      }

      return false;
    }

    /// <summary>
    /// Returns list of expressions if "nm" is a specified attribute:
    /// - if the attribute is {:nm e1,...,en}, then returns (e1,...,en)
    /// Otherwise, returns null.
    /// </summary>
    public static List<Expression> FindExpressions(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      foreach (var attr in attrs.AsEnumerable()) {
        if (attr.Name == nm) {
          return attr.Args;
        }
      }
      return null;
    }

    /// <summary>
    /// Same as FindExpressions, but returns all matches
    /// </summary>
    public static List<List<Expression>> FindAllExpressions(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      List<List<Expression>> ret = null;
      for (; attrs != null; attrs = attrs.Prev) {
        if (attrs.Name == nm) {
          ret = ret ?? new List<List<Expression>>();   // Avoid allocating the list in the common case where we don't find nm
          ret.Add(attrs.Args);
        }
      }
      return ret;
    }

    /// <summary>
    /// Returns true if "nm" is a specified attribute whose arguments match the "allowed" parameter.
    /// - if "nm" is not found in attrs, return false and leave value unmodified.  Otherwise,
    /// - if "allowed" contains Empty and the Args contains zero elements, return true and leave value unmodified.  Otherwise,
    /// - if "allowed" contains Bool and Args contains one bool literal, return true and set value to the bool literal.  Otherwise,
    /// - if "allowed" contains Int and Args contains one BigInteger literal, return true and set value to the BigInteger literal.  Otherwise,
    /// - if "allowed" contains String and Args contains one string literal, return true and set value to the string literal.  Otherwise,
    /// - if "allowed" contains Expression and Args contains one element, return true and set value to the one element (of type Expression).  Otherwise,
    /// - return false, leave value unmodified, and call reporter with an error string.
    /// </summary>
    public enum MatchingValueOption { Empty, Bool, Int, String, Expression }
    public static bool ContainsMatchingValue(Attributes attrs, string nm, ref object value, IEnumerable<MatchingValueOption> allowed, Action<string> reporter) {
      Contract.Requires(nm != null);
      Contract.Requires(allowed != null);
      Contract.Requires(reporter != null);
      List<Expression> args = FindExpressions(attrs, nm);
      if (args == null) {
        return false;
      } else if (args.Count == 0) {
        if (allowed.Contains(MatchingValueOption.Empty)) {
          return true;
        } else {
          reporter("Attribute " + nm + " requires one argument");
          return false;
        }
      } else if (args.Count == 1) {
        Expression arg = args[0];
        StringLiteralExpr stringLiteral = arg as StringLiteralExpr;
        LiteralExpr literal = arg as LiteralExpr;
        if (literal != null && literal.Value is bool && allowed.Contains(MatchingValueOption.Bool)) {
          value = literal.Value;
          return true;
        } else if (literal != null && literal.Value is BigInteger && allowed.Contains(MatchingValueOption.Int)) {
          value = literal.Value;
          return true;
        } else if (stringLiteral != null && stringLiteral.Value is string && allowed.Contains(MatchingValueOption.String)) {
          value = stringLiteral.Value;
          return true;
        } else if (allowed.Contains(MatchingValueOption.Expression)) {
          value = arg;
          return true;
        } else {
          reporter("Attribute " + nm + " expects an argument in one of the following categories: " + String.Join(", ", allowed));
          return false;
        }
      } else {
        reporter("Attribute " + nm + " cannot have more than one argument");
        return false;
      }
    }

    public override IEnumerable<Node> Children => Args.Concat<Node>(
      Prev == null
        ? Enumerable.Empty<Node>()
        : new List<Node> { Prev });

    public override IEnumerable<Node> PreResolveChildren => Children;
  }

  public static class AttributesExtensions {
    /// <summary>
    /// By making this an extension method, it can also be invoked for a null receiver.
    /// </summary>
    public static IEnumerable<Attributes> AsEnumerable(this Attributes attr) {
      while (attr != null) {
        yield return attr;
        attr = attr.Prev;
      }
    }
  }

  public class UserSuppliedAttributes : Attributes {
    public readonly IToken OpenBrace;
    public readonly IToken CloseBrace;
    public bool Recognized;  // set to true to indicate an attribute that is processed by some part of Dafny; this allows it to be colored in the IDE
    public UserSuppliedAttributes(IToken tok, IToken openBrace, IToken closeBrace, List<Expression> args, Attributes prev)
      : base(tok.val, args, prev) {
      Contract.Requires(tok != null);
      Contract.Requires(openBrace != null);
      Contract.Requires(closeBrace != null);
      Contract.Requires(args != null);
      this.tok = tok;
      OpenBrace = openBrace;
      CloseBrace = closeBrace;
    }
  }

  [ContractClass(typeof(IVariableContracts))]
  public interface IVariable : IDeclarationOrUsage {
    string Name {
      get;
    }
    string DafnyName {  // what the user thinks he wrote
      get;
    }
    string DisplayName { // what the user thinks he wrote but with special treatment for wilcards
      get;
    }
    string UniqueName {
      get;
    }
    bool HasBeenAssignedUniqueName {  // unique names are not assigned until the Translator; if you don't already know if that stage has run, this boolean method will tell you
      get;
    }
    static FreshIdGenerator CompileNameIdGenerator = new FreshIdGenerator();
    string AssignUniqueName(FreshIdGenerator generator);
    string SanitizedName {
      get;
    }
    string CompileName {
      get;
    }

    PreType PreType {
      get;
      set;
    }
    Type Type {
      get;
    }
    Type OptionalType {
      get;
    }
    bool IsMutable {
      get;
    }
    bool IsGhost {
      get;
    }
    void MakeGhost();
  }
  [ContractClassFor(typeof(IVariable))]
  public abstract class IVariableContracts : TokenNode, IVariable {
    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string DafnyName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string DisplayName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string UniqueName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string SanitizedName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string CompileName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public Type OptionalType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }

    public PreType PreType { get; set; }

    public bool IsMutable {
      get {
        throw new NotImplementedException();
      }
    }
    public bool IsGhost {
      get {
        throw new NotImplementedException();
      }
    }
    public void MakeGhost() {
      throw new NotImplementedException();
    }
    public string AssignUniqueName(FreshIdGenerator generator) {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();
    }

    public abstract IToken NameToken { get; }
  }

  public abstract class NonglobalVariable : TokenNode, IVariable {
    readonly string name;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(name != null);
      Contract.Invariant(type != null);
    }

    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name;
      }
    }
    public string DafnyName => RangeToken == null || tok.line == 0 ? Name : RangeToken.PrintOriginal();
    public string DisplayName =>
      LocalVariable.DisplayNameHelper(this);

    private string uniqueName;
    public string UniqueName => uniqueName;
    public bool HasBeenAssignedUniqueName => uniqueName != null;
    public string AssignUniqueName(FreshIdGenerator generator) {
      return uniqueName ??= generator.FreshId(Name + "#");
    }

    static char[] specialChars = { '\'', '_', '?', '\\', '#' };
    /// <summary>
    /// Mangle name <c>nm</c> by replacing and escaping characters most likely to cause issues when compiling and
    /// when translating to Boogie.  This transformation is injective.
    /// </summary>
    /// <returns>A string uniquely determined from <c>nm</c>, containing none of the characters in
    /// <c>specialChars</c>.</returns>
    public static string SanitizeName(string nm) {
      if ('0' <= nm[0] && nm[0] <= '9') {
        // the identifier is one that consists of just digits
        return "_" + nm;
      }
      string name = null;
      int i = 0;
      while (true) {
        int j = nm.IndexOfAny(specialChars, i);
        if (j == -1) {
          if (i == 0) {
            return nm;  // this is the common case
          } else {
            return name + nm.Substring(i);
          }
        } else {
          string nxt = nm.Substring(i, j - i);
          name = name == null ? nxt : name + nxt;
          switch (nm[j]) {
            case '\'': name += "_k"; break;
            case '_': name += "__"; break;
            case '?': name += "_q"; break;
            case '\\': name += "_b"; break;
            case '#': name += "_h"; break;
            default:
              Contract.Assume(false);  // unexpected character
              break;
          }
          i = j + 1;
          if (i == nm.Length) {
            return name;
          }
        }
      }
    }

    private string sanitizedName;
    public virtual string SanitizedName =>
      sanitizedName ??= $"_{IVariable.CompileNameIdGenerator.FreshNumericId()}_{SanitizeName(Name)}";

    protected string compileName;
    public virtual string CompileName =>
      compileName ??= SanitizedName;

    Type type;
    public bool IsTypeExplicit = false;
    public Type SyntacticType { get { return type; } }  // returns the non-normalized type
    public PreType PreType { get; set; }

    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return type.Normalize();
      }
    }
    Type IVariable.OptionalType {
      get { return Type; }  // same as Type for NonglobalVariable
    }
    public abstract bool IsMutable {
      get;
    }
    bool isGhost;  // readonly after resolution
    public bool IsGhost {
      get {
        return isGhost;
      }
      set {
        isGhost = value;
      }
    }
    public void MakeGhost() {
      IsGhost = true;
    }

    public NonglobalVariable(IToken tok, string name, Type type, bool isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.tok = tok;
      this.name = name;
      this.type = type;
      this.isGhost = isGhost;
    }

    public IToken NameToken => tok;
    public override IEnumerable<Node> Children => IsTypeExplicit ? new List<Node>() { Type } : Enumerable.Empty<Node>();
    public override IEnumerable<Node> PreResolveChildren => IsTypeExplicit ? new List<Node>() { Type } : Enumerable.Empty<Node>();
  }

  public class Formal : NonglobalVariable, ISymbol {
    public readonly bool InParam;  // true to in-parameter, false for out-parameter
    public override bool IsMutable {
      get {
        return !InParam;
      }
    }
    public readonly bool IsOld;
    public readonly Expression DefaultValue;
    public readonly bool IsNameOnly;
    public readonly bool IsOlder;
    public readonly string NameForCompilation;

    public Formal(IToken tok, string name, Type type, bool inParam, bool isGhost, Expression defaultValue,
      bool isOld = false, bool isNameOnly = false, bool isOlder = false, string nameForCompilation = null)
      : base(tok, name, type, isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Contract.Requires(inParam || defaultValue == null);
      Contract.Requires(!isNameOnly || (inParam && !name.StartsWith("#")));
      InParam = inParam;
      IsOld = isOld;
      DefaultValue = defaultValue;
      IsNameOnly = isNameOnly;
      IsOlder = isOlder;
      NameForCompilation = nameForCompilation ?? name;
    }

    public bool HasName {
      get {
        return !Name.StartsWith("#");
      }
    }

    private string sanitizedName;
    public override string SanitizedName =>
      sanitizedName ??= SanitizeName(Name); // No unique-ification
    public override string CompileName =>
      compileName ??= SanitizeName(NameForCompilation);

    public override IEnumerable<Node> Children =>
      DefaultValue != null ? new List<Node>() { DefaultValue } : Enumerable.Empty<Node>();

    public override IEnumerable<Node> PreResolveChildren => Children;
    public DafnySymbolKind Kind => DafnySymbolKind.Variable;
  }

  /// <summary>
  /// An ImplicitFormal is a parameter that is declared implicitly, in particular the "_k" depth parameter
  /// of each extreme lemma (for use in the extreme-method body only, not the specification).
  /// </summary>
  public class ImplicitFormal : Formal {
    public ImplicitFormal(IToken tok, string name, Type type, bool inParam, bool isGhost)
      : base(tok, name, type, inParam, isGhost, null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  /// <summary>
  /// ThisSurrogate represents the implicit parameter "this". It is used to allow more uniform handling of
  /// parameters. A pointer value of a ThisSurrogate object is not important, only the fact that it is
  /// a ThisSurrogate is. ThisSurrogate objects are only used in specially marked places in the Dafny
  /// implementation.
  /// </summary>
  public class ThisSurrogate : ImplicitFormal {
    public ThisSurrogate(IToken tok, Type type)
      : base(tok, "this", type, true, false) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
    }
  }

  [DebuggerDisplay("Bound<{name}>")]
  public class BoundVar : NonglobalVariable {
    public override bool IsMutable => false;
    public BoundVar(IToken tok, string name, Type type)
      : base(tok, name, type, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  /// <summary>
  /// A QuantifiedVar is a bound variable used in a quantifier such as "forall x :: ...",
  /// a comprehension such as "set x | 0 <= x < 10", etc.
  /// In addition to its type, which may be inferred, it can have an optional domain collection expression
  /// (x <- C) and an optional range boolean expressions (x | E).
  /// </summary>
  [DebuggerDisplay("Quantified<{name}>")]
  public class QuantifiedVar : BoundVar {
    public readonly Expression Domain;
    public readonly Expression Range;

    public QuantifiedVar(IToken tok, string name, Type type, Expression domain, Expression range)
      : base(tok, name, type) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Domain = domain;
      Range = range;
    }

    /// <summary>
    /// Map a list of quantified variables to an eqivalent list of bound variables plus a single range expression.
    /// The transformation looks like this in general:
    ///
    /// x1 <- C1 | E1, ..., xN <- CN | EN
    ///
    /// becomes:
    ///
    /// x1, ... xN | x1 in C1 && E1 && ... && xN in CN && EN
    ///
    /// Note the result will be null rather than "true" if there are no such domains or ranges.
    /// Some quantification contexts (such as comprehensions) will replace this with "true".
    /// </summary>
    public static void ExtractSingleRange(List<QuantifiedVar> qvars, out List<BoundVar> bvars, out Expression range) {
      bvars = new List<BoundVar>();
      range = null;

      foreach (var qvar in qvars) {
        BoundVar bvar = new BoundVar(qvar.tok, qvar.Name, qvar.SyntacticType);
        bvars.Add(bvar);

        if (qvar.Domain != null) {
          // Attach a token wrapper so we can produce a better error message if the domain is not a collection
          var domainWithToken = QuantifiedVariableDomainCloner.Instance.CloneExpr(qvar.Domain);
          var inDomainExpr = new BinaryExpr(domainWithToken.tok, BinaryExpr.Opcode.In, new IdentifierExpr(bvar.tok, bvar), domainWithToken);
          range = range == null ? inDomainExpr : new BinaryExpr(domainWithToken.tok, BinaryExpr.Opcode.And, range, inDomainExpr);
        }

        if (qvar.Range != null) {
          // Attach a token wrapper so we can produce a better error message if the range is not a boolean expression
          var rangeWithToken = QuantifiedVariableRangeCloner.Instance.CloneExpr(qvar.Range);
          range = range == null ? qvar.Range : new BinaryExpr(rangeWithToken.tok, BinaryExpr.Opcode.And, range, rangeWithToken);
        }
      }
    }
  }

  public class ActualBinding : TokenNode {
    public readonly IToken /*?*/ FormalParameterName;
    public readonly Expression Actual;
    public readonly bool IsGhost;

    public override IEnumerable<Node> Children => new List<Node> { Actual }.Where(x => x != null);

    public override IEnumerable<Node> PreResolveChildren => Children;

    public ActualBinding(IToken /*?*/ formalParameterName, Expression actual, bool isGhost = false) {
      Contract.Requires(actual != null);
      FormalParameterName = formalParameterName;
      Actual = actual;
      IsGhost = isGhost;
    }
  }

  public class ActualBindings : TokenNode {
    public readonly List<ActualBinding> ArgumentBindings;

    public ActualBindings(List<ActualBinding> argumentBindings) {
      Contract.Requires(argumentBindings != null);
      ArgumentBindings = argumentBindings;
    }

    public ActualBindings(Cloner cloner, ActualBindings original) {
      ArgumentBindings = original.ArgumentBindings.Select(actualBinding => new ActualBinding(
        actualBinding.FormalParameterName == null ? null : cloner.Tok(actualBinding.FormalParameterName),
        cloner.CloneExpr(actualBinding.Actual))).ToList();
      if (cloner.CloneResolvedFields) {
        arguments = original.Arguments?.Select(cloner.CloneExpr).ToList();
      }
    }

    public ActualBindings(List<Expression> actuals) {
      Contract.Requires(actuals != null);
      ArgumentBindings = actuals.ConvertAll(actual => new ActualBinding(null, actual));
    }

    [FilledInDuringResolution]
    private List<Expression> arguments; // set by ResolveActualParameters during resolution

    public bool WasResolved => arguments != null;

    public List<Expression> Arguments => arguments;

    public void AcceptArgumentExpressionsAsExactParameterList(List<Expression> args = null) {
      Contract.Requires(!WasResolved); // this operation should be done at most once
      Contract.Assume(ArgumentBindings.TrueForAll(arg => arg.Actual.WasResolved()));
      arguments = args ?? ArgumentBindings.ConvertAll(binding => binding.Actual);
    }

    public override IEnumerable<Node> Children => arguments == null ? ArgumentBindings : arguments;
    public override IEnumerable<Node> PreResolveChildren => Children;
  }

  class QuantifiedVariableDomainCloner : Cloner {
    public static readonly QuantifiedVariableDomainCloner Instance = new QuantifiedVariableDomainCloner();
    private QuantifiedVariableDomainCloner() { }
    public override IToken Tok(IToken tok) {
      return new QuantifiedVariableDomainToken(tok);
    }
  }

  class QuantifiedVariableRangeCloner : Cloner {
    public static readonly QuantifiedVariableRangeCloner Instance = new QuantifiedVariableRangeCloner();
    private QuantifiedVariableRangeCloner() { }
    public override IToken Tok(IToken tok) {
      return new QuantifiedVariableRangeToken(tok);
    }
  }

  public class Specification<T> : TokenNode, IAttributeBearingDeclaration
    where T : Node {
    public readonly List<T> Expressions;

    [ContractInvariantMethod]
    private void ObjectInvariant() {
      Contract.Invariant(Expressions == null || cce.NonNullElements<T>(Expressions));
    }

    public Specification(List<T> exprs, Attributes attrs) {
      Contract.Requires(exprs == null || cce.NonNullElements<T>(exprs));
      Expressions = exprs;
      Attributes = attrs;
    }

    public Attributes Attributes { get; set; }

    public bool HasAttributes() {
      return Attributes != null;
    }

    public override IEnumerable<Node> Children => Expressions;
    public override IEnumerable<Node> PreResolveChildren => Children;
  }

  public class BottomUpVisitor {
    public void Visit(IEnumerable<Expression> exprs) {
      exprs.ForEach(Visit);
    }
    public void Visit(IEnumerable<Statement> stmts) {
      stmts.ForEach(Visit);
    }
    public void Visit(AttributedExpression expr) {
      Visit(expr.E);
    }
    public void Visit(FrameExpression expr) {
      Visit(expr.E);
    }
    public void Visit(IEnumerable<AttributedExpression> exprs) {
      exprs.ForEach(Visit);
    }
    public void Visit(IEnumerable<FrameExpression> exprs) {
      exprs.ForEach(Visit);
    }
    public void Visit(ICallable decl) {
      if (decl is Function f) {
        Visit(f);
      } else if (decl is Method m) {
        Visit(m);
      } else if (decl is TypeSynonymDecl tsd) {
        Visit(tsd);
      } else if (decl is NewtypeDecl ntd) {
        Visit(ntd);
      }
      //TODO More?
    }

    public void Visit(SubsetTypeDecl ntd) {
      if (ntd.Constraint != null) {
        Visit(ntd.Constraint);
      }

      if (ntd.Witness != null) {
        Visit(ntd.Witness);
      }
    }
    public void Visit(NewtypeDecl ntd) {
      if (ntd.Constraint != null) {
        Visit(ntd.Constraint);
      }

      if (ntd.Witness != null) {
        Visit(ntd.Witness);
      }
    }
    public void Visit(Method method) {
      Visit(method.Req);
      Visit(method.Mod.Expressions);
      Visit(method.Ens);
      Visit(method.Decreases.Expressions);
      if (method.Body != null) { Visit(method.Body); }
      //TODO More?
    }
    public void Visit(Function function) {
      Visit(function.Req);
      Visit(function.Reads);
      Visit(function.Ens);
      Visit(function.Decreases.Expressions);
      if (function.Body != null) { Visit(function.Body); }
      if (function.ByMethodBody != null) { Visit(function.ByMethodBody); }
      //TODO More?
    }
    public void Visit(Expression expr) {
      Contract.Requires(expr != null);
      // recursively visit all subexpressions and all substatements
      expr.SubExpressions.ForEach(Visit);
      if (expr is StmtExpr) {
        // a StmtExpr also has a substatement
        var e = (StmtExpr)expr;
        Visit(e.S);
      }
      VisitOneExpr(expr);
    }
    public void Visit(Statement stmt) {
      Contract.Requires(stmt != null);
      // recursively visit all subexpressions and all substatements
      stmt.SubExpressions.ForEach(Visit);
      stmt.SubStatements.ForEach(Visit);
      VisitOneStmt(stmt);
    }
    protected virtual void VisitOneExpr(Expression expr) {
      Contract.Requires(expr != null);
      // by default, do nothing
    }
    protected virtual void VisitOneStmt(Statement stmt) {
      Contract.Requires(stmt != null);
      // by default, do nothing
    }
  }
  public class TopDownVisitor<State> {
    protected bool preResolve = false;

    public void Visit(Expression expr, State st) {
      Contract.Requires(expr != null);
      if (VisitOneExpr(expr, ref st)) {
        if (preResolve && expr is ConcreteSyntaxExpression concreteSyntaxExpression) {
          concreteSyntaxExpression.PreResolveSubExpressions.ForEach(e => Visit(e, st));
        } else if (preResolve && expr is QuantifierExpr quantifierExpr) {
          // pre-resolve, split expressions are not children
          quantifierExpr.PreResolveSubExpressions.ForEach(e => Visit(e, st));
        } else {
          // recursively visit all subexpressions and all substatements
          expr.SubExpressions.ForEach(e => Visit(e, st));
        }
        if (expr is StmtExpr) {
          // a StmtExpr also has a substatement
          var e = (StmtExpr)expr;
          Visit(e.S, st);
        }
      }
    }
    public void Visit(Statement stmt, State st) {
      Contract.Requires(stmt != null);
      if (VisitOneStmt(stmt, ref st)) {
        // recursively visit all subexpressions and all substatements
        if (preResolve) {
          stmt.PreResolveSubExpressions.ForEach(e => Visit(e, st));
          stmt.PreResolveSubStatements.ForEach(s => Visit(s, st));
        } else {
          stmt.SubExpressions.ForEach(e => Visit(e, st));
          stmt.SubStatements.ForEach(s => Visit(s, st));
        }
      }
    }
    public void Visit(IEnumerable<Expression> exprs, State st) {
      exprs.ForEach(e => Visit(e, st));
    }
    public void Visit(IEnumerable<Statement> stmts, State st) {
      stmts.ForEach(e => Visit(e, st));
    }
    public void Visit(AttributedExpression expr, State st) {
      Visit(expr.E, st);
    }
    public void Visit(FrameExpression expr, State st) {
      Visit(expr.E, st);
    }
    public void Visit(IEnumerable<AttributedExpression> exprs, State st) {
      exprs.ForEach(e => Visit(e, st));
    }
    public void Visit(IEnumerable<FrameExpression> exprs, State st) {
      exprs.ForEach(e => Visit(e, st));
    }
    public void Visit(ICallable decl, State st) {
      if (decl is Function) {
        Visit((Function)decl, st);
      } else if (decl is Method) {
        Visit((Method)decl, st);
      }
      //TODO More?
    }
    public virtual void Visit(Method method, State st) {
      Visit(method.Ens, st);
      Visit(method.Req, st);
      Visit(method.Mod.Expressions, st);
      Visit(method.Decreases.Expressions, st);
      if (method.Body != null) { Visit(method.Body, st); }
      //TODO More?
    }
    public virtual void Visit(Function function, State st) {
      Visit(function.Ens, st);
      Visit(function.Req, st);
      Visit(function.Reads, st);
      Visit(function.Decreases.Expressions, st);
      if (function.Body != null) { Visit(function.Body, st); }
      //TODO More?
    }
    /// <summary>
    /// Visit one expression proper.  This method is invoked before it is invoked on the
    /// sub-parts (subexpressions and substatements).  A return value of "true" says to
    /// continue invoking the method on sub-parts, whereas "false" says not to do so.
    /// The on-return value of "st" is the value that is passed to sub-parts.
    /// </summary>
    protected virtual bool VisitOneExpr(Expression expr, ref State st) {
      Contract.Requires(expr != null);
      return true;  // by default, visit the sub-parts with the same "st"
    }

    /// <summary>
    /// Visit one statement proper.  For the rest of the description of what this method
    /// does, see VisitOneExpr.
    /// </summary>
    protected virtual bool VisitOneStmt(Statement stmt, ref State st) {
      Contract.Requires(stmt != null);
      return true;  // by default, visit the sub-parts with the same "st"
    }
  }
}
