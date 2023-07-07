#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Errors = Microsoft.Dafny.Errors;
using Function = Microsoft.Dafny.Function;
using Parser = Microsoft.Dafny.Parser;
using Program = Microsoft.Dafny.Program;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  public static class Utils {

    /// <summary>
    /// Call Translator with larger stack to prevent stack overflow
    /// </summary>
    public static List<Microsoft.Boogie.Program> Translate(Program program) {
      var ret = new List<Microsoft.Boogie.Program> { };
      var thread = new System.Threading.Thread(
        () => {
          ret = Translator
            .Translate(program, program.Reporter)
            .ToList().ConvertAll(tuple => tuple.Item2);
        },
        0x10000000); // 256MB stack size to prevent stack overflow
      thread.Start();
      thread.Join();
      return ret;
    }

    /// <summary>
    /// Take a resolved type and change all names to fully-qualified.
    /// </summary>
    public static Type UseFullName(Type type) {
      return DafnyModelTypeUtils
        .ReplaceType(type, _ => true, typ => new UserDefinedType(
          new Token(),
          typ?.ResolvedClass?.FullName == null ?
            typ.Name :
            typ.ResolvedClass.FullName + (typ.Name.Last() == '?' ? "?" : ""),
          typ.TypeArgs));
    }

    /// <summary>
    /// Copy a <param name="type"></param> and recursively replace type
    /// arguments named as in <param name="from"></param> with types from
    /// <param name="to"></param>.
    /// </summary>
    public static Type CopyWithReplacements(Type type, List<string> from, List<Type> to) {
      if (from.Count != to.Count) {
        return type;
      }
      Dictionary<string, Type> replacements = new();
      for (int i = 0; i < from.Count; i++) {
        replacements[from[i]] = to[i];
      }
      replacements["_System.string"] =
        new UserDefinedType(new Token(), "string", new List<Type>());
      replacements["_System.nat"] =
        new UserDefinedType(new Token(), "nat", new List<Type>());
      replacements["_System.object"] =
        new UserDefinedType(new Token(), "object", new List<Type>());
      return DafnyModelTypeUtils.ReplaceType(type, _ => true,
        typ => replacements.ContainsKey(typ.Name) ?
          replacements[typ.Name] :
          new UserDefinedType(typ.tok, typ.Name, typ.TypeArgs));
    }

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public static Program/*?*/ Parse(DafnyOptions options, string source, bool resolve = true, Uri uri = null) {
      uri ??= new Uri(Path.GetTempPath());
      var reporter = new BatchErrorReporter(options);

      var program = new ProgramParser().ParseFiles(uri.LocalPath, new DafnyFile[] { new(reporter.Options, uri, new StringReader(source)) },
        reporter, CancellationToken.None);

      if (!resolve) {
        return program;
      }

      // Substitute function methods with function-by-methods
      new AddByMethodRewriter(new ConsoleErrorReporter(options)).PreResolve(program);
      new ProgramResolver(program).Resolve(CancellationToken.None);
      return program;
    }

    /// <summary>
    /// Deep clone a Boogie program.
    /// </summary>
    public static Microsoft.Boogie.Program DeepCloneProgram(DafnyOptions options, Microsoft.Boogie.Program program) {
      var textRepresentation = GetStringRepresentation(options, program);
      Microsoft.Boogie.Parser.Parse(textRepresentation, "", out var copy);
      return copy;
    }

    /// <summary>
    /// Deep clone and re-resolve a Boogie program.
    /// </summary>
    public static Microsoft.Boogie.Program DeepCloneResolvedProgram(Microsoft.Boogie.Program program, DafnyOptions options) {
      program = DeepCloneProgram(options, program);
      program.Resolve(options);
      program.Typecheck(options);
      return program;
    }

    public static string GetStringRepresentation(DafnyOptions options, Microsoft.Boogie.Program program) {
      var oldPrintInstrumented = options.PrintInstrumented;
      var oldPrintFile = options.PrintFile;
      options.PrintInstrumented = true;
      options.PrintFile = "-";
      var output = new StringWriter();
      program.Emit(new TokenTextWriter(output, options));
      options.PrintInstrumented = oldPrintInstrumented;
      options.PrintFile = oldPrintFile;
      return output.ToString();
    }

    /// <summary>
    /// Turns each function into a function-by-method.
    /// Copies body of the function into the body of the corresponding method.
    /// </summary>
    private class AddByMethodRewriter : IRewriter {

      protected internal AddByMethodRewriter(ErrorReporter reporter) : base(reporter) { }

      internal void PreResolve(Program program) {
        AddByMethod(program.DefaultModule);
      }

      private static void AddByMethod(TopLevelDecl d) {
        if (d is LiteralModuleDecl moduleDecl) {
          foreach (var topLevelDecl in moduleDecl.ModuleDef.TopLevelDecls) {
            AddByMethod(topLevelDecl);
          }
        } else if (d is TopLevelDeclWithMembers withMembers) {
          withMembers.Members.OfType<Function>().Iter(AddByMethod);
        }
      }

      private static Attributes RemoveOpaqueAttr(Attributes attributes, Cloner cloner) {
        if (attributes == null) {
          return null;
        }
        if (attributes.Name == "opaque") {
          RemoveOpaqueAttr(attributes.Prev, cloner);
        }
        if (attributes is UserSuppliedAttributes) {
          var usa = (UserSuppliedAttributes)attributes;
          return new UserSuppliedAttributes(
            cloner.Tok(usa.tok),
            cloner.Tok(usa.OpenBrace),
            cloner.Tok(usa.CloseBrace),
            attributes.Args.ConvertAll(cloner.CloneExpr),
            RemoveOpaqueAttr(attributes.Prev, cloner));
        }
        return new Attributes(attributes.Name,
          attributes.Args.ConvertAll(cloner.CloneExpr),
          RemoveOpaqueAttr(attributes.Prev, cloner));
      }

      private static void AddByMethod(Function func) {
        func.Attributes = RemoveOpaqueAttr(func.Attributes, new Cloner());
        if (func.IsGhost || func.Body == null || func.ByMethodBody != null) {
          return;
        }
        var returnStatement = new ReturnStmt(new RangeToken(new Token(), new Token()),
          new List<AssignmentRhs> { new ExprRhs(new Cloner().CloneExpr(func.Body)) });
        func.ByMethodBody = new BlockStmt(
          new RangeToken(new Token(), new Token()),
          new List<Statement> { returnStatement });
        func.ByMethodTok = func.Body.tok;
      }
    }

    /// <summary>
    /// Scan an unresolved dafny program to look for a specific attribute
    /// </summary>
    internal class AttributeFinder {

      public static bool ProgramHasAttribute(Program program, string attribute) {
        return DeclarationHasAttribute(program.DefaultModule, attribute);
      }

      private static bool DeclarationHasAttribute(TopLevelDecl decl, string attribute) {
        if (decl is LiteralModuleDecl moduleDecl) {
          return moduleDecl.ModuleDef.TopLevelDecls
            .Any(declaration => DeclarationHasAttribute(declaration, attribute));
        }
        if (decl is TopLevelDeclWithMembers withMembers) {
          return withMembers.Members
            .Any(member => MembersHasAttribute(member, attribute));
        }
        return false;
      }

      private static bool MembersHasAttribute(MemberDecl member, string attribute) {
        var attributes = member.Attributes;
        while (attributes != null) {
          if (attributes.Name == attribute) {
            return true;
          }
          attributes = attributes.Prev;
        }
        return false;
      }
    }
  }
}
