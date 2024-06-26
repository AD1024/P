using System;
using System.Collections.Generic;
using System.Linq;
using Plang.Compiler.Backend.Java;
using Plang.Compiler.TypeChecker.AST;
using Plang.Compiler.TypeChecker.AST.Declarations;
using Plang.Compiler.TypeChecker.AST.Expressions;
using Plang.Compiler.TypeChecker.Types;

namespace Plang.Compiler.Backend.PInfer
{
    public class JavaCodegen : MachineGenerator
    {
        public HashSet<string> FuncNames = [];
        private readonly HashSet<IPExpr> Predicates;
        private readonly IEnumerable<IPExpr> Terms;
        private readonly IDictionary<IPExpr, HashSet<Variable>> FreeEvents;

        public JavaCodegen(ICompilerConfiguration job, string filename, HashSet<IPExpr> predicates, IEnumerable<IPExpr> terms, IDictionary<IPExpr, HashSet<Variable>> freeEvents) : base(job, filename)
        {
            Predicates = predicates;
            Terms = terms;
            FreeEvents = freeEvents;
            Job = job;
        }

        private string SimplifiedJavaType(PLanguageType type)
        {
            if (type is EnumType || type is Index)
            {
                return "int";
            }
            var javaType = Types.JavaTypeFor(type);
            if (javaType.IsPrimitive)
            {
                return javaType.TypeName;
            }
            return "JSONObject";
        }

        public string GenerateRawExpr(IPExpr expr)
        {
            var result = GenerateCodeExpr(expr).Replace("\"", "");
            if (FreeEvents.ContainsKey(expr)) {
                var events = FreeEvents[expr].Select(x => {
                        var e = (PEventVariable) x;
                        return $"({e.Name}:{e.EventName})";
                });
                return result + $" => {SimplifiedJavaType(expr.Type)} where " + string.Join(" ", events);
            }
            return result;
        }

        protected override void GenerateCodeImpl()
        {
            WriteLine("public class " + Job.ProjectName + " implements Serializable {");
            WriteLine("public record PredicateWrapper (String repr, boolean negate) {}");
            foreach (var pred in PredicateStore.Store)
            {
                WriteFunction(pred.Function);
            }
            foreach (var func in FunctionStore.Store)
            {
                WriteFunction(func);
            }
            Dictionary<string, (string, List<Variable>)> repr2Metadata = [];
            var i = 0;
            foreach (var predicate in Predicates)
            {
                var rawExpr = GenerateRawExpr(predicate);
                var fname = $"predicate_{i++}";
                var parameters = WritePredicateDefn(predicate, fname);
                repr2Metadata[rawExpr] = (fname, parameters);
            }
            WritePredicateInterface(repr2Metadata);
            repr2Metadata = [];
            foreach (var term in Terms)
            {
                var rawExpr = GenerateRawExpr(term);
                var fname = $"term_{i++}";
                repr2Metadata[rawExpr] = (fname, WriteTermDefn(term, fname));
            }
            WriteTermInterface(repr2Metadata);
            WriteLine("}");
        }

        protected void WriteTermInterface(IDictionary<string, (string, List<Variable>)> nameMap)
        {
            WriteLine($"public static Object termOf(String repr, {Constants.EventNamespaceName}.EventBase[] arguments) {{");
            WriteLine("return switch (repr) {");
            foreach (var (repr, (fname, parameters)) in nameMap)
            {
                WriteLine($"case \"{repr}\" -> {fname}({string.Join(", ", Enumerable.Range(0, parameters.Count).Select(i => $"({Constants.EventNamespaceName}.{Names.GetNameForDecl(((PEventVariable) parameters[i]).EventDecl)}) arguments[{((PEventVariable) parameters[i]).Order}]"))});");
            }
            WriteLine("default -> throw new RuntimeException(\"Invalid representation: \" + repr);");
            WriteLine("};");
            WriteLine("}");
        }

        protected void WritePredicateInterface(IDictionary<string, (string, List<Variable>)> nameMap)
        {
            WriteLine($"public static boolean invoke(PredicateWrapper repr, {Constants.EventNamespaceName}.EventBase[] arguments) {{");
            WriteLine("return switch (repr.repr()) {");
            foreach (var (repr, (fname, parameters)) in nameMap)
            {
                WriteLine($"case \"{repr}\" -> {fname}({string.Join(", ", Enumerable.Range(0, parameters.Count).Select(i => $"({Constants.EventNamespaceName}.{Names.GetNameForDecl(((PEventVariable) parameters[i]).EventDecl)}) arguments[{((PEventVariable) parameters[i]).Order}]"))});");
            }
            WriteLine("default -> throw new RuntimeException(\"Invalid representation: \" + repr);");
            WriteLine("};");
            WriteLine("}");

            WriteLine($"public static boolean conjoin(List<PredicateWrapper> repr, {Constants.EventNamespaceName}.EventBase[] arguments) {{");
            WriteLine("for (PredicateWrapper wrapper: repr) {");
            WriteLine("if (wrapper.negate() == invoke(wrapper, arguments)) return false;");
            WriteLine("}");
            WriteLine("return true;");
            WriteLine("}");
        }

        protected List<Variable> WriteTermDefn(IPExpr term, string fname)
        {
            var parameters = FreeEvents[term].ToList();
            var type = term.Type.Canonicalize();
            var retType = "Object";
            if (type is PrimitiveType)
            {
                retType = Types.JavaTypeFor(type).TypeName;
            }
            if (type is EnumType)
            {
                retType = "int";
            }
            WriteLine($"private static {retType} {fname}({string.Join(", ", parameters.Select(x => $"{Constants.EventNamespaceName}.{Names.GetNameForDecl(((PEventVariable) x).EventDecl)} " + x.Name))}) {{");
            if (type is EnumType)
            {
                WriteLine("return " + GenerateCodeExpr(term) + ".getValue();");
            }
            else
            {
                WriteLine("return " + GenerateCodeExpr(term) + ";");
            }
            WriteLine("}");
            return parameters;
        }

        protected List<Variable> WritePredicateDefn(IPExpr predicate, string fname)
        {
            var parameters = FreeEvents[predicate].ToList();
            WriteLine($"private static boolean {fname}({string.Join(", ", parameters.Select(x => $"{Constants.EventNamespaceName}.{Names.GetNameForDecl(((PEventVariable) x).EventDecl)} " + x.Name))}) {{");
            WriteLine("return " + GenerateCodeExpr(predicate) + ";");
            WriteLine("}");
            return parameters;
        }

        // protected override void WriteFileHeader()
        // {
        //     WriteLine(Constants.DoNotEditWarning[1..]);
        //     WriteImports();
        //     WriteLine();
        // }

        internal string GenerateCodeExpr(IPExpr expr)
        {
            if (expr is VariableAccessExpr v)
            {
                return GenerateCodeVariable(v.Variable);
            }
            else if (expr is PredicateCallExpr p)
            {
                return GenerateCodePredicateCall(p);
            }
            else if (expr is FunCallExpr f)
            {
                return GenerateFuncCall(f);
            }
            else if (expr is TupleAccessExpr t)
            {
                return GenerateCodeTupleAccess(t);
            }
            else if (expr is NamedTupleAccessExpr n)
            {
                return GenerateCodeNamedTupleAccess(n);
            }
            else if (expr is IPredicate)
            {
                var predicate = (IPredicate) expr;
                return $"{predicate.Name} :: {string.Join(" -> ", predicate.Signature.ParameterTypes.Select(PInferPredicateGenerator.ShowType)) + " -> bool"}";
            }
            else if (expr is BinOpExpr binOpExpr)
            {
                var lhs = GenerateCodeExpr(binOpExpr.Lhs);
                var rhs = GenerateCodeExpr(binOpExpr.Rhs);
                return binOpExpr.Operation switch
                {
                    BinOpType.Add => $"(({lhs}) + ({rhs}))",
                    BinOpType.Sub => $"(({lhs}) - ({rhs}))",
                    BinOpType.Mul => $"(({lhs}) * ({rhs}))",
                    BinOpType.Div => $"(({lhs}) / ({rhs}))",
                    BinOpType.Mod => $"(({lhs}) % ({rhs}))",
                    BinOpType.Eq => $"Objects.equals({lhs}, {rhs})",
                    BinOpType.Lt => $"(({lhs}) < ({rhs}))",
                    BinOpType.Gt => $"(({lhs}) < ({rhs}))",
                    BinOpType.And => $"(({lhs}) && ({rhs}))",
                    BinOpType.Or => $"(({lhs}) || ({rhs}))",
                    _ => throw new Exception($"Unsupported BinOp Operatoion: {binOpExpr.Operation}"),
                };
            }
            else
            {
                throw new Exception($"Unsupported expression type {expr.GetType()}");
            }
        }

        private string GenerateCodeCall(string callee, params string[] args)
        {
            return $"{callee}({string.Join(", ", args)})";
        }

        private string GenerateCodeTupleAccess(TupleAccessExpr t)
        {
            return $"{GenerateCodeExpr(t.SubExpr)}[{t.FieldNo}]";
        }

        private string GenerateCodeNamedTupleAccess(NamedTupleAccessExpr n)
        {
            if (n.SubExpr is VariableAccessExpr v && v.Variable is PEventVariable)
            {
                return $"{GenerateCodeExpr(n.SubExpr)}.{n.FieldName}()";
            }
            return GenerateJSONObjectGet(GenerateCodeExpr(n.SubExpr), n.FieldName, n.Type.Canonicalize());
        }

        private string GenerateCodePredicateCall(PredicateCallExpr p)
        {
            if (p.Predicate is BuiltinPredicate)
            {
                switch (p.Predicate.Notation)
                {
                    case Notation.Infix:
                        if (p.Predicate.Name == "==")
                        {
                            return $"Objects.equals({GenerateCodeExpr(p.Arguments[0])}, {GenerateCodeExpr(p.Arguments[1])})";
                        }
                        return $"{GenerateCodeExpr(p.Arguments[0])} {p.Predicate.Name} {GenerateCodeExpr(p.Arguments[1])}";
                }
            }
            var args = (from e in p.Arguments select GenerateCodeExpr(e)).ToArray();
            return GenerateCodeCall(p.Predicate.Name, args);
        }

        private string GenerateFuncCall(FunCallExpr funCallExpr)
        {
            if (funCallExpr.Function is BuiltinFunction builtinFun)
            {
                switch (builtinFun.Notation)
                {
                    case Notation.Infix:
                        if (builtinFun.Name == "==")
                        {
                            return $"Objects.equals({GenerateCodeExpr(funCallExpr.Arguments[0])}, {GenerateCodeExpr(funCallExpr.Arguments[1])})";
                        }
                        return $"({GenerateCodeExpr(funCallExpr.Arguments[0])} {builtinFun.Name} {GenerateCodeExpr(funCallExpr.Arguments[1])})";
                    default:
                        break;
                }
                if (funCallExpr.Function.Name == "index")
                {
                    return $"{GenerateCodeExpr(funCallExpr.Arguments[0])}.index()";
                }
            }
            return $"{funCallExpr.Function.Name}(" + string.Join(", ", (from e in funCallExpr.Arguments select GenerateCodeExpr(e)).ToArray()) + ")";
        }

        private static string GenerateCodeVariable(Variable v)
        {
            if (v is PEventVariable eVar)
            {
                return $"{eVar.Name}.payload()";
            }
            return v.Name;
        }
    }
}