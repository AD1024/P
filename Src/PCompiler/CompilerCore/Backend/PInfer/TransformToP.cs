using System;
using System.Collections.Generic;
using System.Linq;
using Plang.Compiler.TypeChecker;
using Plang.Compiler.TypeChecker.AST;
using Plang.Compiler.TypeChecker.AST.Declarations;
using Plang.Compiler.TypeChecker.AST.Expressions;
using Plang.Compiler.TypeChecker.Types;

namespace Plang.Compiler.Backend.PInfer
{
    public class Transform
    {

        public CompilationContext context;
        public CompiledFile monitorFile;

        public Transform(CompilationContext context)
        {
            this.context = context;
        }

        public Transform WithFile(CompiledFile file)
        {
            monitorFile = file;
            return this;
        }

        public string toP(IPExpr expr)
        {
            if (expr == null)
            {
                throw new ArgumentNullException(nameof(expr));
            }
            switch (expr)
            {
                case VariableAccessExpr varAccess: return $"{varAccess.Variable.Name}";
                case NamedTupleAccessExpr ntAccess:
                {
                    if (ntAccess.SubExpr is VariableAccessExpr && ntAccess.FieldName == "payload")
                    {
                        return toP(ntAccess.SubExpr);
                    }
                    else
                    {
                        return $"{toP(ntAccess.SubExpr)}.{ntAccess.FieldName}";
                    }
                }
                case TupleAccessExpr tAccess: return $"{toP(tAccess.SubExpr)}[{tAccess.FieldNo}]";
                case EnumElemRefExpr enumRef: return $"{enumRef.Value.Name}";
                case IntLiteralExpr intLit: return $"{intLit.Value}";
                case BoolLiteralExpr boolLit: return $"{boolLit.Value}";
                case FloatLiteralExpr floatLit: return $"{floatLit.Value}";
                case FunCallExpr funCall: {
                    if (funCall.Function.Name == "index")
                    {
                        // specifically for monitor functions
                        return $"{toP(funCall.Arguments[0])}_idx";
                    }
                    return $"{funCall.Function.Name}({string.Join(", ", funCall.Arguments.Select(toP))})";
                }
                case UnaryOpExpr unOpExpr:
                {
                    string op = unOpExpr.Operation switch
                    {
                        UnaryOpType.Negate => "-",
                        UnaryOpType.Not => "!",
                        _ => throw new System.Exception("Unknown unary operator")
                    };
                    return $"{op}({toP(unOpExpr.SubExpr)})";
                }
                case BinOpExpr binOpExpr:
                {
                    string op = binOpExpr.Operation switch
                    {
                        BinOpType.Add => "+",
                        BinOpType.Sub => "-",
                        BinOpType.Mul => "*",
                        BinOpType.Div => "/",
                        BinOpType.Mod => "%",
                        BinOpType.And => "&&",
                        BinOpType.Or => "||",
                        BinOpType.Eq => "==",
                        BinOpType.Neq => "!=",
                        BinOpType.Lt => "<",
                        BinOpType.Le => "<=",
                        BinOpType.Gt => ">",
                        BinOpType.Ge => ">=",
                        _ => throw new System.Exception("Unknown binary operator")
                    };
                    return $"({toP(binOpExpr.Lhs)} {op} {toP(binOpExpr.Rhs)})";
                }
                case SizeofExpr sizeofExpr: return $"sizeof({toP(sizeofExpr.Expr)})";
            }
            throw new Exception($"Unsupported expr: {expr}");
        }

        private bool PopulateExprs(PInferPredicateGenerator codegen, ICompilerConfiguration job, Scope globalScope, HashSet<string> reprs, List<IPExpr> list)
        {
            return reprs.Select(repr => {
                if (codegen.TryParseToExpr(job, globalScope, repr, out var expr))
                {
                    list.Add(expr);
                    return true;
                }
                job.Output.WriteError($"Failed to parse: {repr}");
                return false;
            }).All(x => x);
        }

        private void WriteLine(string line) => context.WriteLine(monitorFile.Stream, line);
        private static string MCBuff(string eventName) => $"Hist_{eventName}";
        private static string Counter(string varName) => $"Counter_{varName}";
        private static string HistItem(string payload, string idx) => $"(payload={payload}, idx={idx})";

        private void WriteHandlerForall(Hint h, PEvent e)
        {
            PEventVariable current = new("curr") { EventDecl = e };
            List<PEventVariable> forallVars = [];
            var forallArgs = h.ForallQuantifiedVars();
            bool bind = false;
            foreach (var v in forallArgs)
            {
                if (!bind && v.EventDecl == e)
                {
                    current = v;
                    bind = true;
                }
                else
                {
                    forallVars.Add(v);
                }
            }
            var existsVars = h.ExistentialQuantifiedVars();
            var pendingType = $"({string.Join(", ", forallArgs.Select(x => $"{Counter(x.Name)}: int"))})";
            foreach (var ov in forallArgs.Concat(h.ExistentialQuantifiedVars()))
            {
                WriteLine($"var {Counter(ov.Name)}: int;");
            }
            WriteLine("var exists: bool;");
            WriteLine("var n_exists: int;");
            WriteLine($"var combo: {pendingType};");
            WriteLine($"{MCBuff(e.Name)} += (sizeof({MCBuff(e.Name)}), {HistItem("payload", "event_counter")});");
            WriteLine($"{Counter(current.Name)} = sizeof({MCBuff(e.Name)}) - 1;");
            WriteLine("event_counter = event_counter + 1;");
            
            foreach (var v in forallVars)
            {
                WriteLine($"{Counter(v.Name)} = 0;");
                WriteLine($"while ({Counter(v.Name)} < sizeof({MCBuff(v.EventName)})) {{"); // forall loop
            }

            WriteLine($"if (checkGuards({string.Join(", ", forallArgs.Select(x => $"{Counter(x.Name)}"))})) {{");
            if (h.ExistentialQuantifiers > 0)
            {
                WriteLine("exists = false;");
                WriteLine("n_exists = 0;");
                foreach (var v in existsVars)
                {
                    WriteLine($"{Counter(v.Name)} = 0;");
                    WriteLine($"while ({Counter(v.Name)} < sizeof({MCBuff(v.EventName)}) && !exists) {{");
                }
                WriteLine($"if (checkFilters({string.Join(", ", h.Quantified.Select(x => $"{Counter(x.Name)}"))})) {{");
                {
                    WriteLine("n_exists = n_exists + 1;");
                    WriteLine($"if (checkMetaFilters(n_exists, {string.Join(", ", h.Quantified.Select(x => $"{Counter(x.Name)}"))})) {{");
                        WriteLine("exists = true;");
                        WriteLine("break;");
                        WriteLine("}"); // end meta filters
                    WriteLine("}"); // end filters
                }

                foreach (var v in existsVars.Select(x => x).Reverse())
                {
                    WriteLine($"{Counter(v.Name)} = {Counter(v.Name)} + 1;");
                    WriteLine("}"); // end exists loop
                }
                WriteLine("if (!exists) {");
                WriteLine($"Pending += (({string.Join(", ", forallArgs.Select(x => $"{Counter(x.Name)}={Counter(x.Name)}"))},));");
                WriteLine("}"); // end exists check
            }
            else
            {
                WriteLine($"assert checkFilters({string.Join(", ", forallArgs.Select(x => $"{Counter(x.Name)}"))});");
            }

            WriteLine("}"); // end guards check

            foreach (var v in forallVars.Select(x => x).Reverse())
            {
                WriteLine($"{Counter(v.Name)} = {Counter(v.Name)} + 1;");
                WriteLine("}"); // end forall loop
            }
            
        }

        private void WriteHandlerExists(Hint h, PEvent e)
        {
            var pendingType = $"({string.Join(", ", h.ForallQuantifiedVars().Select(x => $"{Counter(x.Name)}: int"))})";
            WriteLine("var exists: bool;");
            WriteLine("var n_exists: int;");
            WriteLine($"var resolved: set[{pendingType}];");
            WriteLine($"var combo_iter: {pendingType};");
            var existsVars = h.ExistentialQuantifiedVars();
            foreach (var v in existsVars)
            {
                WriteLine($"var {Counter(v.Name)}: int;");
            }
            WriteLine($"resolved = default(set[{pendingType}]);");
            WriteLine($"{MCBuff(e.Name)} += (sizeof({MCBuff(e.Name)}), {HistItem("payload", "event_counter")});");
            WriteLine("event_counter = event_counter + 1;");
            WriteLine("foreach (combo_iter in Pending) {");
            WriteLine("exists = false;");
            WriteLine("n_exists = 0;");
            foreach (var v in existsVars)
            {
                WriteLine($"{Counter(v.Name)} = 0;");
                WriteLine($"while ({Counter(v.Name)} < sizeof({MCBuff(v.EventName)}) && !exists) {{");
            }
            WriteLine($"if (checkFilters({string.Join(", ", h.ForallQuantifiedVars().Select(x => $"combo_iter.{Counter(x.Name)}").Concat(existsVars.Select(x => $"{Counter(x.Name)}")))})) {{");
                WriteLine("n_exists = n_exists + 1;");
                WriteLine($"if (checkMetaFilters(n_exists, {string.Join(", ", h.ForallQuantifiedVars().Select(x => $"combo_iter.{Counter(x.Name)}").Concat(existsVars.Select(x => $"{Counter(x.Name)}")))})) {{");
                    WriteLine("exists = true;");
                    WriteLine("resolved += (combo_iter);");
                    WriteLine("break;");
                WriteLine("}");
            WriteLine("}");
            foreach (var ov in existsVars.Select(x => x).Reverse())
            {
                WriteLine($"{Counter(ov.Name)} = {Counter(ov.Name)} + 1;");
                WriteLine("}"); // end exists loop
            }
            WriteLine("}"); //end combo loop

            WriteLine("foreach (combo_iter in resolved) {");
                WriteLine("Pending -= (combo_iter);");
            WriteLine("}");
        }

        private void WriteHandlerFor(PEvent e, Hint h, bool inHotState, bool existential)
        {
            WriteLine($"on {e.Name} do (payload: {e.PayloadType.OriginalRepresentation}) {{");
            if (existential)
            {
                WriteHandlerExists(h, e);
            }
            else
            {
                WriteHandlerForall(h, e);
            }
            if (!inHotState && h.ExistentialQuantifiers > 0)
            {
                WriteLine("if (sizeof(Pending) > 0) {");
                WriteLine("goto Serving_Hot;");
                WriteLine("}");
            }
            if (inHotState && h.ExistentialQuantifiers > 0)
            {
                WriteLine("if (sizeof(Pending) == 0) {");
                WriteLine("goto Serving_Cold;");
                WriteLine("}");
            }
            WriteLine("}"); // end handler
        }

        public static string GetFunctionParameters(IEnumerable<PEventVariable> evs)
        {
            return string.Join(", ",
                    evs.Select((x, i) => $"{x.Name}: {x.EventDecl.PayloadType.OriginalRepresentation}")
                       .Concat(evs.Select((x, i) => $"{x.Name}_idx: int")));
        }

        public void WriteSpecMonitor(int counter, PInferPredicateGenerator codegen, CompilationContext ctx, ICompilerConfiguration job, Scope globalScope, Hint h, HashSet<string> p, HashSet<string> q, string inv, CompiledFile monitorFile)
        {
            List<IPExpr> guards = [];
            List<IPExpr> filters = [];
            // filters about number of events under existantial quantifications
            // that pass the filters.
            List<IPExpr> metaFilters = [];
            if (PopulateExprs(codegen, job, globalScope, p, guards)
                && PopulateExprs(codegen, job, globalScope, q.Where(x => !x.Contains("_num_e_exists_")).ToHashSet(), filters)
                && PopulateExprs(codegen, job, globalScope, q.Where(x => x.Contains("_num_e_exists_")).ToHashSet(), metaFilters))
            {
                WriteLine($"// Monitor for spec: {inv}");
                string config_event = h.ConfigEvent == null ? "" : h.ConfigEvent.Name + ",";
                WriteLine($"spec {h.Name}_{counter} observes {config_event} {string.Join(", ", h.Quantified.Select(x => x.EventName).Distinct())} {{");

                var forallVars = h.ForallQuantifiedVars();

                // Guards
                WriteLine($"fun checkGuardsImpl({GetFunctionParameters(forallVars)}): bool {{");
                WriteLine($"return {(guards.Count > 0 ? string.Join(" && ", guards.Select(toP)) : "true")};");
                WriteLine($"}}");

                // Filters
                WriteLine($"fun checkFiltersImpl({GetFunctionParameters(h.Quantified)}): bool {{");
                WriteLine($"return {(filters.Count > 0 ? string.Join(" && ", filters.Select(toP)) : "true")};");
                WriteLine($"}}");

                // Meta filters
                WriteLine($"fun checkMetaFiltersImpl(_num_e_exists_: int, {GetFunctionParameters(h.Quantified)}): bool {{");
                WriteLine($"return {(metaFilters.Count > 0 ? string.Join(" && ", metaFilters.Select(toP)) : "true")};");
                WriteLine($"}}");

                // Helper function
                WriteLine($"fun checkGuards({string.Join(", ", forallVars.Select(x => $"{x.Name}_idx: int"))}): bool {{");
                WriteLine($"return checkGuardsImpl({string.Join(", ",
                                                        forallVars.Select(x => $"{MCBuff(x.EventName)}[{x.Name}_idx].payload")
                                                                  .Concat(forallVars.Select(x => $"{MCBuff(x.EventName)}[{x.Name}_idx].idx")))});");
                WriteLine("}");

                WriteLine($"fun checkFilters({string.Join(", ", h.Quantified.Select(x => $"{x.Name}_idx: int"))}): bool {{");
                WriteLine($"return checkFiltersImpl({string.Join(", ", h.Quantified.Select(x => $"{MCBuff(x.EventName)}[{x.Name}_idx].payload")
                                                                                     .Concat(h.Quantified.Select(x => $"{MCBuff(x.EventName)}[{x.Name}_idx].idx")))});");
                WriteLine("}");

                WriteLine($"fun checkMetaFilters(_num_e_exists_: int, {string.Join(", ", h.Quantified.Select(x => $"{x.Name}_idx: int"))}): bool {{");
                WriteLine($"return checkMetaFiltersImpl(_num_e_exists_, {string.Join(", ", h.Quantified.Select(x => $"{MCBuff(x.EventName)}[{x.Name}_idx].payload")
                                                                                     .Concat(h.Quantified.Select(x => $"{MCBuff(x.EventName)}[{x.Name}_idx].idx")))});");
                WriteLine("}");

                // Monitor states
                WriteLine("");

                // config events
                List<(string, string)> configFields = [];
                if (h.ConfigEvent != null)
                {
                    // this must succeed at this stage, since it was checked in the compilation stage
                    var configType = (NamedTupleType) h.ConfigEvent.PayloadType.Canonicalize();
                    foreach (var field in configType.Fields)
                    {
                        WriteLine($"var {field.Name}: {field.Type.OriginalRepresentation};");
                        configFields.Add((field.Name, field.Type.OriginalRepresentation));
                    }
                }
                WriteLine("var event_counter: int;");

                // event history
                var pendingType = $"({string.Join(", ", h.ForallQuantifiedVars().Select(x => $"{Counter(x.Name)}: int"))})";
                string histItemType(string payload) => $"(payload: {payload}, idx: int)";
                foreach (var forall_e in h.ForallQuantified())
                {
                    WriteLine($"var {MCBuff(forall_e.Name)}: seq[{histItemType(forall_e.PayloadType.OriginalRepresentation)}];");
                }
                WriteLine($"var Pending: set[{pendingType}];");
                foreach (var exists_e in h.ExistentialQuantified())
                {
                    WriteLine($"var {MCBuff(exists_e.Name)}: seq[{histItemType(exists_e.PayloadType.OriginalRepresentation)}];");
                }

                // Begin Init state
                WriteLine("start state Init {"); // Init
                WriteLine("entry {");
                foreach (var (n, t) in configFields)
                {
                    WriteLine($"{n} = default({t});");
                }
                WriteLine("event_counter = 0;");
                foreach (var forall_e in h.ForallQuantified())
                {
                    WriteLine($"{MCBuff(forall_e.Name)} = default(seq[{histItemType(forall_e.PayloadType.OriginalRepresentation)}]);");
                }
                WriteLine($"Pending = default(set[{pendingType}]);");
                foreach (var exists_e in h.ExistentialQuantified())
                {
                    WriteLine($"{MCBuff(exists_e.Name)} = default(seq[{histItemType(exists_e.PayloadType.OriginalRepresentation)}]);");
                }
                if (h.ConfigEvent == null)
                {
                    // directly goto monitoring state
                    WriteLine("goto Serving_Cold;");
                }
                WriteLine("}"); // End entry
                if (h.ConfigEvent != null)
                {
                    WriteLine($"on {h.ConfigEvent.Name} do (payload: {h.ConfigEvent.PayloadType.OriginalRepresentation}) {{");
                    foreach (var (n, _) in configFields)
                    {
                        WriteLine($"{n} = payload.{n};");
                    }
                    WriteLine("goto Serving_Cold;");
                    WriteLine("}"); // End config event
                }
                WriteLine("}"); // End Init

                WriteLine("cold state Serving_Cold {"); // Serving_Cold
                foreach (var ev in h.ForallQuantified())
                {
                    WriteHandlerFor(ev, h, false, false);
                }
                foreach (var ev in h.ExistentialQuantified())
                {
                    WriteHandlerFor(ev, h, false, true);
                }
                WriteLine("}"); // End Serving_Cold

                if (h.ExistentialQuantifiers > 0)
                {
                    WriteLine("hot state Serving_Hot {"); // Serving_Hot
                    foreach (var ev in h.ForallQuantified())
                    {
                        WriteHandlerFor(ev, h, true, false);
                    }
                    foreach (var ev in h.ExistentialQuantified())
                    {
                        WriteHandlerFor(ev, h, true, true);
                    }
                    WriteLine("}"); // End Serving_Hot
                }
                WriteLine($"}} // {h.Name}");
            }
            else
            {
                return;
            }
        }
    }
}