﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

using Microsoft.Formula.API;
using Microsoft.Formula.API.Nodes;

namespace Microsoft.Pc
{
    partial class PToZing : PTranslation
    {
        public const string SM_EVENT = "SM_EVENT";
        public static AST<Node> SmEvent = Factory.Instance.MkCnst("SM_EVENT");
        public const string SM_TRANSITION = "SM_TRANSITION";
        public static AST<Node> SmTransition = Factory.Instance.MkCnst("SM_TRANSITION");
        public const string SM_STATE = "SM_STATE";
        public static AST<Node> SmState = Factory.Instance.MkCnst("SM_STATE");
        public const string SM_HANDLE = "SM_HANDLE";
        public static AST<Node> SmHandle = Factory.Instance.MkCnst("SM_HANDLE");
        public static string SM_EVENT_SET = "SM_EVENT_SET";
        public static AST<Node> SmEventSet = Factory.Instance.MkCnst("SM_EVENT_SET");
        public const string PRT_VALUE = "PRT_VALUE";
        public static AST<Node> PrtValue = Factory.Instance.MkCnst("PRT_VALUE");
        public static AST<Node> PrtType = Factory.Instance.MkCnst("PRT_TYPE");
        public static AST<Node> PrtCastValue = MkZingDot("PRT_VALUE", "PrtCastValue");
        public static AST<Node> PrtMkDefaultValue = MkZingDot("PRT_VALUE", "PrtMkDefaultValue");
        public static AST<Node> PrtCloneValue = MkZingDot("PRT_VALUE", "PrtCloneValue");
        public static AST<Node> PrtIsEqualValue = MkZingDot("PRT_VALUE", "PrtIsEqualValue");

        private static HashSet<string> ReservedNames = new HashSet<string>(
            new string[] { "Main", "SM_NULL", "MachineId", "SM_EVENT", "SM_TRANSITION", "SM_STATE", "SM_HANDLE", "EVENT_NODE", "EVENT_BUFFER", "StateStack", "StackFrame", "Continuation",
                           "FairScheduler", "FairChoice", "FairCycle", "PRT_FIELD_NAME", "PRT_TYPE", "PRT_VALUE", "PRT_SEQ", "PRT_MAP",
                           "Machine", "Event", "State", "ActionOrFun", "ContinuationReason", "GateStatus", "StateTemperature", "PRT_TYPE_KIND",
                            "SM_EVENT_ARRAY", "SM_TRANSITION_ARRAY", "ActionOrFun_ARRAY", "PRT_TYPE_ARRAY", "PRT_FIELD_NAME_ARRAY", "PRT_VALUE_ARRAY" });

        private static string ZingMachineClassName(string machineName)
        {
            return string.Format("MACHINE_{0}", machineName);
        }

        public PToZing(Compiler compiler, AST<Model> modelWithTypes, Dictionary<string, Dictionary<int, SourceInfo>> idToSourceInfo)
            : base(compiler, modelWithTypes, idToSourceInfo)
        {
            this.typeContext = new TypeTranslationContext(this);
            GenerateTypeInfo(modelWithTypes);
        }

        #region Static helpers
        private static AST<Model> Add(AST<Model> m, AST<FuncTerm> ft)
        {
            return Factory.Instance.AddFact(m, Factory.Instance.MkModelFact(null, ft));
        }

        private static AST<Node> ConstructList(AST<FuncTerm> constructor, IEnumerable<AST<Node>> elems, AST<Node> def = null)
        {
            AST<Node> ret = def == null ? ZingData.Cnst_Nil : def;
            var reverseElems = new List<AST<Node>>(elems);
            reverseElems.Reverse();
            foreach (var n in reverseElems)
            {
                ret = Factory.Instance.AddArg(Factory.Instance.AddArg(constructor, n), ret);
            }

            return ret;
        }

        private static AST<Node> ConstructList(AST<FuncTerm> constructor, params AST<Node>[] elems)
        {
            return ConstructList(constructor, new List<AST<Node>>(elems));
        }

        private static AST<FuncTerm> MkZingFile(string filename, List<AST<Node>> elements)
        {
            return AddArgs(ZingData.App_File, Factory.Instance.MkCnst(filename), ConstructList(ZingData.App_Decls, elements));
        }

        private static AST<FuncTerm> MkZingIdentifier(string name)
        {
            return Factory.Instance.AddArg(ZingData.App_Identifier, Factory.Instance.MkCnst(name));
        }

        private static AST<FuncTerm> MkZingDot(string first, params string[] names)
        {
            AST<FuncTerm> lhs = MkZingIdentifier(first);
            for (int i = 0; i < names.Length; i++)
            {
                AST<FuncTerm> rhs = MkZingIdentifier(names[i]);
                lhs = MkZingApply(ZingData.Cnst_Dot, lhs, rhs);
            }
            return lhs;
        }

        private static AST<FuncTerm> MkZingDot(AST<Node> n, string first, params string[] names)
        {
            AST<FuncTerm> lhs = MkZingApply(ZingData.Cnst_Dot, n, MkZingIdentifier(first));
            for (int i = 0; i < names.Length; i++)
            {
                AST<FuncTerm> rhs = MkZingIdentifier(names[i]);
                lhs = MkZingApply(ZingData.Cnst_Dot, lhs, rhs);
            }
            return lhs;
        }

        private static AST<Node> MkZingEvent(string eventName)
        {
            return MkZingDot("Main", string.Format("{0}_SM_EVENT", eventName));
        }

        private static AST<Node> MkZingEnum(string enumName)
        {
            return MkZingDot("Main", string.Format("{0}_SM_ENUM", enumName));
        }

        private static AST<Node> MkZingState(string stateName)
        {
            return MkZingDot("Main", string.Format("{0}_SM_STATE", stateName));
        }

        private static AST<FuncTerm> MkZingReturn(AST<Node> rVal)
        {
            return AddArgs(ZingData.App_Return, rVal);
        }

        private static AST<FuncTerm> MkZingIfThen(AST<Node> cond, AST<Node> then)
        {
            return AddArgs(ZingData.App_ITE, cond, then, ZingData.Cnst_Nil);
        }

        private static AST<FuncTerm> MkZingIfThenElse(AST<Node> cond, AST<Node> thenstmt, AST<Node> elsestmt)
        {
            return AddArgs(ZingData.App_ITE, cond, thenstmt, elsestmt);
        }

        private static AST<Node> MkZingNeq(AST<Node> e1, AST<Node> e2)
        {
            return MkZingApply(ZingData.Cnst_NEq, e1, e2);
        }

        private static AST<Node> MkZingEq(AST<Node> e1, AST<Node> e2)
        {
            return MkZingApply(ZingData.Cnst_Eq, e1, e2);
        }

        private static AST<Node> MkZingOr(AST<Node> e1, AST<Node> e2)
        {
            return MkZingApply(ZingData.Cnst_Or, e1, e2);
        }

        private static AST<Node> MkZingIn(AST<Node> e1, AST<Node> e2)
        {
            return MkZingApply(ZingData.Cnst_In, e1, e2);
        }

        private static void AddEventSet(List<AST<Node>> stmts, IEnumerable<string> eventNames, AST<Node> set)
        {
            foreach (var eventName in eventNames)
            {
                var addExpr = MkZingApply(ZingData.Cnst_Add, set, MkZingEvent(eventName));
                var addStmt = AddArgs(ZingData.App_Assign, set, addExpr);
                stmts.Add(addStmt);
            }
        }

        private static void SubtractEventSet(List<AST<Node>> stmts, IEnumerable<string> eventNames, AST<Node> actionSet)
        {
            foreach (var eventName in eventNames)
            {
                var subExpr = MkZingApply(ZingData.Cnst_Sub, actionSet, MkZingEvent(eventName));
                var subStmt = AddArgs(ZingData.App_Assign, actionSet, subExpr);
                stmts.Add(subStmt);
            }
        }

        private static AST<FuncTerm> MkZingCall(AST<Node> methodExpr, params AST<Node>[] args)
        {
            List<AST<Node>> argList = new List<AST<Node>>();
            argList.Add(methodExpr);
            foreach (var arg in args)
                argList.Add(arg);
            return Factory.Instance.AddArg(ZingData.App_Call, ConstructList(ZingData.App_Args, argList));
        }

        private static AST<FuncTerm> MkZingStrings(IEnumerable<AST<Node>> args)
        {
            List<AST<Node>> argList = new List<AST<Node>>();
            foreach (var arg in args)
                argList.Add(arg);
            return AddArgs(ZingData.App_Apply, args);
        }

        private static AST<FuncTerm> MkZingCall(AST<Node> methodExpr, IEnumerable<AST<Node>> args)
        {
            List<AST<Node>> argList = new List<AST<Node>>();
            argList.Add(methodExpr);
            foreach (var arg in args)
                argList.Add(arg);
            return Factory.Instance.AddArg(ZingData.App_Call, ConstructList(ZingData.App_Args, argList));
        }

        private static AST<FuncTerm> MkZingCallStmt(AST<Node> callExpr, params AST<Node>[] attrs)
        {
            return AddArgs(ZingData.App_CallStmt, callExpr, ConstructList(ZingData.App_Attrs, attrs));
        }

        private static AST<FuncTerm> MkZingMethodDecl(string methodName, AST<Node> parameters, AST<Node> returnType, AST<Node> locals, AST<Node> body, params AST<Node>[] attrs)
        {
            return AddArgs(ZingData.App_MethodDecl, Factory.Instance.MkCnst(methodName), parameters, returnType, locals, body, ConstructList(ZingData.App_Attrs, attrs));
        }

        private static AST<FuncTerm> MkZingGoto(string labelName)
        {
            return Factory.Instance.AddArg(ZingData.App_Goto, Factory.Instance.MkCnst(labelName));
        }

        private static AST<FuncTerm> MkZingBlock(string label, AST<Node> body)
        {
            return AddArgs(ZingData.App_LabelStmt, Factory.Instance.MkCnst(label), body);
        }

        private static AST<Node> MkZingBlocks(params AST<Node>[] blocks)
        {
            return ConstructList(ZingData.App_Blocks, blocks);
        }

        private static AST<Node> MkZingBlocks(List<AST<Node>> blocks)
        {
            return ConstructList(ZingData.App_Blocks, blocks);
        }

        private static AST<Node> MkZingNew(AST<Node> constructedType, AST<Node> optionalSize)
        {
            return AddArgs(ZingData.App_New, constructedType, optionalSize);
        }

        private static AST<FuncTerm> MkZingAssign(AST<Node> lhs, AST<Node> rhs)
        {
            return AddArgs(ZingData.App_Assign, lhs, rhs);
        }

        private static AST<FuncTerm> MkZingVarDecl(string varName, AST<Node> varType, params AST<Node>[] attrs)
        {
            return AddArgs(ZingData.App_VarDecl, Factory.Instance.MkCnst(varName), varType, ConstructList(ZingData.App_Attrs, attrs));
        }

        private static AST<Node> MkZingVarDecls(IEnumerable<AST<Node>> vars)
        {
            return ConstructList(ZingData.App_VarDecls, vars);
        }

        private static AST<Node> MkZingEnumDecl(string enumName, List<AST<Node>> enumElems)
        {
            return AddArgs(ZingData.App_EnumDecl, Factory.Instance.MkCnst(enumName), ConstructList(ZingData.App_EnumElems, enumElems));
        }

        private static AST<Node> MkZingMethodDecls(IEnumerable<AST<Node>> decls)
        {
            return ConstructList(ZingData.App_MethodDecls, decls);
        }

        private static AST<FuncTerm> MkZingApply(AST<Id> op, params AST<Node>[] args)
        {
            return AddArgs(ZingData.App_Apply, op, ConstructList(ZingData.App_Args, args));
        }

        private AST<Node> MkZingActionOrFun(string machineName, string entityName)
        {
            if (allMachines[machineName].funNameToFunInfo.ContainsKey(entityName))
            {
                return MkZingDot("ActionOrFun", string.Format("_{0}_{1}", machineName, entityName));
            }
            else
            {
                return MkZingDot("ActionOrFun", string.Format("_{0}", entityName));
            }
        }

        private static AST<Node> MkZingVarDecls(params AST<Node>[] vars)
        {
            return ConstructList(ZingData.App_VarDecls, vars);
        }

        private static AST<Node> MkZingIndex(AST<Node> baseExp, AST<Node> indExp)
        {
            return MkZingApply(ZingData.Cnst_Index, baseExp, indExp);
        }

        private static AST<Node> MkZingSeq(List<AST<Node>> stmts)
        {
            AST<Node> ret = ZingData.Cnst_Nil;
            foreach (var stmt in stmts.Reverse<AST<Node>>())
            {
                ret = AddArgs(ZingData.App_Seq, stmt, ret);
            }
            return ret;
        }

        private static AST<Node> MkZingSeq(params AST<Node>[] stmts)
        {
            return MkZingSeq(new List<AST<Node>>(stmts));
        }

        private static AST<Node> MkZingWhile(AST<Node> condition, AST<Node> stmt)
        {
            return AddArgs(ZingData.App_While, condition, stmt);
        }

        private static AST<FuncTerm> MkZingTrace(string msg, params AST<Node>[] exprs)
        {
            var argList = new List<AST<Node>>(new AST<Node>[] { Factory.Instance.MkCnst("\"" + msg + "\"") });
            argList.AddRange(exprs);
            return MkZingCallStmt(MkZingCall(MkZingIdentifier("trace"), argList));
        }

        private static AST<FuncTerm> MkZingAssert(AST<Node> condition)
        {
            return AddArgs(ZingData.App_Assert, condition, ZingData.Cnst_Nil);
        }

        private static AST<FuncTerm> MkZingAssert(AST<Node> condition, string msg)
        {
            return AddArgs(ZingData.App_Assert, condition, Factory.Instance.MkCnst("\"" + msg + "\""));
        }

        private static AST<FuncTerm> MkZingAssume(AST<Node> condition)
        {
            return AddArgs(ZingData.App_Assume, condition);
        }

        private static AST<FuncTerm> MkZingAdd(AST<Node> a, AST<Node> b)
        {
            return MkZingApply(ZingData.Cnst_Add, a, b);
        }

        private static AST<FuncTerm> MkZingSub(AST<Node> a, AST<Node> b)
        {
            return MkZingApply(ZingData.Cnst_Sub, a, b);
        }

        private static AST<FuncTerm> MkZingNot(AST<Node> a)
        {
            return MkZingApply(ZingData.Cnst_Not, a);
        }
        #endregion

        #region ZingCompiler
        public bool GenerateZing(string zingFileName, ref AST<Model> outModel)
        {
            if (!allMachines.ContainsKey("Main"))
            {
                Console.WriteLine("Unable to generate Zing code since Main machine absent.");
                return false;
            }
            List<AST<Node>> elements = new List<AST<Node>>();
            MkZingEnums(elements);
            MkZingClasses(elements);
            outModel = Add(outModel, MkZingFile(zingFileName, elements));
            return true;
        }

        private void MkZingEnums(List<AST<Node>> elements)
        {
            List<AST<Node>> machineConsts = new List<AST<Node>>();
            machineConsts.Add(Factory.Instance.MkCnst("_default"));
            foreach (string machineName in allMachines.Keys)
            {
                machineConsts.Add(Factory.Instance.MkCnst(string.Format("_{0}", machineName)));
            }
            elements.Add(MkZingEnumDecl("Machine", machineConsts));

            List<AST<Node>> eventConsts = new List<AST<Node>>();
            eventConsts.Add(Factory.Instance.MkCnst("_default"));
            foreach (string eventName in allEvents.Keys.Where(x => x != NullEvent))
            {
                eventConsts.Add(Factory.Instance.MkCnst(string.Format("_{0}", eventName)));
            }
            elements.Add(MkZingEnumDecl("Event", eventConsts));

            List<AST<Node>> stateConsts = new List<AST<Node>>();
            stateConsts.Add(Factory.Instance.MkCnst("_default"));
            foreach (var machine in allMachines.Values)
            {
                foreach (var stateName in machine.stateNameToStateInfo.Keys)
                {
                    stateConsts.Add(Factory.Instance.MkCnst(string.Format("_{0}", stateName)));
                }
            }
            elements.Add(MkZingEnumDecl("State", stateConsts));

            List<AST<Node>> actionOrFunConsts = new List<AST<Node>>();
            actionOrFunConsts.Add(Factory.Instance.MkCnst("_default"));
            foreach (string funName in allGlobalFuns.Keys)
            {
                actionOrFunConsts.Add(Factory.Instance.MkCnst(string.Format("_{0}", funName)));
            }
            foreach (string machineName in allMachines.Keys)
            {
                foreach (string funName in allMachines[machineName].funNameToFunInfo.Keys)
                {
                    actionOrFunConsts.Add(Factory.Instance.MkCnst(string.Format("_{0}_{1}", machineName, funName)));
                }
            }
            elements.Add(MkZingEnumDecl("ActionOrFun", actionOrFunConsts));
        }

        private string GetSpecMachineName(string machineName)
        {
            return string.Format("{0}_handle", machineName);
        }

        private string GetObservesSetName(string machineName)
        {
            return string.Format("{0}_observes", machineName);
        }

        private string GetFairChoice(string entityName, int i)
        {
            return string.Format("FairChoice_{0}_{1}", entityName, i);
        }

        private AST<FuncTerm> GenerateMainClass()
        {
            List<AST<Node>> fields = new List<AST<Node>>();
            foreach (var eventName in allEvents.Keys)
            {
                fields.Add(MkZingVarDecl(string.Format("{0}_SM_EVENT", eventName), SmEvent, ZingData.Cnst_Static));
            }
            foreach (var enumName in allEnums.Keys)
            {
                foreach (var tuple in allEnums[enumName])
                {
                    fields.Add(MkZingVarDecl(string.Format("{0}_SM_ENUM", tuple.Key), ZingData.Cnst_Int, ZingData.Cnst_Static));
                }
            }
            foreach (var machine in allMachines.Values)
            {
                foreach (var stateName in machine.stateNameToStateInfo.Keys)
                {
                    fields.Add(MkZingVarDecl(string.Format("{0}_SM_STATE", stateName), SmState, ZingData.Cnst_Static));
                }
            }
            foreach (var machineName in allMachines.Keys)
            {
                if (allMachines[machineName].IsSpec) continue;
                fields.Add(MkZingVarDecl(string.Format("{0}_instance", machineName), ZingData.Cnst_Int, ZingData.Cnst_Static));
            }
            foreach (var machineName in allMachines.Keys)
            {
                if (!allMachines[machineName].IsSpec) continue;
                fields.Add(MkZingVarDecl(GetSpecMachineName(machineName), Factory.Instance.MkCnst(ZingMachineClassName(machineName)), ZingData.Cnst_Static));
                fields.Add(MkZingVarDecl(GetObservesSetName(machineName), Factory.Instance.MkCnst(PToZing.SM_EVENT_SET), ZingData.Cnst_Static));
            }

            List<AST<Node>> methods = new List<AST<Node>>();
            foreach (var machineName in allMachines.Keys)
            {
                AST<Node> method;
                if (allMachines[machineName].IsSpec)
                {
                    method = MkCreateSpecMachineMethod(machineName);
                }
                else
                {
                    method = MkCreateMachineMethod(machineName);
                }
                methods.Add(method);
            }
            foreach (var machineName in allMachines.Keys)
            {
                if (!allMachines[machineName].IsSpec) continue;
                AST<Node> method = MkInvokeAnnounceMethod(machineName);
                methods.Add(method);
            }

            // Generate method for computing complement of a set of events
            AST<Node> calculateComplementParameters = MkZingVarDecls(MkZingVarDecl("eventSet", SmEventSet));
            AST<Node> calculateComplementLocalVars = MkZingVarDecls(MkZingVarDecl("returnEventSet", SmEventSet));
            AST<Node> calculateComplementBody = MkZingAssign(MkZingIdentifier("returnEventSet"), MkZingNew(SmEventSet, ZingData.Cnst_Nil));
            foreach (var eventName in allEvents.Keys)
            {
                if (eventName == HaltEvent)
                    continue;
                var iteExpr = MkZingIn(MkZingEvent(eventName), MkZingIdentifier("eventSet"));
                var assignStmt = MkZingAssign(MkZingIdentifier("returnEventSet"), MkZingApply(ZingData.Cnst_Add, MkZingIdentifier("returnEventSet"), MkZingEvent(eventName)));
                var iteStmt = MkZingIfThenElse(iteExpr, ZingData.Cnst_Nil, assignStmt);
                calculateComplementBody = MkZingSeq(calculateComplementBody, iteStmt);
            }
            calculateComplementBody = MkZingSeq(calculateComplementBody, MkZingReturn(MkZingIdentifier("returnEventSet")));
            calculateComplementBody = MkZingBlock("dummy", calculateComplementBody);
            calculateComplementBody = MkZingBlocks(calculateComplementBody);
            AST<Node> calculateComplementMethod = MkZingMethodDecl("CalculateComplementOfEventSet", calculateComplementParameters, SmEventSet, calculateComplementLocalVars, calculateComplementBody, ZingData.Cnst_Static);
            methods.Add(calculateComplementMethod);

            // Generate the PayloadOf static method. PayloadOf :: (EventId) -> Discriminator
            // Returns the statically declared type for the given event.
            var payloadOfBody = new List<AST<Node>>();
            payloadOfBody.Add(MkZingIfThen(MkZingEq(MkZingIdentifier("e"), MkZingIdentifier("null")),
                MkZingReturn(typeContext.PTypeToZingExpr(PTypeNull.Node))));
            foreach (var evt in allEvents.Keys.Where(x => x != NullEvent))
            {
                payloadOfBody.Add(MkZingIfThenElse(MkZingEq(MkZingDot("e", "name"), MkZingDot("Event", "_" + evt)),
                    MkZingReturn(typeContext.PTypeToZingExpr(allEvents[evt].payloadType)),
                    ZingData.Cnst_Nil));
            }
            payloadOfBody.Add(MkZingAssert(ZingData.Cnst_False, "Internal error"));
            AST<Node> payloadOfMethod = MkZingMethodDecl("PayloadOf",
                MkZingVarDecls(MkZingVarDecl("e", Factory.Instance.MkCnst("SM_EVENT"))),
                Factory.Instance.MkCnst("PRT_TYPE"), ZingData.Cnst_Nil, MkZingBlocks(MkZingBlock("dummy", MkZingSeq(payloadOfBody))), ZingData.Cnst_Static);
            methods.Add(payloadOfMethod);

            foreach (var funName in allGlobalFuns.Keys)
            {
                var funInfo = allGlobalFuns[funName];
                methods.Add(MkZingStaticFunMethod(funName, funInfo));
            }

            fields.AddRange(typeContext.MainVarDecls());

            List<AST<Node>> runBodyStmts = new List<AST<Node>>();
            foreach (var eventName in allEvents.Keys)
            {
                AST<Node> rhs;
                if (eventName == NullEvent)
                    rhs = MkZingIdentifier("null");
                else
                    rhs = MkZingCall(
                                    MkZingDot("SM_EVENT", "Construct"),
                                    MkZingDot("Event", string.Format("_{0}", eventName)),
                                    Factory.Instance.MkCnst(allEvents[eventName].maxInstances),
                                    allEvents[eventName].maxInstancesAssumed ? ZingData.Cnst_True : ZingData.Cnst_False);

                var assignStmt = MkZingAssign(MkZingEvent(eventName), rhs);
                runBodyStmts.Add(assignStmt);
            }
            foreach (var enumName in allEnums.Keys)
            {
                foreach (var tuple in allEnums[enumName])
                {
                    var assignStmt = MkZingAssign(MkZingEnum(tuple.Key), Factory.Instance.MkCnst(tuple.Value));
                    runBodyStmts.Add(assignStmt);
                }
            }
            foreach (var machineName in allMachines.Keys)
            {
                var machine = allMachines[machineName];
                foreach (var stateName in machine.stateNameToStateInfo.Keys)
                {
                    var stateInfo = machine.stateNameToStateInfo[stateName];
                    var stateTemperature = stateInfo.temperature == StateTemperature.COLD
                                           ? MkZingDot("StateTemperature", "Cold")
                                           : (stateInfo.temperature == StateTemperature.HOT ? MkZingDot("StateTemperature", "Hot") : MkZingDot("StateTemperature", "Warm"));
                    var state = MkZingCall(
                                        MkZingDot("SM_STATE", "Construct"),
                                        MkZingDot("State", string.Format("_{0}", stateName)),
                                        MkZingActionOrFun(machineName, stateInfo.entryActionName),
                                        MkZingActionOrFun(machineName, stateInfo.exitFunName),
                                        Factory.Instance.MkCnst(stateInfo.transitions.Count),
                                        stateInfo.hasNullTransition ? ZingData.Cnst_True : ZingData.Cnst_False,
                                        stateTemperature
                                        );
                    runBodyStmts.Add(MkZingAssign(MkZingState(stateName), state));
                }
            }
            foreach (var machineName in allMachines.Keys)
            {
                var machine = allMachines[machineName];
                foreach (var stateName in machine.stateNameToStateInfo.Keys)
                {
                    var stateInfo = machine.stateNameToStateInfo[stateName];
                    int i = 0;
                    foreach (var eventName in stateInfo.transitions.Keys)
                    {
                        var transitionInfo = stateInfo.transitions[eventName];
                        var transition = MkZingCall(
                                            MkZingDot("SM_TRANSITION", "Construct"),
                                            MkZingEvent(eventName),
                                            transitionInfo.IsPush ? MkZingDot("ActionOrFun", "_default") : MkZingActionOrFun(machineName, transitionInfo.transFunName),
                                            MkZingState(transitionInfo.target)
                                            );
                        var lhs = MkZingIndex(MkZingDot(MkZingState(stateName), "transitions"), Factory.Instance.MkCnst(i));
                        runBodyStmts.Add(MkZingAssign(lhs, transition));
                        i++;
                    }
                }
            }
            foreach (var machineName in allMachines.Keys)
            {
                if (allMachines[machineName].IsSpec) continue;
                var assignStmt = MkZingAssign(MkZingIdentifier(string.Format("{0}_instance", machineName)), Factory.Instance.MkCnst(0));
                runBodyStmts.Add(assignStmt);
            }
            runBodyStmts.Add(typeContext.InitializeFieldNamesAndTypes());
            runBodyStmts.Add(MkZingAssign(MkZingIdentifier("nullValue"), MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeNull.Node))));

            var locals = new List<AST<Node>>();
            locals.Add(MkZingVarDecl("nullValue", PrtValue));

            foreach (var machineName in allMachines.Keys)
            {
                var machineInfo = allMachines[machineName];
                if (!machineInfo.IsSpec) continue;
                if (machineInfo.specType != SpecType.SAFETY) continue;
                runBodyStmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("Main", string.Format("CreateMachine_{0}", machineName)))));
            }
            int numLivenessSpecs = allMachines.Where(x => x.Value.specType != SpecType.SAFETY).Count();
            if (0 < numLivenessSpecs)
            {
                Debug.Assert(compiler.Options.liveness != LivenessOption.None);
                locals.Add(MkZingVarDecl("choice", ZingData.Cnst_Int));
                var livenessStmt = MkZingAssume(ZingData.Cnst_False);
                var choice = MkZingIdentifier("choice");
                runBodyStmts.Add(MkZingAssign(choice, MkZingCall(MkZingDot("FairCycle", "Choose"), Factory.Instance.MkCnst(numLivenessSpecs))));
                var count = 0;
                foreach (var machineName in allMachines.Keys)
                {
                    var machineInfo = allMachines[machineName];
                    if (!machineInfo.IsSpec) continue;
                    if (machineInfo.specType == SpecType.SAFETY) continue;
                    livenessStmt = MkZingIfThenElse(
                                                MkZingEq(choice, Factory.Instance.MkCnst(count)),
                                                MkZingCallStmt(MkZingCall(MkZingDot("Main", string.Format("CreateMachine_{0}", machineName)))),
                                                livenessStmt);
                    count++;
                }
                runBodyStmts.Add(livenessStmt);
            }
            foreach (var machineName in allMachines.Keys)
            {
                if (!allMachines[machineName].IsSpec) continue;
                MachineInfo machineInfo = allMachines[machineName];
                var currentObservesSet = MkZingDot("Main", GetObservesSetName(machineName));
                runBodyStmts.Add(MkZingAssign(currentObservesSet, MkZingNew(SmEventSet, ZingData.Cnst_Nil)));
                List<AST<Node>> stmts = new List<AST<Node>>();
                AddEventSet(stmts, machineInfo.observesEvents, currentObservesSet);
                runBodyStmts.Add(MkZingSeq(stmts));
            }
            runBodyStmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("Main", "CreateMachine_Main"), MkZingIdentifier("nullValue"))));
            AST<Node> runMethod = MkZingMethodDecl("Run", ZingData.Cnst_Nil, ZingData.Cnst_Void, MkZingVarDecls(locals), MkZingBlocks(MkZingBlock("dummy", MkZingSeq(runBodyStmts))), ZingData.Cnst_Static, ZingData.Cnst_Activate);
            methods.Add(runMethod);

            return AddArgs(ZingData.App_ClassDecl, Factory.Instance.MkCnst("Main"), MkZingVarDecls(fields), MkZingMethodDecls(methods));
        }

        private AST<FuncTerm> GenerateMachineClass(string machineName)
        {
            List<AST<Node>> fields = new List<AST<Node>>(allMachines[machineName].localVariableToVarInfo.Keys.Select(name => MkZingVarDecl(name, PrtValue)));
            fields.Add(MkZingVarDecl("myHandle", SmHandle));

            List<AST<Node>> methods = new List<AST<Node>>();
            foreach (var x in allMachines[machineName].stateNameToStateInfo)
            {
                AST<Node> dequeueEventMethod = GenerateCalculateDeferredAndActionSetMethodDecl(x.Key, x.Value);
                methods.Add(dequeueEventMethod);
            }
            AST<Node> startMethod = GenerateStartMethodDecl(machineName);
            methods.Add(startMethod);
            AST<Node> runMethod = GenerateRunMethodDecl();
            methods.Add(runMethod);
            AST<Node> traceEnterStateMethod = GenerateTraceEnterStateMethodDecl(machineName);
            methods.Add(traceEnterStateMethod);
            AST<Node> traceExitStateMethod = GenerateTraceExitStateMethodDecl(machineName);
            methods.Add(traceExitStateMethod);
            AST<Node> calculateDeferredAndActionSetMethod = GenerateCalculateDeferredAndActionSetMethodDecl(machineName);
            methods.Add(calculateDeferredAndActionSetMethod);
            AST<Node> runHelperMethod = GenerateRunHelperMethodDecl(machineName);
            methods.Add(runHelperMethod);
            AST<Node> processContinuationMethod = GenerateProcessContinuationMethodDecl();
            methods.Add(processContinuationMethod);
            AST<Node> actionHelperMethod = GenerateReentrancyHelperMethodDecl(machineName);
            methods.Add(actionHelperMethod);
            foreach (var funName in allMachines[machineName].funNameToFunInfo.Keys)
            {
                var funInfo = allMachines[machineName].funNameToFunInfo[funName];
                methods.Add(MkZingFunMethod(machineName, funName, funInfo));
            }
            foreach (var funName in allMachines[machineName].funNameToFunInfo.Keys)
            {
                var funInfo = allMachines[machineName].funNameToFunInfo[funName];
                for (int i = 0; i < funInfo.numFairChoices; i++)
                {
                    fields.Add(MkZingVarDecl(GetFairChoice(funName, i), Factory.Instance.MkCnst("FairChoice")));
                }
            }
            return AddArgs(ZingData.App_ClassDecl, Factory.Instance.MkCnst(ZingMachineClassName(machineName)), MkZingVarDecls(fields), MkZingMethodDecls(methods));
        }

        private void MkZingClasses(List<AST<Node>> elements)
        {
            foreach (string machineName in allMachines.Keys)
            {
                elements.Add(GenerateMachineClass(machineName));
            }
            elements.Add(GenerateMainClass());
        }

        private AST<Node> GenerateCalculateDeferredAndActionSetMethodDecl(string stateName, StateInfo stateInfo)
        {
            var smEventSetType = Factory.Instance.MkCnst("SM_EVENT_SET");
            var currentDeferredSet = MkZingDot("myHandle", "stack", "deferredSet");
            var currentActionSet = MkZingDot("myHandle", "stack", "actionSet");

            var ownerName = stateInfo.ownerName;
            var localDeferredSet = stateInfo.deferredEvents;
            var actions = stateInfo.dos;
            var transitions = stateInfo.transitions;

            List<AST<Node>> stmts = new List<AST<Node>>();
            stmts.Add(MkZingAssign(currentDeferredSet, MkZingNew(smEventSetType, ZingData.Cnst_Nil)));
            stmts.Add(MkZingAssign(currentActionSet, MkZingNew(smEventSetType, ZingData.Cnst_Nil)));
            stmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("myHandle", "stack", "AddStackDeferredSet"), currentDeferredSet)));
            AddEventSet(stmts, localDeferredSet, currentDeferredSet);
            SubtractEventSet(stmts, actions.Keys, currentDeferredSet);
            SubtractEventSet(stmts, transitions.Keys, currentDeferredSet);
            stmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("myHandle", "stack", "AddStackActionSet"), currentActionSet)));
            SubtractEventSet(stmts, localDeferredSet, currentActionSet);
            AddEventSet(stmts, actions.Keys, currentActionSet);
            SubtractEventSet(stmts, transitions.Keys, currentActionSet);
            stmts.Add(MkZingAssign(MkZingDot("myHandle", "stack", "es"), MkZingNew(Factory.Instance.MkCnst("SM_EVENT_ARRAY"), Factory.Instance.MkCnst(actions.Count))));
            stmts.Add(MkZingAssign(MkZingDot("myHandle", "stack", "as"), MkZingNew(Factory.Instance.MkCnst("ActionOrFun_ARRAY"), Factory.Instance.MkCnst(actions.Count))));
            int count = 0;
            foreach (var eventName in actions.Keys)
            {
                var actionName = actions[eventName];
                stmts.Add(MkZingAssign(MkZingApply(ZingData.Cnst_Index, MkZingDot("myHandle", "stack", "es"), Factory.Instance.MkCnst(count)), MkZingEvent(eventName)));
                stmts.Add(MkZingAssign(MkZingApply(ZingData.Cnst_Index, MkZingDot("myHandle", "stack", "as"), Factory.Instance.MkCnst(count)), MkZingActionOrFun(ownerName, actionName)));
                count = count + 1;
            }

            var body = MkZingBlock("dummy", MkZingSeq(stmts.ToArray()));
            return MkZingMethodDecl(string.Format("{0}_CalculateDeferredAndActionSet", stateName), ZingData.Cnst_Nil, ZingData.Cnst_Void, ZingData.Cnst_Nil, MkZingBlocks(body));
        }

        private AST<Node> GenerateStartMethodDecl(string machineName)
        {
            string initStateName = allMachines[machineName].initStateName;
            var callStmt = MkZingCallStmt(MkZingCall(MkZingIdentifier("Run"), MkZingState(initStateName)));
            var iteStmt = MkZingIfThen(MkZingEq(MkZingDot("myHandle", "currentEvent"), MkZingEvent("halt")),
                                    MkZingSeq(
                                        MkZingAssign(MkZingDot("myHandle", "stack"), MkZingIdentifier("null")),
                                        MkZingAssign(MkZingDot("myHandle", "buffer"), MkZingIdentifier("null")),
                                        MkZingAssign(MkZingDot("myHandle", "currentArg"), MkZingIdentifier("null")),
                                        MkZingAssign(MkZingDot("SM_HANDLE", "halted"), MkZingAdd(MkZingDot("SM_HANDLE", "halted"), MkZingIdentifier("myHandle"))),
                                        MkZingAssign(MkZingDot("SM_HANDLE", "enabled"), MkZingSub(MkZingDot("SM_HANDLE", "enabled"), MkZingIdentifier("myHandle"))),
                                        MkZingReturn(ZingData.Cnst_Nil))
                                        );
            var traceStmt = MkZingTrace(string.Format("<StateLog> Unhandled event exception by machine {0}-{{0}}\\n", machineName), MkZingDot("myHandle", "instance"));
            var assertStmt = MkZingAssert(ZingData.Cnst_False, string.Format("Unhandled event exception by machine {0}", machineName));
            var body = MkZingBlocks(MkZingBlock("dummy", MkZingSeq(callStmt, iteStmt, traceStmt, assertStmt)));
            return MkZingMethodDecl("Start", ZingData.Cnst_Nil, ZingData.Cnst_Void, ZingData.Cnst_Nil, body);
        }

        private AST<Node> GenerateRunMethodDecl()
        {
            List<AST<Node>> parameters = new List<AST<Node>>();
            parameters.Add(MkZingVarDecl("state", SmState));

            List<AST<Node>> locals = new List<AST<Node>>();
            locals.Add(MkZingVarDecl("doPop", ZingData.Cnst_Bool));
            locals.Add(MkZingVarDecl("hasNullTransitionOrAction", ZingData.Cnst_Bool));

            var doPop = MkZingIdentifier("doPop");
            var hasNullTransitionOrAction = MkZingIdentifier("hasNullTransitionOrAction");

            List<AST<Node>> initStmts = new List<AST<Node>>();
            initStmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("myHandle", "Push"))));
            initStmts.Add(MkZingAssign(MkZingDot("myHandle", "stack", "state"), MkZingIdentifier("state")));
            initStmts.Add(MkZingAssign(doPop, MkZingCall(MkZingIdentifier("RunHelper"), ZingData.Cnst_True)));
            var whileStmts = new List<AST<Node>>();
            whileStmts.Add(MkZingAssign(hasNullTransitionOrAction, MkZingCall(MkZingDot("myHandle", "stack", "HasNullTransitionOrAction"))));
            whileStmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("myHandle", "DequeueEvent"), hasNullTransitionOrAction)));
            whileStmts.Add(MkZingAssign(doPop, MkZingCall(MkZingIdentifier("RunHelper"), ZingData.Cnst_False)));
            initStmts.Add(MkZingWhile(MkZingNot(doPop), MkZingSeq(whileStmts)));
            initStmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("myHandle", "Pop"))));

            var initBlock = MkZingBlock("init", MkZingSeq(initStmts));
            return MkZingMethodDecl("Run", MkZingVarDecls(parameters), ZingData.Cnst_Void, MkZingVarDecls(locals), MkZingBlocks(initBlock));
        }

        private AST<Node> ContinuationPrepareHelper(string machineName, string funName)
        {
            FunInfo funInfo = allGlobalFuns.ContainsKey(funName) ? allGlobalFuns[funName] : allMachines[machineName].funNameToFunInfo[funName];
            var locals = MkZingIdentifier("locals");
            var cont = MkZingDot("myHandle", "cont");
            var stmts = new List<AST<Node>>();
            if (funInfo.maxNumLocals == 0)
            {
                stmts.Add(MkZingAssign(locals, MkZingIdentifier("null")));
            }
            else
            {
                stmts.Add(MkZingAssign(locals, MkZingNew(Factory.Instance.MkCnst("PRT_VALUE_ARRAY"), Factory.Instance.MkCnst(funInfo.maxNumLocals))));
            }
            if (funInfo.isAnonymous)
            {
                stmts.Add(MkZingAssign(MkZingIndex(locals, Factory.Instance.MkCnst(funInfo.localNameToInfo[funInfo.PayloadVarName].index)), MkZingIdentifier("payload")));
            }
            foreach (var localName in funInfo.localNames)
            {
                var localVarInfo = funInfo.localNameToInfo[localName];
                stmts.Add(MkZingAssign(MkZingIndex(locals, Factory.Instance.MkCnst(localVarInfo.index)), MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(localVarInfo.type))));
            }

            stmts.Add(MkZingCallStmt(MkZingCall(MkZingDot(cont, "PushReturnTo"), Factory.Instance.MkCnst(0), locals)));
            return MkZingSeq(stmts);
        }

        private AST<Node> GenerateReentrancyHelperMethodDecl(string machineName)
        {
            List<AST<Node>> parameters = new List<AST<Node>>();
            parameters.Add(MkZingVarDecl("actionFun", Factory.Instance.MkCnst("ActionOrFun")));
            parameters.Add(MkZingVarDecl("payload", PrtValue));
            List<AST<Node>> locals = new List<AST<Node>>();
            locals.Add(MkZingVarDecl("locals", Factory.Instance.MkCnst("PRT_VALUE_ARRAY")));
            locals.Add(MkZingVarDecl("doPop", ZingData.Cnst_Bool));

            var cont = MkZingDot("myHandle", "cont");
            var doPop = MkZingIdentifier("doPop");

            List<AST<Node>> initStmts = new List<AST<Node>>();
            initStmts.Add(MkZingAssign(doPop, ZingData.Cnst_False));
            initStmts.Add(MkZingCallStmt(MkZingCall(MkZingDot(cont, "Reset"))));
            foreach (var funName in allGlobalFuns.Keys)
            {
                var funInfo = allGlobalFuns[funName];
                if (funInfo.parameterNames.Count > 0) continue;
                var resetStmt = ContinuationPrepareHelper(machineName, funName);
                var funExpr = MkZingActionOrFun(machineName, funName);
                var condExpr = MkZingApply(ZingData.Cnst_Eq, MkZingIdentifier("actionFun"), funExpr);
                var gotoStmt = MkZingGoto("execute_" + funName);
                var traceStmt = MkZingTrace(string.Format("<FunctionLog> Machine {0}-{{0}} executing Function {1}\\n", machineName, funName), MkZingDot("myHandle", "instance"));
                initStmts.Add(MkZingIfThen(condExpr, MkZingSeq(traceStmt, resetStmt, gotoStmt)));
            }
            foreach (var funName in allMachines[machineName].funNameToFunInfo.Keys)
            {
                var funInfo = allMachines[machineName].funNameToFunInfo[funName];
                if (!funInfo.isAnonymous && funInfo.parameterNames.Count > 0) continue;
                var resetStmt = ContinuationPrepareHelper(machineName, funName);
                var funExpr = MkZingActionOrFun(machineName, funName);
                var condExpr = MkZingApply(ZingData.Cnst_Eq, MkZingIdentifier("actionFun"), funExpr);
                var gotoStmt = MkZingGoto("execute_" + funName);
                if (funInfo.isAnonymous)
                {
                    initStmts.Add(MkZingIfThen(condExpr, MkZingSeq(resetStmt, gotoStmt)));
                }
                else
                {
                    var traceStmt = MkZingTrace(string.Format("<FunctionLog> Machine {0}-{{0}} executing Function {1}\\n", machineName, funName), MkZingDot("myHandle", "instance"));
                    initStmts.Add(MkZingIfThen(condExpr, MkZingSeq(traceStmt, resetStmt, gotoStmt)));
                }
            }
            initStmts.Add(MkZingAssert(ZingData.Cnst_False, "Internal error"));
            AST<Node> initStmt = MkZingBlock("init", MkZingSeq(initStmts));

            // Action blocks
            List<AST<Node>> blocks = new List<AST<Node>>();
            blocks.Add(initStmt);
            foreach (var funName in allGlobalFuns.Keys)
            {
                var funInfo = allGlobalFuns[funName];
                if (funInfo.parameterNames.Count > 0) continue;
                var callStmt = MkZingCallStmt(MkZingCall(MkZingDot("Main", funName), MkZingIdentifier("myHandle"), cont));
                List<AST<Node>> whileStmts = new List<AST<Node>>();
                whileStmts.Add(callStmt);
                whileStmts.Add(MkZingAssign(doPop, MkZingCall(MkZingIdentifier("ProcessContinuation"))));
                AST<Node> payloadReturnStmt = MkZingReturn(MkZingIdentifier("payload"));
                if (funInfo.isAnonymous)
                {
                    AST<Node> payloadReturnStmt1 = MkZingReturn(MkZingIndex(MkZingDot("myHandle", "cont", "retLocals"), Factory.Instance.MkCnst(funInfo.localNameToInfo[funInfo.PayloadVarName].index)));
                    payloadReturnStmt = MkZingIfThenElse(MkZingEq(MkZingDot("myHandle", "cont", "retLocals"), MkZingIdentifier("null")), payloadReturnStmt, payloadReturnStmt1);
                }
                blocks.Add(MkZingBlock("execute_" + funName, MkZingSeq(MkZingWhile(MkZingNot(doPop), MkZingSeq(whileStmts)), payloadReturnStmt)));
            }
            foreach (var funName in allMachines[machineName].funNameToFunInfo.Keys)
            {
                var funInfo = allMachines[machineName].funNameToFunInfo[funName];
                if (!funInfo.isAnonymous && funInfo.parameterNames.Count > 0) continue;
                var callStmt = MkZingCallStmt(MkZingCall(MkZingIdentifier(funName), cont));
                List<AST<Node>> whileStmts = new List<AST<Node>>();
                whileStmts.Add(callStmt);
                whileStmts.Add(MkZingAssign(doPop, MkZingCall(MkZingIdentifier("ProcessContinuation"))));
                AST<Node> payloadReturnStmt = MkZingReturn(MkZingIdentifier("payload"));
                if (funInfo.isAnonymous)
                {
                    AST<Node> payloadReturnStmt1 = MkZingReturn(MkZingIndex(MkZingDot("myHandle", "cont", "retLocals"), Factory.Instance.MkCnst(funInfo.localNameToInfo[funInfo.PayloadVarName].index)));
                    payloadReturnStmt = MkZingIfThenElse(MkZingEq(MkZingDot("myHandle", "cont", "retLocals"), MkZingIdentifier("null")), payloadReturnStmt, payloadReturnStmt1);
                }
                blocks.Add(MkZingBlock("execute_" + funName, MkZingSeq(MkZingWhile(MkZingNot(doPop), MkZingSeq(whileStmts)), payloadReturnStmt)));
            }
            return MkZingMethodDecl("ReentrancyHelper", MkZingVarDecls(parameters), PrtValue, MkZingVarDecls(locals), MkZingBlocks(blocks));
        }

        private AST<Node> GenerateProcessContinuationMethodDecl()
        {
            List<AST<Node>> parameters = new List<AST<Node>>();
            List<AST<Node>> locals = new List<AST<Node>>();
            locals.Add(MkZingVarDecl("doPop", ZingData.Cnst_Bool));

            var cont = MkZingDot("myHandle", "cont");
            var body = new List<AST<Node>>();
            body.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Return")), MkZingReturn(ZingData.Cnst_True)));
            body.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Pop")), MkZingReturn(ZingData.Cnst_True)));
            body.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Goto")), MkZingReturn(ZingData.Cnst_True)));
            body.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Raise")), MkZingReturn(ZingData.Cnst_True)));
            AST<Node> atChooseLivenessStmt = ZingData.Cnst_Nil;
            AST<Node> atYieldLivenessStmt = ZingData.Cnst_Nil;
            if (compiler.Options.liveness == LivenessOption.Standard)
            {
                atChooseLivenessStmt = MkZingSeq(
                    MkZingCallStmt(MkZingCall(MkZingDot("FairCycle", "GateProgress"))),
                    MkZingCallStmt(MkZingCall(MkZingDot("FairScheduler", "AtChooseStatic"))),
                    MkZingCallStmt(MkZingCall(MkZingDot("FairChoice", "AtYieldOrChooseStatic"))));
                atYieldLivenessStmt = MkZingSeq(
                    MkZingCallStmt(MkZingCall(MkZingDot("FairCycle", "GateProgress"))),
                    MkZingCallStmt(MkZingCall(MkZingDot("FairScheduler", "AtYieldStatic"), MkZingIdentifier("myHandle"))),
                    MkZingCallStmt(MkZingCall(MkZingDot("FairChoice", "AtYieldOrChooseStatic"))));
            }
            body.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Receive")),
                                  MkZingSeq(MkZingCallStmt(MkZingCall(MkZingDot("myHandle", "DequeueEvent"), ZingData.Cnst_False)), MkZingReturn(ZingData.Cnst_False))));
            body.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Nondet")),
                MkZingSeq(
                    atChooseLivenessStmt,
                    MkZingAssign(MkZingDot(cont, "nondet"), MkZingCall(Factory.Instance.MkCnst("choose"), Factory.Instance.MkCnst("bool"))),
                    MkZingReturn(ZingData.Cnst_False))));
            body.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "NewMachine")),
                MkZingSeq(
                    atYieldLivenessStmt,
                    ZingData.Cnst_Yield,
                    MkZingReturn(ZingData.Cnst_False))));
            body.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Send")),
                MkZingSeq(
                    atYieldLivenessStmt,
                    ZingData.Cnst_Yield,
                    MkZingReturn(ZingData.Cnst_False))));

            return MkZingMethodDecl("ProcessContinuation", MkZingVarDecls(parameters), ZingData.Cnst_Bool, MkZingVarDecls(locals), MkZingBlocks(MkZingBlock("init", MkZingSeq(body))));
        }

        private AST<Node> GenerateTraceEnterStateMethodDecl(string machineName)
        {
            AST<Node> parameters = MkZingVarDecls(MkZingVarDecl("state", SmState));
            List<AST<Node>> locals = new List<AST<Node>>();

            var state = MkZingIdentifier("state");

            List<AST<Node>> blocks = new List<AST<Node>>();
            List<AST<Node>> initStmts = new List<AST<Node>>();
            foreach (var stateName in allMachines[machineName].stateNameToStateInfo.Keys)
            {
                var stateInfo = allMachines[machineName].stateNameToStateInfo[stateName];
                var stateExpr = MkZingState(stateName);
                var condExpr = MkZingApply(ZingData.Cnst_Eq, state, stateExpr);
                List<AST<Node>> seqStmts = new List<AST<Node>>();
                seqStmts.Add(MkZingTrace(string.Format("<StateLog> Machine {0}-{{0}} entering State {1}\\n", machineName, stateInfo.printedName), MkZingDot("myHandle", "instance")));
                seqStmts.Add(MkZingReturn(ZingData.Cnst_Nil));
                initStmts.Add(MkZingIfThen(condExpr, MkZingSeq(seqStmts)));
            }
            initStmts.Add(MkZingAssert(ZingData.Cnst_False, "Internal error"));
            blocks.Add(MkZingBlock("init", MkZingSeq(initStmts)));

            return MkZingMethodDecl("TraceEnterState", parameters, ZingData.Cnst_Void, MkZingVarDecls(locals), MkZingBlocks(blocks));
        }

        private AST<Node> GenerateTraceExitStateMethodDecl(string machineName)
        {
            AST<Node> parameters = MkZingVarDecls(MkZingVarDecl("state", SmState));
            List<AST<Node>> locals = new List<AST<Node>>();

            var state = MkZingIdentifier("state");

            List<AST<Node>> blocks = new List<AST<Node>>();
            List<AST<Node>> initStmts = new List<AST<Node>>();
            foreach (var stateName in allMachines[machineName].stateNameToStateInfo.Keys)
            {
                var stateInfo = allMachines[machineName].stateNameToStateInfo[stateName];
                var stateExpr = MkZingState(stateName);
                var condExpr = MkZingApply(ZingData.Cnst_Eq, state, stateExpr);
                List<AST<Node>> seqStmts = new List<AST<Node>>();
                seqStmts.Add(MkZingTrace(string.Format("<StateLog> Machine {0}-{{0}} exiting State {1}\\n", machineName, stateInfo.printedName), MkZingDot("myHandle", "instance")));
                seqStmts.Add(MkZingReturn(ZingData.Cnst_Nil));
                initStmts.Add(MkZingIfThen(condExpr, MkZingSeq(seqStmts)));
            }
            initStmts.Add(MkZingAssert(ZingData.Cnst_False, "Internal error"));
            blocks.Add(MkZingBlock("init", MkZingSeq(initStmts)));

            return MkZingMethodDecl("TraceExitState", parameters, ZingData.Cnst_Void, MkZingVarDecls(locals), MkZingBlocks(blocks));
        }

        private AST<Node> GenerateCalculateDeferredAndActionSetMethodDecl(string machineName)
        {
            AST<Node> parameters = MkZingVarDecls(MkZingVarDecl("state", SmState));
            List<AST<Node>> locals = new List<AST<Node>>();

            var state = MkZingIdentifier("state");

            List<AST<Node>> blocks = new List<AST<Node>>();
            List<AST<Node>> initStmts = new List<AST<Node>>();
            foreach (var stateName in allMachines[machineName].stateNameToStateInfo.Keys)
            {
                var stateInfo = allMachines[machineName].stateNameToStateInfo[stateName];
                var stateExpr = MkZingState(stateName);
                var condExpr = MkZingApply(ZingData.Cnst_Eq, state, stateExpr);
                List<AST<Node>> seqStmts = new List<AST<Node>>();
                seqStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier(string.Format("{0}_CalculateDeferredAndActionSet", stateName)))));
                seqStmts.Add(MkZingReturn(ZingData.Cnst_Nil));
                initStmts.Add(MkZingIfThen(condExpr, MkZingSeq(seqStmts)));
            }
            initStmts.Add(MkZingAssert(ZingData.Cnst_False, "Internal error"));
            blocks.Add(MkZingBlock("init", MkZingSeq(initStmts)));

            return MkZingMethodDecl("CalculateDeferredAndActionSet", parameters, ZingData.Cnst_Void, MkZingVarDecls(locals), MkZingBlocks(blocks));
        }

        private AST<Node> GenerateRunHelperMethodDecl(string machineName)
        {
            AST<Node> parameters = MkZingVarDecls(MkZingVarDecl("start", ZingData.Cnst_Bool));
            List<AST<Node>> locals = new List<AST<Node>>();
            locals.Add(MkZingVarDecl("state", SmState));
            locals.Add(MkZingVarDecl("transition", SmTransition));
            locals.Add(MkZingVarDecl("actionFun", Factory.Instance.MkCnst("ActionOrFun")));
            locals.Add(MkZingVarDecl("payload", PrtValue));

            var start = MkZingIdentifier("start");
            var state = MkZingIdentifier("state");
            var cont = MkZingDot("myHandle", "cont");
            var transition = MkZingIdentifier("transition");
            var actionFun = MkZingIdentifier("actionFun");
            var payload = MkZingIdentifier("payload");

            List<AST<Node>> blocks = new List<AST<Node>>();

            List<AST<Node>> initStmts = new List<AST<Node>>();
            initStmts.Add(MkZingAssign(state, MkZingDot("myHandle", "stack", "state")));
            initStmts.Add(MkZingIfThenElse(start, MkZingSeq(MkZingAssign(payload, MkZingDot("myHandle", "currentArg")), MkZingGoto("enter")), MkZingGoto("handle")));
            blocks.Add(MkZingBlock("init", MkZingSeq(initStmts)));

            List<AST<Node>> enterStmts = new List<AST<Node>>();
            enterStmts.Add(MkZingAssign(state, MkZingDot("myHandle", "stack", "state")));
            enterStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("TraceEnterState"), state)));
            if (allMachines[machineName].IsSpec)
            {
                if (compiler.Options.liveness == LivenessOption.None)
                {
                    enterStmts.Add(
                        MkZingIfThenElse(
                            MkZingEq(MkZingDot(state, "temperature"), MkZingDot("StateTemperature", "Hot")),
                            MkZingAssign(MkZingDot("SM_HANDLE", "hot"), MkZingAdd(MkZingDot("SM_HANDLE", "hot"), MkZingIdentifier("myHandle"))),
                            MkZingAssign(MkZingDot("SM_HANDLE", "hot"), MkZingSub(MkZingDot("SM_HANDLE", "hot"), MkZingIdentifier("myHandle")))));
                }
                else if (compiler.Options.liveness == LivenessOption.Standard)
                {
                    enterStmts.Add(
                        MkZingIfThenElse(
                            MkZingEq(MkZingDot(state, "temperature"), MkZingDot("StateTemperature", "Hot")),
                            MkZingAssign(MkZingDot("FairCycle", "temperature"), MkZingDot("StateTemperature", "Hot")),
                            MkZingIfThenElse(
                                MkZingEq(MkZingDot(state, "temperature"), MkZingDot("StateTemperature", "Warm")),
                                MkZingAssign(MkZingDot("FairCycle", "temperature"), MkZingDot("StateTemperature", "Warm")),
                                MkZingSeq(MkZingAssume(MkZingNeq(MkZingDot("FairCycle", "gate"), MkZingDot("GateStatus", "Closed"))),
                                          MkZingAssign(MkZingDot("FairCycle", "temperature"), MkZingDot("StateTemperature", "Cold"))))));
                }
                else
                {
                    // compiler.Options.liveness == LivenessOption.Sampling
                    enterStmts.Add(
                        MkZingIfThenElse(
                            MkZingEq(MkZingDot(state, "temperature"), MkZingDot("StateTemperature", "Hot")),
                            MkZingCallStmt(MkZingCall(MkZingIdentifier("invokescheduler"), Factory.Instance.MkCnst("\"updatemonitor\""), Factory.Instance.MkCnst(string.Format("\"{0}\"", machineName)), Factory.Instance.MkCnst("\"hot\""))),
                            MkZingIfThenElse(
                            MkZingEq(MkZingDot(state, "temperature"), MkZingDot("StateTemperature", "Cold")),
                            MkZingCallStmt(MkZingCall(MkZingIdentifier("invokescheduler"), Factory.Instance.MkCnst("\"updatemonitor\""), Factory.Instance.MkCnst(string.Format("\"{0}\"", machineName)), Factory.Instance.MkCnst("\"cold\""))),
                            MkZingCallStmt(MkZingCall(MkZingIdentifier("invokescheduler"), Factory.Instance.MkCnst("\"updatemonitor\""), Factory.Instance.MkCnst(string.Format("\"{0}\"", machineName)), Factory.Instance.MkCnst("\"warm\""))))));
                }
            }
            enterStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("CalculateDeferredAndActionSet"), state)));
            enterStmts.Add(MkZingAssign(actionFun, MkZingDot(state, "entryFun")));
            blocks.Add(MkZingBlock("enter", MkZingSeq(enterStmts)));

            List<AST<Node>> gotoStmts = new List<AST<Node>>();
            gotoStmts.Add(MkZingAssign(payload, MkZingDot("myHandle", "currentArg")));
            gotoStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("TraceExitState"), state)));
            gotoStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("ReentrancyHelper"), MkZingDot(state, "exitFun"), MkZingIdentifier("null"))));
            gotoStmts.Add(MkZingAssign(MkZingDot("myHandle", "stack", "state"), MkZingDot("myHandle", "destState")));
            gotoStmts.Add(MkZingGoto("enter"));

            List<AST<Node>> executeStmts = new List<AST<Node>>();
            executeStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("ReentrancyHelper"), actionFun, payload)));
            executeStmts.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Goto")), MkZingSeq(gotoStmts)));
            executeStmts.Add(MkZingIfThen(MkZingEq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Raise")), MkZingGoto("handle")));
            executeStmts.Add(MkZingIfThen(MkZingNeq(MkZingDot(cont, "reason"), MkZingDot("ContinuationReason", "Pop")), MkZingReturn(ZingData.Cnst_False)));
            executeStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("TraceExitState"), state)));
            executeStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("ReentrancyHelper"), MkZingDot(state, "exitFun"), MkZingIdentifier("null"))));
            executeStmts.Add(MkZingAssign(MkZingDot("myHandle", "currentEvent"), MkZingIdentifier("null")));
            executeStmts.Add(MkZingAssign(MkZingDot("myHandle", "currentArg"), MkZingIdentifier("null")));
            executeStmts.Add(MkZingReturn(ZingData.Cnst_True));
            blocks.Add(MkZingBlock("execute", MkZingSeq(executeStmts)));

            List<AST<Node>> seqStmts = new List<AST<Node>>();
            List<AST<Node>> handleStmts = new List<AST<Node>>();
            seqStmts.Add(MkZingAssign(actionFun, MkZingCall(MkZingDot("myHandle", "stack", "Find"), MkZingDot("myHandle", "currentEvent"))));
            seqStmts.Add(MkZingGoto("execute"));
            handleStmts.Add(MkZingAssign(payload, MkZingDot("myHandle", "currentArg")));
            handleStmts.Add(MkZingIfThen(MkZingIn(MkZingDot("myHandle", "currentEvent"), MkZingDot("myHandle", "stack", "actionSet")), MkZingSeq(seqStmts)));
            handleStmts.Add(MkZingAssign(transition, MkZingCall(MkZingDot(state, "FindPushTransition"), MkZingDot("myHandle", "currentEvent"))));
            seqStmts = new List<AST<Node>>();
            seqStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("Run"), MkZingDot("transition", "to"))));
            seqStmts.Add(MkZingIfThenElse(MkZingEq(MkZingDot("myHandle", "currentEvent"), MkZingIdentifier("null")), MkZingReturn(ZingData.Cnst_False), MkZingGoto("handle")));
            handleStmts.Add(MkZingIfThen(MkZingNeq(transition, MkZingIdentifier("null")), MkZingSeq(seqStmts)));
            handleStmts.Add(MkZingAssign(transition, MkZingCall(MkZingDot(state, "FindTransition"), MkZingDot("myHandle", "currentEvent"))));
            handleStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("TraceExitState"), state)));
            handleStmts.Add(MkZingCallStmt(MkZingCall(MkZingIdentifier("ReentrancyHelper"), MkZingDot(state, "exitFun"), MkZingIdentifier("null"))));
            handleStmts.Add(MkZingIfThen(MkZingEq(transition, MkZingIdentifier("null")), MkZingReturn(ZingData.Cnst_True)));
            handleStmts.Add(MkZingAssign(payload, MkZingCall(MkZingIdentifier("ReentrancyHelper"), MkZingDot("transition", "fun"), payload)));
            handleStmts.Add(MkZingAssign(MkZingDot("myHandle", "stack", "state"), MkZingDot("transition", "to")));
            handleStmts.Add(MkZingGoto("enter"));
            blocks.Add(MkZingBlock("handle", MkZingSeq(handleStmts)));

            return MkZingMethodDecl("RunHelper", parameters, ZingData.Cnst_Bool, MkZingVarDecls(locals), MkZingBlocks(blocks));
        }

        private IEnumerable<Node> ZingUnfold(ZingFoldContext ctxt, Node n)
        {
            if (n.NodeKind != NodeKind.FuncTerm)
            {
                yield break;
            }

            var ft = (FuncTerm)n;
            var funName = ((Id)ft.Function).Name;
            if (funName == PData.Con_New.Node.Name)
            {
                Debug.Assert(false, "New expr in ZingUnfold");
                yield break;
            }
            else if (funName == PData.Con_Print.Node.Name)
            {
                foreach (var a in ZingUnfold(ctxt, GetArgByIndex(ft, 2)))
                {
                    yield return a;
                }
            }
            else if (funName == PData.Con_Goto.Node.Name)
            {
                foreach (var a in ZingUnfold(ctxt, GetArgByIndex(ft, 1)))
                {
                    yield return a;
                }
            }
            else if (funName == PData.Con_Announce.Node.Name || funName == PData.Con_Raise.Node.Name)
            {
                yield return GetArgByIndex(ft, 0);
                foreach (var a in ZingUnfold(ctxt, GetArgByIndex(ft, 1)))
                {
                    yield return a;
                }
            }
            else if (funName == PData.Con_Send.Node.Name)
            {
                yield return GetArgByIndex(ft, 0);
                yield return GetArgByIndex(ft, 1);
                foreach (var a in ZingUnfold(ctxt, GetArgByIndex(ft, 2)))
                {
                    yield return a;
                }
            }
            else if (funName == PData.Con_Receive.Node.Name)
            {
                yield break;
            }
            else if (funName == PData.Con_FunApp.Node.Name)
            {
                foreach (var a in ZingUnfold(ctxt, GetArgByIndex(ft, 1)))
                {
                    yield return a;
                }
            }
            else if (funName == PData.Con_FunStmt.Node.Name || funName == PData.Con_NewStmt.Node.Name)
            {
                foreach (var a in ZingUnfold(ctxt, GetArgByIndex(ft, 1)))
                {
                    yield return a;
                }
                var node = GetArgByIndex(ft, 2);
                if (node.NodeKind != NodeKind.Id)
                {
                    yield return node;
                }
            }
            else if (funName == PData.Con_BinApp.Node.Name)
            {
                var opName = ((Id)GetArgByIndex(ft, 0)).Name;
                if (opName == PData.Cnst_Idx.Node.Name && ctxt.lhsStack.Count > 0 && ctxt.lhsStack.Peek())
                {
                    ctxt.lhsStack.Push(true);
                    yield return GetArgByIndex(ft, 1);
                    ctxt.lhsStack.Pop();
                    ctxt.lhsStack.Push(false);
                    yield return GetArgByIndex(ft, 2);
                    ctxt.lhsStack.Pop();
                }
                else
                {
                    yield return GetArgByIndex(ft, 1);
                    yield return GetArgByIndex(ft, 2);
                }
            }
            else if (funName == PData.Con_Name.Node.Name ||
                     funName == PData.Con_NulApp.Node.Name ||
                     funName == PData.Con_UnApp.Node.Name ||
                     funName == PData.Con_Default.Node.Name ||
                     funName == PData.Con_NulStmt.Node.Name)
            {
                var first = true;
                foreach (var t in ft.Args)
                {
                    if (first)
                    {
                        first = false;
                        continue;
                    }
                    yield return t;
                }
            }
            else if (funName == PData.Con_Assert.Node.Name)
            {
                yield return GetArgByIndex(ft, 0);
            }
            else if (funName == PData.Con_BinStmt.Node.Name)
            {
                yield return GetArgByIndex(ft, 3);
                var op = ((Id)GetArgByIndex(ft, 0)).Name;
                if (op == PData.Cnst_Assign.Node.Name)
                {
                    var lhs = (FuncTerm)GetArgByIndex(ft, 1);
                    var lhsName = ((Id)lhs.Function).Name;
                    if (lhsName == PData.Con_BinApp.Node.Name && ((Id)GetArgByIndex(lhs, 0)).Name == PData.Cnst_Idx.Node.Name)
                    {
                        ctxt.lhsStack.Push(true);
                        yield return GetArgByIndex(lhs, 1);
                        ctxt.lhsStack.Pop();
                        yield return GetArgByIndex(lhs, 2);
                    }
                    else if (lhsName == PData.Con_Field.Node.Name)
                    {
                        ctxt.lhsStack.Push(true);
                        yield return GetArgByIndex(lhs, 0);
                        ctxt.lhsStack.Pop();
                    }
                    else
                    {
                        ctxt.lhsStack.Push(true);
                        yield return lhs;
                        ctxt.lhsStack.Pop();
                    }
                }
                else
                {
                    ctxt.lhsStack.Push(true);
                    yield return GetArgByIndex(ft, 1);
                    ctxt.lhsStack.Pop();
                }
            }
            else if (funName == PData.Con_Field.Node.Name || funName == PData.Con_Cast.Node.Name)
            {
                yield return ft.Args.First<Node>();
            }
            else if (funName == PData.Con_Tuple.Node.Name)
            {
                foreach (var a in ZingUnfold(ctxt, GetArgByIndex(ft, 0)))
                {
                    yield return a;
                }
            }
            else if (funName == PData.Con_NamedTuple.Node.Name)
            {
                foreach (var a in ZingUnfold(ctxt, GetArgByIndex(ft, 0)))
                {
                    yield return a;
                }
            }
            else if (funName == PData.Con_Exprs.Node.Name)
            {
                do
                {
                    yield return GetArgByIndex(ft, 1);
                    ft = GetArgByIndex(ft, 2) as FuncTerm;
                }
                while (ft != null);
            }
            else if (funName == PData.Con_NamedExprs.Node.Name)
            {
                do
                {
                    yield return GetArgByIndex(ft, 1);
                    ft = GetArgByIndex(ft, 2) as FuncTerm;
                }
                while (ft != null);
            }
            else if (funName == PData.Con_Seq.Node.Name)
            {
                using (var it = ft.Args.GetEnumerator())
                {
                    it.MoveNext();
                    yield return it.Current;
                    it.MoveNext();
                    ctxt.PushSideEffectStack();
                    yield return it.Current;
                }
            }
            else if (funName == PData.Con_Ite.Node.Name)
            {
                using (var it = ft.Args.GetEnumerator())
                {
                    it.MoveNext();
                    yield return it.Current;
                    it.MoveNext();
                    ctxt.PushSideEffectStack();
                    yield return it.Current;
                    it.MoveNext();
                    ctxt.PushSideEffectStack();
                    yield return it.Current;
                }
            }
            else if (funName == PData.Con_While.Node.Name)
            {
                using (var it = ft.Args.GetEnumerator())
                {
                    it.MoveNext();
                    ctxt.PushSideEffectStack();
                    yield return it.Current;
                    it.MoveNext();
                    ctxt.PushSideEffectStack();
                    yield return it.Current;
                }
            }
            else
            {
                foreach (var t in ft.Args)
                {
                    yield return t;
                }
            }
        }

        private AST<Node> MkZingAssignWithClone(AST<Node> lhs, AST<Node> rhs)
        {
            return MkZingAssign(lhs, MkZingCall(PrtCloneValue, rhs));
        }

        private AST<Node> MkPayload(ZingFoldContext ctxt, List<AST<Node>> args, AST<Node> tupTypeExpr)
        {
            var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpPayload");
            if (args.Count == 0)
            {
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeNull.Node))));
            }
            else if (args.Count == 1)
            {
                ctxt.AddSideEffect(MkZingAssignWithClone(tmpVar, args[0]));
            }
            else
            {
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, tupTypeExpr)));
                int i = 0;
                foreach (var arg in args)
                {
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtTupleSet"), tmpVar, Factory.Instance.MkCnst(i), arg)));
                    i++;
                }
            }
            return tmpVar;
        }

        private ZingTranslationInfo ZingFold(ZingFoldContext ctxt, Node n, IEnumerable<ZingTranslationInfo> children)
        {
            if (n.NodeKind == NodeKind.Id || n.NodeKind == NodeKind.Cnst)
                return new ZingTranslationInfo(ZingData.Cnst_Nil);

            var ft = (FuncTerm)n;
            var funName = ((Id)ft.Function).Name;

            if (funName == PData.Con_Name.Node.Name)
            {
                return FoldName(ft, children, ctxt);
            }
            else if (funName == PData.Con_Receive.Node.Name)
            {
                return FoldReceive(ft, children, ctxt);
            }
            else if (funName == PData.Con_FunApp.Node.Name)
            {
                return FoldFunApp(ft, children, ctxt);
            }
            else if (funName == PData.Con_NulApp.Node.Name)
            {
                return FoldNulApp(ft, children, ctxt);
            }
            else if (funName == PData.Con_UnApp.Node.Name)
            {
                return FoldUnApp(ft, children, ctxt);
            }
            else if (funName == PData.Con_BinApp.Node.Name)
            {
                return FoldBinApp(ft, children, ctxt);
            }
            else if (funName == PData.Con_Field.Node.Name)
            {
                return FoldField(ft, children, ctxt);
            }
            else if (funName == PData.Con_Default.Node.Name)
            {
                return FoldDefault(ft, children, ctxt);
            }
            else if (funName == PData.Con_Cast.Node.Name)
            {
                return FoldCast(ft, children, ctxt);
            }
            else if (funName == PData.Con_Tuple.Node.Name)
            {
                return FoldTuple(ft, children, ctxt);
            }
            else if (funName == PData.Con_NamedTuple.Node.Name)
            {
                return FoldNamedTuple(ft, children, ctxt);
            }
            else if (funName == PData.Con_NewStmt.Node.Name)
            {
                return FoldNewStmt(ft, children, ctxt);
            }
            else if (funName == PData.Con_Goto.Node.Name)
            {
                return FoldGoto(ft, children, ctxt);
            }
            else if (funName == PData.Con_Raise.Node.Name)
            {
                return FoldRaise(ft, children, ctxt);
            }
            else if (funName == PData.Con_Send.Node.Name)
            {
                return FoldSend(ft, children, ctxt);
            }
            else if (funName == PData.Con_Announce.Node.Name)
            {
                return FoldAnnounce(ft, children, ctxt);
            }
            else if (funName == PData.Con_FunStmt.Node.Name)
            {
                return FoldFunStmt(ft, children, ctxt);
            }
            else if (funName == PData.Con_NulStmt.Node.Name)
            {
                return FoldNulStmt(ft, children, ctxt);
            }
            else if (funName == PData.Con_Assert.Node.Name)
            {
                return FoldAssert(ft, children, ctxt);
            }
            else if (funName == PData.Con_Print.Node.Name)
            {
                return FoldPrint(ft, children, ctxt);
            }
            else if (funName == PData.Con_BinStmt.Node.Name)
            {
                return FoldBinStmt(ft, children, ctxt);
            }
            else if (funName == PData.Con_Return.Node.Name)
            {
                return FoldReturn(ft, children, ctxt);
            }
            else if (funName == PData.Con_While.Node.Name)
            {
                return FoldWhile(ft, children, ctxt);
            }
            else if (funName == PData.Con_Ite.Node.Name)
            {
                return FoldIte(ft, children, ctxt);
            }
            else if (funName == PData.Con_Seq.Node.Name)
            {
                return FoldSeq(ft, children, ctxt);
            }
            else if (funName == PData.Con_IdList.Node.Name)
            {
                return new ZingTranslationInfo(ZingData.Cnst_Nil);
            }
            else
            {
                Console.WriteLine("Unknown term name: " + funName);
                throw new NotImplementedException();
            }
        }

        private List<AST<Node>> CaseFunCallHelper(ZingFoldContext ctxt, List<string> eventNames, List<string> funNames, string afterAfterLabel)
        {
            List<AST<Node>> eventStmts = new List<AST<Node>>();
            List<AST<Node>> funStmts = new List<AST<Node>>();

            for (int i = 0; i < eventNames.Count; i++)
            {
                var beforeLabel = ctxt.GetFreshLabel();
                var eventName = eventNames[i];
                var funName = funNames[i];
                var calleeInfo = allGlobalFuns.ContainsKey(funName) ? allGlobalFuns[funName] : allMachines[ctxt.machineName].funNameToFunInfo[funName];
                Debug.Assert(calleeInfo.isAnonymous);
                List<AST<Node>> ifStmts = new List<AST<Node>>();
                ifStmts.Add(MkZingAssign(MkZingIndex(MkZingIdentifier("locals"), Factory.Instance.MkCnst(calleeInfo.localNameToInfo[calleeInfo.PayloadVarName].index)), MkZingCall(PrtCloneValue, MkZingDot("myHandle", "currentArg"))));
                foreach (var calleeLocal in calleeInfo.localNames)
                {
                    var calleeLocalInfo = calleeInfo.localNameToInfo[calleeLocal];
                    ifStmts.Add(MkZingAssign(MkZingIndex(MkZingIdentifier("locals"), Factory.Instance.MkCnst(calleeLocalInfo.index)), MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(calleeLocalInfo.type))));
                }
                ifStmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "PushReturnTo"), Factory.Instance.MkCnst(0), MkZingIdentifier("locals"))));
                ifStmts.Add(MkZingGoto(beforeLabel));
                eventStmts.Add(MkZingIfThen(MkZingEq(MkZingDot("myHandle", "currentEvent"), MkZingEvent(eventName)), MkZingSeq(ifStmts)));
                if (allGlobalFuns.ContainsKey(funName))
                {
                    funStmts.Add(MkZingBlock(beforeLabel, MkZingCallStmt(MkZingCall(MkZingDot("Main", funName), MkZingIdentifier("myHandle"), MkZingIdentifier("entryCtxt")))));
                }
                else
                {
                    funStmts.Add(MkZingBlock(beforeLabel, MkZingCallStmt(MkZingCall(MkZingIdentifier(funName), MkZingIdentifier("entryCtxt")))));
                }
                funStmts.Add(MkZingIfThenElse(
                                     MkZingEq(MkZingDot("entryCtxt", "reason"), MkZingDot("ContinuationReason", "Return")),
                                     MkZingGoto(afterAfterLabel),
                                     MkZingSeq(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "PushReturnTo"), Factory.Instance.MkCnst(ctxt.LabelToId(beforeLabel)), MkZingIdentifier("locals"))),
                                               MkZingReturn(ZingData.Cnst_Nil))));
            }
            List<AST<Node>> stmts = new List<AST<Node>>();
            stmts.AddRange(eventStmts);
            stmts.Add(MkZingAssert(ZingData.Cnst_False));
            stmts.AddRange(funStmts);
            return stmts;
        }

        ZingTranslationInfo FoldReceive(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            List<AST<Node>> stmts = new List<AST<Node>>();
            List<string> eventNames = new List<string>();
            List<string> funNames = new List<string>();
            var cases = GetArgByIndex(ft, 0) as FuncTerm;
            while (cases != null)
            {
                Node evt = GetArgByIndex(cases, 0);
                string eventName = null;
                if (evt is Cnst)
                {
                    eventName = (evt as Cnst).GetStringValue();
                }
                else if ((evt as Id).Name == "NULL")
                {
                    eventName = NullEvent;
                }
                else
                {
                    eventName = HaltEvent;
                }
                eventNames.Add(eventName);
                stmts.Add(MkZingAssign(MkZingDot("myHandle", "receiveSet"), MkZingAdd(MkZingDot("myHandle", "receiveSet"), MkZingEvent(eventName))));
                var fun = GetArgByIndex(cases, 1);
                string funName = anonFunToName[Factory.Instance.ToAST(fun)];
                funNames.Add(funName);
                cases = GetArgByIndex(cases, 2) as FuncTerm;
            }
            var afterLabel = ctxt.GetFreshLabel();
            stmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Receive"), Factory.Instance.MkCnst(ctxt.LabelToId(afterLabel)), MkZingIdentifier("locals"))));
            stmts.Add(MkZingReturn(ZingData.Cnst_Nil));
            stmts.Add(MkZingBlock(afterLabel, ZingData.Cnst_Nil));
            var afterAfterLabel = ctxt.GetFreshLabel();
            stmts.AddRange(CaseFunCallHelper(ctxt, eventNames, funNames, afterAfterLabel));
            stmts.Add(MkZingBlock(afterAfterLabel, ZingData.Cnst_Nil));
            return new ZingTranslationInfo(MkZingSeq(stmts));
        }

        ZingTranslationInfo FoldName(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            AST<Node> retVal;
            var name = GetName(ft, 0);
            FunInfo funInfo = ctxt.entityInfo as FunInfo;
            if (funInfo != null && funInfo.localNameToInfo.ContainsKey(name))
            {
                retVal = MkZingIndex(MkZingIdentifier("locals"), Factory.Instance.MkCnst(funInfo.localNameToInfo[name].index));
            }
            else if (ctxt.machineName != null && allMachines[ctxt.machineName].localVariableToVarInfo.ContainsKey(name))
            {
                retVal = MkZingIdentifier(name);
            }
            else
            {
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                var type = LookupType(ctxt, ft);
                if (PTypeEvent.Equals(Factory.Instance.ToAST(type)))
                {
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeEvent.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetEvent"), tmpVar, MkZingEvent(name))));
                }
                else
                {
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(type))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetInt"), tmpVar, MkZingEnum(name))));
                }
                retVal = tmpVar;
            }
            return new ZingTranslationInfo(retVal);
        }

        ZingTranslationInfo FoldNewStmt(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            AST<Node> aout = null;
            List<AST<Node>> args = new List<AST<Node>>(children.Select(x => x.node));
            if (GetArgByIndex(ft, 2).NodeKind != NodeKind.Id)
            {
                aout = args.Last();
                args.RemoveAt(args.Count-1);
            }
            var machineName = GetName(ft, 0);
            // Ignore all indirect creation 
            // PtoZing does not support indirect creation via interfaces
            if (allMachines.ContainsKey(machineName))
            {
                MachineInfo machineInfo = allMachines[machineName];
                string initStateEntryActionName = machineInfo.stateNameToStateInfo[machineInfo.initStateName].entryActionName;
                FunInfo entryFunInfo = allGlobalFuns.ContainsKey(initStateEntryActionName)
                                        ? allGlobalFuns[initStateEntryActionName]
                                        : machineInfo.funNameToFunInfo[initStateEntryActionName];
                AST<Node> payloadVar = MkPayload(ctxt, args, typeContext.PTypeToZingExpr(entryFunInfo.PayloadType));
                var newMachine = ctxt.GetTmpVar(SmHandle, "newMachine");
                ctxt.AddSideEffect(MkZingAssign(newMachine, MkZingCall(MkZingDot("Main", string.Format("CreateMachine_{0}", machineName)), payloadVar)));
                string afterLabel = ctxt.GetFreshLabel();
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "NewMachine"), Factory.Instance.MkCnst(ctxt.LabelToId(afterLabel)), MkZingIdentifier("locals"), newMachine)));
                ctxt.AddSideEffect(MkZingReturn(ZingData.Cnst_Nil));
                ctxt.AddSideEffect(MkZingBlock(afterLabel, MkZingAssign(newMachine, MkZingDot("entryCtxt", "id"))));
                ctxt.AddSideEffect(MkZingAssign(MkZingDot("entryCtxt", "id"), MkZingIdentifier("null")));
                if (aout != null)
                {
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetMachine"), aout, newMachine)));
                }
            }
            return new ZingTranslationInfo(ZingData.Cnst_Nil);
        }

        ZingTranslationInfo FoldFunApp(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            List<bool> isSwapParameter = new List<bool>();
            var exprs = GetArgByIndex(ft, 1) as FuncTerm;
            while (exprs != null)
            {
                var qualifier = GetArgByIndex(exprs, 0) as Id;
                isSwapParameter.Add(qualifier.Name == "SWAP");
                exprs = GetArgByIndex(exprs, 2) as FuncTerm;
            }

            var calleeName = GetName(ft, 0);
            var calleeInfo = allGlobalFuns.ContainsKey(calleeName) ? allGlobalFuns[calleeName] : allMachines[ctxt.machineName].funNameToFunInfo[calleeName];

            ZingTranslationInfo outputVarInfo = null;
            var argCloneVar = ctxt.GetTmpVar(Factory.Instance.MkCnst("PRT_VALUE_ARRAY"), "argCloneVar");
            if (calleeInfo.maxNumLocals == 0)
            {
                ctxt.AddSideEffect(MkZingAssign(argCloneVar, MkZingIdentifier("null")));
            }
            else
            {
                ctxt.AddSideEffect(MkZingAssign(argCloneVar, MkZingNew(Factory.Instance.MkCnst("PRT_VALUE_ARRAY"), Factory.Instance.MkCnst(calleeInfo.maxNumLocals))));
            }
            int parameterCount = 0;
            List<AST<Node>> processRefParams = new List<AST<Node>>();
            foreach (var child in children)
            {
                if (parameterCount == calleeInfo.parameterNames.Count)
                {
                    // output variable
                    outputVarInfo = child;
                    break;
                }
                var calleeArg = calleeInfo.parameterNames[parameterCount];
                var calleeArgInfo = calleeInfo.localNameToInfo[calleeArg];
                ctxt.AddSideEffect(MkZingAssignWithClone(MkZingIndex(argCloneVar, Factory.Instance.MkCnst(calleeArgInfo.index)), child.node));
                if (isSwapParameter[parameterCount])
                {
                    processRefParams.Add(MkZingAssign(child.node, MkZingIndex(MkZingDot("entryCtxt", "retLocals"), Factory.Instance.MkCnst(calleeArgInfo.index))));
                }
                if (calleeInfo.printArgs.Contains(calleeArg))
                {
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "Print"), MkZingIndex(argCloneVar, Factory.Instance.MkCnst(calleeArgInfo.index)))));
                    ctxt.AddSideEffect(MkZingTrace("\\n"));
                }
                parameterCount++;
            }

            foreach (var calleeLocal in calleeInfo.localNames)
            {
                var calleeLocalInfo = calleeInfo.localNameToInfo[calleeLocal];
                ctxt.AddSideEffect(MkZingAssign(MkZingIndex(argCloneVar, Factory.Instance.MkCnst(calleeLocalInfo.index)), MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(calleeLocalInfo.type))));
            }

            foreach (var x in calleeInfo.invokeSchedulerFuns)
            {
                List<AST<Node>> invokeSchedulerArgs = new List<AST<Node>>();
                if (x.NodeKind == NodeKind.Cnst)
                {
                    Cnst cnst = x as Cnst;
                    if (cnst.CnstKind == CnstKind.String)
                    {
                        invokeSchedulerArgs.Add(Factory.Instance.MkCnst(string.Format("\"{0}\"", cnst.GetStringValue())));
                    }
                    else
                    {
                        invokeSchedulerArgs.Add(Factory.Instance.ToAST(x));
                    }
                }
                for (int i = 0; i < children.Count(); i++)
                {
                    invokeSchedulerArgs.Add(MkZingDot(MkZingIndex(argCloneVar, Factory.Instance.MkCnst(i)), "nt"));
                }
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingIdentifier("invokescheduler"), invokeSchedulerArgs)));
            }

            foreach (var x in calleeInfo.invokePluginFuns)
            {
                List<AST<Node>> invokePluginArgs = new List<AST<Node>>();
                if (x.NodeKind == NodeKind.Cnst)
                {
                    Cnst cnst = x as Cnst;
                    if (cnst.CnstKind == CnstKind.String)
                    {
                        invokePluginArgs.Add(Factory.Instance.MkCnst(string.Format("\"{0}\"", cnst.GetStringValue())));
                    }
                    else
                    {
                        invokePluginArgs.Add(Factory.Instance.ToAST(x));
                    }
                }
                for (int i = 0; i < children.Count(); i++)
                {
                    invokePluginArgs.Add(MkZingDot(MkZingIndex(argCloneVar, Factory.Instance.MkCnst(i)), "nt"));
                }
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingIdentifier("invokeplugin"), invokePluginArgs)));
            }

            ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "PushReturnTo"), Factory.Instance.MkCnst(0), argCloneVar)));

            var beforeLabel = ctxt.GetFreshLabel();
            if (allGlobalFuns.ContainsKey(calleeName))
            {
                ctxt.AddSideEffect(MkZingBlock(beforeLabel, MkZingCallStmt(MkZingCall(MkZingDot("Main", calleeName), MkZingIdentifier("myHandle"), MkZingIdentifier("entryCtxt")))));
            }
            else
            {
                ctxt.AddSideEffect(MkZingBlock(beforeLabel, MkZingCallStmt(MkZingCall(MkZingIdentifier(calleeName), MkZingIdentifier("entryCtxt")))));
            }

            AST<Node> processOutput;
            AST<Node> retVal;
            if (((Id)ft.Function).Name == "FunStmt")
            {
                retVal = ZingData.Cnst_Nil;
                if (outputVarInfo == null)
                {
                    processOutput = ZingData.Cnst_Nil;
                }
                else
                {
                    processOutput = MkZingAssignWithClone(outputVarInfo.node, MkZingDot("entryCtxt", "retVal"));
                }
            }
            else
            {
                retVal = ctxt.GetTmpVar(PrtValue, "ret");
                processOutput = MkZingAssign(retVal, MkZingDot("entryCtxt", "retVal"));
            }
            processOutput = MkZingSeq(processOutput, MkZingSeq(processRefParams));
            ctxt.AddSideEffect(MkZingIfThenElse(
                                 MkZingEq(MkZingDot("entryCtxt", "reason"), MkZingDot("ContinuationReason", "Return")),
                                 processOutput,
                                 MkZingSeq(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "PushReturnTo"), Factory.Instance.MkCnst(ctxt.LabelToId(beforeLabel)), MkZingIdentifier("locals"))),
                                           MkZingReturn(ZingData.Cnst_Nil))));
            return new ZingTranslationInfo(retVal);
        }

        ZingTranslationInfo FoldNulApp(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var n = GetArgByIndex(ft, 0);
            if (n.NodeKind == NodeKind.Cnst)
            {
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeInt.Node))));
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetInt"), tmpVar, Factory.Instance.ToAST(n))));
                return new ZingTranslationInfo(tmpVar);
            }

            // n.NodeKind == NodeKind.Id
            AST<Node> retVal;
            var op = ((Id)n).Name;
            if (op == PData.Cnst_True.Node.Name)
            {
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, ZingData.Cnst_True)));
                retVal = tmpVar;
            }
            else if (op == PData.Cnst_False.Node.Name)
            {
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, ZingData.Cnst_False)));
                retVal = tmpVar;
            }
            else if (op == PData.Cnst_This.Node.Name)
            {
                var machineType = PTypeMachine;
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(machineType.Node))));
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetMachine"), tmpVar, MkZingIdentifier("myHandle"))));
                retVal = tmpVar;
            }
            else if (op == PData.Cnst_Nondet.Node.Name || op == PData.Cnst_FairNondet.Node.Name)
            {
                /*
                var afterLabel = ctxt.GetFreshLabel();
                var bvar = ctxt.GetTmpVar(ZingData.Cnst_Bool, "nondet");
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Nondet"), Factory.Instance.MkCnst(ctxt.LabelToId(afterLabel)), MkZingIdentifier("locals"))));
                ctxt.AddSideEffect(MkZingReturn(ZingData.Cnst_Nil));
                ctxt.AddSideEffect(MkZingBlock(afterLabel, MkZingAssign(bvar, MkZingDot("entryCtxt", "nondet"))));
                ctxt.AddSideEffect(MkZingAssign(MkZingDot("entryCtxt", "nondet"), ZingData.Cnst_False));
                if (compiler.Options.liveness == LivenessOption.Standard && op == PData.Cnst_FairNondet.Node.Name)
                {
                    int i = ctxt.entityInfo.numFairChoices;
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(GetFairChoice(ctxt.entityName, i), "AtChoose"), bvar)));
                    ctxt.entityInfo.numFairChoices++;
                }
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, bvar)));
                retVal = tmpVar;
                */
                var bvar = ctxt.GetTmpVar(ZingData.Cnst_Bool, "nondet");
                ctxt.AddSideEffect(MkZingAssign(bvar, MkZingCall(Factory.Instance.MkCnst("choose"), Factory.Instance.MkCnst("bool"))));
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, bvar)));
                retVal = tmpVar;
                if (compiler.Options.liveness == LivenessOption.Standard && op == PData.Cnst_FairNondet.Node.Name)
                {
                    int i = ctxt.entityInfo.numFairChoices;
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(GetFairChoice(ctxt.entityName, i), "AtChoose"), bvar)));
                    ctxt.entityInfo.numFairChoices++;
                }
            }
            else if (op == PData.Cnst_Null.Node.Name)
            {
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeNull.Node))));
                retVal = tmpVar;
            }
            else
            {
                // op == PData.Cnst_Halt.Node.Name
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmp");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeEvent.Node))));
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetEvent"), tmpVar, MkZingEvent(HaltEvent))));
                retVal = tmpVar;
            }
            return new ZingTranslationInfo(retVal);
        }

        ZingTranslationInfo FoldUnApp(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var op = ((Id)GetArgByIndex(ft, 0)).Name;
            using (var it = children.GetEnumerator())
            {
                AST<Node> retVal;
                it.MoveNext();
                var arg = it.Current.node;
                if (op == PData.Cnst_Not.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, MkZingNot(MkZingDot(arg, "bl")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Neg.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeInt.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetInt"), tmpVar, MkZingApply(ZingData.Cnst_Neg, MkZingDot(arg, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Keys.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtMapGetKeys"), arg)));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Values.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtMapGetValues"), arg)));
                    retVal = tmpVar;
                }
                else
                {
                    //  op == PData.Cnst_Sizeof.Node.Name
                    var type = LookupType(ctxt, GetArgByIndex(ft, 1));
                    var typeOp = ((Id)type.Function).Name;
                    var tmpVar = ctxt.GetTmpVar(ZingData.Cnst_Int, "tmpVar");
                    if (typeOp == PData.Con_SeqType.Node.Name)
                    {
                        ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtSeqSizeOf"), arg)));
                    }
                    else
                    {
                        // typeOp == PData.Con_MapType.Node.Name)
                        ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtMapSizeOf"), arg)));
                    }
                    retVal = ctxt.GetTmpVar(PrtValue, "retVal");
                    ctxt.AddSideEffect(MkZingAssign(retVal, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeInt.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetInt"), retVal, tmpVar)));
                }
                return new ZingTranslationInfo(retVal);
            }
        }

        ZingTranslationInfo FoldBinApp(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var op = ((Id)GetArgByIndex(ft, 0)).Name;
            using (var it = children.GetEnumerator())
            {
                AST<Node> retVal;
                it.MoveNext();
                var arg1 = it.Current.node;
                it.MoveNext();
                var arg2 = it.Current.node;

                if (op == PData.Cnst_Add.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeInt.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetInt"), tmpVar, MkZingApply(ZingData.Cnst_Add, MkZingDot(arg1, "nt"), MkZingDot(arg2, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Sub.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeInt.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetInt"), tmpVar, MkZingApply(ZingData.Cnst_Sub, MkZingDot(arg1, "nt"), MkZingDot(arg2, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Mul.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeInt.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetInt"), tmpVar, MkZingApply(ZingData.Cnst_Mul, MkZingDot(arg1, "nt"), MkZingDot(arg2, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Div.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeInt.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetInt"), tmpVar, MkZingApply(ZingData.Cnst_IntDiv, MkZingDot(arg1, "nt"), MkZingDot(arg2, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_And.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, MkZingApply(ZingData.Cnst_And, MkZingDot(arg1, "bl"), MkZingDot(arg2, "bl")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Or.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, MkZingApply(ZingData.Cnst_Or, MkZingDot(arg1, "bl"), MkZingDot(arg2, "bl")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Eq.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(ZingData.Cnst_Bool, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtIsEqualValue"), arg1, arg2)));
                    retVal = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(retVal, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), retVal, tmpVar)));
                }
                else if (op == PData.Cnst_NEq.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(ZingData.Cnst_Bool, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtIsEqualValue"), arg1, arg2)));
                    retVal = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(retVal, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), retVal, MkZingNot(tmpVar))));
                }
                else if (op == PData.Cnst_Lt.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, MkZingApply(ZingData.Cnst_Lt, MkZingDot(arg1, "nt"), MkZingDot(arg2, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Le.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, MkZingApply(ZingData.Cnst_Le, MkZingDot(arg1, "nt"), MkZingDot(arg2, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Gt.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, MkZingApply(ZingData.Cnst_Gt, MkZingDot(arg1, "nt"), MkZingDot(arg2, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Ge.Node.Name)
                {
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), tmpVar, MkZingApply(ZingData.Cnst_Ge, MkZingDot(arg1, "nt"), MkZingDot(arg2, "nt")))));
                    retVal = tmpVar;
                }
                else if (op == PData.Cnst_Idx.Node.Name)
                {
                    var type = LookupType(ctxt, GetArgByIndex(ft, 1));
                    var typeOp = ((Id)type.Function).Name;
                    var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    if (typeOp == PData.Con_SeqType.Node.Name)
                    {
                        if (ctxt.lhsStack.Count > 0 && ctxt.lhsStack.Peek())
                        {
                            ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtSeqGetNoClone"), arg1, arg2)));
                        }
                        else
                        {
                            ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtSeqGet"), arg1, arg2)));
                        }
                    }
                    else
                    {
                        // op == PData.Con_MapType.Node.Name
                        if (ctxt.lhsStack.Count > 0 && ctxt.lhsStack.Peek())
                        {
                            ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtMapGetNoClone"), arg1, arg2)));
                        }
                        else
                        {
                            ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtMapGet"), arg1, arg2)));
                        }
                    }
                    retVal = tmpVar;
                }
                else
                {
                    // op == PData.Cnst_In.Node.Name
                    var tmpVar = ctxt.GetTmpVar(ZingData.Cnst_Bool, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtMapExists"), arg2, arg1)));
                    retVal = ctxt.GetTmpVar(PrtValue, "tmpVar");
                    ctxt.AddSideEffect(MkZingAssign(retVal, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeBool.Node))));
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtPrimSetBool"), retVal, tmpVar)));
                }
                return new ZingTranslationInfo(retVal);
            }
        }

        private int GetFieldIndex(string fieldName, FuncTerm nmdTupType)
        {
            int fieldIndex = 0;
            while (nmdTupType != null)
            {
                var fieldInfo = (FuncTerm)GetArgByIndex(nmdTupType, 0);
                var fieldNameInFieldInfo = (Cnst)GetArgByIndex(fieldInfo, 0);
                if (fieldName == fieldNameInFieldInfo.GetStringValue())
                    return fieldIndex;
                nmdTupType = GetArgByIndex(nmdTupType, 1) as FuncTerm;
                fieldIndex++;
            }
            Debug.Assert(false);
            return 0;
        }

        ZingTranslationInfo FoldField(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var expr = GetArgByIndex(ft, 0);
            var field = (Cnst)GetArgByIndex(ft, 1);
            int fieldIndex;
            if (field.CnstKind == CnstKind.Numeric)
            {
                fieldIndex = (int)field.GetNumericValue().Numerator;
            }
            else
            {
                fieldIndex = GetFieldIndex(field.GetStringValue(), LookupType(ctxt, expr));
            }
            using (var it = children.GetEnumerator())
            {
                it.MoveNext();
                var arg = it.Current.node;
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVal");
                if (ctxt.lhsStack.Count > 0 && ctxt.lhsStack.Peek())
                {
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingIndex(MkZingDot(arg, "tuple"), Factory.Instance.MkCnst(fieldIndex))));
                }
                else
                {
                    ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(MkZingDot(PRT_VALUE, "PrtTupleGet"), arg, Factory.Instance.MkCnst(fieldIndex))));
                }
                return new ZingTranslationInfo(tmpVar);
            }
        }

        ZingTranslationInfo FoldDefault(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var typeArg = (FuncTerm)GetArgByIndex(ft, 0);
            var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
            ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(typeArg))));
            return new ZingTranslationInfo(tmpVar);
        }

        ZingTranslationInfo FoldCast(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var typeArg = (FuncTerm)GetArgByIndex(ft, 1);
            using (var it = children.GetEnumerator())
            {
                it.MoveNext();
                var valueArg = it.Current.node;
                var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpVar");
                ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtCastValue, valueArg, typeContext.PTypeToZingExpr(typeArg))));
                return new ZingTranslationInfo(tmpVar);
            }
        }

        ZingTranslationInfo FoldTuple(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var tupType = LookupType(ctxt, ft);
            var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpTuple");
            ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(tupType))));
            int i = 0;
            foreach (var c in children)
            {
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtTupleSet"), tmpVar, Factory.Instance.MkCnst(i), c.node)));
                i++;
            }
            return new ZingTranslationInfo(tmpVar);
        }

        ZingTranslationInfo FoldNamedTuple(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var tupType = LookupType(ctxt, ft);
            var tmpVar = ctxt.GetTmpVar(PrtValue, "tmpTuple");
            ctxt.AddSideEffect(MkZingAssign(tmpVar, MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(tupType))));
            int i = 0;
            foreach (var c in children)
            {
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtTupleSet"), tmpVar, Factory.Instance.MkCnst(i), c.node)));
                i++;
            }
            return new ZingTranslationInfo(tmpVar);
        }

        ZingTranslationInfo FoldGoto(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var qualifiedStateName = (FuncTerm)GetArgByIndex(ft, 0);
            var stateName = GetNameFromQualifiedName(ctxt.machineName, qualifiedStateName);
            var stateExpr = MkZingState(stateName);
            MachineInfo machineInfo = allMachines[ctxt.machineName];
            string stateEntryActionName = machineInfo.stateNameToStateInfo[stateName].entryActionName;
            FunInfo entryFunInfo = allGlobalFuns.ContainsKey(stateEntryActionName)
                                    ? allGlobalFuns[stateEntryActionName]
                                    : machineInfo.funNameToFunInfo[stateEntryActionName];
            List<AST<Node>> args = new List<AST<Node>>(children.Select(x => x.node));
            var payloadVar = MkPayload(ctxt, args, typeContext.PTypeToZingExpr(entryFunInfo.PayloadType));
            var traceStmt = MkZingTrace(string.Format("<GotoLog> Machine {0}-{{0}} goes to {{1}}\\n", ctxt.machineName), MkZingDot("myHandle", "instance"), MkZingDot(stateExpr, "name"));
            var assignStmt = MkZingSeq(MkZingAssign(MkZingDot("myHandle", "currentEvent"), MkZingIdentifier("null")),
                                       MkZingAssign(MkZingDot("myHandle", "currentArg"), payloadVar),
                                       MkZingAssign(MkZingDot("myHandle", "destState"), stateExpr));
            var createRetCtxt = MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Goto")));
            return new ZingTranslationInfo(MkZingSeq(traceStmt, assignStmt, createRetCtxt, MkZingReturn(ZingData.Cnst_Nil)));
        }

        ZingTranslationInfo FoldRaise(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            List<AST<Node>> args = new List<AST<Node>>(children.Select(x => x.node));
            var eventExpr = MkZingDot(args[0], "ev");
            args.RemoveAt(0);
            var eventPayloadTypeTmpVar = ctxt.GetTmpVar(PrtType, "eventPayloadType");
            ctxt.AddSideEffect(MkZingAssign(eventPayloadTypeTmpVar, MkZingCall(MkZingDot("Main", "PayloadOf"), eventExpr)));
            var payloadVar = MkPayload(ctxt, args, eventPayloadTypeTmpVar);
            var assertStmt = MkZingAssert(MkZingNeq(eventExpr, MkZingIdentifier("null")), SpanToString(LookupSpan(ft), "Raised event must be non-null"));
            var traceStmt = MkZingTrace(string.Format("<RaiseLog> Machine {0}-{{0}} raised Event {{1}}\\n", ctxt.machineName), MkZingDot("myHandle", "instance"), MkZingDot(eventExpr, "name"));
            var assignStmt = MkZingSeq(MkZingAssign(MkZingDot("myHandle", "currentEvent"), eventExpr), MkZingAssign(MkZingDot("myHandle", "currentArg"), payloadVar));
            var createRetCtxt = MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Raise")));
            return new ZingTranslationInfo(MkZingSeq(assertStmt, traceStmt, assignStmt, createRetCtxt, MkZingReturn(ZingData.Cnst_Nil)));
        }

        ZingTranslationInfo FoldSend(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            List<AST<Node>> args = new List<AST<Node>>(children.Select(x => x.node));
            var targetExpr = MkZingDot(args[0], "mach");
            var eventExpr = MkZingDot(args[1], "ev");
            args.RemoveRange(0, 2);
            var eventPayloadTypeTmpVar = ctxt.GetTmpVar(PrtType, "eventPayloadType");
            ctxt.AddSideEffect(MkZingAssign(eventPayloadTypeTmpVar, MkZingCall(MkZingDot("Main", "PayloadOf"), eventExpr)));
            var payloadVar = MkPayload(ctxt, args, eventPayloadTypeTmpVar);
            ctxt.AddSideEffect(MkZingAssert(MkZingNeq(targetExpr, MkZingIdentifier("null")), "Target of send must be non-null"));
            var afterLabel = ctxt.GetFreshLabel();
            foreach (var machineName in allMachines.Keys)
            {
                if (!allMachines[machineName].IsSpec) continue;
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("Main", string.Format("InvokeMachine_{0}", machineName)), eventExpr, payloadVar)));
            }
            ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot(targetExpr, "EnqueueEvent"), eventExpr, payloadVar, Factory.Instance.MkCnst("myHandle"))));
            ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Send"), Factory.Instance.MkCnst(ctxt.LabelToId(afterLabel)), MkZingIdentifier("locals"))));
            return new ZingTranslationInfo(MkZingSeq(MkZingReturn(ZingData.Cnst_Nil), MkZingBlock(afterLabel, ZingData.Cnst_Nil)));
        }

        ZingTranslationInfo FoldAnnounce(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            List<AST<Node>> args = new List<AST<Node>>(children.Select(x => x.node));
            AST<Node> eventExpr = MkZingDot(args[0], "ev");
            args.RemoveAt(0);
            var eventPayloadTypeTmpVar = ctxt.GetTmpVar(PrtType, "eventPayloadType");
            ctxt.AddSideEffect(MkZingAssign(eventPayloadTypeTmpVar, MkZingCall(MkZingDot("Main", "PayloadOf"), eventExpr)));
            var payloadVar = MkPayload(ctxt, args, eventPayloadTypeTmpVar);
            var assertStmt = MkZingAssert(MkZingNeq(eventExpr, MkZingIdentifier("null")), SpanToString(LookupSpan(ft), "Enqueued event must be non-null"));
            ctxt.AddSideEffect(assertStmt);
            List<AST<Node>> stmts = new List<AST<Node>>();
            foreach (var machineName in allMachines.Keys)
            {
                if (!allMachines[machineName].IsSpec) continue;
                stmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("Main", string.Format("InvokeMachine_{0}", machineName)), eventExpr, payloadVar)));
            }
            return new ZingTranslationInfo(MkZingSeq(stmts));
        }

        ZingTranslationInfo FoldFunStmt(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            return FoldFunApp(ft, children, ctxt);
        }

        ZingTranslationInfo FoldNulStmt(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var op = ((Id)GetArgByIndex(ft, 0)).Name;
            if (op == PData.Cnst_Pop.Node.Name)
            {
                ctxt.AddSideEffect(MkZingAssign(MkZingDot("myHandle", "currentEvent"), MkZingIdentifier("null")));
                ctxt.AddSideEffect(MkZingAssign(MkZingDot("myHandle", "currentArg"), MkZingIdentifier("null")));
                ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Pop"))));
                ctxt.AddSideEffect(MkZingReturn(ZingData.Cnst_Nil));
            }
            return new ZingTranslationInfo(ZingData.Cnst_Nil);
        }

        ZingTranslationInfo FoldAssert(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            Cnst msgCnst = GetArgByIndex(ft, 1) as Cnst;
            using (var it = children.GetEnumerator())
            {
                it.MoveNext();
                if (msgCnst != null)
                {
                    return new ZingTranslationInfo(MkZingAssert(MkZingDot(it.Current.node, "bl"), msgCnst.GetStringValue()));
                }
                else
                {
                    return new ZingTranslationInfo(MkZingAssert(MkZingDot(it.Current.node, "bl"), SpanToString(LookupSpan(ft), "Assert failed")));
                }
            }
        }

        ZingTranslationInfo FoldPrint(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            string msg = (GetArgByIndex(ft, 0) as Cnst).GetStringValue();
            List<AST<Node>> stmts = new List<AST<Node>>();
            stmts.Add(MkZingTrace(msg));
            List<AST<Node>> args = new List<AST<Node>>();
            foreach (var child in children)
            {
                args.Add(child.node);
            }
            FuncTerm seg = GetArgByIndex(ft, 1) as FuncTerm;
            while (seg != null)
            {
                int formatArg = (int) (GetArgByIndex(seg, 0) as Cnst).GetNumericValue().Numerator;
                string str = (GetArgByIndex(seg, 1) as Cnst).GetStringValue();
                seg = GetArgByIndex(seg, 2) as FuncTerm;
                stmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "Print"), args[formatArg])));
                stmts.Add(MkZingTrace(str));
            }
            return new ZingTranslationInfo(MkZingSeq(stmts));
        }

        ZingTranslationInfo FoldBinStmt(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            var op = ((Id)GetArgByIndex(ft, 0)).Name;
            var lhs = (FuncTerm)GetArgByIndex(ft, 1);
            var type = LookupType(ctxt, lhs);
            var typeName = ((Id)type.Function).Name;
            AST<Node> src = null, dest = null;
            using (var it = children.GetEnumerator())
            {
                AST<Node> index = null;
                it.MoveNext();
                src = it.Current.node;
                it.MoveNext();
                dest = it.Current.node;
                if (it.MoveNext())
                {
                    index = it.Current.node;
                }

                if (op == PData.Cnst_Assign.Node.Name)
                {
                    string assignType = (GetArgByIndex(ft, 2) as Id).Name;
                    if (((Id)lhs.Function).Name == PData.Con_Field.Node.Name)
                    {
                        var field = (Cnst)GetArgByIndex(lhs, 1);
                        int fieldIndex;
                        if (field.CnstKind == CnstKind.Numeric)
                        {
                            fieldIndex = (int)field.GetNumericValue().Numerator;
                        }
                        else
                        {
                            fieldIndex = GetFieldIndex(field.GetStringValue(), LookupType(ctxt, GetArgByIndex(lhs, 0)));
                        }
                        if (assignType == "NONE")
                        {
                            var returnStmt = MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "PrtTupleSet"), dest, Factory.Instance.MkCnst(fieldIndex), src));
                            return new ZingTranslationInfo(returnStmt);
                        }
                        else if (assignType == "MOVE")
                        {
                            var returnStmt = 
                                MkZingSeq(
                                    MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "PrtTupleSet"), dest, Factory.Instance.MkCnst(fieldIndex), src)),
                                    MkZingAssign(src, MkZingIdentifier("null")));
                            return new ZingTranslationInfo(returnStmt);
                        }
                        else
                        {   // assignType = "SWAP" 
                            var returnStmt = MkZingAssign(src, MkZingCall(MkZingDot("PRT_VALUE", "PrtTupleSetAndReturnOldValue"), dest, Factory.Instance.MkCnst(fieldIndex), src));
                            return new ZingTranslationInfo(returnStmt);
                        }
                    }
                    else if (index == null)
                    {
                        if (assignType == "NONE")
                        {
                            return new ZingTranslationInfo(MkZingAssignWithClone(dest, src));
                        }
                        else if (assignType == "MOVE")
                        {
                            return new ZingTranslationInfo(MkZingSeq(MkZingAssign(dest, src), MkZingAssign(src, MkZingIdentifier("null"))));
                        }
                        else
                        {   // assignType == "SWAP"
                            var swapVar = ctxt.GetTmpVar(PrtValue, "swap");
                            return new ZingTranslationInfo(MkZingSeq(MkZingAssign(swapVar, dest), MkZingAssign(dest, src), MkZingAssign(src, swapVar)));
                        }
                    }
                    else
                    {
                        lhs = (FuncTerm)GetArgByIndex(lhs, 1);
                        type = LookupType(ctxt, lhs);
                        typeName = ((Id)type.Function).Name;
                        if (typeName == PData.Con_SeqType.Node.Name)
                        {
                            if (assignType == "NONE")
                            {
                                var returnStmt = MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "PrtSeqSet"), dest, index, src));
                                return new ZingTranslationInfo(returnStmt);
                            }
                            else if (assignType == "MOVE")
                            {
                                var returnStmt =
                                    MkZingSeq(
                                        MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "PrtSeqSet"), dest, index, src)),
                                        MkZingAssign(src, MkZingIdentifier("null")));
                                return new ZingTranslationInfo(returnStmt);
                            }
                            else
                            {   // assignType == "SWAP"
                                var returnStmt = MkZingAssign(src, MkZingCall(MkZingDot("PRT_VALUE", "PrtSeqSetAndReturnOldValue"), dest, index, src));
                                return new ZingTranslationInfo(returnStmt);
                            }
                        }
                        else
                        {
                            // type is PMapType
                            if (assignType == "NONE")
                            {
                                var returnStmt = MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "PrtMapSet"), dest, index, src));
                                return new ZingTranslationInfo(returnStmt);
                            }
                            else if (assignType == "MOVE")
                            {
                                var returnStmt =
                                    MkZingSeq(
                                        MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "PrtMapSet"), dest, index, src)),
                                        MkZingAssign(src, MkZingIdentifier("null")));
                                return new ZingTranslationInfo(returnStmt);
                            }
                            else
                            {   // assignType == "SWAP"
                                var returnStmt = MkZingAssign(src, MkZingCall(MkZingDot("PRT_VALUE", "PrtMapSetAndReturnOldValue"), dest, index, src));
                                return new ZingTranslationInfo(returnStmt);
                            }
                        }
                    }
                }
                else if (op == PData.Cnst_Remove.Node.Name)
                {
                    if (typeName == PData.Con_SeqType.Node.Name)
                    {
                        return new ZingTranslationInfo(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtSeqRemove"), dest, src)));
                    }
                    else
                    {
                        return new ZingTranslationInfo(MkZingCallStmt(MkZingCall(MkZingDot(PRT_VALUE, "PrtMapRemove"), dest, src)));
                    }
                }
                else
                {
                    // op == PData.Cnst_Insert.Node.Name
                    var idx = ctxt.GetTmpVar(PrtValue, "idx");
                    var val = ctxt.GetTmpVar(PrtValue, "val");
                    ctxt.AddSideEffect(MkZingAssign(idx, MkZingCall(MkZingDot("PRT_VALUE", "PrtTupleGet"), src, Factory.Instance.MkCnst(0))));
                    ctxt.AddSideEffect(MkZingAssign(val, MkZingCall(MkZingDot("PRT_VALUE", "PrtTupleGet"), src, Factory.Instance.MkCnst(1))));
                    return new ZingTranslationInfo(MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "PrtSeqInsert"), dest, idx, val)));
                    
                }
            }
        }

        ZingTranslationInfo FoldReturn(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            FunInfo funInfo = ctxt.entityInfo as FunInfo;
            AST<FuncTerm> returnType = PTypeNull;
            if (funInfo != null)
            {
                returnType = funInfo.returnType;
            }
            using (var it = children.GetEnumerator())
            {
                it.MoveNext();
                if (returnType.Equals(PTypeNull))
                {
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Return"), MkZingIdentifier("locals"))));
                }
                else
                {
                    ctxt.AddSideEffect(MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "ReturnVal"), it.Current.node, MkZingIdentifier("locals"))));
                }
                ctxt.AddSideEffect(MkZingReturn(ZingData.Cnst_Nil));
                return new ZingTranslationInfo(ZingData.Cnst_Nil);
            }
        }

        ZingTranslationInfo FoldWhile(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            using (var it = children.GetEnumerator())
            {
                it.MoveNext();
                var condExpr = MkZingDot(it.Current.node, "bl");
                it.MoveNext();
                var loopStart = GetUnique(ctxt.entityName + "_loop_start");
                var loopEnd = GetUnique(ctxt.entityName + "_loop_end");
                var body = it.Current.node;
                body = ctxt.EmitZingSideEffects(body);
                var res = MkZingBlock(loopStart, MkZingSeq(
                    ctxt.EmitZingSideEffects(MkZingIfThen(MkZingNot(condExpr), MkZingGoto(loopEnd))),
                    body,
                    MkZingGoto(loopStart),
                    MkZingBlock(loopEnd, ZingData.Cnst_Nil)));
                return new ZingTranslationInfo(res);
            }
        }

        ZingTranslationInfo FoldIte(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            using (var it = children.GetEnumerator())
            {
                it.MoveNext();
                var condExpr = MkZingDot(it.Current.node, "bl");
                it.MoveNext();
                var thenStmt = it.Current.node;
                it.MoveNext();
                var elseStmt = it.Current.node;

                // Order in which we emit side effets (else,then) is the reverse of the order in which the side effect stacks were pushed(then, else).
                var ifName = GetUnique(ctxt.entityName + "_if");
                var elseLabel = ifName + "_else";
                var afterLabel = ifName + "_end";
                var cookedElse = MkZingBlock(elseLabel, ctxt.EmitZingSideEffects(elseStmt));
                var cookedThen = ctxt.EmitZingSideEffects(thenStmt);
                var res = MkZingSeq(MkZingIfThen(MkZingNot(condExpr), MkZingGoto(elseLabel)),
                    cookedThen,
                    MkZingGoto(afterLabel),
                    cookedElse,
                    MkZingBlock(afterLabel, ZingData.Cnst_Nil));
                return new ZingTranslationInfo(res);
            }
        }

        ZingTranslationInfo FoldSeq(FuncTerm ft, IEnumerable<ZingTranslationInfo> children, ZingFoldContext ctxt)
        {
            using (var it = children.GetEnumerator())
            {
                it.MoveNext();
                var first = it.Current;
                it.MoveNext();
                var second = it.Current;
                return new ZingTranslationInfo(MkZingSeq(first.node, ctxt.EmitZingSideEffects(second.node)));
            }
        }

        private AST<Node> MkZingStaticFunMethod(string funName, FunInfo funInfo)
        {
            List<AST<Node>> parameters = new List<AST<Node>>();
            parameters.Add(MkZingVarDecl("myHandle", Factory.Instance.MkCnst("SM_HANDLE")));
            parameters.Add(MkZingVarDecl("entryCtxt", Factory.Instance.MkCnst("Continuation")));

            List<AST<Node>> localVars = new List<AST<Node>>();
            localVars.Add(MkZingVarDecl("locals", Factory.Instance.MkCnst("PRT_VALUE_ARRAY")));
            localVars.Add(MkZingVarDecl("currentEvent", Factory.Instance.MkCnst("SM_EVENT")));
            localVars.Add(MkZingVarDecl("currentArg", PrtValue));

            var ctxt = new ZingFoldContext(this, null, funName, funInfo);
            var tuple = Factory.Instance.ToAST(funInfo.body).Compute<ZingTranslationInfo>(
                x => ZingUnfold(ctxt, x),
                (x, ch) => ZingFold(ctxt, x, ch));
            Debug.Assert(ctxt.sideEffectsStack.Count == 1);
            var funBody = ctxt.EmitZingSideEffects(tuple.node);
            ctxt.PushSideEffectStack();
            funBody = MkZingSeq(
                ctxt.EmitLabelPrelude(),
                MkZingBlock("start", funBody),
                MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Return"), MkZingIdentifier("locals"))),
                MkZingReturn(ZingData.Cnst_Nil));
            return MkZingMethodDecl(funName, MkZingVarDecls(parameters), ZingData.Cnst_Void, MkZingVarDecls(localVars.Union(ctxt.EmitLocals())), MkZingBlocks(MkZingBlock("dummy", funBody)), ZingData.Cnst_Static);
        }

        private AST<Node> MkZingFunMethod(string machineName, string funName, FunInfo funInfo)
        {
            List<AST<Node>> parameters = new List<AST<Node>>();
            parameters.Add(MkZingVarDecl("entryCtxt", Factory.Instance.MkCnst("Continuation")));

            List<AST<Node>> localVars = new List<AST<Node>>();
            localVars.Add(MkZingVarDecl("locals", Factory.Instance.MkCnst("PRT_VALUE_ARRAY")));

            var ctxt = new ZingFoldContext(this, machineName, funName, funInfo);
            var tuple = Factory.Instance.ToAST(funInfo.body).Compute<ZingTranslationInfo>(
                x => ZingUnfold(ctxt, x),
                (x, ch) => ZingFold(ctxt, x, ch));
            Debug.Assert(ctxt.sideEffectsStack.Count == 1);
            var funBody = ctxt.EmitZingSideEffects(tuple.node);
            ctxt.PushSideEffectStack();
            funBody = MkZingSeq(
                ctxt.EmitLabelPrelude(),
                MkZingBlock("start", funBody),
                MkZingCallStmt(MkZingCall(MkZingDot("entryCtxt", "Return"), MkZingIdentifier("locals"))),
                MkZingReturn(ZingData.Cnst_Nil));
            return MkZingMethodDecl(funName, MkZingVarDecls(parameters), ZingData.Cnst_Void, MkZingVarDecls(localVars.Union(ctxt.EmitLocals())), MkZingBlocks(MkZingBlock("dummy", funBody)));
        }

        private AST<Node> MkZingForeach(AST<Cnst> type, AST<Node> iter, AST<Node> collection, AST<Node> loopBody)
        {
            return AddArgs(ZingData.App_Foreach, type, iter, collection, loopBody);
        }

        private AST<Node> MkInvokeAnnounceMethod(string machineName)
        {
            List<AST<Node>> parameters = new List<AST<Node>>();
            parameters.Add(MkZingVarDecl("evt", Factory.Instance.MkCnst("SM_EVENT")));
            parameters.Add(MkZingVarDecl("arg", PrtValue));

            List<AST<Node>> localVars = new List<AST<Node>>();
            localVars.Add(MkZingVarDecl("doPop", ZingData.Cnst_Bool));

            var evt = MkZingIdentifier("evt");
            var arg = MkZingIdentifier("arg");
            var doPop = MkZingIdentifier("doPop");
            var machineHandle = GetSpecMachineName(machineName);

            List<AST<Node>> stmts = new List<AST<Node>>();
            stmts.Add(
                MkZingIfThen(
                    MkZingEq(MkZingDot("Main", machineHandle), MkZingIdentifier("null")),
                    MkZingReturn(ZingData.Cnst_Nil)));
            stmts.Add(
                MkZingIfThen(
                    MkZingNot(MkZingIn(evt, MkZingDot("Main", GetObservesSetName(machineName)))),
                    MkZingReturn(ZingData.Cnst_Nil)));
            stmts.Add(MkZingTrace("<AnnounceLog> Enqueued Event < {0}, ", MkZingDot(evt, "name")));
            stmts.Add(MkZingCallStmt(MkZingCall(MkZingDot("PRT_VALUE", "Print"), arg)));
            stmts.Add(MkZingTrace(string.Format(" > to {0} spec machine\\n", machineName)));

            stmts.Add(MkZingAssign(MkZingDot("Main", machineHandle, "myHandle", "currentEvent"), MkZingIdentifier("evt")));
            stmts.Add(MkZingAssign(MkZingDot("Main", machineHandle, "myHandle", "currentArg"), MkZingIdentifier("arg")));
            stmts.Add(MkZingAssign(doPop, MkZingCall(MkZingDot("Main", machineHandle, "RunHelper"), ZingData.Cnst_False)));
            stmts.Add(MkZingIfThen(doPop,
                         MkZingSeq(MkZingTrace(string.Format("<StateLog> Unhandled event exception by machine {0}-{{0}}\\n", machineName), MkZingDot("Main", machineHandle, "myHandle", "instance")),          
                                   MkZingAssert(ZingData.Cnst_False))));

            AST<Node> body = MkZingBlock("dummy", MkZingSeq(stmts));
            return MkZingMethodDecl(string.Format("InvokeMachine_{0}", machineName), MkZingVarDecls(parameters), ZingData.Cnst_Void, MkZingVarDecls(localVars), MkZingBlocks(body), ZingData.Cnst_Static);
        }

        AST<Node> MkInitializers(string machineName, string obj)
        {
            List<AST<Node>> initializers = new List<AST<Node>>();
            var machineInfo = allMachines[machineName];
            foreach (string varName in machineInfo.localVariableToVarInfo.Keys)
            {
                var t = machineInfo.localVariableToVarInfo[varName].type;
                initializers.Add(MkZingAssign(MkZingDot(obj, varName), MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(t))));
            }
            return MkZingSeq(initializers);
        }

        private AST<Node> MkCreateSpecMachineMethod(string machineName)
        {
            var objectName = string.Format("o_{0}", machineName);
            var localVars = new List<AST<Node>>();
            localVars.Add(MkZingVarDecl(objectName, Factory.Instance.MkCnst(ZingMachineClassName(machineName))));
            localVars.Add(MkZingVarDecl("doPop", ZingData.Cnst_Bool));

            var machineInfo = allMachines[machineName];

            AST<Node> body = ZingData.Cnst_Nil;
            
            if (machineInfo.specType != SpecType.SAFETY)
            {
                List<AST<Node>> stmts = new List<AST<Node>>();
                stmts.Add(MkZingIfThen(MkZingNeq(MkZingDot("FairCycle", "gate"), MkZingDot("GateStatus", "Init")), MkZingReturn(ZingData.Cnst_Nil)));
                if (machineInfo.specType == SpecType.FINALLY)
                {
                    stmts.Add(MkZingAssign(MkZingDot("FairCycle", "gate"), MkZingDot("GateStatus", "Closed")));
                }
                else
                {
                    stmts.Add(MkZingAssign(MkZingDot("FairCycle", "gate"), MkZingDot("GateStatus", "Selected")));
                }
                body = MkZingSeq(stmts);
            }

            var doPop = MkZingIdentifier("doPop");
            var machineHandle = MkZingDot("Main", GetSpecMachineName(machineName));

            //Add the liveness instrumentation if liveness sampling 
            if(compiler.Options.liveness == LivenessOption.Sampling)
            {
                body = MkZingSeq(body,
                    MkZingCallStmt(MkZingCall(MkZingIdentifier("invokescheduler"), Factory.Instance.MkCnst("\"mapmonitor\""), Factory.Instance.MkCnst(string.Format("\"{0}\"", machineName)))));
            }

            body = MkZingSeq(body,
                    MkZingAssign(MkZingIdentifier(objectName), MkZingNew(Factory.Instance.MkCnst(ZingMachineClassName(machineName)), ZingData.Cnst_Nil)),
                    MkInitializers(machineName, objectName),
                    MkZingAssign(MkZingDot(objectName, "myHandle"),
                                 MkZingCall(MkZingDot("SM_HANDLE", "Construct"), MkZingDot("Machine", string.Format("_{0}", machineName)), Factory.Instance.MkCnst(0), Factory.Instance.MkCnst(0))),
                    MkZingTrace(string.Format("<CreateLog> Created spec {0}\\n", machineName)),
                    MkZingAssign(MkZingDot(objectName, "myHandle", "currentArg"), MkZingCall(PrtMkDefaultValue, typeContext.PTypeToZingExpr(PTypeNull.Node))),
                    MkZingCallStmt(MkZingCall(MkZingDot(objectName, "myHandle", "Push"))),
                    MkZingAssign(MkZingDot(objectName, "myHandle", "stack", "state"), MkZingState(machineInfo.initStateName)),
                    MkZingAssign(machineHandle, MkZingIdentifier(objectName)),
                    MkZingAssign(doPop, MkZingCall(MkZingDot(objectName, "RunHelper"), ZingData.Cnst_True)),
                    MkZingIfThen(doPop,
                                 MkZingSeq(MkZingTrace(string.Format("<StateLog> Unhandled event exception by spec {0}\\n", machineName)),
                                           MkZingAssert(ZingData.Cnst_False)))
                    );
            body = MkZingBlock("dummy", body);

            return MkZingMethodDecl(string.Format("CreateMachine_{0}", machineName), ZingData.Cnst_Nil, ZingData.Cnst_Void, MkZingVarDecls(localVars), MkZingBlocks(body), ZingData.Cnst_Static);
        }

        private AST<Node> MkCreateMachineMethod(string machineName)
        {
            var objectName = string.Format("o_{0}", machineName);
            var parameters = new List<AST<Node>>();
            parameters.Add(MkZingVarDecl("arg", PrtValue));
            var localVars = new List<AST<Node>>();
            localVars.Add(MkZingVarDecl(objectName, Factory.Instance.MkCnst(ZingMachineClassName(machineName))));
            localVars.Add(MkZingVarDecl("fairScheduler", Factory.Instance.MkCnst("FairScheduler")));
            localVars.Add(MkZingVarDecl("fairChoice", Factory.Instance.MkCnst("FairChoice")));

            var machineInstance = MkZingIdentifier(string.Format("{0}_instance", machineName));
            var body = MkZingSeq(
                    MkZingAssign(MkZingIdentifier(objectName), MkZingNew(Factory.Instance.MkCnst(ZingMachineClassName(machineName)), ZingData.Cnst_Nil)),
                    MkInitializers(machineName, objectName),
                    MkZingAssign(MkZingDot(objectName, "myHandle"),
                                 MkZingCall(MkZingDot("SM_HANDLE", "Construct"), MkZingDot("Machine", string.Format("_{0}", machineName)), machineInstance, Factory.Instance.MkCnst(allMachines[machineName].maxQueueSize))),
                    MkZingAssign(MkZingDot("SM_HANDLE", "enabled"), MkZingAdd(MkZingDot("SM_HANDLE", "enabled"), MkZingDot(objectName, "myHandle"))),
                    MkZingTrace(string.Format("<CreateLog> Created Machine {0}-{{0}}\\n", machineName), machineInstance),
                    MkZingAssign(MkZingDot(objectName, "myHandle", "currentArg"), MkZingIdentifier("arg")),
                    MkZingAssign(machineInstance, MkZingApply(ZingData.Cnst_Add, machineInstance, Factory.Instance.MkCnst(1)))
                    );

            if (compiler.Options.liveness == LivenessOption.Standard)
            {
                body = MkZingSeq(body,
                                 MkZingAssign(MkZingIdentifier("fairScheduler"), MkZingNew(Factory.Instance.MkCnst("FairScheduler"), ZingData.Cnst_Nil)),
                                 MkZingCallStmt(MkZingCall(MkZingDot("FairScheduler", "Init"), MkZingIdentifier("fairScheduler"), MkZingDot(objectName, "myHandle"))));
                foreach (var funName in allMachines[machineName].funNameToFunInfo.Keys)
                {
                    var funInfo = allMachines[machineName].funNameToFunInfo[funName];
                    for (int i = 0; i < funInfo.numFairChoices; i++)
                    {
                        body = MkZingSeq(body,
                                         MkZingAssign(MkZingIdentifier("fairChoice"), MkZingNew(Factory.Instance.MkCnst("FairChoice"), ZingData.Cnst_Nil)),
                                         MkZingCallStmt(MkZingCall(MkZingDot("FairChoice", "Init"), MkZingIdentifier("fairChoice"))),
                                         MkZingAssign(MkZingDot(objectName, GetFairChoice(funName, i)), MkZingIdentifier("fairChoice")));
                    }
                }
            }

            body = MkZingSeq(
                body,
                MkZingCallStmt(MkZingCall(MkZingDot(objectName, "Start")), ZingData.Cnst_Async),
                MkZingCallStmt(MkZingCall(MkZingIdentifier("invokescheduler"), Factory.Instance.MkCnst("\"map\""), MkZingDot(objectName, "myHandle", "machineId"))),
                MkZingReturn(MkZingDot(objectName, "myHandle"))
                );
            body = MkZingBlock("dummy", body);

            return MkZingMethodDecl(string.Format("CreateMachine_{0}", machineName), MkZingVarDecls(parameters), Factory.Instance.MkCnst("SM_HANDLE"), MkZingVarDecls(localVars), MkZingBlocks(body), ZingData.Cnst_Static);
        }

        private FuncTerm LookupType(ZingFoldContext ctxt, Node node)
        {
            return ctxt.entityInfo.typeInfo[Factory.Instance.ToAST(node)];
        }

        void GenerateTypeInfo(AST<Model> model)
        {
            var terms = GetBin(factBins, "TypeOf");
            foreach (var term in terms)
            {
                using (var it = term.Node.Args.GetEnumerator())
                {
                    it.MoveNext();
                    var typingContextAlias = Factory.Instance.ToAST(it.Current);
                    FuncTerm typingContext = aliasToTerm[typingContextAlias];
                    it.MoveNext();
                    var expr = Factory.Instance.ToAST(it.Current);
                    it.MoveNext();
                    var type = it.Current as FuncTerm;

                    string typingContextKind = ((Id)typingContext.Function).Name;
                    if (typingContextKind == "FunDecl")
                    {
                        string ownerName = GetOwnerName(typingContext, 1);
                        string funName = GetName(typingContext, 0);
                        if (ownerName == null)
                        {
                            allGlobalFuns[funName].typeInfo[expr] = type;
                        }
                        else
                        {
                            allMachines[ownerName].funNameToFunInfo[funName].typeInfo[expr] = type;
                        }
                    }
                    else
                    {
                        // typingContextKind == "AnonFunDecl"
                        string ownerName = GetOwnerName(typingContext, 0);
                        string funName = anonFunToName[typingContextAlias];
                        if (ownerName == null)
                        {
                            allGlobalFuns[funName].typeInfo[expr] = type;
                        }
                        else
                        {
                            allMachines[ownerName].funNameToFunInfo[funName].typeInfo[expr] = type;
                        }
                    }
                }
            }

            terms = GetBin(factBins, "TranslatedTypeExpr");
            foreach (var term in terms)
            {
                using (var it = term.Node.Args.GetEnumerator())
                {
                    it.MoveNext();
                    var eType = (FuncTerm)it.Current;
                    typeContext.PTypeToZingExpr(eType);
                }
            }

            terms = GetBin(factBins, "TypeExpansion");
            foreach (var term in terms)
            {
                using (var it = term.Node.Args.GetEnumerator())
                {
                    it.MoveNext();
                    var type = (FuncTerm)it.Current;
                    it.MoveNext();
                    var eType = (FuncTerm)it.Current;
                    typeContext.AddOriginalType(type, eType);
                }
            }
        }

        TypeTranslationContext typeContext;

        #endregion
    }
}
