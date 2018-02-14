using System.Collections.Generic;
using System.Diagnostics;
using Antlr4.Runtime;
using Microsoft.Pc.Antlr;
using Microsoft.Pc.TypeChecker.AST.Declarations;

namespace Microsoft.Pc.TypeChecker.AST.States
{
    public class StateGroup : IStateContainer, IHasScope, IPDecl
    {
        private readonly Dictionary<string, StateGroup> groups = new Dictionary<string, StateGroup>();
        private readonly Dictionary<string, State> states = new Dictionary<string, State>();

        public StateGroup(string name, ParserRuleContext sourceNode)
        {
            Debug.Assert(sourceNode is PParser.GroupContext);
            Name = name;
            SourceLocation = sourceNode;
        }

        public Machine OwningMachine { get; set; }
        public Scope Scope { get; set; }
        public ParserRuleContext SourceLocation { get; }

        public string Name { get; }

        public IStateContainer ParentStateContainer { get; set; }
        public IEnumerable<State> States => states.Values;
        public IEnumerable<StateGroup> Groups => groups.Values;

        public void AddState(State state)
        {
            Debug.Assert(state.Container == null);
            state.Container = this;
            states.Add(state.Name, state);
        }

        public void AddGroup(StateGroup group)
        {
            Debug.Assert(group.ParentStateContainer == null);
            group.ParentStateContainer = this;
            groups.Add(group.Name, group);
        }

        public IStateContainer GetGroup(string groupName)
        {
            return groups.TryGetValue(groupName, out StateGroup group) ? group : null;
        }

        public State GetState(string stateName)
        {
            return states.TryGetValue(stateName, out State state) ? state : null;
        }
    }
}
