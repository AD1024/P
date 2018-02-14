using Antlr4.Runtime;
using Microsoft.Pc.TypeChecker.Types;

namespace Microsoft.Pc.TypeChecker.AST.Expressions
{
    public class CoerceExpr : IPExpr
    {
        public CoerceExpr(ParserRuleContext sourceLocation, IPExpr subExpr, PLanguageType newType)
        {
            SourceLocation = sourceLocation;
            SubExpr = subExpr;
            NewType = newType;
        }

        public IPExpr SubExpr { get; }
        public PLanguageType NewType { get; }

        public PLanguageType Type => NewType;
        public ParserRuleContext SourceLocation { get; }
    }
}
