module ALPHA2.Analyzer where

import ALPHA2.Ast
import ALPHA2.Grammar
import ALPHA2.Header
import ALPHA2.PlanHolLexer
import ALPHA2.PlanHolParser
import Z.Utils

type AnalyzerOuput = Either TermRep [DeclRep]

runAnalyzer :: String -> Either ErrMsg AnalyzerOuput
runAnalyzer src0
    = case runHolLexer src0 of
        Left (row, col) -> Left ("*** lexing error at { row = " ++ showsPrec 0 row (", col = " ++ showsPrec 0 col " }."))
        Right src1 -> case runHolParser src1 of
            Left Nothing -> Left ("*** parsing error at EOF.")
            Left (Just token) -> case getSLoc token of
                SLoc (row1, col1) (row2, col2) -> Left ("*** parsing error at { row = " ++ showsPrec 0 row1 (", col = " ++ showsPrec 0 col1 " }."))
            Right output -> Right output
