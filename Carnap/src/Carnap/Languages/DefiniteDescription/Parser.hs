{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses#-}
module Carnap.Languages.DefiniteDescription.Parser where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes (Schematizable)
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.DefiniteDescription.Syntax
import Carnap.Languages.PurePropositional.Parser (gamutOpTable, standardOpTable)
import Carnap.Languages.PureFirstOrder.Parser hiding (parserFromOptions)
import Carnap.Languages.PurePropositional.Util (isBoolean)
import Carnap.Languages.PureFirstOrder.Util (isOpenFormula)
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, BooleanConstLanguage, StandardVarLanguage, DefinDescLanguage(..), IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Control.Monad.Identity

coreSubformulaParser :: ( BoundVars lex
                        , BooleanLanguage (FixLang lex (Form Bool))
                        , BooleanConstLanguage (FixLang lex (Form Bool))
                        , DefinDescLanguage (FixLang lex (Form Bool)) (FixLang lex (Term Int))
                        , QuantLanguage (FixLang lex (Form Bool)) (FixLang lex (Term Int))
                        , CopulaSchema (FixLang lex)
                        , Schematizable (lex (FixLang lex))
                        ) =>
    (FirstOrderParserOptions lex u Identity -> Parsec String u (FixLang lex (Form Bool))) -> FirstOrderParserOptions lex u Identity
        -> Parsec String u (FixLang lex (Form Bool))
coreSubformulaParser fp opts = try (parenRecur opts opts fp <* spaces)
                             <|> try (unaryOpParser [parseNeg] (coreSubformulaParser fp opts))
                             <|> try (quantifiedSentenceParser' opts vparser (coreSubformulaParser fp opts) <* spaces)
                             <|> (atomicSentenceParser opts (tparser (coreSubformulaParser fp opts)) <* spaces)
                             <|> if hasBooleanConstants opts then try (booleanConstParser <* spaces) else parserZero
    where cparser = case constantParser opts of Just c -> c
                                                Nothing -> mzero
          --Function symbols, if there are any
          fparser = case functionParser opts of Just f -> f
                                                Nothing -> const mzero
          --Free variables
          vparser = freeVarParser opts 
          --Terms (we pass in recur, rather than calling
          --coreSubformulaParser to make sure that we discharge class
          --constraints using the given constraints)
          tparser recur = try (descriptionParser recur) <|> try (fparser (tparser recur)) <|> try cparser <|> vparser 
          descriptionParser recur = do s <- oneOf "iι℩"
                                       v <- vparser
                                       f <- recur
                                       let bf x = subBoundVar v x f
                                       return (ddesc (show v) bf)

gamutNDDescParserOptions :: FirstOrderParserOptions FregeanDescLex u Identity
gamutNDDescParserOptions =  FirstOrderParserOptions { atomicSentenceParser = 
                                                         \x -> try (parsePredicateSymbolNoParen ['A' .. 'Z'] x)
                                                               <|> equalsParser x
                                                    , opTable = gamutOpTable
                                                    , constantParser = Just (parseConstant "abcdefghijklmnopqr")
                                                    , functionParser = Just (\x -> parseFunctionSymbol "abcdefghijklmnopqrst" x)
                                                    , parenRecur = magnusDispatch
                                                    , freeVarParser = parseFreeVar "stuvwxyz"
                                                    , quantifiedSentenceParser' = quantifiedSentenceParser
                                                    , finalValidation = \x -> if isOpenFormula x then unexpected "unbound variable" else return ()
                                                    , hasBooleanConstants = True
                                                    }
    where magnusDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= boolean
          boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

standardDescParserOptions :: FirstOrderParserOptions FregeanDescLex u Identity
standardDescParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbol "FGHIJKLMNO" x
                                                        <|> try (parseSchematicPredicateSymbol x)
                                                        <|> try schemevarParser
                                                        <|> sentenceLetterParser "PQRSTUVW"
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde" <|> parseSchematicConstant) 
                         , functionParser = Just (\x -> parseFunctionSymbol "fgh" x <|> parseSchematicFunctionSymbol x)
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

instance ParsableLex (Form Bool) FregeanDescLex where
        langParser = descFormulaParser

parserFromOptions opts = do f <- buildExpressionParser (opTable opts) subformulaParser 
                            finalValidation opts f
                            return f
    where subformulaParser = coreSubformulaParser parserFromOptions (opts {finalValidation = const (return ())})

gamutNDDescFormulaParser :: Parsec String u (FregeanDescLang (Form Bool))
gamutNDDescFormulaParser = parserFromOptions gamutNDDescParserOptions

descFormulaParser :: Parsec String u (FregeanDescLang (Form Bool))
descFormulaParser = parserFromOptions standardDescParserOptions
