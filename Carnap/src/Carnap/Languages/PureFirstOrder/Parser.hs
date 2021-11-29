{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses#-}
module Carnap.Languages.PureFirstOrder.Parser 
( folFormulaParser, folFormulaParserRelaxed, mfolFormulaParser
, arthurFOLFormulaParser, magnusFOLFormulaParser, gallowPLFormulaParser, thomasBolducAndZachFOLFormulaParser
, gamutNDFormulaParser, thomasBolducAndZachFOL2019FormulaParser, thomasBolducAndZachFOL2019FormulaParserStrict
, hardegreePLFormulaParser, belotPDFormulaParser, belotPDEFormulaParser
, bergmannMoorAndNelsonPDFormulaParser, bergmannMoorAndNelsonPDEFormulaParser
, gregoryPDFormulaParser, goldfarbNDFormulaParser, tomassiQLFormulaParser, hurleyPLFormulaParser
, hausmanPLFormulaParser, cortensQLFormulaParser, lemmonQuantFormulaParser, landeQuantFormulaParser
, FirstOrderParserOptions(..), parserFromOptions, parseFreeVar, howardSnyderPLFormulaParser) where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes (Schematizable)
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, BooleanConstLanguage, StandardVarLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (isBoolean, isBooleanBinary)
import Carnap.Languages.PureFirstOrder.Util (isOpenFormula)
import Text.Parsec
import Text.Parsec.Expr
import Control.Monad.Identity

data FirstOrderParserOptions lex u m = FirstOrderParserOptions 
                                         { atomicSentenceParser :: ParsecT String u m (FixLang lex (Term Int)) 
                                            -> ParsecT String u m (FixLang lex (Form Bool))
                                         , quantifiedSentenceParser' :: ParsecT String u m (FixLang lex (Term Int)) 
                                            -> ParsecT String u m (FixLang lex (Form Bool))
                                            -> ParsecT String u m (FixLang lex (Form Bool))
                                         , freeVarParser  :: ParsecT String u m (FixLang lex (Term Int)) 
                                         , constantParser :: Maybe (ParsecT String u m (FixLang lex (Term Int)))
                                         , functionParser :: Maybe (ParsecT String u m (FixLang lex (Term Int)) 
                                            -> ParsecT String u m (FixLang lex (Term Int)))
                                         , hasBooleanConstants :: Bool
                                         , finalValidation :: FixLang lex (Form Bool) -> ParsecT String u m ()
                                         , parenRecur :: FirstOrderParserOptions lex u m
                                            -> (FirstOrderParserOptions lex u m -> ParsecT String u m (FixLang lex (Form Bool))) 
                                            -> ParsecT String u m (FixLang lex (Form Bool))
                                         , opTable :: [[Operator String u m (FixLang lex (Form Bool))]]
                                         }

standardFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
standardFOLParserOptions = FirstOrderParserOptions 
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

--These should mirror the way that show values look, since this will be
--used in the read instance
maximalFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
maximalFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbol "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> try (parseSchematicPredicateSymbol x)
                                                        <|> try schemevarParser
                                                        <|> sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstu" <|> parseSchematicConstant) 
                         , functionParser = Just (\x -> parseFunctionSymbol "abcdefghijklmnopqrstuvwxyz" x <|> parseSchematicFunctionSymbol x)
                         , hasBooleanConstants = True
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

simplePolyadicFOLParserOptions :: FirstOrderParserOptions PureLexiconPFOL u Identity
simplePolyadicFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbol "FGHIJKLMNO" x)
                                                        <|> sentenceLetterParser "PQRSTUVW"
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

simpleMonadicFOLParserOptions :: FirstOrderParserOptions PureLexiconMFOL u Identity
simpleMonadicFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (monadicSentenceParser x) <|> sentenceLetterParser "PQRSTUVW"
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

magnusFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
magnusFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "xyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvw")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = magnusDispatch
                         , opTable = standardOpTable
                         , finalValidation = \x -> if isOpenFormula x then unexpected "unbound variable" else return ()
                         }
    where magnusDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= boolean
          boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

arthurFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
arthurFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "xyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvw")
                         , functionParser = Nothing
                         , hasBooleanConstants = True
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTableStrict
                         , finalValidation = const (pure ())
                         }

thomasBolducAndZachFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
thomasBolducAndZachFOLParserOptions = magnusFOLParserOptions { hasBooleanConstants = True
                                                             , freeVarParser = parseFreeVar "stuvwxyz"
                                                             , constantParser = Just (parseConstant "abcdefghijklmnopqr")
                                                             , parenRecur = zachDispatch
                                                             , atomicSentenceParser = 
                                                                    \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                                          <|> try (sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
                                                                          <|> equalsParser x
                                                             , opTable = calgaryOpTable
                                                             , finalValidation = \x -> if isOpenFormula x then unexpected "unbound variable" else return ()
                                                             }
    where zachDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= boolean
          boolean a = if isBooleanBinary a then return a else unexpected "atomic, negated, or quantified sentence wrapped in parentheses"

thomasBolducAndZachFOL2019ParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
thomasBolducAndZachFOL2019ParserOptions = thomasBolducAndZachFOLParserOptions 
                         { quantifiedSentenceParser' = lplQuantifiedSentenceParser
                         , functionParser = Just (\x -> parseFunctionSymbol "abcdefghijklmnopqrst" x)
                         , atomicSentenceParser = 
                                \x -> try (parsePredicateSymbol "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x) 
                                      <|> try (sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
                                      <|> try (equalsParser x)
                                      <|> inequalityParser x
                         , opTable = calgary2019OpTable
                         }

thomasBolducAndZachFOL2019ParserOptionsStrict :: FirstOrderParserOptions PureLexiconFOL u Identity
thomasBolducAndZachFOL2019ParserOptionsStrict = thomasBolducAndZachFOL2019ParserOptions { opTable = calgaryOpTable}

gallowPLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
gallowPLParserOptions = magnusFOLParserOptions { freeVarParser = parseFreeVar "wxyz"
                                             , constantParser = Just (parseConstant "abcdefghijklmnopqrstuv")
                                             , atomicSentenceParser = 
                                                    \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                          <|> try (sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
                                             , opTable = calgaryOpTable
                                             , finalValidation = \x -> if isOpenFormula x then unexpected "unbound variable" else return ()
                                             }

gamutNDParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
gamutNDParserOptions = thomasBolducAndZachFOLParserOptions { atomicSentenceParser = 
                                                                    \x -> try (parsePredicateSymbolNoParen ['A' .. 'Z'] x)
                                                                          <|> equalsParser x
                                                           , opTable = gamutOpTable
                                                           }

bergmanMoorAndNelsonPDParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
bergmanMoorAndNelsonPDParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 
                         , quantifiedSentenceParser' = altAltQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "wxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuv")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith -> parenParser (recurWith opt) >>= boolean
                         , opTable = standardOpTable
                         , finalValidation = \x -> if isOpenFormula x then unexpected "unbound variable" else return ()
                         }
          where boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

belotPDParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
belotPDParserOptions = bergmanMoorAndNelsonPDParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen ['A' .. 'Z'] x)
                                                        <|> lowerCaseSentenceLetterParser "pqr"
                         , freeVarParser = parseFreeVar "xyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvo")
                         }

gregoryPDParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
gregoryPDParserOptions = bergmanMoorAndNelsonPDParserOptions 
                         { freeVarParser = parseFreeVar "vwxyz"
                         , atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> try (sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
                                                        <|> try (equalsParser x)
                                                        <|> inequalityParser x
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstu")
                         , parenRecur = gregoryDispatch
                         , opTable = standardOpTableStrict
                         }
          where gregoryDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= boolean
                boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

bergmannMoorAndNelsonPDEParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
bergmannMoorAndNelsonPDEParserOptions = bergmanMoorAndNelsonPDParserOptions 
                        { functionParser = Just (\x -> parseFunctionSymbol "abcdefghijklmnopqrst" x)
                        , atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> try (sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
                                                        <|> equalsParser x
                        }

belotPDEParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
belotPDEParserOptions = bergmanMoorAndNelsonPDParserOptions 
                        { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen ['A' .. 'Z'] x)
                                                       <|> try (equalsParser x)
                                                       <|> lowerCaseSentenceLetterParser "pqr"
                        , freeVarParser = parseFreeVar "xyz"
                        , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvo")
                        }
                        
hardegreePLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
hardegreePLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = parsePredicateSymbolNoParen ['A' .. 'Z']
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar ['t' .. 'z']
                         , constantParser = Just (parseConstant ['a' .. 's'])
                         , functionParser = Nothing
                         , hasBooleanConstants = True
                         , parenRecur = \opt recurWith -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

goldfarbNDParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
goldfarbNDParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = parsePredicateSymbolNoParen ['A' .. 'Z']
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar ['a' .. 'z']
                         , constantParser = Nothing
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

hurleyPLOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
hurleyPLOptions = FirstOrderParserOptions
                         { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = altQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "xyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvw")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = hurleyDispatch
                         , opTable = hausmanOpTable
                         , finalValidation = const (pure ())
                         }
    where hurleyDispatch opt rw = (wrappedWith '{' '}' (rw opt) <|> wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= boolean
          boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

hausmanPLOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
hausmanPLOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = altQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "uvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrst")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = hausmanDispatch
                         , opTable = hausmanOpTable
                         , finalValidation = const (pure ())
                         }
    where hausmanDispatch opt rw = (wrappedWith '{' '}' (rw opt) <|> wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= boolean
          boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

cortensQLOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
cortensQLOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "uvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrst")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = cortensParens
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }
    where cortensParens opt recurWith = wrappedWith '(' ')' (recurWith opt) >>= boolean
          boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

tomassiQLOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
tomassiQLOptions = FirstOrderParserOptions
                    { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                   <|> parsePredicateSymbol "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                                                   <|> equalsParser x
                    , quantifiedSentenceParser' = quantifiedSentenceParser
                    , freeVarParser = parseFreeVar "uvwxyz"
                    , constantParser = Just (parseConstant "abcdefghijklmnopqrst")
                    , functionParser = Nothing
                    , hasBooleanConstants = False
                    , parenRecur = tomassiDispatch
                    , opTable = standardOpTable
                    , finalValidation = const (pure ())
                    }
    where tomassiDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

lemmonQuantOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
lemmonQuantOptions = FirstOrderParserOptions
                         { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> try (parenParser (equalsParser x ))
                                                        <|> sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = altQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "xyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvw")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt) >>= boolean
                         , opTable = standardOpTable
                         , finalValidation = \x -> if isOpenFormula x then unexpected "unbound variable" else return ()
                         }
    where boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

landeQuantOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
landeQuantOptions = lemmonQuantOptions
                         { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> try (sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" )
                                                        <|> try (parenParser (equalsParser x))
                                                        <|> try (parenParser (inequalityParser x))
                                                        <|> try (equalsParser x)
                                                        <|> inequalityParser x
                         , quantifiedSentenceParser' = altAltQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "uvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrst")
                         , finalValidation = const (return ())
                         }

howardSnyderPLOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
howardSnyderPLOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = altQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "uvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrst")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = hsDispatch
                         , opTable = howardSnyderOpTable
                         , finalValidation = const (pure ())
                         }
    where hsDispatch opt rw = (wrappedWith '{' '}' (rw opt) <|> wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= boolean
          boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"

coreSubformulaParser :: ( BoundVars lex
                        , BooleanLanguage (FixLang lex (Form Bool))
                        , BooleanConstLanguage (FixLang lex (Form Bool))
                        , QuantLanguage (FixLang lex (Form Bool)) (FixLang lex (Term Int))
                        ) =>
    (FirstOrderParserOptions lex u Identity -> Parsec String u (FixLang lex (Form Bool))) -> FirstOrderParserOptions lex u Identity
        -> Parsec String u (FixLang lex (Form Bool))
coreSubformulaParser fp opts = try (parenRecur opts opts fp <* spaces)
                             <|> try (unaryOpParser [parseNeg] (coreSubformulaParser fp opts))
                             <|> try (quantifiedSentenceParser' opts vparser (coreSubformulaParser fp opts) <* spaces)
                             <|> (atomicSentenceParser opts tparser <* spaces)
                             <|> if hasBooleanConstants opts then try (booleanConstParser <* spaces) else parserZero
    where cparser = case constantParser opts of Just c -> c
                                                Nothing -> mzero
          --Function symbols, if there are any
          fparser = case functionParser opts of Just f -> f
                                                Nothing -> const mzero
          --Free variables
          vparser = freeVarParser opts 
          --Terms
          tparser = try (fparser tparser) <|> try cparser <|> vparser 

parserFromOptions opts = do f <- buildExpressionParser (opTable opts) subformulaParser 
                            finalValidation opts f
                            return f
    where subformulaParser = coreSubformulaParser parserFromOptions (opts {finalValidation = const (return ())})

magnusFOLFormulaParser :: Parsec String u PureFOLForm
magnusFOLFormulaParser = parserFromOptions magnusFOLParserOptions

arthurFOLFormulaParser :: Parsec String u PureFOLForm
arthurFOLFormulaParser = parserFromOptions arthurFOLParserOptions

gallowPLFormulaParser :: Parsec String u PureFOLForm
gallowPLFormulaParser = parserFromOptions gallowPLParserOptions

thomasBolducAndZachFOLFormulaParser :: Parsec String u PureFOLForm
thomasBolducAndZachFOLFormulaParser = parserFromOptions thomasBolducAndZachFOLParserOptions

thomasBolducAndZachFOL2019FormulaParserStrict :: Parsec String u PureFOLForm
thomasBolducAndZachFOL2019FormulaParserStrict = parserFromOptions thomasBolducAndZachFOL2019ParserOptionsStrict

gamutNDFormulaParser :: Parsec String u PureFOLForm
gamutNDFormulaParser = parserFromOptions gamutNDParserOptions

thomasBolducAndZachFOL2019FormulaParser :: Parsec String u PureFOLForm
thomasBolducAndZachFOL2019FormulaParser = parserFromOptions thomasBolducAndZachFOL2019ParserOptions

hardegreePLFormulaParser :: Parsec String u PureFOLForm
hardegreePLFormulaParser = parserFromOptions hardegreePLParserOptions

goldfarbNDFormulaParser:: Parsec String u PureFOLForm
goldfarbNDFormulaParser = parserFromOptions goldfarbNDParserOptions

bergmannMoorAndNelsonPDFormulaParser :: Parsec String u PureFOLForm
bergmannMoorAndNelsonPDFormulaParser = parserFromOptions bergmanMoorAndNelsonPDParserOptions

bergmannMoorAndNelsonPDEFormulaParser :: Parsec String u PureFOLForm
bergmannMoorAndNelsonPDEFormulaParser = parserFromOptions bergmannMoorAndNelsonPDEParserOptions

belotPDFormulaParser :: Parsec String u PureFOLForm
belotPDFormulaParser = parserFromOptions belotPDParserOptions

belotPDEFormulaParser :: Parsec String u PureFOLForm
belotPDEFormulaParser = parserFromOptions belotPDEParserOptions

gregoryPDFormulaParser :: Parsec String u PureFOLForm
gregoryPDFormulaParser = parserFromOptions gregoryPDParserOptions

hausmanPLFormulaParser :: Parsec String u PureFOLForm
hausmanPLFormulaParser = parserFromOptions hausmanPLOptions

hurleyPLFormulaParser :: Parsec String u PureFOLForm
hurleyPLFormulaParser = parserFromOptions hurleyPLOptions

howardSnyderPLFormulaParser :: Parsec String u PureFOLForm
howardSnyderPLFormulaParser = parserFromOptions howardSnyderPLOptions

cortensQLFormulaParser :: Parsec String u PureFOLForm
cortensQLFormulaParser = parserFromOptions cortensQLOptions

tomassiQLFormulaParser :: Parsec String u PureFOLForm
tomassiQLFormulaParser = parserFromOptions tomassiQLOptions

lemmonQuantFormulaParser :: Parsec String u PureFOLForm
lemmonQuantFormulaParser = parserFromOptions lemmonQuantOptions

landeQuantFormulaParser :: Parsec String u PureFOLForm
landeQuantFormulaParser = parserFromOptions landeQuantOptions

folFormulaParser :: Parsec String u PureFOLForm
folFormulaParser = parserFromOptions standardFOLParserOptions

maxFormulaParser :: Parsec String u PureFOLForm
maxFormulaParser = parserFromOptions maximalFOLParserOptions

folFormulaParserRelaxed :: Parsec String u PureFOLForm
folFormulaParserRelaxed = parserFromOptions (standardFOLParserOptions 
    { atomicSentenceParser = \x -> (try (atomicSentenceParser standardFOLParserOptions x) <|> parsePredicateSymbolNoParen "FGHIJKLMNO" x) })

instance ParsableLex (Form Bool) PureLexiconFOL where
        langParser = folFormulaParser

--XXX: This is necessary to mirror the show instance, while still using the
--less permissive folFormulaParser as the default for most languages.
instance {-# OVERLAPPING #-} Read PureFOLForm where
    readsPrec prec input = case parse (withRemaining (spaces *> maxFormulaParser)) "" input of
            Left _ -> []
            Right result -> [result]
        where withRemaining p = (,) <$> p <*> getInput

pfolFormulaParser :: Parsec String u PurePFOLForm
pfolFormulaParser = parserFromOptions simplePolyadicFOLParserOptions

mfolFormulaParser :: Parsec String u PureMFOLForm
mfolFormulaParser = parserFromOptions simpleMonadicFOLParserOptions

parseFreeVar :: StandardVarLanguage (FixLang lex (Term Int)) => String -> Parsec String u (FixLang lex (Term Int))
parseFreeVar s = choice [try $ do c <- oneOf s
                                  char '_'
                                  dig <- many1 digit
                                  return $ foVar $ [c] ++ "_" ++ dig
                        ,      do c <- oneOf s
                                  return $ foVar [c]
                        ]

monadicSentenceParser :: Parsec String u PureMFOLTerm -> Parsec String u PureMFOLForm
monadicSentenceParser parseTerm = do _ <- string "P_"
                                     n <- number
                                     _ <- char '('
                                     t <- parseTerm
                                     _ <- char ')'
                                     return (PMPred n :!$: t)

