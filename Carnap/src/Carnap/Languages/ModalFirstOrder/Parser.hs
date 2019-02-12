{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses#-}
module Carnap.Languages.ModalFirstOrder.Parser ( hardegreeMPLFormulaPreParser, hardegreeMPLFormulaParser) where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes (Schematizable)
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PureFirstOrder.Syntax (foVar)
import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.ModalFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, StandardVarLanguage, ModalLanguage, PrismModality, BooleanConstLanguage, IndexingLang(..), IndexConsLang(..), IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Control.Monad.Identity

data ModalFirstOrderParserOptions lex u m = ModalFirstOrderParserOptions 
                                          { atomicSentenceParser :: ParsecT String u m (FixLang lex (Term Int)) 
                                             -> ParsecT String u m (FixLang lex (Form (World -> Bool)))
                                          , quantifiedSentenceParser' :: ParsecT String u m (FixLang lex (Term Int)) 
                                             -> ParsecT String u m (FixLang lex (Form (World -> Bool)))
                                             -> ParsecT String u m (FixLang lex (Form (World -> Bool)))
                                          , freeVarParser  :: ParsecT String u m (FixLang lex (Term Int)) 
                                          , constantParser :: Maybe (ParsecT String u m (FixLang lex (Term Int)))
                                          , functionParser :: Maybe (ParsecT String u m (FixLang lex (Term Int)) 
                                             -> ParsecT String u m (FixLang lex (Term Int)))
                                          , hasBooleanConstants :: Bool
                                          }

hardegreeMPLParserOptions :: ModalFirstOrderParserOptions IndexedModalFirstOrderLex u Identity
hardegreeMPLParserOptions = ModalFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "tuvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrs")
                         , functionParser = Nothing
                         , hasBooleanConstants = True
                         }

coreSubformulaParser :: ( BoundVars lex
                        , BooleanLanguage (FixLang lex (Form (World -> Bool)))
                        , ModalLanguage (FixLang lex (Form (World -> Bool)))
                        , BooleanConstLanguage (FixLang lex (Form (World -> Bool)))
                        , QuantLanguage (FixLang lex (Form (World -> Bool))) (FixLang lex (Term Int))
                        ) =>
    Parsec String u (FixLang lex (Form (World -> Bool))) -> ModalFirstOrderParserOptions lex u Identity
        -> Parsec String u (FixLang lex (Form (World -> Bool)))
coreSubformulaParser fp opts = (parenParser fp <* spaces)
                             <|> try (unaryOpParser [parseNeg, parsePos, parseNec] (coreSubformulaParser fp opts))
                             <|> try ((quantifiedSentenceParser' opts) vparser (coreSubformulaParser fp opts) <* spaces)
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
          tparser = try (fparser tparser) <|> cparser <|> vparser

parserFromOptions opts = buildExpressionParser opTable subformulaParser
    where subformulaParser = coreSubformulaParser (parserFromOptions opts) opts 

hardegreeMPLFormulaParser :: Parsec String u (IndexedModalFirstOrderLanguage (Form Bool))
hardegreeMPLFormulaParser = hardegreeMPLFormulaPreParser >>= indexIt
    where indexIt :: IndexedModalFirstOrderLanguage (Form (World -> Bool)) -> Parsec String u (IndexedModalFirstOrderLanguage (Form Bool))
          indexIt f = do char '/'
                         (w:ws)<- sepBy1 parseWorld (char '-')
                         let idx = foldl indexcons w ws
                         return (f `atWorld` idx)

hardegreeMPLFormulaPreParser :: Parsec String u (IndexedModalFirstOrderLanguage (Form (World -> Bool)))
hardegreeMPLFormulaPreParser = buildExpressionParser opTable subFormulaParser
          where subFormulaParser = coreSubformulaParser hardegreeMPLFormulaPreParser hardegreeMPLParserOptions

instance ParsableLex (Form (World -> Bool)) IndexedModalFirstOrderLex where
        langParser = hardegreeMPLFormulaPreParser

instance ParsableLex (Form Bool) IndexedModalFirstOrderLex where
        langParser = hardegreeMPLFormulaParser

parseFreeVar :: StandardVarLanguage ((ModalFirstOrderLanguageOverWith b a (Term Int))) => String -> Parsec String u (ModalFirstOrderLanguageOverWith b a (Term Int))
parseFreeVar s = choice [try $ do _ <- string "x_"
                                  dig <- many1 digit
                                  return $ foVar $ "x_" ++ dig
                        ,      do c <- oneOf s
                                  return $ foVar [c]
                        ]

opTable :: ( BooleanLanguage (ModalFirstOrderLanguageOverWith b a (Form (World -> Bool)))
           , PrismModality (ModalFirstOrderLexOverWith b a) (World -> Bool)
           , Monad m)
    => [[Operator String u m (ModalFirstOrderLanguageOverWith b a (Form (World -> Bool)))]]
opTable = [[ Prefix (try parseNeg), Prefix (try parseNec), Prefix (try parsePos)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

parseWorld :: (IndexingLang lex (Term World) (Form c) (Form b), Monad m) => ParsecT String u m (FixLang lex (Term World))
parseWorld = do digits <- many1 digit
                return $ world (read digits)
