{-# LANGUAGE FlexibleContexts #-}
module Carnap.Languages.ModalPropositional.Parser
    (modalPropFormulaParser,worldTheoryPropFormulaParser, absoluteModalPropFormulaParser)
where

import Carnap.Core.Data.AbstractSyntaxDataTypes (Term, Form, FixLang)
import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, BooleanConstLanguage, ModalLanguage, IndexedPropLanguage, IndexedSchemePropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Control.Monad.Identity (Identity)
import Carnap.Core.Unification.Unification

data ModalPropositionalParserOptions lex u m = ModalPropositionalParserOptions
                                     { atomicSentenceParser :: ParsecT String u m (FixLang lex (Form (World -> Bool)))
                                     , quantifiedSentenceParser' :: Maybe (ParsecT String u m (FixLang lex (Term World)) 
                                            -> ParsecT String u m (FixLang lex (Form (World -> Bool)))
                                            -> ParsecT String u m (FixLang lex (Form (World -> Bool))))
                                     , freeVarParser :: Maybe (ParsecT String u m (FixLang lex (Term World)))
                                     , hasBooleanConstants :: Bool
                                     }

--subformulas are either
coreSubformulaParser :: ( BooleanLanguage (FixLang lex (Form (World -> Bool)))
                        , BooleanConstLanguage (FixLang lex (Form (World -> Bool)))
                        , ModalLanguage (FixLang lex (Form (World -> Bool)))
                        , IndexedPropLanguage (FixLang lex (Form (World -> Bool)))
                        , IndexedSchemePropLanguage (FixLang lex (Form (World -> Bool)))) =>
    Parsec String u (FixLang lex (Form (World -> Bool))) -> ModalPropositionalParserOptions lex u Identity
        -> Parsec String u (FixLang lex (Form (World -> Bool)))
coreSubformulaParser fp opts = 
        --formulas wrapped in parentheses
        (parenParser fp <* spaces)
        --negations of subformulas
        <|> unaryOpParser [parseNeg, parsePos, parseNec]
           (coreSubformulaParser fp opts <* spaces)
        -- maybe quantified sentences
        <|> case (quantifiedSentenceParser' opts,freeVarParser opts) of
                 (Just qparse, Just vparse) -> try $ qparse vparse (coreSubformulaParser fp opts)
                 _ -> parserZero
        --or atoms
        <|> try (sentenceLetterParser "PQRSTUVW" <* spaces)
        <|> if hasBooleanConstants opts 
                then try (booleanConstParser <* spaces) 
                else parserZero
        <|> (schemevarParser <* spaces)

simpleModalOptions :: ( BooleanLanguage (FixLang lex (Form (World -> Bool)))
                      , BooleanConstLanguage (FixLang lex (Form (World -> Bool)))
                      , ModalLanguage (FixLang lex (Form (World -> Bool)))
                      , IndexedPropLanguage (FixLang lex (Form (World -> Bool)))
                      , IndexedSchemePropLanguage (FixLang lex (Form (World -> Bool)))) =>
    ModalPropositionalParserOptions lex u Identity
simpleModalOptions = ModalPropositionalParserOptions
                   { atomicSentenceParser = sentenceLetterParser "PQRSTUVW"
                   , quantifiedSentenceParser' = Nothing
                   , freeVarParser = Nothing
                   , hasBooleanConstants = False
                   }

modalPropFormulaParser :: Parsec String u ModalForm
modalPropFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = coreSubformulaParser modalPropFormulaParser simpleModalOptions

absoluteModalPropFormulaParser :: Parsec String u AbsoluteModalForm
absoluteModalPropFormulaParser = formulaParser >>= indexIt
    where formulaParser = buildExpressionParser opTable subFormulaParser
          subFormulaParser = coreSubformulaParser formulaParser simpleModalOptions{hasBooleanConstants = True}
          indexIt :: AbsoluteModalPreForm -> Parsec String u AbsoluteModalForm
          indexIt f = do char '/'
                         w <- parseWorld <|> parseWorldVar "ijklmn"
                         return (f `atWorld` w)

worldTheoryOptions :: ModalPropositionalParserOptions WorldTheoryPropLexicon u Identity
worldTheoryOptions = simpleModalOptions
                   { quantifiedSentenceParser' = Just quantifiedSentenceParser
                   , freeVarParser = Just (parseWorldVar "ijklmn")
                   , hasBooleanConstants = True
                   }

worldTheoryPropFormulaParser :: Parsec String u WorldTheoryForm
worldTheoryPropFormulaParser = buildExpressionParser (worldTheoryOpTable worldTheoryOptions) subFormulaParser 
    where subFormulaParser = coreSubformulaParser worldTheoryPropFormulaParser worldTheoryOptions

opTable :: Monad m => [[Operator String u m (ModalPropLanguageWith a (Form (World -> Bool)))]]
opTable = [ [Prefix (try parseNeg), Prefix (try parseNec), Prefix (try parsePos)]
          , [ Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft]
          , [ Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]
          ]

worldTheoryOpTable :: Monad m => ModalPropositionalParserOptions WorldTheoryPropLexicon u m -> [[Operator String u m WorldTheoryForm]]
worldTheoryOpTable opts = [ [Prefix (try parseNeg), Prefix (try parseNec), Prefix (try parsePos)]
                          , [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft]
                          , [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]
                          , [Postfix (try $ parseWorldIndexer opts)]
                          ]

parseWorldIndexer :: Monad m => ModalPropositionalParserOptions WorldTheoryPropLexicon u m -> ParsecT String u m (WorldTheoryForm -> WorldTheoryForm)
parseWorldIndexer opts = do char '/'
                            term <- parseWorld <|> vparse
                            return (\x -> x `atWorld` term)
    where vparse = case freeVarParser opts of
                       Just vp -> vp
                       _ -> parserZero

parseWorldVar :: (IndexingLang lex unindexed indexed, Monad m) => String -> ParsecT String u m (FixLang lex (Term World))
parseWorldVar s = choice [try $ do _ <- string "i_"
                                   dig <- many1 digit
                                   return $ worldVar $ "i_" ++ dig
                         ,      do c <- oneOf s
                                   return $ worldVar [c]
                         ]

parseWorld :: (IndexingLang lex unindexed indexed, Monad m) => ParsecT String u m (FixLang lex (Term World))
parseWorld = do digits <- many1 digit
                return $ world (read digits)
