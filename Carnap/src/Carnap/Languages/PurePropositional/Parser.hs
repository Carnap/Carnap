{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Parser 
    ( purePropFormulaParser, standardLetters, standardLettersStrict, extendedLetters, landeOpts, belotOpts, hausmanOpts
    , thomasBolducZachOpts, thomasBolducZach2019Opts, hardegreeOpts, arthurOpts, standardOpTable, standardOpTableStrict
    , calgaryOpTable, calgary2019OpTable, hausmanOpTable, howardSnyderOpTable, gamutOpTable
    , gamutOpts, bonevacOpts, howardSnyderOpts, hurleyOpts, gregoryOpts, magnusOpts, extendedPropSeqParser
    , englishPropFormulaParser, englishPropFormulaParserStrict
    ) where

import Carnap.Core.Data.Types
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Util (isAtom, isBooleanBinary)
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage(..), IndexedPropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

data PurePropositionalParserOptions u m = PurePropositionalParserOptions 
                                        { atomicSentenceParser :: ParsecT String u m PureForm 
                                        , hasBooleanConstants :: Bool
                                        , opTable :: [[Operator String u m PureForm]]
                                        , parenRecur :: PurePropositionalParserOptions u m
                                            -> (PurePropositionalParserOptions u m -> ParsecT String u m PureForm) 
                                            -> ParsecT String u m PureForm
                                        }

standardLetters :: Monad m => PurePropositionalParserOptions u m
standardLetters = PurePropositionalParserOptions 
                        { atomicSentenceParser = sentenceLetterParser "PQRSTUVW" 
                        , hasBooleanConstants = False
                        , opTable = standardOpTable
                        , parenRecur = \opt recurWith -> parenParser (recurWith opt)
                        }

gamutOpts :: Monad m => PurePropositionalParserOptions u m
gamutOpts = PurePropositionalParserOptions 
                { atomicSentenceParser = lowerCaseSentenceLetterParser ['a' .. 'z']
                , hasBooleanConstants = True
                , opTable = gamutOpTable
                , parenRecur = \opt recurWith -> parenParser (recurWith opt)
                }

bonevacOpts :: Monad m => PurePropositionalParserOptions u m
bonevacOpts = PurePropositionalParserOptions 
                { atomicSentenceParser = lowerCaseSentenceLetterParser ['a' .. 'z']
                , hasBooleanConstants = False
                , opTable = gamutOpTable
                , parenRecur = \opt recurWith -> parenParser (recurWith opt)
                }

hardegreeOpts :: Monad m => PurePropositionalParserOptions u m
hardegreeOpts = extendedLetters { hasBooleanConstants = True }

arthurOpts :: Monad m => PurePropositionalParserOptions u m
arthurOpts = extendedLetters { hasBooleanConstants = True 
                             , opTable = standardOpTableStrict
                             }

extendedLetters :: Monad m => PurePropositionalParserOptions u m
extendedLetters = standardLetters { atomicSentenceParser = sentenceLetterParser ['A' .. 'Z'] }

landeOpts :: Monad m => PurePropositionalParserOptions u m
landeOpts = extendedLetters { parenRecur = landeDispatch }
    where noatoms a = if isAtom a then unexpected "atomic sentence wrapped in parentheses" else return a
          landeDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt) <|> wrappedWith '{' '}' (rw opt)) >>= noatoms

belotOpts :: Monad m => PurePropositionalParserOptions u m
belotOpts = standardLetters { atomicSentenceParser = lowerCaseSentenceLetterParser ['a' .. 'z'] }

standardLettersStrict :: Monad m => PurePropositionalParserOptions u m
standardLettersStrict = standardLetters { opTable = standardOpTableStrict }

gregoryOpts :: Monad m => PurePropositionalParserOptions u m
gregoryOpts = extendedLetters { parenRecur = gregoryDispatch
                              , opTable = standardOpTableStrict
                              }
    where noatoms a = if isAtom a then unexpected "atomic sentence wrapped in parentheses" else return a
          gregoryDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= noatoms

magnusOpts :: Monad m => PurePropositionalParserOptions u m
magnusOpts = extendedLetters { parenRecur = magnusDispatch }
    where noatoms a = if isAtom a then unexpected "atomic sentence wrapped in parentheses" else return a
          magnusDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= noatoms

thomasBolducZachOpts :: Monad m => PurePropositionalParserOptions u m
thomasBolducZachOpts = magnusOpts { hasBooleanConstants = True 
                                  , opTable = calgaryOpTable
                                  , parenRecur = zachDispatch
                                  }
    where noatoms a = if isBooleanBinary a then return a else unexpected "parentheses around an atom or negation"
          zachDispatch opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= noatoms

thomasBolducZach2019Opts :: Monad m => PurePropositionalParserOptions u m
thomasBolducZach2019Opts = thomasBolducZachOpts { opTable = calgary2019OpTable }

hurleyOpts ::  Monad m => PurePropositionalParserOptions u m
hurleyOpts = hausmanOpts

hausmanOpts ::  Monad m => PurePropositionalParserOptions u m
hausmanOpts = extendedLetters 
                { opTable = hausmanOpTable 
                , parenRecur = hausmanDispatch
                }
    where hausmanDispatch opt rw = (wrappedWith '{' '}' (rw opt) <|> wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= noatoms
          noatoms a = if isAtom a then unexpected "atomic sentence wrapped in parentheses" else return a

howardSnyderOpts ::  Monad m => PurePropositionalParserOptions u m
howardSnyderOpts = extendedLetters 
                { opTable = howardSnyderOpTable
                , parenRecur = hsDispatch
                }
    where noatoms a = if isAtom a then unexpected "atomic sentence wrapped in parentheses" else return a
          hsDispatch opt rw = (wrappedWith '{' '}' (rw opt) <|> wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt)) >>= noatoms

--this parses as much formula as it can, but is happy to return an output if the
--initial segment of a string is a formula
purePropFormulaParser :: Monad m => PurePropositionalParserOptions u m -> ParsecT String u m PureForm
purePropFormulaParser opts = buildExpressionParser (opTable opts) subFormulaParser
    --subformulas are either
    where subFormulaParser = ((parenRecur opts) opts purePropFormulaParser <* spaces) --formulas wrapped in parentheses
                          <|> unaryOpParser [parseNeg] subFormulaParser --negations or modalizations of subformulas
                          <|> try (atomicSentenceParser opts <* spaces)--or atoms
                          <|> (if hasBooleanConstants opts then try (booleanConstParser <* spaces) else parserZero)
                          <|> ((schemevarParser <* spaces) <?> "")

instance ParsableLex (Form Bool) PurePropLexicon where
        langParser = purePropFormulaParser extendedLetters { hasBooleanConstants = True }

extendedPropSeqParser = parseSeqOver (purePropFormulaParser extendedLetters)

standardOpTable :: (BooleanLanguage (FixLang lex (Form Bool)), Monad m)
    => [[Operator String u m (FixLang lex (Form Bool))]]
standardOpTable = [ [ Prefix (try parseNeg)]
                  , [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft]
                  , [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]
                  ]

standardOpTableStrict :: (BooleanLanguage (FixLang lex (Form Bool)), Monad m)
    => [[Operator String u m (FixLang lex (Form Bool))]]
standardOpTableStrict = [ [ Prefix (try parseNeg)]
                  , [ Infix (try parseOr) AssocNone, Infix (try parseAnd) AssocNone
                    , Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]
                  ]

calgaryOpTable :: (BooleanLanguage (FixLang lex (Form Bool)), Monad m)
    => [[Operator String u m (FixLang lex (Form Bool))]]
calgaryOpTable = [ [ Prefix (try parseNeg)]
                 , [ Infix (try $ parseAsOr ["\\/", "∨", "|", "or"]) AssocNone, Infix (try parseAnd) AssocNone
                   , Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]
                 ]

calgary2019OpTable :: (BooleanLanguage (FixLang lex (Form Bool)), Monad m)
    => [[Operator String u m (FixLang lex (Form Bool))]]
calgary2019OpTable = [ [ Prefix (try parseNeg)]
                 , [ Infix (try $ parseAsOr ["\\/", "∨", "|", "or"]) AssocLeft, Infix (try parseAnd) AssocLeft
                   , Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]
                 ]

gamutOpTable :: (BooleanLanguage (FixLang lex (Form Bool)), Monad m)
    => [[Operator String u m (FixLang lex (Form Bool))]]
gamutOpTable = [ [ Prefix (try parseNeg)]
               , [ Infix (try $ parseAsOr ["\\/", "∨", "|", "or"]) AssocNone, Infix (try parseAnd) AssocNone 
                 , Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]
               ]

hausmanOpTable :: (BooleanLanguage (FixLang lex (Form Bool)), Monad m)
    => [[Operator String u m (FixLang lex (Form Bool))]]
hausmanOpTable = [[ Prefix (try parseNeg)
                  , Infix (try parseOr) AssocNone
                  , Infix (try (parseAsAnd [".", "∧", "∙"])) AssocNone
                  , Infix (try (parseAsIf ["⊃","→",">"])) AssocNone
                  , Infix (try parseIff) AssocNone
                  ]]

howardSnyderOpTable :: (BooleanLanguage (FixLang lex (Form Bool)), Monad m)
    => [[Operator String u m (FixLang lex (Form Bool))]]
howardSnyderOpTable = [[ Prefix (try parseNeg)
                       , Infix (try parseOr) AssocNone
                       , Infix (try (parseAsAnd [".", "∧", "∙"])) AssocNone
                       , Infix (try parseIf) AssocNone
                       , Infix (try parseIff) AssocNone
                       ]]

-----------------------
--  Special Parsers  --
-----------------------

englishPropFormulaParserStrict :: Monad m => ParsecT String u m PureForm
englishPropFormulaParserStrict = (spaces >> string "if " >> (lif <$> subFormulaParser <*> (string "then " *> subFormulaParser)))
                          <|> (spaces >> string "both " >> (land <$> subFormulaParser <*> (string "and " *> subFormulaParser)))
                          <|> (spaces >> string "either " >> (lor <$> subFormulaParser <*> (string "or " *> subFormulaParser)))
                          <|> buildExpressionParser englishOps subFormulaParser
    where subFormulaParser = (parenParser englishPropFormulaParserStrict <* spaces) --formulas wrapped in parentheses
                          <|> unaryOpParser [englishNeg] subFormulaParser 
                          <|> (sentenceLetterParser ['A'..'Z'] <* spaces) --or atoms

          englishOps = [ [Prefix (try englishNeg) ]
                       , [Infix (try englishAnd) AssocNone, Infix (try englishOr) AssocNone, Infix (try englishIff) AssocNone, Infix (try englishIf) AssocNone]
                       ]
          englishNeg = spaces >> string "not" >> spaces >> return lneg
          englishOr = spaces >> string "or" >> spaces >> return lor
          englishAnd = spaces >> string "and" >> spaces >> return land
          englishIff = spaces >> string "if and only if" >> spaces >> return liff
          englishIf = spaces >> string "only if" >> spaces >> return lif

englishPropFormulaParser :: Monad m => ParsecT String u m PureForm
englishPropFormulaParser = buildExpressionParser englishOps subFormulaParser
    --subformulas are either
    where subFormulaParser = (parenParser englishPropFormulaParser <* spaces) --formulas wrapped in parentheses
                          <|> unaryOpParser [englishNeg] subFormulaParser 
                          <|> try (spaces >> string "if " >> (lif <$> englishPropFormulaParser <*> (string "then " *> englishPropFormulaParser)))
                          <|> (spaces >> string "if " >> (lif <$> englishPropFormulaParser <*> (string ", then " *> englishPropFormulaParser)))
                          <|> try (spaces >> string "both " >> (land <$> englishPropFormulaParserSansComma <*> (string ", and " *> englishPropFormulaParser)))
                          <|> (spaces >> string "both " >> (land <$> englishPropFormulaParserSansAnd <*> (string "and " *> englishPropFormulaParser)))
                          <|> try (spaces >> string "either " >> (lor <$> englishPropFormulaParserSansComma <*> (string ", or " *> englishPropFormulaParser)))
                          <|> (spaces >> string "either " >> (lor <$> englishPropFormulaParserSansOr <*> (string "or " *> englishPropFormulaParser)))
                          <|> (sentenceLetterParser ['A'..'Z'] <* spaces) --or atoms

          englishPropFormulaParserSansAnd = buildExpressionParser sansAnd subFormulaParser

          englishPropFormulaParserSansOr = buildExpressionParser sansOr subFormulaParser

          englishPropFormulaParserSansComma = buildExpressionParser sansComma subFormulaParser

          sansOr = [ [Prefix (try englishNeg) ]
                       , [Infix (try englishAnd) AssocLeft]
                       , [Infix (try englishIff) AssocNone, Infix (try englishIf) AssocNone]
                       , [Infix (try oxfordAnd) AssocLeft]
                       ]
          sansAnd = [ [Prefix (try englishNeg) ]
                       , [Infix (try englishOr) AssocLeft]
                       , [Infix (try englishIff) AssocNone, Infix (try englishIf) AssocNone]
                       , [Infix (try oxfordOr) AssocLeft]
                       ]

          sansComma = [ [Prefix (try englishNeg) ]
                       , [Infix (try englishAnd) AssocLeft, Infix (try englishOr) AssocLeft]
                       , [Infix (try englishIff) AssocNone, Infix (try englishIf) AssocNone]
                       ]

          englishOps = [ [Prefix (try englishNeg) ]
                       , [Infix (try englishAnd) AssocLeft, Infix (try englishOr) AssocLeft]
                       , [Infix (try englishIff) AssocNone, Infix (try englishIf) AssocNone]
                       , [Infix (try oxfordAnd) AssocLeft, Infix (try oxfordOr) AssocLeft]
                       ]
          englishNeg = spaces >> string "not" >> spaces >> return lneg
          englishOr = spaces >> string "or" >> spaces >> return lor
          englishAnd = spaces >> string "and" >> spaces >> return land
          englishIff = spaces >> string "if and only if" >> spaces >> return liff
          englishIf = spaces >> string "only if" >> spaces >> return lif

          oxfordOr = string "," >> englishOr 
          oxfordAnd = string "," >> englishAnd
