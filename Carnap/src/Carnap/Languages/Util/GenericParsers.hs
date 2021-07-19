{-#LANGUAGE FlexibleContexts, AllowAmbiguousTypes #-}
module Carnap.Languages.Util.GenericParsers
where

import Carnap.Core.Data.Types
import Carnap.Languages.Util.LanguageClasses
import Text.Parsec
import Data.Typeable(Typeable)
import Data.List (elemIndex)

listToTry :: [ParsecT s u m a] -> ParsecT s u m a
listToTry (x:xs) = foldr ((<|>) . try) (try x) xs

stringsToTry :: Stream s m Char => [String] -> b -> ParsecT s u m b
stringsToTry l op = do spaces
                       _ <- listToTry (map string l)
                       spaces
                       return op

--------------------------------------------------------
--Operators
--------------------------------------------------------

parseAsAnd :: (Monad m, BooleanLanguage l) => [String] -> ParsecT String u m (l -> l -> l)
parseAsAnd s = stringsToTry s land

parseAnd :: (Monad m, BooleanLanguage l) => ParsecT String u m (l -> l -> l)
parseAnd = parseAsAnd ["/\\", "∧", "^", "&", "and"]

parseAsOr :: (Monad m, BooleanLanguage l) => [String] -> ParsecT String u m (l -> l -> l)
parseAsOr s = stringsToTry s lor

parseOr :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseOr = parseAsOr ["\\/", "∨", "v", "|", "or"] 

parseAsIf :: (Monad m, BooleanLanguage l) => [String] -> ParsecT String u m (l -> l -> l)
parseAsIf s = stringsToTry s lif

parseIf :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseIf = parseAsIf [ "=>", "->", ">", "→", "⊃", "only if"]

parseAsIff :: (Monad m, BooleanLanguage l) => [String] -> ParsecT String u m (l -> l -> l)
parseAsIff s = stringsToTry s liff

parseIff :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseIff = parseAsIff [ "<=>",  "<->", "<>", "↔", "≡", "if and only if"]

parseNeg :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l)
parseNeg = do spaces >> (string "-" <|> string "~" <|> string "¬" <|> string "not") >> spaces >> return lneg

booleanConstParser :: (BooleanConstLanguage l, Monad m) => ParsecT String u m l
booleanConstParser = stringsToTry ["!?","_|_","⊥"] lfalsum <|> stringsToTry ["⊤"] lverum 

parseNec :: (ModalLanguage l, Monad m) => ParsecT String u m (l -> l)
parseNec = do spaces >> (string "[]" <|> string "□") >> return nec

parsePos :: (ModalLanguage l, Monad m) => ParsecT String u m (l -> l)
parsePos = spaces >> (string "<>" <|> string "◇") >> return pos

parseIntersect :: (ElementarySetsLanguage lang, Monad m) => ParsecT String u m (lang -> lang -> lang)
parseIntersect = spaces >> (string "I" <|> string "∩" <|> string "cap") >> spaces >> return setIntersect

parseUnion :: (ElementarySetsLanguage lang, Monad m) => ParsecT String u m (lang -> lang -> lang)
parseUnion = spaces >> (string "U" <|> string "∪" <|> string "cup") >> spaces >> return setUnion

parseComplement :: (ElementarySetsLanguage lang, Monad m) => ParsecT String u m (lang -> lang -> lang)
parseComplement = spaces >> (string "/" <|> string "\\") >> spaces >> return setComplement

powersetParser :: (ElementarySetsLanguage lang, Monad m) =>  ParsecT String u m lang -> ParsecT String u m lang
powersetParser parseTerm = (try (string "P(") <|> string "Pow(") *> parseTerm <* string ")" >>= return . powerset

parsePlus :: (ElementaryArithmeticLanguage lang, Monad m) => ParsecT String u m (lang -> lang -> lang)
parsePlus = spaces >> (string "+") >> spaces >> return arithPlus

parseTimes :: (ElementaryArithmeticLanguage lang, Monad m) => ParsecT String u m (lang -> lang -> lang)
parseTimes = spaces >> (string "×" <|> string "*") >> spaces >> return arithTimes

parseSucc :: (ElementaryArithmeticLanguage lang, Monad m) => ParsecT String u m (lang -> lang)
parseSucc = spaces >> (string "'") >> spaces >> return arithSucc

--------------------------------------------------------
--Predicates and Sentences
--------------------------------------------------------

sentenceLetterParser :: (IndexedPropLanguage l, Monad m) 
    => String -> ParsecT String u m l
sentenceLetterParser s = parse <?> "a sentence letter"
    where parse = do c <- oneOf s
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = ucIndex c 
                         m = maybe 0 id midx
                     return $ pn (n  + (m * 26))

lowerCaseSentenceLetterParser :: (IndexedPropLanguage l, Monad m) 
    => String -> ParsecT String u m l
lowerCaseSentenceLetterParser s = parse <?> "a sentence letter"
    where parse = do c <- oneOf s
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = lcIndex c 
                         m = maybe 0 id midx
                     return $ pn (n  + (m * 26))

schemevarParser :: (IndexedSchemePropLanguage l , Monad m) 
    => ParsecT String u m l
schemevarParser = parse <?> "a schematic sentence letter"
    where parse = do c <- oneOf "ζφψχθγξ"
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = elemIndex c "ζφψχθγξ"
                         m = maybe 2 id midx
                     return $ phin (n  + (m * 7))

unaryOpParser :: (Monad m) => [ParsecT String u m (a -> b)] -> ParsecT String u m a ->  ParsecT String u m b
unaryOpParser ops arg = do n <- listToTry ops
                           f <- arg
                           return $ n f

binaryInfixOpParser :: (Monad m) => [ParsecT String u m (a -> a -> b)] -> ParsecT String u m a ->  ParsecT String u m b
binaryInfixOpParser ops arg = do t1 <- arg
                                 spaces
                                 op <- listToTry ops
                                 spaces
                                 t2 <- arg
                                 return $ op t1 t2

equalsParser :: (EqLanguage lang arg ret, Monad m) => ParsecT String u m (lang arg) -> ParsecT String u m (lang ret) 
equalsParser parseTerm = binaryInfixOpParser [char '=' >> return equals] parseTerm

inequalityParser :: (EqLanguage lang arg ret, BooleanLanguage (lang ret), Monad m) => ParsecT String u m (lang arg) -> ParsecT String u m (lang ret) 
inequalityParser parseTerm = binaryInfixOpParser [string "!=" >> theparser, string "≠" >> theparser] parseTerm
    where theparser = return (\x y -> lneg (equals x y))

elementParser :: (ElemLanguage lang arg ret , Monad m) => ParsecT String u m (lang arg) -> ParsecT String u m (lang ret) 
elementParser parseTerm = binaryInfixOpParser ops parseTerm
    where ops = map (>> return isIn)  [string "∈", string "<<", string "<e", string "in"]

subsetParser :: (SubsetLanguage lang arg ret , Monad m) => ParsecT String u m (lang arg) -> ParsecT String u m (lang ret) 
subsetParser parseTerm = binaryInfixOpParser ops parseTerm
    where ops = map (>> return within) [string "⊆", string "<(", string "<s", string "sub", string "within"]

lessThanParser :: (LessThanLanguage lang arg ret , Monad m) => ParsecT String u m (lang arg) -> ParsecT String u m (lang ret) 
lessThanParser parseTerm = binaryInfixOpParser ops parseTerm
    where ops = map (>> return lessThan) [string "<"]

separationParser :: 
    ( SeparatingLang (FixLang lex f) (FixLang lex t)
    , BoundVars lex
    , Show (FixLang lex t)
    , Monad m
    ) => ParsecT String u m (FixLang lex t) -> ParsecT String u m (FixLang lex t) -> ParsecT String u m (FixLang lex f) -> ParsecT String u m (FixLang lex t)
separationParser parseFreeVar parseTerm formulaParser = 
        do v <- char '{' *> spaces *> parseFreeVar <* spaces
           listToTry [string "∈", string "<<", string "<e", string "in"]
           t <- spaces *> parseTerm <* spaces
           char '|' <|> char ':'
           f <- spaces *> formulaParser <* spaces <* char '}'
           let bf x = subBoundVar v x f
               --partially applied, returning a function
           return $ separate (show v) t bf

parsePredicateSymbol :: 
    ( PolyadicPredicateLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => String -> ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parsePredicateSymbol s parseTerm = parse <?> "a predicate symbol"
    where parse = do c <- oneOf s
                     _ <- optionMaybe (char '^' >> posnumber)
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = ucIndex c 
                         m = maybe 0 id midx
                     char '(' *> spaces *> argParser parseTerm (ppn (n + (m * 26)) AOne)

parsePredicateString :: 
    ( PolyadicStringPredicateLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => [Char] -> ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parsePredicateString extraChars parseTerm = parse <?> "a predicate string"
    where parse = do c <- upper
                     s <- many (alphaNum <|> oneOf extraChars)
                     char '(' *> spaces *> argParser parseTerm (stringPred (c:s) AOne)

parseSchematicPredicateSymbol :: 
    ( PolyadicSchematicPredicateLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parseSchematicPredicateSymbol parseTerm = parse <?> "a schematic predicate symbol"
    where parse = do c <- oneOf "ξχθγζϚφψ"
                     _ <- optionMaybe (char '^' >> posnumber)
                     midx <- optionMaybe (char '_' >> posnumber)
                     --these are out of order to make sure that
                     --the 15th schematic variable is φ,
                     --corresponding to the 15th sentence letter, P.
                     let Just n = elemIndex c "ξθγζϚφψχ"
                         m = maybe 0 id midx
                     char '(' *> spaces *> argParser parseTerm (pphin (n + (m * 8)) AOne)

--This is intended for easy keyboard input of schematic predicate symbols
parseFriendlySchematicPredicateSymbol :: 
    ( PolyadicSchematicPredicateLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parseFriendlySchematicPredicateSymbol parseTerm = parse <?> "a schematic predicate symbol abbreviation"
    where parse = do char '\''
                     c <- oneOf ['A' .. 'Z']
                     _ <- optionMaybe (char '^' >> posnumber)
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = ucIndex c
                         m = maybe 0 id midx
                     char '(' *> spaces *> argParser parseTerm (pphin (n + (m * 26)) AOne)

parsePredicateSymbolNoParen :: 
    ( PolyadicPredicateLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => String -> ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parsePredicateSymbolNoParen s parseTerm = parse <?> "a predicate symbol"
    where parse = do c <- oneOf s
                     _ <- optionMaybe (char '^' >> posnumber)
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = ucIndex c 
                         m = maybe 0 id midx
                     argParserNoParen parseTerm (ppn (n + (m * 26)) AOne)

quantifiedSentenceParser, lplQuantifiedSentenceParser, altAltQuantifiedSentenceParser, altQuantifiedSentenceParser :: 
    ( QuantLanguage (FixLang lex f) (FixLang lex t)
    , BoundVars lex
    , Show (FixLang lex t)
    , Monad m
    ) => ParsecT String u m (FixLang lex t) -> ParsecT String u m (FixLang lex f) 
            -> ParsecT String u m (FixLang lex f)
quantifiedSentenceParser parseFreeVar formulaParser =
        do s <- oneOf "AE∀∃" <?> "a quantifer symbol"
           spaces
           v <- parseFreeVar
           spaces
           f <- formulaParser
           let bf x = subBoundVar v x f
               --partially applied, returning a function
           return $ if s `elem` "A∀" then lall (show v) bf else lsome (show v) bf
               --which we bind

lplQuantifiedSentenceParser parseFreeVar formulaParser =
        do s <- oneOf "AE∀∃@3" <?> "a quantifer symbol"
           spaces
           v <- parseFreeVar
           spaces
           f <- formulaParser
           let bf x = subBoundVar v x f
               --partially applied, returning a function
           return $ if s `elem` "A∀@" then lall (show v) bf else lsome (show v) bf
               --which we bind

altQuantifiedSentenceParser parseFreeVar formulaParser =
        do char '('
           s <- optionMaybe (oneOf "E∃" <?> "a quantifer symbol")
           v <- parseFreeVar
           char ')'
           spaces
           f <- formulaParser
           let bf x = subBoundVar v x f
               --partially applied, returning a function
           return $ case s of Just _ -> lsome (show v) bf; Nothing -> lall (show v) bf
               --which we bind

altAltQuantifiedSentenceParser parseFreeVar formulaParser =
        do char '('
           s <- oneOf "AE∀∃" <?> "a quantifer symbol"
           v <- parseFreeVar
           char ')'
           spaces
           f <- formulaParser
           let bf x = subBoundVar v x f
               --partially applied, returning a function
           return $ if s `elem` "E∃" then lsome (show v) bf else lall (show v) bf
               --which we bind

--------------------------------------------------------
--Terms
--------------------------------------------------------

parseFunctionSymbol ::     
    ( PolyadicFunctionLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => String -> ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parseFunctionSymbol s parseTerm = parse <?> "a function symbol"
    where parse = do c <- oneOf s
                     _ <- optionMaybe (char '^' >> posnumber)
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = lcIndex c 
                         m = maybe 0 id midx
                     -- an int K represents the symbol at index
                     -- (k `mod` 26) with subscript (k `div` 26)
                     -- we need to compensate for offset, since
                     -- lcIndex begins at 1
                     char '(' *> spaces *> argParser parseTerm (pfn (n + (m * 26)) AOne)

parseFunctionString ::     
    ( PolyadicStringFunctionLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => [Char] -> ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parseFunctionString extraChars parseTerm = parse <?> "a function string"
    where parse = do c <- lower
                     s <- many (alphaNum <|> oneOf extraChars)
                     char '(' *> spaces *> argParser parseTerm (stringFunc (c:s) AOne)

parseSchematicFunctionSymbol ::     
    ( SchematicPolyadicFunctionLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parseSchematicFunctionSymbol parseTerm = parse <?> "a schematic function symbol"
    where parse = do c <- oneOf "τνυρκ"
                     _ <- optionMaybe (char '^' >> posnumber)
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = elemIndex c "τνυρκ"
                         m = maybe 1 id midx
                     char '(' *> spaces *> argParser parseTerm (spfn (n + (m * 5)) AOne)

--This is intended for easy keyboard input of schematic function symbols
parseFriendlySchematicFunctionSymbol ::     
    ( SchematicPolyadicFunctionLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parseFriendlySchematicFunctionSymbol parseTerm = parse <?> "a schematic function symbol abbreviation"
    where parse = do char '\''
                     c <- oneOf ['a' .. 'z']
                     _ <- optionMaybe (char '^' >> posnumber)
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = lcIndex c
                         m = maybe 1 id midx
                     char '(' *> spaces *> argParser parseTerm (spfn (n + (m * 26)) AOne)

parseConstant :: 
    ( IndexedConstantLanguage (FixLang lex ret)
    , Typeable ret
    , Monad m
    ) => String -> ParsecT String u m (FixLang lex ret)
parseConstant s = parse <?> "a constant"
    where parse = do c <- oneOf s
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = lcIndex c 
                         m = maybe 0 id midx
                     return $ cn (n  + (m * 26))

parseSchematicConstant :: 
    ( IndexedSchemeConstantLanguage (FixLang lex ret)
    , Typeable ret
    , Monad m
    ) => ParsecT String u m (FixLang lex ret)
parseSchematicConstant = parse <?> "a constant"
    where parse = do c <- oneOf "τπμ"
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = elemIndex c "τπμ" 
                         m = maybe 0 id midx
                     return $ taun (n  + (m * 3))

parseFriendlySchematicConstant :: 
    ( IndexedSchemeConstantLanguage (FixLang lex ret)
    , Typeable ret
    , Monad m
    ) => ParsecT String u m (FixLang lex ret)
parseFriendlySchematicConstant = parse <?> "a schematic constant symbol abbreviation"
    where parse = do char '\''
                     c <- oneOf ['a' .. 'z']
                     midx <- optionMaybe (char '_' >> posnumber)
                     let Just n = lcIndex c 
                         m = maybe 0 id midx
                     return $ taun (n  + (m * 26))

parseZero :: (ElementaryArithmeticLanguage lang, Monad m) => ParsecT String u m lang
parseZero = spaces >> (string "0") >> spaces >> return arithZero

parseEmptySet :: (ElementarySetsLanguage lang, Monad m) => ParsecT String u m lang
parseEmptySet = spaces >> (string "∅" <|> string "{}" <|> string "empty") >> spaces >> return emptySet

--------------------------------------------------------
--Structural Elements
--------------------------------------------------------

iteratedParse :: Monad m => ParsecT String u m (lang -> lang) -> ParsecT String u m (lang -> lang)
iteratedParse it = do h:its <- many1 it
                      return $ foldr (.) h its

wrappedWith :: Monad m => Char -> Char -> ParsecT String u m l -> ParsecT String u m l
wrappedWith l r recur = char l *> spaces *> recur <* spaces <* char r

parenParser :: Monad m => ParsecT String u m l -> ParsecT String u m l
parenParser recur = wrappedWith '(' ')' recur

number :: Monad m => ParsecT String u m Int
number = do valence <- option "+" (string "-") 
            ds <- many1 digit
            if valence == "+" 
                then return (read ds) 
                else return (read ds * (-1))

posnumber :: Monad m => ParsecT String u m Int
posnumber = do ds <- many1 digit
               return (read ds) 

--------------------------------------------------------
--Helper functions
--------------------------------------------------------

lcIndex c = elemIndex c ['a' .. 'z']

ucIndex c = elemIndex c ['A' .. 'Z']

argParser :: 
    ( Typeable b
    , Typeable t2
    , Incrementable lex t2
    , Monad m) => ParsecT String u m (FixLang lex t2) -> FixLang lex (t2 -> b) 
            -> ParsecT String u m (FixLang lex b)
argParser pt p = do spaces
                    t <- pt
                    spaces
                    incrementHead pt p t
                        <|> char ')' *> return (p :!$: t)

incrementHead :: 
    ( Monad m
    , Typeable t2
    , Typeable b
    , Incrementable lex t2
    ) => ParsecT String u m (FixLang lex t2) -> FixLang lex (t2 -> b) -> FixLang lex t2 
        -> ParsecT String u m (FixLang lex b)
incrementHead pt p t = do char ','
                          case incBody p of
                               Just p' -> argParser pt (p' :!$: t)
                               Nothing -> fail "Weird error with function"

argParserNoParen :: 
    ( Typeable b
    , Typeable t2
    , Incrementable lex t2
    , Monad m) => ParsecT String u m (FixLang lex t2) -> FixLang lex (t2 -> b) 
            -> ParsecT String u m (FixLang lex b)
argParserNoParen pt p = do t <- pt
                           incrementHeadNoParen pt p t
                               <|> return (p :!$: t)

incrementHeadNoParen :: 
    ( Monad m
    , Typeable t2
    , Typeable b
    , Incrementable lex t2
    ) => ParsecT String u m (FixLang lex t2) -> FixLang lex (t2 -> b) -> FixLang lex t2 
        -> ParsecT String u m (FixLang lex b)
incrementHeadNoParen pt p t = case incBody p of
                                   Just p' -> argParserNoParen pt (p' :!$: t)
                                   Nothing -> fail "Weird error with function"
