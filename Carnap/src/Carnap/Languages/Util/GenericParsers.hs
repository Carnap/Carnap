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
parseIntersect = spaces >> (string "I" <|> string "∩") >> spaces >> return setIntersect

parseUnion :: (ElementarySetsLanguage lang, Monad m) => ParsecT String u m (lang -> lang -> lang)
parseUnion = spaces >> (string "U" <|> string "∪") >> spaces >> return setUnion

parseComplement :: (ElementarySetsLanguage lang, Monad m) => ParsecT String u m (lang -> lang -> lang)
parseComplement = spaces >> string "/" >> spaces >> return setComplement

powersetParser :: (ElementarySetsLanguage lang, Monad m) =>  ParsecT String u m lang -> ParsecT String u m lang
powersetParser parseTerm = (try (string "P(") <|> string "Pow(") *> parseTerm <* string ")" >>= return . powerset

--------------------------------------------------------
--Predicates and Sentences
--------------------------------------------------------

sentenceLetterParser :: (IndexedPropLanguage l, Monad m) => String ->
    ParsecT String u m l
sentenceLetterParser s = (try parseNumbered <|> parseUnnumbered) <?> "a sentence letter"
        where parseUnnumbered = do c <- oneOf s
                                   let Just n = elemIndex c "_ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                                   return $ pn (-1 * n)
              parseNumbered = do char 'P'
                                 char '_'
                                 n <- number
                                 return $ pn n

lowerCaseSentenceLetterParser :: (IndexedPropLanguage l, Monad m) => String ->
    ParsecT String u m l
lowerCaseSentenceLetterParser s = (try parseNumbered <|> parseUnnumbered) <?> "a sentence letter"
        where parseUnnumbered = do c <- oneOf s
                                   let Just n = elemIndex c "_abcdefghijklmnopqrstuvwxyz"
                                   return $ pn (-1 * n)
              parseNumbered = do char 'p'
                                 char '_'
                                 n <- number
                                 return $ pn n

schemevarParser :: 
    ( IndexedSchemePropLanguage l
    , Monad m
    ) => ParsecT String u m l
schemevarParser = try parseNumbered <|> parseUnnumbered
    where parseUnnumbered = do c <- oneOf "_φψχθγζξ"
                               let Just n = elemIndex c "_φψχθγζξ"
                               return $ phin (-1 * (n + 15))
          parseNumbered = do string "Phi" <|> string "φ"
                             char '_'
                             n <- number <?> "a number"
                             return $ phin n

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

elementParser :: (ElemLanguage lang arg ret , Monad m) => ParsecT String u m (lang arg) -> ParsecT String u m (lang ret) 
elementParser parseTerm = binaryInfixOpParser ops parseTerm
    where ops = map (>> return isIn)  [string "∈", string "<<", string "<e", string "in"]

subsetParser :: (SubsetLanguage lang arg ret , Monad m) => ParsecT String u m (lang arg) -> ParsecT String u m (lang ret) 
subsetParser parseTerm = binaryInfixOpParser ops parseTerm
    where ops = map (>> return within) [string "⊆", string "<(", string "<s", string "within"]

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
parsePredicateSymbol s parseTerm = (try parseNumbered <|> parseUnnumbered) <?> "a predicate symbol"
    where parseUnnumbered = do c <- oneOf s
                               let Just n = ucIndex c
                               char '(' *> spaces *> argParser parseTerm (ppn (-1 * n) AOne)
          parseNumbered = do string "F" >> optionMaybe (char '^' >> number)
                             n <- char '_' *> number
                             char '(' *> spaces *> argParser parseTerm (ppn n AOne)

parseSchematicPredicateSymbol :: 
    ( PolyadicSchematicPredicateLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parseSchematicPredicateSymbol parseTerm = (try parseUnnumbered <|> parseNumbered) <?> "a schematic predicate symbol"
    where parseNumbered = do string "φ" >> optionMaybe (char '^' >> number)
                             n <- char '_' *> number
                             char '(' *> spaces *> argParser parseTerm (pphin n AOne)
          parseUnnumbered = do c <- oneOf "φψχθγζξ"
                               let Just n = elemIndex c "_φψχθγζξ"
                               char '(' *> spaces *> argParser parseTerm (pphin (-1 * (n + 5)) AOne)

parsePredicateSymbolNoParen :: 
    ( PolyadicPredicateLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => String -> ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parsePredicateSymbolNoParen s parseTerm = (try parseNumbered <|> parseUnnumbered) <?> "a predicate symbol"
    where parseUnnumbered = do c <- oneOf s
                               let Just n = ucIndex c
                               argParserNoParen parseTerm (ppn (-1 * n) AOne)
          parseNumbered = do string "F" >> optionMaybe (char '^' >> number)
                             n <- char '_' *> number
                             argParserNoParen parseTerm (ppn n AOne)

quantifiedSentenceParser :: 
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

lplQuantifiedSentenceParser :: 
    ( QuantLanguage (FixLang lex f) (FixLang lex t)
    , BoundVars lex
    , Show (FixLang lex t)
    , Monad m
    ) => ParsecT String u m (FixLang lex t) -> ParsecT String u m (FixLang lex f) 
            -> ParsecT String u m (FixLang lex f)
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

altQuantifiedSentenceParser :: 
    ( QuantLanguage (FixLang lex f) (FixLang lex t)
    , BoundVars lex
    , Show (FixLang lex t)
    , Monad m
    ) => ParsecT String u m (FixLang lex t) -> ParsecT String u m (FixLang lex f) 
            -> ParsecT String u m (FixLang lex f)
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

---XXX:DRY
altAltQuantifiedSentenceParser :: 
    ( QuantLanguage (FixLang lex f) (FixLang lex t)
    , BoundVars lex
    , Show (FixLang lex t)
    , Monad m
    ) => ParsecT String u m (FixLang lex t) -> ParsecT String u m (FixLang lex f) 
            -> ParsecT String u m (FixLang lex f)
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
parseFunctionSymbol s parseTerm = (try parseNumbered <|> parseUnnumbered) <?> "a function symbol"
    where parseNumbered = do string "f" >> char '^' >> number >> char '_' 
                             n <- number
                             char '(' *> spaces *> argParser parseTerm (pfn (-1 * n) AOne)
          parseUnnumbered = do c <- oneOf s
                               midx <- optionMaybe (char '_' >> number)
                               let Just n = lcIndex c 
                                   m = maybe 0 id midx
                               -- an int K represents the symbol at index
                               -- (k `mod` 26) with subscript (k `div` 26)
                               -- we need to compensate for offset, since
                               -- lcIndex begins at 1
                               char '(' *> spaces *> argParser parseTerm (pfn (n + (m * 26)) AOne)

parseSchematicFunctionSymbol ::     
    ( SchematicPolyadicFunctionLanguage (FixLang lex) arg ret
    , Incrementable lex arg
    , Monad m
    , Typeable ret
    , Typeable arg
    ) => ParsecT String u m (FixLang lex arg) -> ParsecT String u m (FixLang lex ret)
parseSchematicFunctionSymbol parseTerm = (try parseNumbered <|> parseUnnumbered) <?> "a function symbol"
    where parseNumbered = do string "τ" >> optionMaybe (char '^' >> number) >> char '_'
                             n <- number
                             char '(' *> spaces *> argParser parseTerm (spfn n AOne)
          parseUnnumbered = do c <- oneOf "τνυ"
                               let Just n = elemIndex c "_τνυ"
                               char '(' *> spaces *> argParser parseTerm (spfn (-1 * (n + 5)) AOne)

parseConstant :: 
    ( IndexedConstantLanguage (FixLang lex ret)
    , Typeable ret
    , Monad m
    ) => String -> ParsecT String u m (FixLang lex ret)
parseConstant s = parse <?> "a constant"
    where parse = do c <- oneOf s
                     midx <- optionMaybe (char '_' >> number)
                     let Just n = lcIndex c 
                         m = maybe 0 id midx
                     return $ cn (n  + (m * 26))

parseSchematicConstant :: 
    ( IndexedSchemeConstantLanguage (FixLang lex ret)
    , Typeable ret
    , Monad m
    ) => ParsecT String u m (FixLang lex ret)
parseSchematicConstant = (try parseNumbered <|> parseUnnumbered) <?> "a constant"
    where parseUnnumbered = do c <- oneOf "τπμ"
                               let Just n = elemIndex c "_τπμ"
                               return $ taun (-1 * n)
          parseNumbered  = do _ <- string "τ_" >> optionMaybe (string "^0")
                              n <- number
                              return $ taun n

--------------------------------------------------------
--Structural Elements
--------------------------------------------------------

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

--------------------------------------------------------
--Helper functions
--------------------------------------------------------

lcIndex c = elemIndex c "abcdefghijklmnopqrstuvwxyz"

ucIndex c = elemIndex c "_ABCDEFGHIJKLMNOPQRSTUVWXYZ"

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
