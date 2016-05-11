{-#LANGUAGE FlexibleContexts, AllowAmbiguousTypes #-}
module Carnap.Languages.Util.GenericParsers 
where

import Carnap.Languages.Util.LanguageClasses
import Text.Parsec

listToTry :: [ParsecT s u m a] -> ParsecT s u m a
listToTry (x:xs) = foldr (\y -> (<|>) (try y)) (try x) xs

stringsToTry :: Stream s m Char => [String] -> b -> ParsecT s u m b
stringsToTry l op = do spaces
                       _ <- listToTry (map string l)
                       spaces
                       return op

parseAnd :: (Monad m, BooleanLanguage l) => ParsecT String u m (l -> l -> l)
parseAnd = stringsToTry ["/\\", "∧", "^", "&", "and"] land

parseOr :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseOr = stringsToTry ["\\/", "∨", "v", "|", "or"] lor

parseIf :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseIf = stringsToTry [ "=>", "->", ">", "→", "only if"] lif

parseIff :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseIff = stringsToTry [ "<=>",  "<->", "<>", "↔", "if and only if"] liff

parseNeg :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l)
parseNeg = do spaces
              _ <- string "-" <|> string "~" <|> string "¬" <|> string "not "
              return lneg

parseNec :: (ModalLanguage l, Monad m) => ParsecT String u m (l -> l)
parseNec = do spaces
              _ <- string "[]" <|> string "□"
              return nec

parsePos :: (ModalLanguage l, Monad m) => ParsecT String u m (l -> l)
parsePos = do spaces
              _ <- string "<>" <|> string "◇"
              return pos

atomParser :: (IndexedPropLanguage l, Monad m) => ParsecT String u m l
atomParser = do char 'P'
                char '_'
                n <- number
                return $ pn n
    where number = do { ds <- many1 digit; return (read ds) } <?> "number"

parenParser :: (BooleanLanguage l, Monad m, IndexedPropLanguage l) => ParsecT String u m l -> ParsecT String u m l
parenParser recur = char '(' *> recur <* char ')' 

unaryOpParser :: (Monad m, BooleanLanguage l, IndexedPropLanguage l) => [ParsecT String u m (l -> l)] -> ParsecT String u m l ->  ParsecT String u m l
unaryOpParser ops recur = do n <- listToTry ops
                             f <- recur
                             return $ n f

