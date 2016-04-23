{-#LANGUAGE FlexibleContexts, AllowAmbiguousTypes #-}
module Carnap.Languages.Util.GenericParsers 
where

import Carnap.Languages.Util.LanguageClasses
import Text.Parsec

fromList (x:xs) op = do spaces
                        _ <- foldr (\y -> (<|>) (try $ string y)) (try $ string x) xs
                        spaces
                        return op

parseAnd :: (Monad m, BooleanLanguage l) => ParsecT String u m (l -> l -> l)
parseAnd = fromList ["/\\", "∧", "^", "&", "and"] land

parseOr :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseOr = fromList ["\\/", "∨", "v", "|", "or"] lor

parseIf :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseIf = fromList [ "=>", "->", ">", "→", "only if"] lif

parseIff :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l -> l)
parseIff = fromList [ "<=>",  "<->", "<>", "↔", "if and only if"] liff

parseNeg :: (BooleanLanguage l, Monad m) => ParsecT String u m (l -> l)
parseNeg = do spaces
              _ <- string "-" <|> string "~" <|> string "¬" <|> string "not "
              return lneg

atomParser :: (IndexedPropLanguage l, Monad m) => ParsecT String u m l
atomParser = do char 'P'
                char '_'
                n <- number
                return $ pn n
    where number = do { ds <- many1 digit; return (read ds) } <?> "number"

parenParser :: (BooleanLanguage l, Monad m, IndexedPropLanguage l) => ParsecT String u m l -> ParsecT String u m l
parenParser recur = char '(' *> recur <* char ')' 

negParser :: (Monad m, BooleanLanguage l, IndexedPropLanguage l) => ParsecT String u m l -> ParsecT String u m l
negParser recur = do n <- try parseNeg 
                     f <- recur
                     return $ n f
