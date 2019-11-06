{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Util 
(showClean,isValid, isEquivTo, toSchema, getIndicies, getValuations,
isBooleanBinary, isBooleanUnary, isBoolean, isAtom, HasLiterals(..), isCNF,
isDNF, conjunctiveClause, disjunctiveClause) 
where

import Carnap.Core.Data.Classes
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.Util.LanguageClasses
import Control.Lens
import Data.Maybe
import Data.List

--------------------------------------------------------
--1. Show Clean
--------------------------------------------------------

showClean :: PurePropLanguage (Form Bool) -> String
showClean = dropOutermost . preShowClean

preShowClean :: PurePropLanguage (Form Bool) -> String
preShowClean = show
            & outside (binaryOpPrism _if)  .~ (\(x,y) -> schematize theIf [dropOn isJunction x, dropOn isJunction y])
            & outside (binaryOpPrism _iff) .~ (\(x,y) -> schematize theIff [dropOn isJunction x, dropOn isJunction y])
            & outside (binaryOpPrism _and) .~ (\(x,y) -> schematize theAnd [dropOn isJunction x, preShowClean y])
            & outside (binaryOpPrism _or)  .~ (\(x,y) -> schematize theOr [dropOn isJunction x, preShowClean y])
    where isAnd x = x ^? (binaryOpPrism _and) /= Nothing
          isOr x = x ^? (binaryOpPrism _or) /= Nothing
          dropOn cond x = if cond x then dropParens x else preShowClean x
          theIf :: PurePropLanguage (Form Bool -> Form Bool -> Form Bool)
          theIf = review _if ()
          theIff :: PurePropLanguage (Form Bool -> Form Bool -> Form Bool)
          theIff = review _iff ()
          theAnd :: PurePropLanguage (Form Bool -> Form Bool -> Form Bool)
          theAnd = review _and ()
          theOr :: PurePropLanguage (Form Bool -> Form Bool -> Form Bool)
          theOr = review _or ()
    
dropParens :: PurePropLanguage (Form Bool) -> String
dropParens =  init . tail . preShowClean

dropOutermost :: String -> String
dropOutermost s@('(':_) = init . tail $ s
dropOutermost s = s

--------------------------------------------------------
--2. Truth Tables
--------------------------------------------------------

getIndicies :: PurePropLanguage (Form Bool) -> [Int]
getIndicies = catMaybes . map (preview _propIndex) . universe

getValuations :: PurePropLanguage (Form Bool) -> [Int -> Bool]
getValuations = (map toValuation) . subsequences . getIndicies 
    where toValuation l = \x -> x `elem` l

isValid p = and $ map (\v -> unform $ satisfies v p) (getValuations p)
    where unform (Form x) = x

isEquivTo x y = isValid (x .<=>. y)

--------------------------------------------------------
--3. Transformations
--------------------------------------------------------

instance ToSchema PurePropLexicon (Form Bool) where
    toSchema = transform trans
        where trans = id & outside (_propIndex) .~ (\n -> phin n)

---------------
--4. Optics  --
---------------


conjunctiveClause :: PrismBooleanConnLex lex b => Traversal' (FixLang lex (Form b)) (FixLang lex (Form b))
conjunctiveClause f s = case s ^? binaryOpPrism _and of
                            Nothing -> f s
                            Just (a,b) -> (./\.) <$> conjunctiveClause f a <*> conjunctiveClause f b

disjunctiveClause :: PrismBooleanConnLex lex b => Traversal' (FixLang lex (Form b)) (FixLang lex (Form b))
disjunctiveClause f s = case s ^? binaryOpPrism _or of
                            Nothing -> f s
                            Just (a,b) -> (./\.) <$> disjunctiveClause f a <*> disjunctiveClause f b

--------------
--5. Tests  --
--------------

isJunction :: (PrismBooleanConnLex lex b) => FixLang lex (Form b) -> Bool
isJunction x = not . null . catMaybes $ map (x ^? ) [binaryOpPrism _and, binaryOpPrism _or]

isBooleanBinary :: (PrismBooleanConnLex lex b) => FixLang lex (Form b) -> Bool
isBooleanBinary a = not . null . catMaybes $ map (a ^? ) [binaryOpPrism _and, binaryOpPrism _or, binaryOpPrism _if,binaryOpPrism _iff]

isBooleanUnary :: (PrismBooleanConnLex lex b) => FixLang lex (Form b) -> Bool
isBooleanUnary a = case (a ^? unaryOpPrism _not) of Nothing -> False; _ -> True

isBoolean x = isBooleanUnary x || isBooleanBinary x

class PrismBooleanConnLex lex sem => HasLiterals lex sem where
        isLiteral :: FixLang lex (Form sem) -> Bool
        isLiteral l = case l ^? unaryOpPrism _not of
                          Just a' -> isAtom a'
                          Nothing -> isAtom l
        isAtom :: FixLang lex (Form sem) -> Bool

instance HasLiterals PurePropLexicon Bool where
    isAtom a = (a ^? _propIndex) /= Nothing

isCNF :: (PrismBooleanConnLex lex b, HasLiterals lex b) => FixLang lex (Form b) -> Bool
isCNF = all isLiteral . toListOf (conjunctiveClause . disjunctiveClause)

isDNF :: (PrismBooleanConnLex lex b, HasLiterals lex b) => FixLang lex (Form b) -> Bool
isDNF = all isLiteral . toListOf (disjunctiveClause . conjunctiveClause)
