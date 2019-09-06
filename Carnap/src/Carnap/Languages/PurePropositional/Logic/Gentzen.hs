{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Gentzen
    ( parseGentzenPropLK, gentzenPropLKCalc, GentzenPropLK()
    , parseGentzenPropLJ, gentzenPropLJCalc, GentzenPropLJ()) where

import Text.Parsec
import Data.List
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Types (Form, FirstOrderLex(..))
import Carnap.Core.Unification.Unification
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.Util
import Control.Lens
import Carnap.Languages.Util.LanguageClasses

data GentzenPropLK = Ax    | Rep   | Cut
                   | AndL1 | AndL2 | AndR
                   | OrR1  | OrR2  | OrL
                   | CondR | CondL
                   | NegR  | NegL

newtype GentzenPropLJ = LJ GentzenPropLK

instance Show GentzenPropLK where
    show Ax     = "Ax"
    show Rep    = "Rep"
    show Cut    = "Cut"
    show AndL1  = "L&1"
    show AndL2  = "L&2"
    show AndR   = "R&"
    show OrR1   = "R∨1" 
    show OrR2   = "R∨2"
    show OrL    = "L∨"
    show CondR  = "R→"
    show CondL  = "L→"
    show NegR   = "R¬" 
    show NegL   = "L¬"

instance Show GentzenPropLJ where
    show (LJ x) = show x

parseGentzenPropLK :: Parsec String u GentzenPropLK
parseGentzenPropLK =  do r <- choice (map (try . string) [ "Ax", "Rep", "Cut"
                                                         , "R&","R∧","R/\\"
                                                         ,"L&1","L∧1","L/\\1"
                                                         ,"L&2","L∧2","L/\\2"
                                                         , "L∨","Lv","L\\/"
                                                         ,"R∨1","Rv1","R\\/1"
                                                         ,"R∨2","Rv2","R\\/2"
                                                         , "L→","L->"
                                                         , "R→","R->"
                                                         , "L¬","L~","L-"
                                                         , "R¬","R~","R-"
                                                         ])
                         return $ case r of
                            r | r == "Ax" -> Ax
                              | r == "Rep" -> Rep
                              | r == "Cut" -> Cut
                              | r `elem` ["R&","R∧","R/\\"] -> AndR
                              | r `elem` ["L&1","L∧1","L/\\1"] -> AndL1
                              | r `elem` ["L&2","L∧2","L/\\2"] -> AndL2
                              | r `elem` ["L∨","Lv","L\\/"] -> OrL
                              | r `elem` ["R∨1","Rv1","R\\/1"] -> OrR1
                              | r `elem` ["R∨2","Rv2","R\\/2"] -> OrR2
                              | r `elem` ["L→","L->"] -> CondL
                              | r `elem` ["R→","R->"] -> CondR
                              | r `elem` ["L¬","L~","L-"] -> NegL
                              | r `elem` ["R¬","R~","R-"] -> NegR

parseGentzenPropLJ = LJ <$> parseGentzenPropLK

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         ) => CoreInference GentzenPropLK lex (Form Bool) where
         corePremisesOf AndL1 = [SA (phin 1) :+: GammaV 1 :|-: DeltaV 1]
         corePremisesOf AndL2 = [SA (phin 2) :+: GammaV 1 :|-: DeltaV 1]
         corePremisesOf AndR = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1
                               , GammaV 2 :|-: SS (phin 2) :-: DeltaV 2
                               ]
         corePremisesOf OrR1 = [ GammaV 1 :|-: DeltaV 1 :-: SS(phin 1)]
         corePremisesOf OrR2 = [ GammaV 1 :|-: DeltaV 1 :-: SS(phin 2)]
         corePremisesOf OrL  = [ GammaV 1 :+: SA (phin 1) :|-: DeltaV 1
                               , GammaV 2 :+: SA (phin 1) :|-: DeltaV 2
                               ] 
         corePremisesOf CondL = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1
                                , GammaV 2 :+: SA (phin 2) :|-: DeltaV 2
                                ]
         corePremisesOf CondR = [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) :-: DeltaV 2 ]
         corePremisesOf NegL = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1 ]
         corePremisesOf NegR = [ SA (phin 1) :+: GammaV 1 :|-:  DeltaV 1 ]
         corePremisesOf Rep =  [GammaV 1 :|-: DeltaV 1 ]
         corePremisesOf Cut =  [ SA (phin 1) :+: GammaV 1 :|-: DeltaV 1 
                               , GammaV 2 :|-: DeltaV 2 :-: SS (phin 1)
                               ]
         corePremisesOf Ax = [] 

         coreConclusionOf AndL1 = SA (phin 1 ./\. phin 2) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf AndL2 = SA (phin 1 ./\. phin 2) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf AndR = GammaV 1 :+: GammaV 2 :|-: SS (phin 1 ./\. phin 2) :-: DeltaV 1 :-: DeltaV 2
         coreConclusionOf OrR1 =  GammaV 1 :|-: SS (phin 1 .\/. phin 2) :-: DeltaV 1
         coreConclusionOf OrR2 = GammaV 1 :|-: SS (phin 1 .\/. phin 2) :-: DeltaV 1
         coreConclusionOf OrL = SA (phin 1 .\/. phin 2) :+: GammaV 1 :+: GammaV 2 :|-:  DeltaV 1 :-: DeltaV 2
         coreConclusionOf CondL = SA (phin 1 .=>. phin 2) :+: GammaV 1 :+: GammaV 2 :|-:  DeltaV 1 :-: DeltaV 2
         coreConclusionOf CondR =  GammaV 1 :+: GammaV 2 :|-:  SS (phin 1 .=>. phin 2) :-: DeltaV 1 :-: DeltaV 2
         coreConclusionOf NegL = SA (lneg $ phin 1) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf NegR =  GammaV 1 :|-: SS (lneg $ phin 1) :-: DeltaV 1
         coreConclusionOf Rep =  GammaV 1 :|-: DeltaV 1 
         coreConclusionOf Cut =  GammaV 1 :+: GammaV 2 :|-: DeltaV 1 :-: DeltaV 2
         coreConclusionOf Ax =  GammaV 1 :+: SA (phin 1) :|-: SS (phin 1) :-: DeltaV 1 

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference GentzenPropLJ lex (Form Bool) where
         corePremisesOf (LJ x) = corePremisesOf x

         coreConclusionOf (LJ x) = coreConclusionOf x

         coreRestriction x = Just $ \sub -> monoConsequent (applySub sub $ coreConclusionOf x)
             where monoConsequent :: forall lex . Eq (ClassicalSequentOver lex (Form Bool)) => ClassicalSequentOver lex (Sequent (Form Bool)) -> Maybe String
                   monoConsequent (_:|-:x)= case nub (toListOf concretes x :: [ClassicalSequentOver lex (Form Bool)]) of
                                              _:_:xs -> Just "LJ requires that the right hand side of each sequent contain at most one formula"
                                              _ -> Nothing

gentzenPropLKCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLK
gentzenPropLKCalc = TableauCalc 
    { tbParseForm = langParser
    , tbParseRule = parseGentzenPropLK
    }

gentzenPropLJCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLJ
gentzenPropLJCalc = TableauCalc 
    { tbParseForm = langParser
    , tbParseRule = parseGentzenPropLJ
    }
