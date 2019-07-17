{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Gentzen
    ( parseGentzenPropLK, gentzenPropLKCalc, GentzenPropLK(..)) where

import Text.Parsec
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.Util
import Carnap.Languages.Util.LanguageClasses

data GentzenPropLK = Ax | AndL1 | AndL2 | AndR
                        | OrR1  | OrR2  | OrL
                        | CondR | CondL
                        | NegR  | NegL

instance Show GentzenPropLK where
    show Ax     = "Ax"
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

parseGentzenPropLK :: Parsec String u GentzenPropLK
parseGentzenPropLK =  do r <- choice (map (try . string) [ "Ax", "R&","R∧","R/\\"
                                                         ,"L&1","L∧1","L/\\1"
                                                         ,"L&2","L∧2","L/\\2"
                                                         , "L∨","Lv","L\\/"
                                                         ,"R∨1","Rv1","R\\/1"
                                                         ,"R∨2","Rv2","R\\/2"
                                                         , "L→","LC","L->"
                                                         , "R→","RC","R->"
                                                         , "L¬","L~","L-"
                                                         , "R¬","R~","R-"
                                                         ])
                         return $ case r of
                            r | r == "Ax" -> Ax
                              | r `elem` ["R&","R∧","R/\\"] -> AndR
                              | r `elem` ["L&1","L∧1","L/\\1"] -> AndL1
                              | r `elem` ["L&2","L∧2","L/\\2"] -> AndL2
                              | r `elem` ["L∨","Lv","L\\/"] -> OrL
                              | r `elem` ["R∨1","Rv1","R\\/1"] -> OrR1
                              | r `elem` ["R∨2","Rv2","R\\/2"] -> OrR2
                              | r `elem` ["L→","LC","L->"] -> CondL
                              | r `elem` ["R→","RC","R->"] -> CondR
                              | r `elem` ["L¬","L~","L-"] -> NegL
                              | r `elem` ["R¬","R~","R-"] -> NegR

instance CoreInference GentzenPropLK PurePropLexicon (Form Bool) where
        corePremisesOf AndL1 = [SA (phin 1) :+: GammaV 1 :|-: DeltaV 1]
        corePremisesOf AndL2 = [SA (phin 2) :+: GammaV 1 :|-: DeltaV 1]
        corePremisesOf AndR = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1
                              , GammaV 2 :|-: SS (phin 2) :-: DeltaV 2
                              ]
        corePremisesOf OrR1 = [ GammaV 1 :|-: DeltaV 1 :-: SS(phin 1)]
        corePremisesOf OrR1 = [ GammaV 1 :|-: DeltaV 1 :-: SS(phin 2)]
        corePremisesOf OrL  = [ GammaV 1 :+: SA (phin 1) :|-: DeltaV 1
                              , GammaV 2 :+: SA (phin 1) :|-: DeltaV 2
                              ] 
        corePremisesOf CondL = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1
                               , GammaV 2 :+: SA (phin 2) :|-: DeltaV 2
                               ]
        corePremisesOf CondR = [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) :-: DeltaV 2 ]
        corePremisesOf NegL = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1 ]
        corePremisesOf NegR = [ SA (phin 1) :+: GammaV 1 :|-:  DeltaV 1 ]
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
        coreConclusionOf Ax =  GammaV 1 :+: SA (phin 1) :|-: SS (phin 1) :-: DeltaV 1 

gentzenPropLKCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLK
gentzenPropLKCalc = TableauCalc 
    { tbParseForm = langParser
    , tbParseRule = parseGentzenPropLK
    }
