{-#LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic (parsePropLogic, parsePropProof, DerivedRule(..)) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Languages.ClassicalSequent.Syntax

data DerivedRule = DerivedRule { conclusion :: PureForm, premises :: [PureForm]}
               deriving Show

data PropLogic = MP | MT | DNE | DNI | DD | AX | CP1 | CP2 | ID1 | ID2 | ID3 | ID4 | DER DerivedRule
               deriving Show

instance Inference PropLogic PurePropLexicon where
    premisesOf MP  = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
                     , GammaV 2 :|-: SS (SeqPhi 1)
                     ]
    premisesOf MT  = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
                     , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf AX  = []
    premisesOf DD  = [ GammaV 1 :|-: SS (SeqPhi 1) ]
    premisesOf DNE = [ GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) ]
    premisesOf DNI = [ GammaV 1 :|-: SS (SeqPhi 1) ]
    premisesOf CP1 = [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) ]
    premisesOf CP2 = [ GammaV 1 :|-: SS (SeqPhi 2) ]
    premisesOf ID1 = [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                     , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf ID2 = [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                     , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf ID3 = [ GammaV 1  :|-: SS (SeqPhi 2) 
                     , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf ID4 = [ GammaV 1  :|-: SS (SeqPhi 2) 
                     , GammaV 2  :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf (DER r) = zipWith gammafy (premises r) [1..]
        where gammafy p n = GammaV n :|-: SS (liftToSequent p)

    conclusionOf MP  = (GammaV 1 :+: GammaV 2) :|-: SS (SeqPhi 2)
    conclusionOf MT  = (GammaV 1 :+: GammaV 2) :|-: SS (SeqNeg $ SeqPhi 1)
    conclusionOf AX  = SA (SeqPhi 1) :|-: SS (SeqPhi 1)
    conclusionOf DD  = GammaV 1 :|-: SS (SeqPhi 1) 
    conclusionOf DNE = GammaV 1 :|-: SS (SeqPhi 1) 
    conclusionOf DNI = GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) 
    conclusionOf CP1 = GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2) 
    conclusionOf CP2 = GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
    conclusionOf ID1 = GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
    conclusionOf ID2 = GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
    conclusionOf ID3 = GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
    conclusionOf ID4 = GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
    conclusionOf (DER r) = gammas :|-: SS (liftToSequent $ conclusion r)
        where gammas = foldl (:+:) Top (map GammaV [1..length (premises r)])

parsePropLogic :: Map String DerivedRule -> Parsec String u [PropLogic]
parsePropLogic ders = do r <- choice (map (try . string) ["AS","PR","MP","MT","DD","DNE","DNI", "DN", "CD", "ID", "D-"])
                         case r of
                             "AS"   -> return [AX]
                             "PR"   -> return [AX]
                             "MP"   -> return [MP]
                             "MT"   -> return [MT]
                             "DD"   -> return [DD]
                             "DNE"  -> return [DNE]
                             "DNI"  -> return [DNI]
                             "DN"   -> return [DNE,DNI]
                             "CD"   -> return [CP1,CP2]
                             "ID"   -> return [ID1,ID2,ID3,ID4]
                             "D-" -> do rn <- many1 upper
                                        case M.lookup rn ders of
                                            Just r  -> return [DER r]
                                            Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"

parsePropProof :: Map String DerivedRule -> String -> [Either ParseError (DeductionLine PropLogic PurePropLexicon (Form Bool))]
parsePropProof ders = toDeduction (parsePropLogic ders) prePurePropFormulaParser
