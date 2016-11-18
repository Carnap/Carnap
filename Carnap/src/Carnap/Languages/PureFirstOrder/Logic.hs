{-#LANGUAGE GADTs, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic
        ( parseFOLLogic, parseFOLProof, folSeqParser, phiS, phi, tau, ss, FOLSequentCalc)
    where

import Data.Map as M (lookup, Map)
import Data.List (intercalate)
import Text.Parsec
import Carnap.Core.Data.Util (scopeHeight)
--import Carnap.Core.Util
import Carnap.Core.Unification.Unification
--import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.GenericConnectives

--------------------------------------------------------
--1. FirstOrder Sequent Calculus
--------------------------------------------------------

type FOLSequentCalc = ClassicalSequentOver PureLexiconFOL

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema FOLSequentCalc where 

    appSchema (SeqQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SeqV x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SeqV x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

pattern SeqQuant q        = FX (Lx2 (Lx1 (Lx2 (Bind q))))
pattern SeqSV n           = FX (Lx2 (Lx1 (Lx3 (StaticVar n))))
pattern SeqDV n           = FX (Lx2 (Lx1 (Lx3 (SubVar n))))
pattern SeqPred x arity   = FX (Lx2 (Lx2 (Lx1 (Predicate x arity))))
pattern SeqSPred x arity  = FX (Lx2 (Lx2 (Lx2 (Predicate x arity))))
pattern SeqCon x arity    = FX (Lx2 (Lx1 (Lx1 (Connective x arity))))
pattern SeqEq             = FX (Lx2 (Lx3 (Lx1 (Predicate TermEq ATwo))))
pattern SeqFunc x arity   = FX (Lx2 (Lx3 (Lx2 (Function x arity))))
pattern SeqConst c a      = FX (Lx2 (Lx1 (Lx4 (Function c a))))
pattern SeqVar c a        = FX (Lx2 (Lx1 (Lx5 (Function c a))))
pattern SeqTau c a        = FX (Lx2 (Lx1 (Lx6 (Function c a))))
pattern SeqP n a1 a2      = SeqPred (Pred a1 n) a2
pattern SeqPhi n a1 a2    = SeqSPred (SPred a1 n) a2
pattern SeqAnd            = SeqCon And ATwo
pattern SeqOr             = SeqCon Or ATwo
pattern SeqIf             = SeqCon If ATwo
pattern SeqIff            = SeqCon Iff ATwo
pattern SeqNot            = SeqCon Not AOne
pattern SeqC n            = SeqConst (Constant n) AZero
pattern SeqV s            = SeqVar (Var s) AZero
pattern SeqT n            = SeqTau (SFunc AZero n) AZero

instance Eq (FOLSequentCalc a) where
        (==) = (=*)

instance Sequentable PureLexiconFOL where
    liftToSequent (x :!$: y)      = (liftToSequent x :!$: liftToSequent y)
    liftToSequent (LLam f)        = LLam (liftToSequent . f . fromSequent)
    liftToSequent (PP n a1 a2)    = SeqP n a1 a2
    liftToSequent (PPhi n a1 a2)  = SeqPhi n a1 a2
    liftToSequent PAnd            = SeqAnd
    liftToSequent POr             = SeqOr
    liftToSequent PIf             = SeqIf
    liftToSequent PIff            = SeqIff
    liftToSequent PNot            = SeqNot
    liftToSequent (PQuant q)      = SeqQuant q
    liftToSequent (PC n)          = SeqC n
    liftToSequent (PV s)          = SeqV s
    liftToSequent (PT n)          = SeqT n
    liftToSequent (PSV n)         = SeqSV n
    liftToSequent (PDV n)         = SeqDV n
    liftToSequent (PFunc x a)     = SeqFunc x a
    liftToSequent PEq             = SeqEq

    fromSequent (x :!$: y)       = (fromSequent x :!$: fromSequent y)
    fromSequent (LLam f)         = LLam (fromSequent . f . liftToSequent)
    fromSequent (SeqP n a1 a2)   = PP n a1 a2
    fromSequent (SeqPhi n a1 a2) = PPhi n a1 a2
    fromSequent SeqAnd           = PAnd
    fromSequent SeqOr            = POr
    fromSequent SeqIf            = PIf
    fromSequent SeqIff           = PIff
    fromSequent SeqNot           = PNot
    fromSequent (SeqQuant q)     = PQuant q
    fromSequent (SeqC n)         = PC n
    fromSequent (SeqV s)         = PV s
    fromSequent (SeqT n)         = PT n
    fromSequent (SeqFunc x a)    = PFunc x a
    fromSequent SeqEq            = PEq
    fromSequent (SeqDV n)       = PDV n
    fromSequent (SeqSV n)       = PSV n
    fromSequent x                = error ("fromSequent can't handle " ++ show x)

data FOLogic = MP | MT  | DNE | DNI | DD   | AX 
                  | CP1 | CP2 | ID1 | ID2  | ID3  | ID4 
                  | ADJ | S1  | S2  | ADD1 | ADD2 | MTP1 | MTP2 | BC1 | BC2 | CB  
                  | UD  | UI  | EG  | ED1  | ED2
               deriving Show

instance ParsableLex (Form Bool) PureLexiconFOL where
        langParser = folFormulaParser

folSeqParser = seqFormulaParser :: Parsec String u (FOLSequentCalc Sequent)

--------------------------------------------------------
--2. Classical First-Order Logic
--------------------------------------------------------

ss :: PureLanguageFOL (Form Bool) -> FOLSequentCalc Succedent
ss = SS . liftToSequent

sa :: PureLanguageFOL (Form Bool) -> FOLSequentCalc Antecedent
sa = SA . liftToSequent

phiS n = PPhi n AZero AZero

phi n x = PPhi n AOne AOne :!$: x

tau = PT 1

instance Inference FOLogic PureLexiconFOL where
     premisesOf MP    = [ GammaV 1 :|-: ss (phiS 1 :->: phiS 2)
                        , GammaV 2 :|-: ss (phiS 1)
                        ]
     premisesOf MT    = [ GammaV 1 :|-: ss (phiS 1 :->: phiS 2)
                        , GammaV 2 :|-: ss (PNeg $ phiS 2)
                        ]
     premisesOf AX    = []
     premisesOf DD    = [ GammaV 1 :|-: ss (phiS 1) ]
     premisesOf DNE   = [ GammaV 1 :|-: ss (PNeg $ PNeg $ phiS 1) ]
     premisesOf DNI   = [ GammaV 1 :|-: ss (phiS 1) ]
     premisesOf CP1   = [ GammaV 1 :+: sa (phiS 1) :|-: ss (phiS 2) ]
     premisesOf CP2   = [ GammaV 1 :|-: ss (phiS 2) ]
     premisesOf ID1   = [ GammaV 1 :+: sa (phiS 1) :|-: ss (phiS 2) 
                        , GammaV 2 :+: sa (phiS 1) :|-: ss (PNeg $ phiS 2)
                        ]
     premisesOf ID2   = [ GammaV 1 :+: sa (phiS 1) :|-: ss (phiS 2) 
                        , GammaV 2 :|-: ss (PNeg $ phiS 2)
                        ]
     premisesOf ID3   = [ GammaV 1  :|-: ss (phiS 2) 
                        , GammaV 2 :+: sa (phiS 1) :|-: ss (PNeg $ phiS 2)
                        ]
     premisesOf ID4   = [ GammaV 1  :|-: ss (phiS 2) 
                        , GammaV 2  :|-: ss (PNeg $ phiS 2)
                        ]
     premisesOf ADJ   = [ GammaV 1  :|-: ss (phiS 1) 
                        , GammaV 2  :|-: ss (phiS 2)
                        ]
     premisesOf S1    = [ GammaV 1  :|-: ss (phiS 1 :&: phiS 2) ]
     premisesOf S2    = [ GammaV 1  :|-: ss (phiS 1 :&: phiS 2) ]
     premisesOf ADD1  = [ GammaV 1  :|-: ss (phiS 1) ]
     premisesOf ADD2  = [ GammaV 1  :|-: ss (phiS 1) ]
     premisesOf MTP1  = [ GammaV 1  :|-: ss (PNeg $ phiS 1) 
                        , GammaV 2  :|-: ss (phiS 1 :||: phiS 2)
                        ]
     premisesOf MTP2  = [ GammaV 1  :|-: ss (PNeg $ phiS 1) 
                        , GammaV 2  :|-: ss (phiS 2 :||: phiS 1)
                        ]
     premisesOf BC1   = [ GammaV 1  :|-: ss (phiS 1 :<->: phiS 2) ]
     premisesOf BC2   = [ GammaV 1  :|-: ss (phiS 1 :<->: phiS 2) ]
     premisesOf CB    = [ GammaV 1  :|-: ss (phiS 1 :->: phiS 2)
                        , GammaV 2  :|-: ss (phiS 2 :->: phiS 1) ]
     premisesOf UI    = [ GammaV 1  :|-: ss (PBind (All "v") (phi 1))]
     premisesOf EG    = [ GammaV 1 :|-: ss (phi 1 tau)]
     -- XXX : need eigenvariable constraint for these
     premisesOf UD    = [ GammaV 1 :|-: ss (phi 1 tau)]
     premisesOf ED1   = [ GammaV 1 :+:  sa (phi 1 tau) :|-: ss (phiS 1)
                        , GammaV 2 :|-: ss (PBind (Some "v") $ phi 1)
                        , sa (phi 1 tau) :|-: ss (phi 1 tau)]
     premisesOf ED2   = [ GammaV 1 :|-: ss (phiS 1)
                        , sa (phi 1 tau) :|-: ss (phi 1 tau)
                        , GammaV 2 :|-: ss (PBind (Some "v") $ phi 1)]

     conclusionOf MP    = (GammaV 1 :+: GammaV 2) :|-: ss (phiS 2)
     conclusionOf MT    = (GammaV 1 :+: GammaV 2) :|-: ss (PNeg $ phiS 1)
     conclusionOf AX    = sa (phiS 1) :|-: ss (phiS 1)
     conclusionOf DD    = GammaV 1 :|-: ss (phiS 1) 
     conclusionOf DNE   = GammaV 1 :|-: ss (phiS 1) 
     conclusionOf DNI   = GammaV 1 :|-: ss (PNeg $ PNeg $ phiS 1) 
     conclusionOf CP1   = GammaV 1 :|-: ss (phiS 1 :->: phiS 2) 
     conclusionOf CP2   = GammaV 1 :|-: ss (phiS 1 :->: phiS 2)
     conclusionOf ID1   = GammaV 1 :+: GammaV 2 :|-: ss (PNeg $ phiS 1)
     conclusionOf ID2   = GammaV 1 :+: GammaV 2 :|-: ss (PNeg $ phiS 1)
     conclusionOf ID3   = GammaV 1 :+: GammaV 2 :|-: ss (PNeg $ phiS 1)
     conclusionOf ID4   = GammaV 1 :+: GammaV 2 :|-: ss (PNeg $ phiS 1)
     conclusionOf ADJ   = GammaV 1 :+: GammaV 2 :|-: ss (phiS 1 :&: phiS 2)
     conclusionOf S1    = GammaV 1 :|-: ss (phiS 1)
     conclusionOf S2    = GammaV 1 :|-: ss (phiS 2)
     conclusionOf ADD1  = GammaV 1 :|-: ss (phiS 2 :||: phiS 1)
     conclusionOf ADD2  = GammaV 1 :|-: ss (phiS 1 :||: phiS 2)
     conclusionOf MTP1  = GammaV 1 :+: GammaV 2 :|-: ss (phiS 2)
     conclusionOf MTP2  = GammaV 1 :+: GammaV 2 :|-: ss (phiS 2)
     conclusionOf BC1   = GammaV 1 :|-: ss (phiS 2 :->: phiS 1)
     conclusionOf BC2   = GammaV 1 :|-: ss (phiS 1 :->: phiS 2)
     conclusionOf CB    = GammaV 1 :+: GammaV 2 :|-: ss (phiS 1 :<->: phiS 2)
     conclusionOf UI    = GammaV 1 :|-: ss (phi 1 tau)
     conclusionOf EG    = GammaV 1  :|-: ss (PBind (Some "v") (phi 1))
     conclusionOf UD    = GammaV 1  :|-: ss (PBind (All "v") (phi 1))
     conclusionOf ED1   = GammaV 1 :+: GammaV 2 :|-: ss (phiS 1)
     conclusionOf ED2   = GammaV 1 :+: GammaV 2 :|-: ss (phiS 1)

     restriction UD     = Just (eigenConstraint (SeqT 1) (ss $ PBind (All "v") $ phi 1) (GammaV 1))
     restriction ED1    = Just (eigenConstraint (SeqT 1) ((ss $ PBind (Some "v") $ phi 1) :-: (ss $ phiS 1)) (GammaV 1 :+: GammaV 2))
     restriction ED2    = Nothing --Since this one does not use the assumption with a fresh object
     restriction _      = Nothing

eigenConstraint c suc ant sub
    | c' `occursIn` ant' = Just $ "The constant " ++ show c' ++ " appears not to be fresh, given that this line relies on " ++ show ant'
    | c' `occursIn` suc' = Just $ "The constant " ++ show c' ++ " appears not to be fresh in the other premise " ++ show suc'
    | otherwise = Nothing
    where c'   = applySub sub c
          ant' = applySub sub ant
          suc' = applySub sub suc
          -- XXX : this is not the most efficient way of checking
          -- imaginable.
          occursIn x y = not $ (subst x (static 0) y) =* y

parseFOLLogic :: Parsec String u [FOLogic]
parseFOLLogic = do r <- choice (map (try . string) ["AS","PR","MP","MTP","MT","DD","DNE","DNI", "DN", "S", "ADJ",  "ADD" , "BC", "CB",  "CD", "ID", "UI", "UD", "EG", "ED"])
                   case r of "AS"   -> return [AX]
                             "PR"   -> return [AX]
                             "MP"   -> return [MP]
                             "MT"   -> return [MT]
                             "DD"   -> return [DD]
                             "DNE"  -> return [DNE]
                             "DNI"  -> return [DNI]
                             "DN"   -> return [DNE,DNI]
                             "CD"   -> return [CP1,CP2]
                             "ID"   -> return [ID1,ID2,ID3,ID4]
                             "ADJ"  -> return [ADJ]
                             "S"    -> return [S1, S2]
                             "ADD"  -> return [ADD1, ADD2]
                             "MTP"  -> return [MTP1, MTP2]
                             "BC"   -> return [BC1, BC2]
                             "CB"   -> return [CB]
                             "UI"   -> return [UI]
                             "UD"   -> return [UD]
                             "EG"   -> return [EG]
                             "ED"   -> return [ED1,ED2]

parseFOLProof ::  String -> [Either ParseError (DeductionLine FOLogic PureLexiconFOL (Form Bool))]
parseFOLProof = toDeduction parseFOLLogic folFormulaParser
