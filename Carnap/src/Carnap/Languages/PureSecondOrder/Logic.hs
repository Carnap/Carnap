{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureSecondOrder.Logic where

import Carnap.Core.Data.Util (mapover)
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.GenericConnectives
import Carnap.Languages.Util.LanguageClasses
import Carnap.Calculi.NaturalDeduction.Syntax
import Data.List (intercalate)
import Data.Typeable (Typeable)
import Carnap.Core.Data.Util (scopeHeight)

---------------------------------------
--  1.Second Order Sequent Calculus  --
---------------------------------------

type MSOLSequentCalc = ClassicalSequentOver MonadicallySOLLex

pattern SeqQuant q        = FX (Lx2 (Lx1 (Lx1 (Lx2 (Bind q)))))
pattern SeqSOMQuant q     = FX (Lx2 (Lx3 (Bind q)))
pattern SeqAbst a         = FX (Lx2 (Lx4 (Abstract a)))
-- pattern SeqSV n           = FX (Lx2 (Lx1 (Lx1 (Lx4 (StaticVar n)))))
-- pattern SeqVar c a        = FX (Lx2 (Lx1 (Lx4 (Function c a))))
-- pattern SeqTau c a        = FX (Lx2 (Lx1 (Lx5 (Function c a))))
-- pattern SeqV s            = SeqVar (Var s) AZero
-- pattern SeqT n            = SeqTau (SFunc AZero n) AZero

seqv :: String -> MSOLSequentCalc (Term Int)
seqv x = liftToSequent $ SOV x

seqsov :: String -> MSOLSequentCalc (Form (Int -> Bool))
seqsov x = liftToSequent $ SOMVar x

instance CopulaSchema MSOLSequentCalc where 

    appSchema (SeqQuant (All x)) (LLam f) e = 
        schematize (All x) (show (f $ seqv x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = 
        schematize (Some x) (show (f $ seqv x) : e)
    appSchema (SeqSOMQuant (SOAll x)) (LLam f) e = 
        schematize (SOAll x) (show (f $ seqsov x) : e)
    appSchema (SeqSOMQuant (SOSome x)) (LLam f) e = 
        schematize (SOSome x) (show (f $ seqsov x) : e)
    appSchema (SeqAbst (SOLam v)) (LLam f) e = 
        schematize (SOLam v) (show (f $ (seqv v)) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f $ liftToSequent $ SOSV (-1 * h))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f $ liftToSequent $ SOSV (-1 * h)) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

data MSOLogic = ABS | APP | SOUI | SOEG
              deriving (Show,Eq)

ss :: MonadicallySOL (Form Bool) -> MSOLSequentCalc Succedent
ss = SS . liftToSequent

sa :: MonadicallySOL (Form Bool) -> MSOLSequentCalc Antecedent
sa = SA . liftToSequent

phi :: Int -> MonadicallySOL (Term Int) -> MonadicallySOL (Form Bool)
phi n x = SOPhi n AOne AOne :!$: x

tau :: MonadicallySOL (Term Int)
tau = SOT 0

apply l t = SOMApp SOApp :!$: l :!$: t

-- | produces a schematic formula abstracting n terms from a given formula
lambdaScheme :: Int -> MonadicallySOL (Form Bool)
lambdaScheme n = ls' n n
        where v n = SOV $ "v_" ++ show n
              phi n | n < 1 = SOPhi 1 AOne AOne
                    | n > 0 = case incBody (phi (n - 1))  of
                                  Just p' -> mapover bump p' :!$: v 0 
                                  Nothing -> error "trouble in lambdaScheme algorithm"
              ls' n m | n < 1 = SOMApp SOApp :!$: incLam 0 (mapover bump (phi m) :!$: v 0) (v 0) :!$: SOT 0
                      | n > 0 = SOMApp SOApp :!$: incLam n (ls' (n - 1) m) (v n) :!$: SOT n
              bump (SOV s) = SOV $ "v_" ++ show (((read $ drop 2 s) :: Int) + 1)
              bump x = x

-- | produces an n-ary schematic predicate with n schematic terms for
-- arguments
predScheme :: Int -> MonadicallySOL (Form Bool)
predScheme n = phi n :!$: SOT n
        where phi n | n < 1 = SOPhi 1 AOne AOne
                    | n > 0 = case incBody (phi (n - 1)) of
                                   Just p' -> p' :!$: SOT (n - 1)
                                   Nothing -> error "trouble in predScheme algorithm"

instance Inference MSOLogic MonadicallySOLLex where
        premisesOf ABS  = [GammaV 1 :|-: ss (predScheme 0)]
        premisesOf APP  = [GammaV 1 :|-: ss (lambdaScheme 0)]
        premisesOf SOUI = [GammaV 1 :|-: ss (SOMBind (SOAll "v") (\x -> SOMCtx 1 :!$: (apply x tau)))]
        premisesOf SOEG = [GammaV 1 :|-: ss (SOMCtx 1 :!$: (apply (SOMScheme 1) tau))]

        conclusionOf ABS  = GammaV 1 :|-: ss (lambdaScheme 0)
        conclusionOf APP  = GammaV 1 :|-: ss (predScheme 0)
        conclusionOf SOUI = GammaV 1 :|-: ss (SOMCtx 1 :!$: (apply (SOMScheme 1) tau))
        conclusionOf SOEG = GammaV 1 :|-: ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: (apply x tau)))
