{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureSecondOrder.Logic.Rules where

import Carnap.Core.Data.Util (scopeHeight,mapover)
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureSecondOrder.Parser
import Carnap.Languages.ClassicalSequent.Parser
import Data.List (intercalate)
import Data.Typeable (Typeable)


---------------------------------------
--  1.Second Order Sequent Calculus  --
---------------------------------------

------------------------------------------
--  1.1 Monadically Second Order Logic  --
------------------------------------------

type MSOLSequentCalc = ClassicalSequentOver MonadicallySOLLex

pattern SeqQuant q        = FX (Lx2 (Lx1 (Lx1 (Lx2 (Bind q)))))
pattern SeqSOMQuant q     = FX (Lx2 (Lx3 (Bind q)))
pattern SeqAbst a         = FX (Lx2 (Lx4 (Abstract a)))
-- pattern SeqSV n           = FX (Lx2 (Lx1 (Lx1 (Lx4 (StaticVar n)))))
-- pattern SeqVar c a        = FX (Lx2 (Lx1 (Lx4 (Function c a))))
-- pattern SeqV s            = SeqVar (Var s) AZero

instance ParsableLex (Form Bool) MonadicallySOLLex where
        langParser = msolFormulaParser

instance CopulaSchema MSOLSequentCalc where 

    appSchema (SeqQuant (All x)) (LLam f) e = 
        schematize (All x) (show (f $ seqv x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = 
        schematize (Some x) (show (f $ seqv x) : e)
    appSchema (SeqSOMQuant (SOAll x)) (LLam f) e = 
        schematize (SOAll x) (show (f $ seqsomv x) : e)
    appSchema (SeqSOMQuant (SOSome x)) (LLam f) e = 
        schematize (SOSome x) (show (f $ seqsomv x) : e)
    appSchema (SeqAbst (SOLam v)) (LLam f) e = 
        schematize (SOLam v) (show (f $ seqv v) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f $ liftToSequent $ SOSV (-1 * h))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f $ liftToSequent $ SOSV (-1 * h)) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

-- TODO unify the different kinds of eigenconstrants 
eigenConstraint c suc ant sub
    | c' `occursIn` ant' = Just $ "The constant " ++ show c' ++ " appears not to be fresh, given that this line relies on " ++ show ant'
    | c' `occursIn` suc' = Just $ "The constant " ++ show c' ++ " appears not to be fresh in the other premise " ++ show suc'
    | otherwise = case fromSequent c' of 
                          SOC _ -> Nothing
                          SOT _ -> Nothing
                          _ -> Just $ "The term " ++ show c' ++ " is not a constant"
    where c' = applySub sub c
          ant' = applySub sub ant
          suc' = applySub sub suc
          occursIn x y = not $ (subst x (static 0) y) =* y

sopredicateEigenConstraint c suc ant sub
    | c' `occursIn` ant' = Just $ "The predicate " ++ show c' ++ " appears not to be fresh, given that this line relies on " ++ show ant'
    | c' `occursIn` suc' = Just $ "The predicate " ++ show c' ++ " appears not to be fresh in the other premise " ++ show suc'
    | otherwise = if msolVarHead (fromSequent c') 
                      then Nothing
                      else Just $ "the expression " ++ show c' ++ " appears not to be a variable predication."

    where c'   = applySub sub c
          ant' = applySub sub ant
          suc' = applySub sub suc
          -- XXX : this is not the most efficient way of checking
          -- imaginable.
          occursIn x y = not $ (subst x (static 0) y) =* y

psopredicateEigenConstraint c suc ant sub
    | c' `occursIn` ant' = Just $ "The predicate " ++ show c' ++ " appears not to be fresh, given that this line relies on " ++ show ant'
    | c' `occursIn` suc' = Just $ "The predicate " ++ show c' ++ " appears not to be fresh in the other premise " ++ show suc'
    | otherwise = if psolVarHead (fromSequent c') 
                      then Nothing
                      else Just $ "the expression " ++ show c' ++ " appears not to be a predicate."

    where c'   = applySub sub c
          ant' = applySub sub ant
          suc' = applySub sub suc
          occursIn x y = not $ (subst x (static 0) y) =* y

-------------------------------------------
--  1.2 Polyadically Second Order Logic  --
-------------------------------------------

type PSOLSequentCalc = ClassicalSequentOver PolyadicallySOLLex

pattern SeqSOPQuant q     = FX (Lx2 (Lx3 (Bind q)))

instance ParsableLex (Form Bool) PolyadicallySOLLex where
        langParser = psolFormulaParser

instance CopulaSchema PSOLSequentCalc where 

    appSchema (SeqQuant (All x)) (LLam f) e = 
        schematize (All x) (show (f $ seqv x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = 
        schematize (Some x) (show (f $ seqv x) : e)
    appSchema (SeqSOPQuant (SOPAll x a)) (LLam f) e = 
        schematize (SOPAll x a) (show (f $ seqsopv x a) : e)
    appSchema (SeqSOPQuant (SOPSome x a)) (LLam f) e = 
        schematize (SOPSome x a) (show (f $ seqsopv x a) : e)
    appSchema (SeqAbst (SOLam v)) (LLam f) e = 
        schematize (SOLam v) (show (f $ seqv v) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f $ liftToSequent $ SOSV (-1 * h))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f $ liftToSequent $ SOSV (-1 * h)) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

------------------------
--  1.3 Common Rules  --
------------------------

---------------------
--  1.3.1 Monadic  --
---------------------

monadicAbstraction = [ GammaV 1 :|-: ss (predScheme 0)] 
                     ∴ GammaV 1 :|-: ss (SOMApp SOApp :!$: (SOAbstract (SOLam "v") (\x -> SOPhi 1 AOne AOne :!$: x)) :!$: SOT 0)

monadicApplication = [ GammaV 1 :|-: ss (SOMApp SOApp :!$: (SOAbstract (SOLam "v") (\x -> SOPhi 1 AOne AOne :!$: x)) :!$: SOT 0)] 
                     ∴ GammaV 1 :|-: ss (predScheme 0)

monadicUniversalInstantiation = [ GammaV 1 :|-: ss (SOMBind (SOAll "v") (\x -> SOMCtx 1 :!$: x))] 
                                ∴ GammaV 1 :|-: ss (SOMCtx 1 :!$: SOMScheme 1)

monadicExistentialGeneralization = [ GammaV 1 :|-: ss (SOMCtx 1 :!$: SOMScheme 1)] 
                                   ∴ GammaV 1 :|-: ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))

monadicUniversalDerivation = [ GammaV 1 :|-: ss (SOMCtx 1 :!$: SOMScheme 1)] 
                             ∴ GammaV 1 :|-: ss (SOMBind (SOAll "v") (\x -> SOMCtx 1 :!$: x))

---------------------
--  1.3.2 Polyadic --
---------------------

polyadicAbstraction n = [ GammaV 1 :|-: ss' (predScheme (n - 1))] 
                        ∴ GammaV 1 :|-: ss' (lambdaScheme (n - 1))

polyadicApplication n = [ GammaV 1 :|-: ss' (lambdaScheme (n - 1))]
                        ∴  GammaV 1 :|-: ss' (predScheme (n - 1))

polyadicUniversalInstantiation n = [ GammaV 1 :|-: ss' (universalScheme n)]
                                   ∴ GammaV 1 :|-: ss' (schematicContextScheme n)

polyadicUniversalDerivation n = [ GammaV 1 :|-: ss' (schematicContextScheme n)]
                                ∴ GammaV 1 :|-: ss' (universalScheme n)

polyadicExistentialGeneralization n = [ GammaV 1 :|-: ss' (schematicContextScheme n)]
                                      ∴ GammaV 1 :|-: ss' (existentialScheme n)

---------------------------------
--  1.3 Rules With Variations  --
---------------------------------

--------------------
-- 1.3.1 Monadic  --
--------------------


monadicExistentialDerivation = [
                                    [ GammaV 1 :+: sa (SOMCtx 1 :!$: SOMScheme 1) :|-: ss phiS
                                    , GammaV 2 :|-: ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))
                                    ] ∴ GammaV 1 :+: GammaV 2 :|-: ss phiS
                               ,    [ GammaV 1 :|-: ss phiS
                                    , GammaV 2 :|-: ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))
                                    ] ∴ GammaV 1 :+: GammaV 2 :|-: ss phiS
                               ]
                               
--------------------
-- 1.3.2 Polyadic --
--------------------

polyadicExistentialDerivation n = [
                                    [ GammaV 1 :+: sa' (schematicContextScheme n) :|-: ss' phiSp
                                    , GammaV 2 :|-: ss' (existentialScheme n)
                                    ] ∴ GammaV 1 :+: GammaV 2 :|-: ss' phiSp
                                  , [ GammaV 1 :|-: ss' phiSp
                                    , GammaV 2 :|-: ss' (existentialScheme n)
                                    ] ∴ GammaV 1 :+: GammaV 2 :|-: ss' phiSp
                                  ]

---------------------------
--  2. Helper Functions  --
---------------------------

ss :: MonadicallySOL (Form Bool) -> MSOLSequentCalc (Succedent (Form Bool))
ss = SS . liftToSequent

sa :: MonadicallySOL (Form Bool) -> MSOLSequentCalc (Antecedent (Form Bool))
sa = SA . liftToSequent

ss' :: PolyadicallySOL (Form Bool) -> PSOLSequentCalc (Succedent (Form Bool))
ss' = SS . liftToSequent

sa' :: PolyadicallySOL (Form Bool) -> PSOLSequentCalc (Antecedent (Form Bool))
sa' = SA . liftToSequent

tau :: MonadicallySOL (Term Int)
tau = SOT 1

taup :: PolyadicallySOL (Term Int)
taup = SOT 1

phiS ::  MonadicallySOL (Form Bool)
phiS = SOPhi 1 AZero AZero

phiSp ::  PolyadicallySOL (Form Bool)
phiSp = SOPhi 1 AZero AZero

seqv x = liftToSequent $ SOV x

apply l t = SOMApp SOApp :!$: l :!$: t

applySOP l t = SOPApp SOApp :!$: l :!$: t

-- | produces an n-ary schematic predicate with n schematic terms for
-- arguments
predScheme n = phi n :!$: SOT n
        where phi n | n < 1 = SOPhi 1 AOne AOne
                    | n > 0 = case incBody (phi (n - 1)) of
                                   Just p' -> p' :!$: SOT (n - 1)
                                   Nothing -> error "trouble in predScheme algorithm"
                                   --
-- | produces an n-ary schematic applicator with n schematic terms for
-- arguments
psolAppScheme ::  Int -> PolyadicallySOL (Form Bool)
psolAppScheme n = (SOPApp SOApp :!$: phi n) :!$: SOT n
        where phi :: Int -> PolyadicallySOL (Form (Int -> Bool))
              phi n | n < 1 = SOPScheme 1 AOne
                    | n > 0 = (SOPApp SOApp :!$: incScheme (phi (n - 1))) :!$: SOT (n - 1)

seqsomv :: String -> MSOLSequentCalc (Form (Int -> Bool))
seqsomv x = liftToSequent $ SOMVar x

seqsopv :: Typeable t => String -> Arity Int Bool n t -> PSOLSequentCalc (Form t)
seqsopv x a = liftToSequent $ SOPVar x a

-- | produces a schematic formula abstracting n terms from a given formula
lambdaScheme :: Int -> PolyadicallySOL (Form Bool)
lambdaScheme n = ls' n n
        where v n = SOV $ "v_" ++ show n
              phi n | n < 1 = SOPhi 1 AOne AOne
                    | n > 0 = case incBody (phi (n - 1))  of
                                  Just p' -> mapover bump p' :!$: v 0 
                                  Nothing -> error "trouble in lambdaScheme algorithm"
              ls' n m | n < 1 = SOPApp SOApp :!$: incLam 0 (mapover bump (phi m) :!$: v 0) (v 0) :!$: SOT 0
                      | n > 0 = SOPApp SOApp :!$: incLam n (ls' (n - 1) m) (v n) :!$: SOT n
              bump (SOV s) = SOV $ "v_" ++ show (((read $ drop 2 s) :: Int) + 1)
              bump x = x

-- | produces a universal instantiation premise instance for n-adic variables
universalScheme :: Int -> PolyadicallySOL (Form Bool)
universalScheme n = iterate incQuant (SOPQuant (SOPAll ('V' : show n) (AZero)) :!$: LLam (theNthCtx)) !! n
    where theNthCtx x = subBoundVar (SOPVar ('X' : show n) AZero) x (iterate incVarCtx initCtx !! n)
          initCtx = SOPCtx 1 AZero :!$: (SOPVar ('V' : show n) AZero)

-- | produces a existential generalization conclusion instance for n-adic variables
existentialScheme :: Int -> PolyadicallySOL (Form Bool)
existentialScheme n = iterate incQuant (SOPQuant (SOPSome ('V' : show n) (AZero)) :!$: LLam (theNthCtx)) !! n
    where theNthCtx x = subBoundVar (SOPVar ('X' : show n) AZero) x (iterate incVarCtx initCtx !! n)
          initCtx = SOPCtx 1 AZero :!$: (SOPVar ('V' : show n) AZero)

-- | produces a universal instantiation conclusion instance for n-adic variables
schematicContextScheme :: Int -> PolyadicallySOL (Form Bool)
schematicContextScheme n = iterate incSchemeCtx initCtx !! n
    where initCtx = SOPCtx 1 AZero :!$: (SOPScheme 1 AZero)
