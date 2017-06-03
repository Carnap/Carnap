{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureSecondOrder.Logic where

import Carnap.Core.Data.Util (scopeHeight,mapover)
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.GenericConnectives
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Logic (FOLogic(..),parseFOLogic)
import Carnap.Languages.PureSecondOrder.Parser
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLine, hoProcessLineMemo)
import Data.List (intercalate)
import Data.Map (empty)
import Data.Typeable (Typeable)
import Text.Parsec

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

data MSOLogic = ABS | APP | SOUI | SOEG | SOUD | SOED1 | SOED2 | FO FOLogic

instance Show MSOLogic where
        show ABS    = "ABS"
        show APP    = "APP"
        show SOUI   = "UI"
        show SOEG   = "EG"
        show SOUD   = "UD"
        show SOED1  = "ED"
        show SOED2  = "ED"
        show (FO x) = show x

instance Inference MSOLogic MonadicallySOLLex where
        premisesOf ABS    = [ GammaV 1 :|-: ss (predScheme 0)]
        premisesOf APP    = [ GammaV 1 :|-: ss (SOMApp SOApp :!$: (SOAbstract (SOLam "v") (\x -> SOPhi 1 AOne AOne :!$: x)) :!$: SOT 0)]
        premisesOf SOUI   = [ GammaV 1 :|-: ss (SOMBind (SOAll "v") (\x -> SOMCtx 1 :!$: x))]
        premisesOf SOEG   = [ GammaV 1 :|-: ss (SOMCtx 1 :!$: SOMScheme 1)]
        premisesOf SOUD   = [ GammaV 1 :|-: ss (SOMCtx 1 :!$: SOMScheme 1)]
        premisesOf SOED1  = [ GammaV 1 :+: sa (SOMCtx 1 :!$: SOMScheme 1) :|-: ss phiS
                            , GammaV 2 :|-: ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))
                            ]
        premisesOf SOED1  = [ GammaV 1 :+: sa (SOMCtx 1 :!$: SOMScheme 1) :|-: ss phiS
                            , GammaV 2 :|-: ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))
                            ]
        premisesOf SOED2  = [ GammaV 1 :|-: ss phiS
                            , GammaV 2 :|-: ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))
                            ]
        premisesOf (FO x) = map liftSequent (premisesOf x)

        conclusionOf ABS    = GammaV 1 :|-: ss (SOMApp SOApp :!$: (SOAbstract (SOLam "v") (\x -> SOPhi 1 AOne AOne :!$: x)) :!$: SOT 0)
        conclusionOf APP    = GammaV 1 :|-: ss (predScheme 0)
        conclusionOf SOUI   = GammaV 1 :|-: ss (SOMCtx 1 :!$: SOMScheme 1)
        conclusionOf SOEG   = GammaV 1 :|-: ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))
        conclusionOf SOUD   = GammaV 1 :|-: ss (SOMBind (SOAll "v") (\x -> SOMCtx 1 :!$: x))
        conclusionOf SOED1  = GammaV 1 :+: GammaV 2 :|-: ss phiS
        conclusionOf SOED2  = GammaV 1 :+: GammaV 2 :|-: ss phiS
        conclusionOf (FO x) = liftSequent (conclusionOf x)

        restriction SOUD     = Just (sopredicateEigenConstraint 
                                        (liftToSequent $ SOMScheme 1) 
                                        (ss (SOMBind (SOAll "v") (\x -> SOMCtx 1 :!$: x)))  
                                        (GammaV 1))

        restriction SOED1    = Just (sopredicateEigenConstraint
                                        (liftToSequent $ SOMScheme 1)
                                        (ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))
                                            :-: ss phiS)
                                        (GammaV 1 :+: GammaV 2))
        restriction (FO UD)  = Just (eigenConstraint stau 
                                        (ss $ SOBind (All "v") phi) 
                                        (GammaV 1))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent tau

        restriction (FO ED1) = Just (eigenConstraint stau 
                                        ((ss $ SOBind (Some "v") phi) :-: ss phiS) 
                                        (GammaV 1 :+: GammaV 2))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  
                  stau = liftToSequent tau
        restriction _ = Nothing

-- TODO unify the different kinds of eigenconstrants 
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

-- XXX Skipping derived rules for now.
parseMSOLogic :: Parsec String u [MSOLogic]
parseMSOLogic = try soRule <|> liftFO
    where liftFO = do r <- parseFOLogic empty
                      return (map FO r)
          soRule = do r <- choice (map (try . string) [ "UI", "UD", "EG", "ED", "ABS","APP"])
                      case r of 
                            r | r == "UI"   -> return [FO UI, SOUI]
                              | r == "UD"   -> return [SOUD, FO UD]
                              | r == "EG"   -> return [FO EG, SOEG]
                              | r == "ED"   -> return [FO ED1,FO ED2, SOED1, SOED2]
                              | r == "ABS"  -> return [ABS]
                              | r == "APP"  -> return [APP]

parseMSOLProof :: String -> [DeductionLine MSOLogic MonadicallySOLLex (Form Bool)]
parseMSOLProof = toDeduction parseMSOLogic msolFormulaParser

msolSeqParser = seqFormulaParser :: Parsec String () (MSOLSequentCalc Sequent)

msolCalc = NaturalDeductionCalc 
    { ndRenderer = MontegueStyle
    , ndParseProof = const parseMSOLProof -- XXX ignore derived rules for now
    , ndProcessLine = hoProcessLine
    , ndProcessLineMemo = Just hoProcessLineMemo
    , ndParseSeq = msolSeqParser
    }

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

data PSOLogic = ABS_PSOL Int   | APP_PSOL Int 
              | SOUI_PSOL Int  | SOEG_PSOL Int 
              | SOUD_PSOL Int  | SOED1_PSOL Int 
              | SOED2_PSOL Int | FO_PSOL FOLogic

instance Show PSOLogic where
        show (ABS_PSOL n)   = "ABS" ++ show n
        show (APP_PSOL n)   = "APP" ++ show n
        show (SOUI_PSOL n)  = "UI"  ++ show n
        show (SOEG_PSOL n)  = "EG"  ++ show n
        show (SOUD_PSOL n)  = "UD"  ++ show n
        show (SOED1_PSOL n) = "ED"  ++ show n
        show (SOED2_PSOL n) = "ED"  ++ show n
        show (FO_PSOL x) = show x

instance Inference PSOLogic PolyadicallySOLLex where
        premisesOf (ABS_PSOL n)    = [ GammaV 1 :|-: ss' (predScheme (n - 1))]
        premisesOf (APP_PSOL n)    = [ GammaV 1 :|-: ss' (lambdaScheme (n - 1))]
        premisesOf (FO_PSOL x)     = map liftSequent (premisesOf x)
        premisesOf (SOUI_PSOL n)   = [ GammaV 1 :|-: ss' (universalScheme n)]
        premisesOf (SOUD_PSOL n)   = [ GammaV 1 :|-: ss' (schematicContextScheme n)]
        premisesOf (SOEG_PSOL n)   = [ GammaV 1 :|-: ss' (schematicContextScheme n)]
        premisesOf (SOED1_PSOL n)  = [ GammaV 1 :+: sa' (schematicContextScheme n) :|-: ss' phiS
                                     , GammaV 2 :|-: ss' (existentialScheme n)
                                     ]
        premisesOf (SOED2_PSOL n)  = [ GammaV 1 :|-: ss' phiS
                                     , GammaV 2 :|-: ss' (existentialScheme n)
                                     ]

        conclusionOf (ABS_PSOL n)   = GammaV 1 :|-: ss' (lambdaScheme (n - 1))
        conclusionOf (APP_PSOL n)   = GammaV 1 :|-: ss' (predScheme (n - 1))
        conclusionOf (SOUI_PSOL n)  = GammaV 1 :|-: ss' (schematicContextScheme n)
        conclusionOf (SOUD_PSOL n)  = GammaV 1 :|-: ss' (universalScheme n)
        conclusionOf (FO_PSOL x)    = liftSequent (conclusionOf x)
        conclusionOf (SOEG_PSOL n)  = GammaV 1 :|-: ss' (existentialScheme n)
        conclusionOf (SOED1_PSOL n) = GammaV 1 :+: GammaV 2 :|-: ss' phiS
        conclusionOf (SOED2_PSOL n) = GammaV 1 :+: GammaV 2 :|-: ss' phiS

        restriction (SOUD_PSOL n)  = Just (psopredicateEigenConstraint 
                                          (liftToSequent $ psolAppScheme (n - 1)) 
                                          -- XXX would be better to use
                                          -- contexts alone in line above
                                          (ss' $ universalScheme n)  
                                          (GammaV 1))

        restriction (SOED1_PSOL n)  = Just (psopredicateEigenConstraint 
                                           (liftToSequent $ psolAppScheme (n - 1)) 
                                           (ss' $ existentialScheme n)  
                                           (GammaV 1 :+: GammaV 2))

        restriction (FO_PSOL UD)  = Just (eigenConstraint stau 
                                        (ss' $ SOBind (All "v") phi) 
                                        (GammaV 1))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent tau

        restriction (FO_PSOL ED1) = Just (eigenConstraint stau 
                                        ((ss' $ SOBind (Some "v") phi) :-: ss' phiS) 
                                        (GammaV 1 :+: GammaV 2))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  
                  stau = liftToSequent tau
        restriction _ = Nothing
        --
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

-- XXX Skipping derived rules for now.
parsePSOLogic :: Parsec String u [PSOLogic]
parsePSOLogic = try soRule <|> liftFO
    where liftFO = do r <- parseFOLogic empty
                      return (map FO_PSOL r)
          soRule = do r <- choice (map (try . string) [ "UI", "UD", "EG", "ED", "ABS","APP"])
                      ds <- many1 digit
                      let n = read ds :: Int
                      case r of 
                            r | r == "UI"   -> return [SOUI_PSOL n]
                              | r == "UD"   -> return [SOUD_PSOL n]
                              | r == "EG"   -> return [SOEG_PSOL n]
                              | r == "ED"   -> return [SOED1_PSOL n, SOED2_PSOL n]
                              | r == "ABS"  -> return [ABS_PSOL n]
                              | r == "APP"  -> return [APP_PSOL n]

parsePSOLProof :: String -> [DeductionLine PSOLogic PolyadicallySOLLex (Form Bool)]
parsePSOLProof = toDeduction parsePSOLogic psolFormulaParser

psolSeqParser = seqFormulaParser :: Parsec String () (PSOLSequentCalc Sequent)

psolCalc = NaturalDeductionCalc 
    { ndRenderer = MontegueStyle
    , ndParseProof = const parsePSOLProof -- XXX ignore derived rules for now
    , ndProcessLine = hoProcessLine
    , ndProcessLineMemo = Just hoProcessLineMemo
    , ndParseSeq = psolSeqParser
    }

---------------------------
--  2. Helper Functions  --
---------------------------

ss :: MonadicallySOL (Form Bool) -> MSOLSequentCalc Succedent
ss = SS . liftToSequent

sa :: MonadicallySOL (Form Bool) -> MSOLSequentCalc Antecedent
sa = SA . liftToSequent

ss' :: PolyadicallySOL (Form Bool) -> PSOLSequentCalc Succedent
ss' = SS . liftToSequent

sa' :: PolyadicallySOL (Form Bool) -> PSOLSequentCalc Antecedent
sa' = SA . liftToSequent

tau = SOT 1

phiS = SOPhi 1 AZero AZero

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
