{-#LANGUAGE GADTs, UndecidableInstances, RankNTypes, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.ModalFirstOrder.Logic.Rules where

import Data.List (intercalate)
import Data.Typeable (Typeable)
import Data.Maybe (catMaybes)
import Text.Parsec
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification (applySub,subst)
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.ModalFirstOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.ModalFirstOrder.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Calculi.NaturalDeduction.Syntax (DeductionLine(..),depth,assertion)

type FirstOrderModalSequentCalcOverWith b a = ClassicalSequentOver (ModalFirstOrderLexOverWith b a)
type FirstOrderModalSequentCalcLexOverWith b a = ClassicalSequentLexOver (ModalFirstOrderLexOverWith b a)
type FirstOrderModalIndexedSequentCalcWith a = ClassicalSequentOver (IndexedModalFirstOrderLexWith a)
type FirstOrderModalIndexedSequentCalcLexWith a = ClassicalSequentLexOver (IndexedModalFirstOrderLexWith a)
type FirstOrderModalIndexedSequentCalc = FirstOrderModalIndexedSequentCalcWith EndLang

pattern SeqQuant q        = FX (Lx2 (Lx1 (Lx2 (Bind q))))
pattern SeqVar c a        = FX (Lx2 (Lx1 (Lx5 (Function c a))))
pattern SeqTau c a        = FX (Lx2 (Lx1 (Lx6 (Function c a))))
pattern SeqV s            = SeqVar (Var s) AZero
pattern SeqT n            = SeqTau (SFunc AZero n) AZero

pattern SeqSchemIdx c a   = FX (Lx2 (Lx1 (Lx1 (Lx2 (Lx4 (Function c a))))))
pattern SeqSchmIdx n      = SeqSchemIdx (SFunc AZero n) AZero
pattern SomeWorld         = SeqSchmIdx 0

liftAbsRule (SequentRule p c) = map (liftAbsSeq SomeWorld) p ∴ liftAbsSeq SomeWorld c

liftAbsSeq :: IndexingLang (FirstOrderModalIndexedSequentCalcLexWith a) (Term World) (Form Bool) (Form (World -> Bool)) =>
                FirstOrderModalIndexedSequentCalcWith a (Term World) 
                -> FirstOrderModalIndexedSequentCalcWith a (Sequent (Form (World -> Bool))) 
                -> FirstOrderModalIndexedSequentCalcWith a (Sequent (Form Bool))
liftAbsSeq w (a :|-: s) = atSomeAnt a :|-: atSomeSuc s
    where 
          --atSomeAnt :: FirstOrderModalIndexedSequentCalcWith a (Antecedent (Form (World -> Bool))) -> FirstOrderModalIndexedSequentCalcWith a (Antecedent (Form Bool))
          atSomeAnt (x :+: y) = atSomeAnt x :+: atSomeAnt y
          atSomeAnt (SA x) = SA (x `atWorld` w) 
          atSomeAnt (GammaV n) = GammaV n
          atSomeAnt Top = Top

          --atSomeSuc :: FirstOrderModalIndexedSequentCalcWith a (Succedent (Form (World -> Bool))) -> FirstOrderModalIndexedSequentCalcWith a (Succedent (Form Bool))
          atSomeSuc (x :-: y) = atSomeSuc x :-: atSomeSuc y
          atSomeSuc (SS x) = SS (x `atWorld` w) 
          atSomeSuc Bot = Bot

someWorld :: IndexingLang lex (Term World) (Form c) (Form (World -> Bool)) => FixLang lex (Term World)
someWorld = worldScheme 0 

someOtherWorld :: IndexingLang lex (Term World) (Form c) (Form (World -> Bool)) => FixLang lex (Term World)
someOtherWorld = worldScheme 1 

someThirdWorld :: IndexingLang lex (Term World) (Form c) (Form (World -> Bool)) => FixLang lex (Term World)
someThirdWorld = worldScheme 2

instance ParsableLex (Form (World -> Bool)) IndexedModalFirstOrderLex where
        langParser = hardegreeMPLFormulaPreParser

indexedModalFOSeqParser = liftAbsSeq (world 0) <$> (seqFormulaParser :: Parsec String u (FirstOrderModalIndexedSequentCalc (Sequent (Form (World -> Bool)))))

instance IndexedSchemeConstantLanguage (FirstOrderModalSequentCalcOverWith b a (Term Int)) where
        taun = SeqT

instance ( Schematizable (a (FirstOrderModalIndexedSequentCalcWith a))
         , StaticVar (FirstOrderModalIndexedSequentCalcWith a)
         ) => CopulaSchema (FirstOrderModalIndexedSequentCalcWith a) where 

    appSchema (SeqQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SeqV x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SeqV x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (static (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (static (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)
