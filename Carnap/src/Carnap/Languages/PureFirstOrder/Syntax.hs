{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, TypeOperators, PatternSynonyms, FlexibleContexts #-}
module Carnap.Languages.PureFirstOrder.Syntax 
where

import Carnap.Core.Util 
import Carnap.Core.Data.Util 
import Control.Monad.State
import qualified Carnap.Languages.PurePropositional.Syntax as P
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.ClassicalSequent.Syntax
import Control.Lens (Traversal', preview)
import Data.Typeable (Typeable)
import Data.List (intercalate)
import Carnap.Languages.Util.GenericConstructors

--------------------------------------------------------
--1. Data for Pure First Order Logic
--------------------------------------------------------

data PureMonadicPredicate a where
    MonPred :: Int -> PureMonadicPredicate (Term Int -> Form Bool)

instance Schematizable PureMonadicPredicate where
    schematize (MonPred n) = \(x:xs) -> "P_" ++ show n ++ "(" ++ x ++ ")"

instance UniformlyEq PureMonadicPredicate where
    (MonPred n) =* (MonPred m) = n == m

instance FirstOrderLex PureMonadicPredicate 

type PurePredicate = IntPred Bool Int

type PureFunction = IntFunc Int Int

type PureSchematicFunction = SchematicIntFunc Int Int

type PureEq = TermEq Bool Int

type PureSchematicPred = SchematicIntPred Bool Int

type PureConstant = IntConst Int

type PureVar = StandardVar Int

type PureQuant = StandardQuant Bool Int

--------------------------------------------------------
--2. Pure First Order Languages 
--------------------------------------------------------

--------------------------------------------------------
--2.0 Common Core of FOL
--------------------------------------------------------

type CoreLexicon = P.PurePropLexicon
                   :|: Binders PureQuant
                   :|: Function PureConstant
                   :|: Function PureVar
                   :|: Function (SchematicIntFunc Int Int)
                   :|: EndLang

type PureFirstOrderLexWith a = CoreLexicon :|: a

type PureFirstOrderLanguageWith a = FixLang (PureFirstOrderLexWith a)

instance {-# OVERLAPPABLE #-} 
        ( StaticVar (PureFirstOrderLanguageWith a)
        , Schematizable (a (PureFirstOrderLanguageWith a))
        ) => CopulaSchema (PureFirstOrderLanguageWith a) where 

    appSchema h@(Fx _) (LLam f) e = case (qtype h >>= preview _all, qtype h >>= preview _some, oftype (LLam f)) of
                                    (Just x, _, Just (LLam f')) -> schematize (All x) (show (f' $ foVar x) : e)
                                    (_, Just x, Just (LLam f')) -> schematize (Some x) (show (f' $ foVar x) : e)
                                    _ -> schematize h (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    BoundVars (PureFirstOrderLexWith a) where

    scopeUniqueVar q (LLam f) = case castTo $ foVar $ show $ scopeHeight (LLam f) of
                                    Just x -> x
                                    Nothing -> error "cast failed in ScopeUniqueVar"

    scopeUniqueVar _ _ = undefined

    subBoundVar = subst


instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    RelabelVars (PureFirstOrderLexWith a) Form Bool where

    subBinder (q :!$: LLam f) y = case (qtype q >>= preview _all, qtype q >>= preview _some, oftype (LLam f)) of
                                    (Just _, _, Just (LLam f')) -> Just $ lall y f'
                                    (_, Just _, Just (LLam f')) -> Just $ lsome y f'
                                    _ -> Nothing
    subBinder _ _ = Nothing

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    CanonicalForm (PureFirstOrderLanguageWith a (Form Bool)) where

    canonical = relabelVars [i ++ j | i <- ["x"], j <- map show [1 ..]]

instance CanonicalForm (PureFirstOrderLanguageWith a (Term Int))

instance PrismPropLex (PureFirstOrderLexWith a) Bool
instance PrismIndexedConstant (PureFirstOrderLexWith a) Int
instance PrismBooleanConnLex (PureFirstOrderLexWith a) Bool
instance PrismPropositionalContext (PureFirstOrderLexWith a) Bool
instance PrismBooleanConst (PureFirstOrderLexWith a) Bool
instance PrismSchematicProp (PureFirstOrderLexWith a) Bool
instance PrismStandardQuant (PureFirstOrderLexWith a) Bool Int
instance PrismStandardVar (PureFirstOrderLexWith a) Int
instance PrismSubstitutionalVariable (PureFirstOrderLexWith a)
--equality up to α-equivalence
instance UniformlyEq (PureFirstOrderLanguageWith a) => Eq (PureFirstOrderLanguageWith a b) where
        (==) = (=*)
    
--------------------------------------------------------
--2.1 Monadic First Order Logic
--------------------------------------------------------

--Note that we *could* add monadic function symbols and identity while
--preserving decidability

type MonadicPredicates = Predicate PureMonadicPredicate :|: EndLang

type OpenLexiconMFOL a = CoreLexicon :|: MonadicPredicates :|: a

type PureLexiconMFOL = OpenLexiconMFOL EndLang

type OpenLanguageMFOL a = FixLang (OpenLexiconMFOL a)

type PureLanguageMFOL = FixLang PureLexiconMFOL

pattern PMPred n = FX (Lx2 (Lx1 (Predicate (MonPred n) AOne)))

type OpenMFOLForm a = OpenLanguageMFOL a (Form Bool)

type PureMFOLForm = OpenMFOLForm EndLang

type OpenMFOLTerm a = OpenLanguageMFOL a (Term Int)

type PureMFOLTerm = OpenMFOLTerm EndLang

--------------------------------------------------------
--2.2 Polyadic First Order Logic
--------------------------------------------------------

type PolyadicPredicates = Predicate PurePredicate 
                      :|: Predicate PureSchematicPred
                      :|: EndLang

type OpenLexiconPFOL a = CoreLexicon :|: PolyadicPredicates :|: a

type PureLexiconPFOL = OpenLexiconPFOL EndLang

type OpenLanguagePFOL a = FixLang (OpenLexiconPFOL a)

type PureLanguagePFOL = FixLang PureLexiconPFOL

pattern PPred x arity  = FX (Lx2 (Lx1 (Predicate x arity)))
pattern PSPred x arity = FX (Lx2 (Lx2 (Predicate x arity)))
pattern PP n a1 a2     = PPred (Pred a1 n) a2
pattern PPhi n a1 a2   = PSPred (SPred a1 n) a2

type OpenPFOLForm a = OpenLanguagePFOL a (Form Bool)

type PurePFOLForm = OpenPFOLForm EndLang

type OpenPFOLTerm a = OpenLanguagePFOL a (Term Int)

type PurePFOLTerm = OpenPFOLTerm EndLang

instance PrismPolyadicPredicate (OpenLexiconPFOL a) Int Bool
instance PrismPolyadicSchematicPredicate (OpenLexiconPFOL a) Int Bool

instance Incrementable (OpenLexiconPFOL EndLang) (Term Int) where
    incHead (PP n a b)   = Just $ PP n (ASucc a) (ASucc a)
    incHead (PPhi n a b) = Just $ PPhi n (ASucc a) (ASucc a)
    incHead _  = Nothing

--------------------------------------------------------
--2.3 Polyadic First Order Logic with Polyadic Function Symbols and Identity
--------------------------------------------------------

type PolyadicFunctionSymbolsAndIdentity = Predicate PureEq 
                                        :|: Function PureFunction 
                                        :|: Function PureSchematicFunction
                                        :|: EndLang

type PureLexiconFOL = (OpenLexiconPFOL (PolyadicFunctionSymbolsAndIdentity :|: EndLang))

type PureLanguageFOL = FixLang PureLexiconFOL


pattern PFunc x arity  = FX (Lx3 (Lx2 (Function x arity)))
pattern PSFunc x arity  = FX (Lx3 (Lx3 (Function x arity)))
pattern PF n a1 a2     = PFunc (Func a1 n) a2
pattern PSF n a1 a2    = PSFunc (SFunc a1 n) a2

type PureFOLForm = PureLanguageFOL (Form Bool)

type PureFOLTerm = PureLanguageFOL (Term Int)

instance PrismTermEquality PureLexiconFOL Int Bool
instance PrismPolyadicFunction PureLexiconFOL Int Int
instance PrismPolyadicSchematicFunction PureLexiconFOL Int Int

instance Incrementable (OpenLexiconPFOL (PolyadicFunctionSymbolsAndIdentity :|: a)) (Term Int) where
    incHead (PP n a b)   = Just $ PP n (ASucc a) (ASucc a)
    incHead (PF n a b)   = Just $ PF n (ASucc a) (ASucc a)
    incHead (PSF n a b)  = Just $ PSF n (ASucc a) (ASucc a)
    incHead (PPhi n a b) = Just $ PPhi n (ASucc a) (ASucc a)
    incHead _  = Nothing

-------------------------
--  Utility Functions  --
-------------------------
--mostly specializing things for the first-order case

fogamma :: Int -> ClassicalSequentOver lex (Antecedent (Form Bool))
fogamma n = GammaV n

termsOf :: BoundVars lex => FirstOrder (FixLang lex) => Traversal' (FixLang lex (Form Bool)) (FixLang lex (Term Int))
termsOf = genChildren

formsOf :: BoundVars lex => FirstOrder (FixLang lex) => Traversal' (FixLang lex (Form Bool)) (FixLang lex (Form Bool))
formsOf = genChildren

foVar :: StandardVarLanguage (FixLang lex (Term Int))  => String -> FixLang lex (Term Int)
foVar = var

oftype :: Typeable a => FixLang lex a -> Maybe (FixLang lex (Term Int -> Form Bool))
oftype = castTo

qtype :: Typeable a => FixLang lex a -> Maybe (FixLang lex ((Term Int -> Form Bool)->Form Bool))
qtype = castTo
