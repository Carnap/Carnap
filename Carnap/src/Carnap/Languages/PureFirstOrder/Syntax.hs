{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, TypeOperators, PatternSynonyms, FlexibleContexts #-}
module Carnap.Languages.PureFirstOrder.Syntax 
where

import Text.Read
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
import Control.Lens (Traversal', preview, outside, (.~), (&), Prism')
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

type PureQuantCtx = QuantifiedContext Bool Int

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
                   :|: Function PureSchematicFunction
                   :|: PureQuantCtx
                   :|: EndLang

type PureFirstOrderLexWith a = CoreLexicon :|: a

type PureFirstOrderLanguageWith a = FixLang (PureFirstOrderLexWith a)

instance {-# OVERLAPPABLE #-} 
        ( StaticVar (PureFirstOrderLanguageWith a)
        , Schematizable (a (PureFirstOrderLanguageWith a))
        ) => CopulaSchema (PureFirstOrderLanguageWith a) where 

    appSchema q@(Fx _) (LLam f) e = case ( qtype q >>= preview _all >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         ) of
                                     (Just (x,v), _) -> schematize (All x) (show (f v) : e)
                                     (_, Just (x,v)) -> schematize (Some x) (show (f v) : e)
                                     _ -> schematize q (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    BoundVars (PureFirstOrderLexWith a) where

    scopeUniqueVar q (LLam f) = case castTo $ foVar $ show $ maxVar (LLam f) + 1 of
                                    Just x -> x
                                    Nothing -> error "cast failed in ScopeUniqueVar"

    scopeUniqueVar _ _ = undefined

    subBoundVar = saferSubst

instance (ReLex a, FirstOrder (FixLang (ClassicalSequentLexOver (PureFirstOrderLexWith a)))) => 
    BoundVars (ClassicalSequentLexOver (PureFirstOrderLexWith a)) where

    scopeUniqueVar q (LLam f) = case castTo $ foVar $ show $ maxVar (LLam f) + 1 of
                                    Just x -> x
                                    Nothing -> error "cast failed in ScopeUniqueVar"

    scopeUniqueVar _ _ = undefined

    subBoundVar = saferSubst

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    RelabelVars (PureFirstOrderLexWith a) Form Bool where

    subBinder (q :!$: LLam f) y =  case (qtype q >>= preview _all, qtype q >>= preview _some, oftype (LLam f)) of
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
instance PrismGenericContext (PureFirstOrderLexWith a) Bool Bool
instance PrismBooleanConst (PureFirstOrderLexWith a) Bool
instance PrismSchematicProp (PureFirstOrderLexWith a) Bool
instance PrismGenericQuant (PureFirstOrderLexWith a) Term Form Bool Int
instance PrismQuantContext (PureFirstOrderLexWith a) Bool Int
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

type OpenPFOLForm a = OpenLanguagePFOL a (Form Bool)

type PurePFOLForm = OpenPFOLForm EndLang

type OpenPFOLTerm a = OpenLanguagePFOL a (Term Int)

type PurePFOLTerm = OpenPFOLTerm EndLang

instance PrismPolyadicPredicate (OpenLexiconPFOL a) Int Bool
instance PrismPolyadicSchematicPredicate (OpenLexiconPFOL a) Int Bool

instance Incrementable (OpenLexiconPFOL EndLang) (Term Int) where
    incHead = const Nothing
        & outside (_predIdx')  .~ (\(n,a) -> Just $ ppn n (ASucc a))
        & outside (_spredIdx') .~ (\(n,a) -> Just $ pphin n (ASucc a))
        where _predIdx' :: Typeable ret => Prism' (FixLang (OpenLexiconPFOL EndLang) ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _predIdx' = _predIdx
              _spredIdx' :: Typeable ret => Prism' (FixLang (OpenLexiconPFOL EndLang) ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _spredIdx' = _spredIdx

--------------------------------------------------------
--2.3 Polyadic First Order Logic with Polyadic Function Symbols and Identity
--------------------------------------------------------

type PolyadicFunctionSymbolsAndIdentity = Predicate PureEq 
                                        :|: Function PureFunction 
                                        :|: Function PureSchematicFunction
                                        :|: EndLang

type OpenLexiconFOL a = OpenLexiconPFOL (PolyadicFunctionSymbolsAndIdentity :|: a)

type OpenLanguageFOL a = FixLang (OpenLexiconFOL a)

type PureLexiconFOL = OpenLexiconFOL EndLang

type PureLanguageFOL = FixLang PureLexiconFOL

type PureFOLForm = PureLanguageFOL (Form Bool)

type PureFOLTerm = PureLanguageFOL (Term Int)

instance PrismTermEquality (OpenLexiconFOL a) Int Bool
instance PrismPolyadicFunction (OpenLexiconFOL a) Int Int
instance PrismPolyadicSchematicFunction (OpenLexiconFOL a) Int Int

instance {-#OVERLAPPABLE#-} Incrementable (OpenLexiconFOL a) (Term Int) where
    incHead = const Nothing
        & outside (_predIdx')  .~ (\(n,a) -> Just $ ppn n (ASucc a))
        & outside (_spredIdx') .~ (\(n,a) -> Just $ pphin n (ASucc a))
        & outside (_funcIdx')  .~ (\(n,a) -> Just $ pfn n (ASucc a))
        & outside (_sfuncIdx') .~ (\(n,a) -> Just $ spfn n (ASucc a))
        where _predIdx' :: Typeable ret => Prism' (OpenLanguageFOL a ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _predIdx' = _predIdx
              _spredIdx' :: Typeable ret => Prism' (OpenLanguageFOL a ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _spredIdx' = _spredIdx
              _funcIdx' :: Typeable ret => Prism' (OpenLanguageFOL a ret) (Int, Arity (Term Int) (Term Int) ret) 
              _funcIdx' = _funcIdx
              _sfuncIdx' :: Typeable ret => Prism' (OpenLanguageFOL a ret) (Int, Arity (Term Int) (Term Int) ret) 
              _sfuncIdx' = _sfuncIdx

-------------------------
--  Utility Functions  --
-------------------------
--mostly specializing things for the first-order case

maxVar :: (PrismStandardVar lex Int, PrismSubstitutionalVariable lex) => FixLang lex a -> Int
maxVar (x :!$: y) = max (maxVar x) (maxVar y)
maxVar x@(LLam f) =  maxVar (f $ static 0)
maxVar t@(Fx _) = case ttype t >>= preview _varLabel >>= readMaybe of
                   Nothing -> 0
                   Just x -> x

fogamma :: Int -> ClassicalSequentOver lex (Antecedent (Form Bool))
fogamma n = GammaV n

fodelta:: Int -> ClassicalSequentOver lex (Succedent (Form Bool))
fodelta n = DeltaV n

termsOf :: (BoundVars lex, Typeable sem) => FirstOrder (FixLang lex) => Traversal' (FixLang lex sem) (FixLang lex (Term Int))
termsOf = genChildren

formsOf :: (BoundVars lex, Typeable sem) => FirstOrder (FixLang lex) => Traversal' (FixLang lex sem) (FixLang lex (Form Bool))
formsOf = genChildren

foVar :: StandardVarLanguage (FixLang lex (Term Int))  => String -> FixLang lex (Term Int)
foVar = var

oftype :: Typeable a => FixLang lex a -> Maybe (FixLang lex (Term Int -> Form Bool))
oftype = castTo

qtype :: Typeable a => FixLang lex a -> Maybe (FixLang lex ((Term Int -> Form Bool)->Form Bool))
qtype = castTo

ttype :: Typeable a => FixLang lex a -> Maybe (FixLang lex (Term Int))
ttype = castTo
