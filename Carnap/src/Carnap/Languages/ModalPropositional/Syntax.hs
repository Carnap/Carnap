{-#LANGUAGE FunctionalDependencies, FlexibleInstances, GADTs, TypeOperators, FlexibleContexts #-}
module Carnap.Languages.ModalPropositional.Syntax where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Util (checkChildren, castTo)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Carnap.Core.Data.Util (scopeHeight)
import Control.Applicative (liftA2)
import Control.Lens (preview)
import Control.Lens.Plated (transform)
import Data.Typeable (Typeable)
import Data.List (intercalate)
import Data.Map.Lazy (Map, (!))
import qualified Data.Monoid as M
import Carnap.Languages.Util.GenericConstructors

--------------------------------------------------
--  1. Data for Pure Propositional Modal Logic  --
--------------------------------------------------

--the semantic values in this language are intensions rather than boolean
--values

newtype World = World Int
    deriving (Eq, Ord)

type ModalProp = IntProp (World -> Bool)

type ModalSchematicPred = SchematicIntPred (World -> Bool) World

type ModalPropositionalContext = PropositionalContext (World -> Bool)

data PropFrame = PropFrame { valuation :: World -> Bool
                           , accessibility :: Map World [World]
                           }

instance Evaluable ModalProp where
        eval (Prop n) = Form $ const $ even n

instance Modelable PropFrame ModalProp where
        satisfies f (Prop n) = Form $ const $  valuation f (World n)

type ModalConn = BooleanConn (World -> Bool)

instance Evaluable ModalConn where
        eval Iff = liftA2 $ \f g x -> f x == g x
        eval If  = liftA2 $ \f g x -> not (f x) || g x
        eval Or  = liftA2 $ \f g x -> f x || g x
        eval And = liftA2 $ \f g x -> f x && g x
        eval Not = fmap $ \f x -> not $ f x

type ModalConst = BooleanConst (World -> Bool)

instance Modelable PropFrame ModalConn where
    satisfies = const eval

instance Evaluable ModalConst where
        eval Verum = Form (const True)
        eval Falsum = Form (const False)

instance Modelable PropFrame ModalConst where
    satisfies = const eval

type PropModality = Modality (World -> Bool)

--For the eval frame, we stipulate that the accessibility relation is empty
instance Evaluable PropModality where
        eval Box = fmap $ \f -> const True
        eval Diamond = fmap $ \f -> const False

instance Modelable PropFrame PropModality where
        satisfies f Box = fmap $ \f x -> M.getAll $ mconcat (map (M.All . f) (ac x))
            where ac x = accessibility f ! x
        satisfies f Diamond = fmap $ \f x -> M.getAny $ mconcat (map (M.Any . f) (ac x))
            where ac x = accessibility f ! x

type Index = IntIndex World

type IndexScheme = SchematicIntFunc World World

type ModalSchematicProp = SchematicIntProp (World -> Bool)

type WorldTheoryIndexer = Indexer World (World -> Bool) (World -> Bool)

type IndexVar = StandardVar World

type AbsoluteIndexer = Indexer World (World -> Bool) Bool

type IndexCons = Cons World

type IndexQuant = StandardQuant (World -> Bool) World

-------------------------------------------
--  2. Core Lexicon for Modal Languages  --
-------------------------------------------

type CoreLexicon = Predicate ModalProp
                   :|: Predicate ModalSchematicProp
                   :|: Connective ModalConn
                   :|: Connective PropModality
                   :|: Connective ModalConst
                   :|: SubstitutionalVariable
                   :|: Connective ModalPropositionalContext
                   :|: EndLang

instance PrismBooleanConnLex CoreLexicon (World -> Bool)
instance PrismGenericContext CoreLexicon (World -> Bool) (World -> Bool)
instance PrismBooleanConst CoreLexicon (World -> Bool)
instance PrismPropLex CoreLexicon (World -> Bool)
instance PrismSchematicProp CoreLexicon (World -> Bool)
instance PrismModality CoreLexicon (World -> Bool)
instance PrismSubstitutionalVariable CoreLexicon

type ModalPropLexiconWith a = CoreLexicon :|: a :|: EndLang

type ModalPropLanguageWith a = FixLang (ModalPropLexiconWith a)

instance UniformlyEq (ModalPropLanguageWith a) => Eq (ModalPropLanguageWith a b) where
        (==) = (=*)

instance PrismBooleanConnLex (ModalPropLexiconWith a) (World -> Bool)
instance PrismGenericContext (ModalPropLexiconWith a) (World -> Bool) (World -> Bool)
instance PrismBooleanConst (ModalPropLexiconWith a) (World -> Bool)
instance PrismPropLex (ModalPropLexiconWith a) (World -> Bool)
instance PrismSchematicProp (ModalPropLexiconWith a) (World -> Bool)
instance PrismModality (ModalPropLexiconWith a) (World -> Bool)
instance PrismSubstitutionalVariable (ModalPropLexiconWith a)

-------------------------------
--  3. Basic Modal Language  --
-------------------------------

type ModalPropLexicon = ModalPropLexiconWith EndLang

instance BoundVars ModalPropLexicon

type ModalPropLanguage = FixLang ModalPropLexicon

type ModalForm = ModalPropLanguage (Form (World -> Bool))

instance CopulaSchema ModalPropLanguage

--------------------------
--  4. World Languages  --
--------------------------

type WorldTheoryLexicon = WorldTheoryIndexer 
                        :|: Function Index
                        :|: Function IndexCons 
                        :|: Function IndexScheme
                        :|: Binders IndexQuant
                        :|: Predicate ModalSchematicPred
                        :|: Function IndexVar
                        :|: EndLang

type WorldTheoryPropLexicon = ModalPropLexiconWith WorldTheoryLexicon

type WorldTheoryPropLanguage = ModalPropLanguageWith WorldTheoryLexicon

instance CopulaSchema WorldTheoryPropLanguage where
    appSchema q@(Fx _) (LLam f) e = case ( qtype q >>= preview _all  >>= \x -> (,) <$> Just x <*> castTo (worldVar x)
                                         , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (worldVar x)
                                         ) of
                                     (Just (x,v), _) -> schematize (All x) (show (f v) : e)
                                     (_, Just (x,v)) -> schematize (Some x) (show (f v) : e)
                                     _ -> schematize q (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance BoundVars WorldTheoryPropLexicon where
        scopeUniqueVar q (LLam f) = case castTo $ worldVar (show $ scopeHeight (LLam f)) of
                                        Just x -> x
                                        Nothing -> error "cast failed in ScopeUniqueVar"

        subBoundVar = subst

type WorldTheoryForm = WorldTheoryPropLanguage (Form (World -> Bool))

instance PrismGenericQuant WorldTheoryPropLexicon Term Form (World -> Bool) World
instance PrismIndexing WorldTheoryPropLexicon World (World -> Bool) (World->Bool) 
instance PrismIntIndex WorldTheoryPropLexicon World
instance PrismCons WorldTheoryPropLexicon World
instance PrismPolyadicSchematicFunction WorldTheoryPropLexicon World World
instance PrismPolyadicSchematicPredicate WorldTheoryPropLexicon World (World -> Bool) 
instance PrismStandardVar WorldTheoryPropLexicon World

----------------------------------------
--  5. Absolute Modal Logic Language  --
----------------------------------------

type AbsoluteModalLexicon = AbsoluteIndexer
                        :|: Function Index
                        :|: Function IndexCons 
                        :|: Function IndexScheme
                        :|: EndLang

type AbsoluteModalPropLexicon = ModalPropLexiconWith AbsoluteModalLexicon

type AbsoluteModalPropLanguage = ModalPropLanguageWith AbsoluteModalLexicon

instance CopulaSchema AbsoluteModalPropLanguage

instance PrismIndexing AbsoluteModalPropLexicon World (World -> Bool) Bool
instance PrismIntIndex AbsoluteModalPropLexicon World
instance PrismCons AbsoluteModalPropLexicon World
instance PrismPolyadicSchematicFunction AbsoluteModalPropLexicon World World

type AbsoluteModalForm = AbsoluteModalPropLanguage (Form Bool)

type AbsoluteModalPreForm = AbsoluteModalPropLanguage (Form (World -> Bool))

----------------------------
--  6. Utility Functions  --
----------------------------
--convenience functions

worldVar :: StandardVarLanguage (lang (Term World)) => String -> lang (Term World)
worldVar = var

qtype :: Typeable a => FixLang lex a -> Maybe (FixLang lex ((Term World -> Form (World -> Bool)) -> Form (World -> Bool)))
qtype = castTo
