{-#LANGUAGE GADTs, TypeOperators, ScopedTypeVariables, ExplicitForAll, ImpredicativeTypes, MultiParamTypeClasses, FlexibleContexts, PatternSynonyms #-}

module Carnap.Core.Unification.FirstOrder (founify, foUnifySys) where

import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification

(Left x) .<. f = Left (f x)
x .<. _ = x

isVar' varConst x = isVar x && not (varConst x)

--this needs to be generalized to include an optional label
founify :: FirstOrder f
        => (forall a. f a -> Bool)
        -> [Equation f]
        -> [Equation f]
        -> Either (UError f) [Equation f]
founify varConst [] ss = Right ss
founify varConst ((x :=: y):es) ss
    | isVar' varConst x && x =* y     = founify varConst es ss
    | isVar' varConst x && occurs x y = Left $ OccursError x y
    | isVar' varConst x               = founify varConst (mapAll (subst x y) es) ((x :=: y):ss)
    | isVar' varConst y               = founify varConst ((y :=: x):es) ss
    | sameHead x y                    = founify varConst (es ++ decompose x y) ss .<. SubError x y
    | otherwise                       = Left $ MatchError x y

foUnifySys :: (MonadVar f m, FirstOrder f) => (forall a. f a -> Bool) -> [Equation f] -> m [[Equation f]]
foUnifySys varConst sys = return $ case founify varConst sys [] of
    Left  _ -> []
    Right sub -> [sub]
