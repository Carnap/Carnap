module FirstOrder (founify) where

import Carnap.Core.Unification.Unification

--this needs to be generalized to include an optional label
founify :: FirstOrder f => [Equation f] -> [Equation f] -> Either (UError f) [Equation f]
founify [] ss = Right ss
founify ((x :=: y):es) ss
    | isVar x && occurs x y       = Left $ OccursError x y
    | isVar x && not (occurs x y) = founify (mapAll (subst x y) es) ((x :=: y):ss)
    | isVar y                     = founify ((y :=: x):es) ss
    | sameHead x y                = founify (es ++ decompose x y) ss .<. SubError x y
    | otherwise                   = Left $ MatchError x y
