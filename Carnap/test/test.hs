{-#LANGUAGE FlexibleContexts#-}

module Main where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.Huet
import Carnap.Core.Unification.ACUI
import Carnap.Core.Unification.Combination
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Logic
import Carnap.Core.Examples.ACUI
import System.CPUTime
import System.Exit (exitFailure)

main = do putStrLn ""
          testPositives psequents
          testNegatives nsequents
          timeFirstOrder simpleCI "first order positive conditional introduction" (posTest "CI 1")
          timeFirstOrder simpleCI2 "first order positive conditional introduction 2" (posTest "CI 2")
          timeFirstOrder simpleCI3 "first order positive conditional introduction 3" (posTest "CI 3")
          timeFirstOrder simpleCI4 "first order positive conditional introduction 4" (posTest "CI 4")
          timeFirstOrder simpleCIErr "first order negative conditional introduction 1" (negTest "CI Neg 1")
          timeFirstOrder simpleCIErr2 "first order negative conditional introduction 2" (negTest "CI Neg 2")
          timeFirstOrder simpleCIErr3 "first order negative conditional introduction 3" (negTest "CI Neg 3")
          timeFirstOrder simpleModusPonens "first order positive modus ponens 1" (posTest "alt modus ponens 1")
          timeFirstOrder simpleModusPonens2 "first order positive modus ponens 2" (posTest "alt modus ponens 2")
          timeFirstOrder simpleModusPonensErr "first order negative modus ponens 1" (negTest "alt modus ponens err 1")
          putStrLn ""

-------------------------
--  Testing Functions  --
-------------------------

timeFirstOrder = timeMethod (pure . firstOrderMethod)

--the test must be nontrivial (error signal on failure) or Haskell optimizes away the test results
timeMethod method eqs desc test = do startTime <- getCPUTime
                                     subs <- method eqs
                                     test subs
                                     finishTime <- getCPUTime
                                     let t = fromIntegral (finishTime - startTime)
                                     putStrLn $ "Test Results (" ++ desc ++ "):" ++ show t

testTemplate :: Show a => (a -> Bool) -> String -> a -> IO ()
testTemplate pred desc x = if pred x then return ()
                                     else do putStrLn $ "test " ++ desc ++ " failed"
                                             putStrLn $ "failing object: " ++ show x
                                             exitFailure
                                             --
--A simple method of first-order unification
firstOrderMethod eqs = case evalTerm $ foUnifySys (const False) succs of
                     [x] -> evalTerm $ acuiUnifySys (const False) (mapAll (applySub x) ants)
                     [] -> []
            where
              ants  = map antPair eqs
              succs = map succPair eqs

--A simple method of higher-order unification
higherOrderMethod eqs = case evalTerm $ huetUnifySys (const False) succs of
                     [x] -> evalTerm $ acuiUnifySys (const False) (mapAll (applySub x) ants)
                     [] -> []
            where
              ants  = map antPair eqs
              succs = map succPair eqs

succPair :: Equation PropSequentCalc -> Equation PropSequentCalc
succPair ((_ :|-: (SS x)):=:(_:|-: (SS y)))  = x :=: y
succPair ((_ :|-: x):=:(_:|-: y))  = x :=: y

antPair :: Equation PropSequentCalc -> Equation PropSequentCalc
antPair  ((x :|-: _):=:(y:|-: _))  = x :=: y

posTest eq = (testTemplate (not . null) (show eq ++ " as Positive" ))

negTest eq = (testTemplate null (show eq ++ " as Negative" ))

testNegatives = mapM (\eqs -> timeFirstOrder [eqs] ("First order Negative test of " ++ show eqs) (negTest eqs))

testPositives = mapM (\eqs -> timeFirstOrder [eqs] ("First order Positive test of " ++ show eqs) (posTest eqs))

--related to old combination tests
--timeCombine = timeMethod combine
--testNegatives = mapM (\eqs -> timeCombine [eqs] ("Negative test of " ++ show eqs) (negTest eqs))
--testPositives = mapM (\eqs -> timeCombine [eqs] ("Positive test of " ++ show eqs) (posTest eqs))

--some specific tests
--timeCombine [pacuicase1] "big positive acui" (posTest pacuicase1)
--timeCombine [nacuicase1] "big negative acui" (negTest nacuicase1)
--timeCombine simpleModusPonens "positive modus ponens" (posTest "combine modus ponens") 
          

-------------
--  Tests  --
-------------


pacuicase1 = (parseTerm "f(a u b u c u d u e)" :=: parseTerm "f(b u c u d u a)")

nacuicase1 = parseTerm "g(a u b u c u d u e)" :=: parseTerm "f(b u c u d u a)"

pseqcase1 = (p :|-: q) :=: (p :|-: q)
pseqcase2 = ((p :+: p) :|-: q) :=: (p :|-: q)
pseqcase3 = (p :+: Top :|-: q) :=: (p :|-: q)
pseqcase4 = ((p :+: GammaV 1) :|-: q) :=: (p :|-: q)
pseqcase5 = (phi :+: GammaV 1 :|-: q) :=: (phi :|-: q)
pseqcase6 = (phi :+: phi :|-: q) :=: (p :|-: q)
psequents = [pseqcase1
            ,pseqcase2
            ,pseqcase3
            ,pseqcase4
            --,pseqcase5 --XXX: these cases won't wokr with altCombine,
            --since there are formula variables in the antecedent left
            --undetermined by the succedent
            --,pseqcase6 
            ]

nseqcase1 = (p' :|-: q) :=: (p :|-: q)
nseqcase2 = (p' :+: p :|-: q) :=: (p :|-: q)
nseqcase3 = ((p' :+: Top) :|-: q) :=: (p :|-: q)
nseqcase4 = (p' :+: Top :|-: q) :=: (Top :|-: q)
nseqcase5 = (p :|-: q) :=: (p :|-: Bot)
nsequents = [nseqcase1
            ,nseqcase2
            ,nseqcase3
            ,nseqcase4
            ,nseqcase5
            ]

simpleModusPonens = [ (GammaV 1 :|-: ss (phi_ :->: phi'_))    :=: (sa p_    :|-: ss (p_ :->: p'_))
                    , (GammaV 3 :|-: ss phi_)                  :=: (sa p'_   :|-: ss p_)
                    , ((GammaV 1 :+: GammaV 3) :|-: ss phi'_)  :=: ((sa p_ :+: sa p'_) :|-: ss p'_)
                    ]

simpleModusPonens2 = [ (GammaV 1 :|-: ss (phi_ :->: phi'_))    :=: (GammaV 2   :|-: ss (p_ :->: p_))
                     , (GammaV 3 :|-: ss phi_)                  :=: (GammaV 4   :|-: ss p_)
                     , ((GammaV 1 :+: GammaV 3) :|-: ss phi'_)  :=: ((GammaV 2 :+: GammaV 4) :|-: ss p_)
                     ]

simpleModusPonensErr = [ ((GammaV 1) :|-: ss (phi_ :->: phi'_)) :=: 
                         ((sa p_)    :|-: ss (p_ :->: p'_))
                       , ((GammaV 3) :|-: psi) :=: 
                         ((sa p'_) :|-: q)
                       , ((sa p_) :+: (sa p'_) :|-: psi') :=: 
                         ((GammaV 2 :+: GammaV 4) :|-: q)
                       ]

simpleCI          = [ ((GammaV 1 :+: sa phi_) :|-: ss phi'_)        :=: (sa p_ :|-: ss p'_)
                    , (GammaV 1 :|-: ss (phi_ :->: phi'_))         :=: (Top   :|-: ss (p_ :->: p'_))
                    ]

simpleCI2         = [ ((GammaV 1 :+: sa phi_) :|-: ss phi'_)        :=: ((sa p_ :+: sa p_) :|-: ss p'_)
                    , (GammaV 1 :|-: ss (phi_ :->: phi'_))         :=: (Top               :|-: ss (p_ :->: p'_))
                    ]

simpleCI3         = [ ((GammaV 1 :+: sa phi_) :|-: ss phi'_)        :=: ((sa p'_ :+: sa p_) :|-: ss p'_)
                    , (GammaV 1 :|-: ss (phi_ :->: phi'_))         :=: (sa p'_             :|-: ss (p_ :->: p'_))
                    ]

simpleCI4         = [ ((GammaV 1 :+: sa phi_) :|-: ss phi'_)        :=: (sa p_ :|-: ss p'_)
                    , (GammaV 1 :|-: ss (phi_ :->: phi'_))         :=: (sa p_ :|-: ss (p_ :->: p'_))
                    ]

simpleCIErr       = [ ((GammaV 1 :+: sa phi_) :|-: ss phi'_)        :=: (sa p'_ :|-: ss p'_)
                    , (GammaV 1 :|-: ss (phi_ :->: phi'_))         :=: (Top    :|-: ss (p_ :->: p'_))
                    ]

simpleCIErr2      = [ ((GammaV 1 :+: sa phi_) :|-: ss phi'_)        :=: (sa p_  :|-: ss p'_)
                    , (GammaV 1 :|-: ss (phi_ :->: phi'_))         :=: (sa p'_ :|-: ss (p_ :->: p'_))
                    ]

simpleCIErr3      = [ ((GammaV 1 :+: sa phi_) :|-: ss phi'_)        :=: (sa p_                     :|-: ss p'_)
                    , (GammaV 1 :|-: ss (phi_ :->: phi'_))         :=: ((Top :+: sa p_ :+: sa p'_):|-: ss (p_ :->: p'_))
                    ]


-------------------
--  Test Syntax  --
-------------------


p_ :: PureForm
p_ = PP 1

p'_ :: PureForm
p'_ = PP 2

phi_ :: PureForm
phi_ = PPhi 1

phi'_ :: PureForm
phi'_ = PPhi 2

ss = SS . liftToSequent 

sa = SA . liftToSequent

p :: PropSequentCalc Antecedent
p = sa p_

p' :: PropSequentCalc Antecedent
p' = sa p'_

phi :: PropSequentCalc Antecedent
phi = sa phi_

psi :: PropSequentCalc Succedent
psi = ss phi_

psi' :: PropSequentCalc Succedent
psi' = ss phi'_

q :: PropSequentCalc Succedent
q = ss p_

q' :: PropSequentCalc Succedent
q' = ss p'_
