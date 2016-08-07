{-#LANGUAGE FlexibleContexts#-}

module Main where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Unification.Combination
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Core.Examples.ACUI
import System.CPUTime
import System.Exit (exitFailure)

main = do putStrLn ""
          testPositives psequents
          altTestPositives psequents
          testNegatives nsequents
          altTestNegatives nsequents
          timeCombine simpleModusPonens "positive modus ponens" (posTest "combine modus ponens")
          timeAltCombine simpleCI "alt positive conditional introduction" (posTest "CI 1")
          timeAltCombine simpleCI2 "alt positive conditional introduction 2" (posTest "CI 2")
          timeAltCombine simpleCI3 "alt positive conditional introduction 3" (posTest "CI 3")
          timeAltCombine simpleCI4 "alt positive conditional introduction 4" (posTest "CI 4")
          timeAltCombine simpleCIErr "alt negative conditional introduction 1" (negTest "CI Neg 1")
          timeAltCombine simpleCIErr2 "alt negative conditional introduction 2" (negTest "CI Neg 2")
          timeAltCombine simpleCIErr3 "alt negative conditional introduction 3" (negTest "CI Neg 3")
          timeAltCombine simpleModusPonens "alt positive modus ponens 1" (posTest "alt modus ponens 1")
          timeAltCombine simpleModusPonens2 "alt positive modus ponens 2" (posTest "alt modus ponens 2")
          timeAltCombine simpleModusPonensErr "alt negative modus ponens 1" (negTest "alt modus ponens err 1")
          --timeCombine [pacuicase1] "big positive acui" (posTest pacuicase1)
          --timeCombine [nacuicase1] "big negative acui" (negTest nacuicase1)
          putStrLn ""

--test must be nontrivial or it optimizes away the test results
timeCombine eqs desc test = do startTime <- getCPUTime
                               let subs = evalTerm $ combine eqs
                               test subs
                               finishTime <- getCPUTime
                               let t = fromIntegral (finishTime - startTime) / 1000000000000
                               putStrLn $ "Test Results (" ++ desc ++ "):" ++ show t

timeAltCombine eqs desc test = do startTime <- getCPUTime
                                  let subs = altCombine eqs
                                  test subs
                                  finishTime <- getCPUTime
                                  let t = fromIntegral (finishTime - startTime) / 1000000000000
                                  putStrLn $ "Test Results (" ++ desc ++ "):" ++ show t

testTemplate :: Show a => (a -> Bool) -> String -> a -> IO ()
testTemplate pred desc x = if pred x then return ()
                                     else do putStrLn $ "test " ++ desc ++ " failed"
                                             putStrLn $ "failing object: " ++ show x
                                             exitFailure

posTest eq = (testTemplate (not . null) (show eq ++ " as Positive" ))

negTest eq = (testTemplate null (show eq ++ " as Negative" ))

testNegatives = mapM (\eqs -> timeCombine [eqs] ("Negative test of " ++ show eqs) (negTest eqs))

altTestNegatives = mapM (\eqs -> timeAltCombine [eqs] ("Alternative Negative test of " ++ show eqs) (negTest eqs))
                            
testPositives = mapM (\eqs -> timeCombine [eqs] ("Positive test of " ++ show eqs) (posTest eqs))

altTestPositives = mapM (\eqs -> timeAltCombine [eqs] ("Alternative Positive test of " ++ show eqs) (posTest eqs))

pacuicase1 = (parseTerm "f(a u b u c u d u e)" :=: parseTerm "f(b u c u d u a)")

nacuicase1 = parseTerm "g(a u b u c u d u e)" :=: parseTerm "f(b u c u d u a)"

pseqcase1 = p :|-: q :=: (p :|-: q)
pseqcase2 = ((p :+: p) :|-: q) :=: (p :|-: q)
pseqcase3 = p :+: Top :|-: q :=: (p :|-: q)
pseqcase4 = ((p :+: GammaV 1) :|-: q) :=: (p :|-: q)
pseqcase5 = phi :+: GammaV 1 :|-: q :=: (phi :|-: q)
pseqcase6 = phi :+: phi :|-: q :=: (p :|-: q)
psequents = [pseqcase1
            ,pseqcase2
            ,pseqcase3
            ,pseqcase4
            --,pseqcase5 --XXX: these cases won't wokr with altCombine,
            --since there are formula variables in the antecedent left
            --undetermined by the succedent
            --,pseqcase6 
            ]

nseqcase1 = p' :|-: q :=: (p :|-: q)
nseqcase2 = p' :+: p :|-: q :=: (p :|-: q)
nseqcase3 = ((p' :+: Top) :|-: q) :=: (p :|-: q)
nseqcase4 = p' :+: Top :|-: q :=: (Top :|-: q)
nseqcase5 = p :|-: q :=: (p :|-: Bot)
nsequents = [nseqcase1
            ,nseqcase2
            ,nseqcase3
            ,nseqcase4
            ,nseqcase5
            ]


simpleModusPonens = [ (GammaV 1 :|-: SS (phi_ :->-: phi'_))    :=: (SA p_    :|-: SS (p_ :->-: p'_))
                    , (GammaV 3 :|-: SS phi_)                  :=: (SA p'_   :|-: SS p_)
                    , ((GammaV 1 :+: GammaV 3) :|-: SS phi'_)  :=: ((SA p_ :+: SA p'_) :|-: SS p'_)
                    ]

simpleModusPonens2 = [ (GammaV 1 :|-: SS (phi_ :->-: phi'_))    :=: (GammaV 2   :|-: SS (p_ :->-: p_))
                     , (GammaV 3 :|-: SS phi_)                  :=: (GammaV 4   :|-: SS p_)
                     , ((GammaV 1 :+: GammaV 3) :|-: SS phi'_)  :=: ((GammaV 2 :+: GammaV 4) :|-: SS p_)
                     ]

simpleModusPonensErr = [ ((GammaV 1) :|-: SS (phi_ :->-: phi'_)) :=: 
                         ((SA p_)    :|-: SS (p_ :->-: p'_))
                       , ((GammaV 3) :|-: psi) :=: 
                         ((SA p'_) :|-: q)
                       , ((SA p_) :+: (SA p'_) :|-: psi') :=: 
                         ((GammaV 2 :+: GammaV 4) :|-: q)
                       ]

simpleCI          = [ ((GammaV 1 :+: SA phi_) :|-: SS phi'_)        :=: (SA p_ :|-: SS p'_)
                    , (GammaV 1 :|-: SS (phi_ :->-: phi'_))         :=: (Top   :|-: SS (p_ :->-: p'_))
                    ]

simpleCI2         = [ ((GammaV 1 :+: SA phi_) :|-: SS phi'_)        :=: ((SA p_ :+: SA p_) :|-: SS p'_)
                    , (GammaV 1 :|-: SS (phi_ :->-: phi'_))         :=: (Top               :|-: SS (p_ :->-: p'_))
                    ]

simpleCI3         = [ ((GammaV 1 :+: SA phi_) :|-: SS phi'_)        :=: ((SA p'_ :+: SA p_) :|-: SS p'_)
                    , (GammaV 1 :|-: SS (phi_ :->-: phi'_))         :=: (SA p'_             :|-: SS (p_ :->-: p'_))
                    ]

simpleCI4         = [ ((GammaV 1 :+: SA phi_) :|-: SS phi'_)        :=: (SA p_ :|-: SS p'_)
                    , (GammaV 1 :|-: SS (phi_ :->-: phi'_))         :=: (SA p_ :|-: SS (p_ :->-: p'_))
                    ]

simpleCIErr       = [ ((GammaV 1 :+: SA phi_) :|-: SS phi'_)        :=: (SA p'_ :|-: SS p'_)
                    , (GammaV 1 :|-: SS (phi_ :->-: phi'_))         :=: (Top    :|-: SS (p_ :->-: p'_))
                    ]

simpleCIErr2      = [ ((GammaV 1 :+: SA phi_) :|-: SS phi'_)        :=: (SA p_  :|-: SS p'_)
                    , (GammaV 1 :|-: SS (phi_ :->-: phi'_))         :=: (SA p'_ :|-: SS (p_ :->-: p'_))
                    ]

simpleCIErr3      = [ ((GammaV 1 :+: SA phi_) :|-: SS phi'_)        :=: (SA p_                     :|-: SS p'_)
                    , (GammaV 1 :|-: SS (phi_ :->-: phi'_))         :=: ((Top :+: SA p_ :+: SA p'_):|-: SS (p_ :->-: p'_))
                    ]

altCombine :: [Equation PropSequentCalc] -> [[Equation PropSequentCalc]]
altCombine eqs = case evalTerm $ foUnifySys (const False) succs of
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

p_ :: PropSequentCalc (Form Bool)
p_ = SeqProp 1

p'_ :: PropSequentCalc (Form Bool)
p'_ = SeqProp 2

phi_ :: PropSequentCalc (Form Bool)
phi_ = SeqPhi 1

phi'_ :: PropSequentCalc (Form Bool)
phi'_ = SeqPhi 2

p :: PropSequentCalc Antecedent
p = SA p_

p' :: PropSequentCalc Antecedent
p' = SA p'_

phi :: PropSequentCalc Antecedent
phi = SA phi_

psi :: PropSequentCalc Succedent
psi = SS phi_

psi' :: PropSequentCalc Succedent
psi' = SS phi'_

q :: PropSequentCalc Succedent
q = SS p_

q' :: PropSequentCalc Succedent
q' = SS p'_
