{-#LANGUAGE FlexibleContexts#-}

module Main where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.Combination
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Core.Examples.ACUI
import System.CPUTime
import System.Exit (exitFailure)

main = do putStrLn ""
          testPositives [pseqcase1
                        ,pseqcase2
                        ,pseqcase3
                        ,pseqcase4
                        ,pseqcase5
                        ,pseqcase6
                        ]
          testNegatives [nseqcase1
                        ,nseqcase2
                        ,nseqcase3
                        ,nseqcase4
                        ,nseqcase5
                        ]
          timeCombine [pacuicase1] "big positive acui" (posTest pacuicase1)
          timeCombine [nacuicase1] "big negative acui" (negTest nacuicase1)
          timeCombine simpleModusPonens "positive modus ponens" (posTest "modus ponens")
          timeAltCombine simpleModusPonens "alt positive modus ponens" (posTest "modus ponens")
          timeCombine simpleModusPonens "positive modus ponens 2" (posTest "modus ponens")
          timeCombine simpleModusPonensErr "negative modus ponens" (negTest "modus ponens")
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

testTemplate :: (a -> Bool) -> String -> a -> IO ()
testTemplate pred desc x = if pred x then return ()
                                     else do putStrLn $ "test " ++ desc ++ " failed"
                                             exitFailure

posTest eq = (testTemplate (not . null) (show eq ++ " as Positive" ))

negTest eq = (testTemplate null (show eq ++ " as Negative" ))

testNegatives = mapM (\eqs -> timeCombine [eqs] ("Negative test of " ++ show eqs) (negTest eqs))
                            
testPositives = mapM (\eqs -> timeCombine [eqs] ("Positive test of " ++ show eqs) (posTest eqs))

pacuicase1 = (parseTerm "f(a u b u c u d u e)" :=: parseTerm "f(b u c u d u a)")

nacuicase1 = parseTerm "g(a u b u c u d u e)" :=: parseTerm "f(b u c u d u a)"

pseqcase1 = p :|-: q :=: (p :|-: q)
pseqcase2 = ((p :+: p) :|-: q) :=: (p :|-: q)
pseqcase3 = p :+: Top :|-: q :=: (p :|-: q)
pseqcase4 = ((p :+: GammaV 1) :|-: q) :=: (p :|-: q)
pseqcase5 = phi :+: GammaV 1 :|-: q :=: (p :|-: q)
pseqcase6 = phi :+: phi :|-: q :=: (p :|-: q)

nseqcase1 = p' :|-: q :=: (p :|-: q)
nseqcase2 = p' :+: p :|-: q :=: (p :|-: q)
nseqcase3 = ((p' :+: Top) :|-: q) :=: (p :|-: q)
nseqcase4 = p' :+: Top :|-: q :=: (Top :|-: q)
nseqcase5 = p :|-: q :=: (p :|-: Bot)

simpleModusPonensErr = [ ((GammaV 1) :|-: SS (phi_ :->-: phi'_)) :=: 
                         ((GammaV 2) :|-: SS (p_ :->-: p'_))
                       , ((GammaV 3) :|-: psi) :=: 
                         ((GammaV 4) :|-: q)
                       , ((GammaV 1 :+: GammaV 3) :|-: psi') :=: 
                         ((GammaV 2 :+: GammaV 4) :|-: q)
                       ]

simpleModusPonens = [ ((GammaV 1) :|-: SS (phi_ :->-: phi'_)) :=: 
                      ((GammaV 2) :|-: SS (p_ :->-: p'_))
                    , ((GammaV 3) :|-: psi) :=: 
                      ((GammaV 4) :|-: q)
                    , ((GammaV 1 :+: GammaV 3) :|-: psi') :=: 
                      ((GammaV 2 :+: GammaV 4) :|-: SS p'_)
                    ]

simpleModusPonens2 = [ ((GammaV 1) :|-: SS (phi_ :->-: phi'_)) :=: 
                       ((GammaV 2) :|-: SS (p_ :->-: p_))
                     , ((GammaV 3) :|-: psi) :=: 
                       ((GammaV 4) :|-: q)
                     , ((GammaV 1 :+: GammaV 3) :|-: psi') :=: 
                       ((GammaV 2 :+: GammaV 4) :|-: SS p_)
                     ]

altCombine :: [Equation PropSequentCalc] -> [[Equation PropSequentCalc]]
altCombine eqs = evalTerm $ combine $ succs ++ head (evalTerm $ foUnifySys (const False) ants)
        where succPair :: Equation PropSequentCalc -> Equation PropSequentCalc
              succPair ((_ :|-: x):=:(_:|-: y))  = x :=: y
              antPair :: Equation PropSequentCalc -> Equation PropSequentCalc
              antPair  ((x :|-: _):=:(y:|-: _))  = x :=: y
              ants  = map antPair eqs
              succs = map succPair eqs


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
