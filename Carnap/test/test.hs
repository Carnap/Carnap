{-#LANGUAGE QuasiQuotes, FlexibleContexts#-}

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
import Carnap.Languages.PureFirstOrder.Logic (folCalc)
import Carnap.Languages.PureSecondOrder.Logic (msolCalc,psolCalc)
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..),RenderStyle(..), Inference(..))
import Carnap.Calculi.NaturalDeduction.Checker (ProofErrorMessage(..), Feedback(..), seqSubsetUnify, processLine, 
    processLineFitch, hoProcessLine, hoProcessLineMemo, toDisplaySequence, toDisplaySequenceMemo)
import Carnap.Core.Examples.ACUI
import Text.Shakespeare.Text
import Data.Text (unpack)
import Data.IORef
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
          mapM compTiming [1 .. 5]
          solref <- newIORef mempty
          mapM (compTimingMemo solref) [1 .. 5]
          mapM russTiming [1 .. 5]
          rusref <- newIORef mempty
          mapM (russTimingMemo rusref) [1 .. 5]
          invref <- newIORef mempty
          mapM (invTimingMemo invref) [1 .. 5]
          putStrLn ""
    where compTiming n = timeProof msolCalc                 ("comprehension proof,  attempt " ++ show n) comprehensionTheorem
          compTimingMemo ref n = timeProofMemo ref msolCalc ("comprehension proof,  attempt " ++ show n) comprehensionTheorem
          russTiming n = timeProof folCalc                  ("Russell's theorem,    attempt " ++ show n) russellTheorem
          russTimingMemo ref n = timeProofMemo ref folCalc  ("Russell's theorem,    attempt " ++ show n) russellTheorem
          invTimingMemo ref n = timeProofMemo ref psolCalc  ("Inverse theorem,      attempt " ++ show n) inverseTheorem

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

timeProof ndcalc desc prooftext = do startTime <- getCPUTime
                                     let pt = dropWhile (== '\n') (unpack prooftext)
                                     let ded = ndParseProof ndcalc mempty pt
                                     let Feedback mseq ds = toDisplaySequence (ndProcessLine ndcalc) ded
                                     mapM checkline ds
                                     finishTime <- getCPUTime
                                     let t = fromIntegral (finishTime - startTime)
                                     putStrLn $ "Test Results (" ++ desc ++ "):" ++ show t
    where checkline (Right _) = return ()
          checkline (Left (NoResult _)) = return ()
          checkline (Left e) = do putStrLn $ "test " ++ desc ++ " failed"
                                  exitFailure

timeProofMemo ref ndcalc desc prooftext = 
        do startTime <- getCPUTime
           let pt = dropWhile (== '\n') (unpack prooftext)
           let ded = ndParseProof ndcalc mempty pt
           Feedback mseq ds <- case ndProcessLineMemo ndcalc of
                                   Just memo -> toDisplaySequenceMemo (memo ref) ded
                                   Nothing -> return $ toDisplaySequence (ndProcessLine ndcalc) ded
           mapM checkline ds
           finishTime <- getCPUTime
           let t = fromIntegral (finishTime - startTime)
           putStrLn $ "Test Results (" ++ desc ++ "):" ++ show t
    where checkline (Right _) = return ()
          checkline (Left (NoResult _)) = return ()
          checkline (Left e) = do putStrLn $ "test " ++ desc ++ " failed"
                                  case e of (NoParse e' n) -> putStrLn $ "no parse on line " ++ show n ++ ":" ++ show e'
                                            (NoUnify eqs n) -> 
                                                do putStrLn $ "couldn't unify on line " ++ show n
                                                   mapM (putStrLn . show) eqs
                                                   return ()
                                            (GenericError s n) -> putStrLn $ "on line " ++ show n ++ s
                                  exitFailure

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

-----------------
--  Equations  --
-----------------


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
simpleModusPonens2 = [ (GammaV 1 :|-: ss (phi_ :->: phi'_))    :=: (GammaV 2   :|-: ss (p_ :->: p_)) , (GammaV 3 :|-: ss phi_)                  :=: (GammaV 4   :|-: ss p_)
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

--------------
--  Proofs  --
--------------

aristotleTheorem = [st|
Show: P\/-P
    Show: --(P\/-P)
        -(P\/-P):AS
        Show: -P
            P:AS
            P\/-P:ADD 5
        :ID 6 3
        P\/-P:ADD 4
    :ID 3 8
    P\/-P:DNE 2
:DD 10
|]

pierceTheorem = [st|
  (P->Q)->P:AS
     -P:AS
        P:AS
          Q:AS
          P:R 3
          -P:R 2
        Q:-E 4-6
     P->Q:CI 3-7
     P:CE 8 1
     -P:R 2
  P:-E 2-10
((P->Q)->P)->P:CI 1-11
|]

comprehensionTheorem = [st|
Show EXAx(F(x)/\G(x)<->X(x))
   Show Ax(F(x)/\G(x)<->\y[F(y)/\G(y)](x))
       Show F(c)/\G(c)->\y[F(y)/\G(y)](c)
            F(c)/\G(c):AS
            \y[F(y)/\G(y)](c):ABS 4
       :CD 5
       Show \y[F(y)/\G(y)](c)->F(c)/\G(c)
            \y[F(y)/\G(y)](c):AS
            F(c)/\G(c):APP 8
       :CD 9
       F(c)/\G(c)<->\y[F(y)/\G(y)](c):CB 3 7
   :UD 11
   EXAx(F(x)/\G(x)<->X(x)):EG 2
:DD 13
|]

russellTheorem = [st|
Show -ExAy(-F(y,y) <-> F(x,y))
    ExAy(-F(y,y)<->F(x,y)):AS
    Show: -ExAy(-F(y,y) <-> F(x,y))
        Ay(-F(y,y)<->F(c_1,y)):AS
        -F(c_1,c_1)<->F(c_1,c_1):UI 4
        Show:-F(c_1,c_1)
            F(c_1,c_1):AS
            F(c_1,c_1)->-F(c_1,c_1) :BC 5
            -F(c_1,c_1) :MP 8 7
        :ID 7 9
        -F(c_1,c_1) -> F(c_1,c_1) :BC 5
        F(c_1,c_1) :MP 11 6
        Show: -ExAy(-F(y,y) <-> F(x,y))
        :ID 6 12
    :ED 13 2 4
:ID 2 3
|]

russellTheoremForallx = [st|
    ExAy(-Fyy <-> Fxy):AS
       Ay(-Fyy<->Fry):AS
       -Frr<->Frr:AE 2
            -Frr:AS
            Frr:<->E 3 4
            -Frr:R 4
       Frr:-E 4-6
       -Frr:<->E 7 3
            ExAy(-Fyy <-> Fxy):AS
            Frr:R 7
            -Frr:R 8
       -ExAy(-Fyy <-> Fxy):-I 9-11
    -ExAy(-Fyy <-> Fxy):EE 1 2-12
    ExAy(-Fyy <-> Fxy):R 1
-ExAy(-Fyy <-> Fxy):-I 1-14
|]

inverseTheorem = [st|
Show: AX2EY2∀x∀y(X2(x,y) ↔ Y2(y,x))
  Show: ∀x∀y(X2(x,y) ↔ \w\v[X2(v,w)](y,x))
    Show: ∀y(X2(a,y) ↔ \w\v[X2(v,w)](y,a))
      Show: X2(a,b) -> \w\v[X2(v,w)](b,a)
        X2(a,b):AS
        \w\v[X2(v,w)](b,a):ABS2 5
      :CD 6
      Show: \w\v[X2(v,w)](b,a)-> X2(a,b)
        \w\v[X2(v,w)](b,a):AS
        X2(a,b):APP2 9
      :CD 10
      X2(a,b) <-> \x_1\x_2[X2(x_2,x_1)](b,a):CB 4 8
    :UD 12
  :UD 3
  EY2∀x∀y(X2(x,y) ↔ Y2(y,x)):EG2 2
:UD2 15
|]

simplifiedInverseTheorem = [st|
Show: ∀X2∃Y2∀x∀y(X2(x,y) ↔ Y2(x,y))
  Show: ∀x∀y(X2(x,y) ↔ X2(x,y))
    Show: ∀y(X2(a,y) ↔ X2(a,y))
      Show: X2(a,b) -> X2(a,b)
        X2(a,b):AS
      :CD 5
      X2(a,b) <-> X2(a,b):CB 4 4
    :UD 7
  :UD 3
  ∃Y2∀x∀y(X2(x,y) ↔ Y2(x,y)):EG2 2
:UD2 10
|]

simplifiedInverseTheorem2 = [st|
Show: ∀X2∃Y2∀x∀y(X2(x,y) ↔ Y2(x,y))
  ∀x∀y(X2(x,y) ↔ X2(x,y)):PR
  ∃Y2∀x∀y(X2(x,y) ↔ Y2(x,y)):EG2 2
:UD2 3
|]
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
