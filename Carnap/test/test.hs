{-#LANGUAGE FlexibleContexts#-}

module Main where

import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Core.Examples.ACUI
import System.CPUTime

main = do putStrLn ""
          t1 <- timeCombine 
                    (parseTerm "f(a u b u c u d u e)") 
                    (parseTerm "f(b u c u d u a)")
          t2 <- timeCombine 
                    (parseTerm "g(a u b u c u d u e)") 
                    (parseTerm "f(b u c u d u a)")
          t3 <- timeCombine b b
          putStrLn $ "Test Results (Positive Case):" ++ show t1 
          putStrLn $ "Test Results (Negative Case):" ++ show t2
          putStrLn ""

time :: Fractional c => (a -> IO b) -> a -> IO c
time action arg = do startTime <- getCPUTime
                     action arg
                     finishTime <- getCPUTime
                     return $ fromIntegral (finishTime - startTime) / 1000000000000

time' f = time (\x -> f x `seq` return ())

timeCombine x y = time' (\z -> evalTerm $ combine [x :=: z]) y
