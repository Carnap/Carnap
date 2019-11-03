module Main where

import Lib (initCallbackObj)
import Carnap.GHCJS.Action.SyntaxCheck
import Carnap.GHCJS.Action.ProofCheck
import Carnap.GHCJS.Action.Translate
import Carnap.GHCJS.Action.TruthTable
import Carnap.GHCJS.Action.CounterModel
import Carnap.GHCJS.Action.QualitativeProblem
import Carnap.GHCJS.Action.SequentCheck
import Carnap.GHCJS.Action.TreeDeductionCheck
import Carnap.GHCJS.Action.AcceptJSON

main :: IO ()
main = do initCallbackObj
          syntaxCheckAction
          translateAction
          proofCheckAction
          truthTableAction
          counterModelAction
          qualitativeProblemAction
          sequentCheckAction
          treeDeductionCheckAction
          acceptJSONAction
