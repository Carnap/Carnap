module Main where

import Carnap.GHCJS.Action.SyntaxCheck
import Carnap.GHCJS.Action.ProofCheck
import Carnap.GHCJS.Action.Translate
import Carnap.GHCJS.Action.TruthTable

main :: IO ()
main = do syntaxCheckAction
          translateAction
          proofCheckAction
          truthTableAction
