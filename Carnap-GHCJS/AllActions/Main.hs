module Main where

import Carnap.GHCJS.Action.SyntaxCheck
import Carnap.GHCJS.Action.Translate

main :: IO ()
main = do syntaxCheckAction
          translateAction
