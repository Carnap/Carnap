module Carnap.GHCJS.SharedFunctions
        (simpleCipher, simpleDecipher, simpleHash, inOpts,rewriteWith)
    where

import Data.Bits (xor)
import Data.List (foldl')
import qualified Data.Map as M
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Languages.PurePropositional.Logic
import Carnap.Languages.PureFirstOrder.Logic
import Control.Monad

inOpts :: String -> M.Map String String -> Bool
inOpts s opts = s `elem` optList
    where optList = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          
rewriteWith :: M.Map String String -> String -> String
rewriteWith opts = case rewriter of
                       Just f -> f . turnstileHandler
                       Nothing -> turnstileHandler
    where rewriter = (M.lookup "system" opts >>= ofPropSys ndNotation)
             `mplus` (M.lookup "system" opts >>= ofFOLSys ndNotation)
          turnstileHandler = if "double-turnstile" `inOpts` opts 
                                 then map (\c -> if c == '⊢' then '⊨' else c)
                                 else id

simpleCipher :: String -> [Int]
simpleCipher x =  spliceWithWallis (map fromEnum x)

simpleDecipher :: [Int] -> String
simpleDecipher x = map toEnum (spliceWithWallis x)

simpleHash :: Enum a => [a] -> Int
simpleHash = foldl' (\h c -> 19*h `xor` fromEnum c) 21938

spliceWithWallis = zipWith xor (cycle $ map fromEnum "wallis")
