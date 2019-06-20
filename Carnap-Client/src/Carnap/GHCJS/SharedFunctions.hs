module Carnap.GHCJS.SharedFunctions
        (simpleCipher, simpleDecipher, simpleHash)
    where

import Data.Bits (xor)
import Data.List (foldl')

simpleCipher :: String -> [Int]
simpleCipher x =  spliceWithWallis (map fromEnum x)

simpleDecipher :: [Int] -> String
simpleDecipher x = map toEnum (spliceWithWallis x)

simpleHash :: Enum a => [a] -> Int
simpleHash = foldl' (\h c -> 19*h `xor` fromEnum c) 21938

spliceWithWallis = zipWith xor (cycle $ map fromEnum "wallis")
