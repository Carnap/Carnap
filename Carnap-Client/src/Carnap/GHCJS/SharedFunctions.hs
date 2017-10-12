module Carnap.GHCJS.SharedFunctions
        (simpleCipher, simpleDecipher)
    where

import Data.Bits (xor)

simpleCipher :: String -> [Int]
simpleCipher x =  spliceWithWallis (map fromEnum x)

simpleDecipher :: [Int] -> String
simpleDecipher x = map toEnum (spliceWithWallis x)

spliceWithWallis = zipWith xor (cycle $ map fromEnum "wallis")
