module Carnap.GHCJS.SharedFunctions
        (simpleCipher)
    where

import Data.Bits (xor)

simpleCipher :: String -> String
simpleCipher x = map toEnum (zipWith xor (cycle $ map fromEnum "wallis") (map fromEnum x))
