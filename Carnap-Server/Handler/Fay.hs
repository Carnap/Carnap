module Handler.Fay where

import Fay.Convert (readFromFay)
import Import
import Prelude     ((!!))
import Yesod.Fay

fibs :: [Int]
fibs = 0 : 1 : zipWith (+) fibs (drop 1 fibs)

onCommand :: CommandHandler App
onCommand render command =
    case readFromFay command of
      Just (GetFib idx r) -> render r $ fibs !! idx
      Nothing             -> invalidArgs ["Invalid command"]
