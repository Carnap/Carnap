module Handler.Fay where

import Fay.Convert (readFromFay)
import Import
import Prelude     ((!!))
import Yesod.Fay
import Model (Comment)

fibs :: [Int]
fibs = 0 : 1 : zipWith (+) fibs (drop 1 fibs)

onCommand :: CommandHandler App
onCommand render command =
    case readFromFay command of
      Just (PutComment cmmt r)  -> do success <- insertComment cmmt 
                                      render r success
      Just (GetFib idx r)       -> render r $ fibs !! idx
      Nothing                   -> invalidArgs ["Invalid command"]

insertComment cmmt = do
        id <- maybeAuthId
        case id of
            Nothing -> return False
            Just _ -> do runDB $ insertEntity $ Comment cmmt id 
                         return True
