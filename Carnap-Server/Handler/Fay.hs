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
      Just (GetComments r)      -> do comments <- getComments
                                      render r comments
      Nothing                   -> invalidArgs ["Invalid command"]

insertComment cmmt = do
        id <- maybeAuthId
        case id of
            Nothing -> return False
            Just _ -> do runDB $ insertEntity $ Comment cmmt id 
                         return True

getComments = do cmmts <- runDB $ selectList [] []
                 let pairs = map (toPair . fromEnt) cmmts
                 mapM clean pairs
    where toPair (Comment msg mu)  = (mu, msg)

          clean :: (Maybe (Key User), Text) -> Handler (Text,Text)
          clean (Nothing, s)  = return ("annonyous", s)
          clean (Just uid, s) = do usr <- runDB $ get404 uid
                                   return (userIdent usr,s)

          fromEnt (Entity k v) = v
