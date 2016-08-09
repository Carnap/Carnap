{-#LANGUAGE DeriveGeneric #-}
module Carnap.GHCJS.SharedTypes (
        GHCJSCommand(..)
) where

import Prelude
import Data.Aeson
import GHC.Generics

data GHCJSCommand = 
        EchoBack (String, Bool)
        deriving (Generic, Show)

instance ToJSON GHCJSCommand

instance FromJSON GHCJSCommand
