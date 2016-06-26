{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveDataTypeable #-}
module SharedTypes where

import Prelude
import Data.Data
import Fay.Yesod
import Data.Text

data Command = GetFib Int (Returns Int)
             | PutComment Text (Returns Bool)
             | GetComments (Returns [(Text,Text)])
    deriving (Typeable, Data)

