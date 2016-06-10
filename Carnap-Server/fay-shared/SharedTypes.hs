{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveDataTypeable #-}
module SharedTypes where

import Prelude
import Data.Data
import Fay.Yesod

data Command = GetFib Int (Returns Int)
    deriving (Typeable, Data)

