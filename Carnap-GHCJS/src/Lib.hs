{-# LANGUAGE DeriveDataTypeable, CPP, JavaScriptFFI #-}
module Lib
    ( someFunc, jsonCommand
    ) where

import Data.Data
import Data.Aeson
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Marshal

someFunc :: IO ()
someFunc = Prelude.putStrLn "someFunc"

#ifdef __GHCJS__
-- | Run the AJAX command.
foreign import javascript unsafe "jsonCommand($1)" jsonCommand :: JSString -> IO ()

-- | Run the AJAX command, handling errors as well
#else
jsonCommand :: JSString -> IO ()
jsonCommand = error "jsonCommand requires JS FFI"
#endif
