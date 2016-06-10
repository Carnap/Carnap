{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE OverloadedStrings #-}

module Home where

import           FFIExample

import           DOM
import           Data.Text (fromString)
import qualified Data.Text as T
import           Fay.Yesod
import           Prelude
import           SharedTypes

main :: Fay ()
main = do
    input <- getElementById "fibindex"
    result <- getElementById "fibresult"
    onKeyUp input $ do
        indexS <- getValue input
        index <- parseInt indexS
        call (GetFib index) $ setInnerHTML result . T.pack . show
