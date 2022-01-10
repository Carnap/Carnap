module Handler.API.AesonHelper where
import           Data.Char (toLower)
import           Data.List (stripPrefix)
import           Prelude

-- | Remove prefix and leading uppercase letter
unPrefix :: String -> String -> String
unPrefix prefix text =
    -- this code is bad on purpose, it will only crash at compile time
    let Just (first:rest) = stripPrefix prefix text
    in toLower first : rest
