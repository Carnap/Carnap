-- | Example of defining FFI functions.
--
-- The `ffi' method is currently incompatible with 'RebindableSyntax',
-- so these are defined in another module.

module FFIExample where

import Data.Text (Text)
import DOM
import FFI

onKeyUp :: Element -> Fay () -> Fay ()
onKeyUp = ffi "%1.onkeyup=%2"

setInnerHTML :: Element -> Text -> Fay ()
setInnerHTML = ffi "%1.innerHTML=%2"
