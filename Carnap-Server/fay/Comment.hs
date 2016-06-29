{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE OverloadedStrings #-}

module Comment where

import           FFIExample

import           DOM
import           Data.Text (fromString)
import qualified Data.Text as T
import           Fay.Yesod
import           Prelude
import           SharedTypes

main :: Fay ()
main = do 
    input <- getElementById "newcomment"
    result <- getElementById "commentsuccess"
    comments <- getElementById "comments"
    onKeyUp input $ \e -> do
        cmmttext <- getValue input
        k <- getKeyCode e
        if k == 13 then
            call (PutComment cmmttext) $ 
                \x -> if x then do setInnerHTML result "comment posted"
                                   updateComments comments
                           else alert "You can only post a comment if you're logged into your account"
        else
            return ()
    updateComments comments

toSpans (x,y) = do s1 <- createElement "span"
                   setInnerHTML s1 (T.append x ": ")
                   s2 <- createElement "span"
                   setInnerHTML s2 y
                   div <- createElement "div"
                   appendChild div s1
                   appendChild div s2
                   return div

updateComments comments = do
    setInnerHTML comments ""
    call GetComments $ \x -> do divs <- mapM toSpans x
                                mapM_ (appendChild comments) divs
