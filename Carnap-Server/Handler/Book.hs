module Handler.Book where

import Import
import System.Directory (getDirectoryContents)

getBookR :: Handler Html
getBookR = do
    cdir <- lift $ getDirectoryContents "book"
    let ccount = zip (filter (\x -> x /= "." && x /= "..") cdir) [1 ..] 
    defaultLayout $ do
        setTitle $ "The Carnap Book"
        $(widgetFile "carnap-book")
