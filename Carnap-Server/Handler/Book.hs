module Handler.Book where

import Import
import System.Directory (getDirectoryContents, doesDirectoryExist)

getBookR :: Handler Html
getBookR = do
    cdir <- lift $ do localbook <- doesDirectoryExist "book"
                      if localbook then getDirectoryContents "book"
                                   else getDirectoryContents "/root/book"
    let ccount = zip (filter (\x -> x /= "cache" && x /= "." && x /= "..") cdir) [1 ..] 
    defaultLayout $ do
        setTitle $ "The Carnap Book"
        $(widgetFile "carnap-book")
