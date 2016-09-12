module Handler.Book where

import Import
import System.Directory (getDirectoryContents, doesDirectoryExist)



getBookR :: Handler Html
getBookR = do cdir <- lift $ do localbook <- doesDirectoryExist "book"
                                if localbook then getDirectoryContents "book"
                                             else getDirectoryContents "/root/book"
              let ccount = zip (filter (\x -> take 7 x == "chapter") cdir) [1 ..] 
              let acount = zip3 (filter (\x -> take 8 x == "appendix") cdir) [1 ..] [length ccount + 1 ..]
              defaultLayout $ do
                  setTitle $ "The Carnap Book"
                  $(widgetFile "carnap-book")

-- TODO: get pandoc metadata from chapters, including TOC links and titles
