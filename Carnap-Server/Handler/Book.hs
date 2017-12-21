module Handler.Book where

import Import
import System.Directory (getDirectoryContents, doesDirectoryExist)



getBookR :: Handler Html
getBookR = do datadir <- appDataRoot <$> (appSettings <$> getYesod)
              cdir <- lift $ getDirectoryContents (datadir </> "book/")
              let ccount = zip (map getTitle $ filter ctitle cdir) [1 ..] 
              let acount = zip3 (map getTitle $ filter atitle  cdir) [1 ..] [length ccount + 1 ..]
              defaultLayout $ do
                  setTitle $ "The Carnap Book"
                  $(widgetFile "carnap-book")
    where ctitle x = take 7 x == "chapter"
          atitle x = take 8 x == "appendix"

getTitle s = case break (== '_') s of
               (_,[]) -> Nothing
               (_,a)  -> 
                  case break (== '_') (drop 1 a) of
                      (_, []) -> Nothing
                      (b, _) -> Just b

-- TODO: get pandoc metadata from chapters, including TOC links and titles
