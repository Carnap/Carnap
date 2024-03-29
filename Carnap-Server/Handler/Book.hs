module Handler.Book where

import           Import
import           System.Directory (getDirectoryContents)

-- XXX: for uniformity, merge this with ChapterR

getBookR :: Handler Html
getBookR = do bookdir <- appBookRoot <$> (appSettings <$> getYesod)
              cdir <- liftIO $ getDirectoryContents bookdir
              let ccount = zip (map getTitle $ filter ctitle cdir) [1 :: Integer ..]
              let acount = zip3 (map getTitle $ filter atitle cdir) [1 :: Integer ..] [length ccount + 1 ..]
              defaultLayout $ do
                  setTitle $ "The Carnap Book"
                  $(widgetFile "carnap-book")
    where ctitle x = take 7 x == "chapter"
          atitle x = take 8 x == "appendix"

getTitle :: [Char] -> Maybe [Char]
getTitle s = case break (== '_') s of
               (_,[]) -> Nothing
               (_,a)  ->
                  case break (== '_') (drop 1 a) of
                      (_, []) -> Nothing
                      (b, _)  -> Just b

-- TODO: get pandoc metadata from chapters, including TOC links and titles
