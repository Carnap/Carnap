{-#LANGUAGE OverloadedStrings #-}
module Filter.Diagrams (makeDiagrams)
where

import           Prelude
import           Control.Monad.IO.Class          (liftIO)
import           Control.Monad.State.Lazy as S   (StateT, get, modify)
import           Data.Char                       (toLower)
import           Lucid
import           Control.Lens ((.~), (&))
import           Diagrams.Backend.SVG
import           Diagrams.TwoD.Size
import qualified Diagrams.Builder                as DB
import           Diagrams.Prelude                (centerXY, pad, (&), (.~))
import           Linear                          (V2 (..), zero)
import           System.Directory                (createDirectoryIfMissing, doesDirectoryExist)
import           System.FilePath                 ((<.>), (</>))
import           System.IO              
import           Text.Pandoc.Definition


makeDiagrams :: Block -> StateT [String] IO (Block)
makeDiagrams cb@(CodeBlock (_,classes,_) contents)
    | "diagram" `elem` classes = if "snip" `elem` classes 
                                     then do S.modify (\x -> contents:x)
                                             return $ RawBlock "html" ""
                                     else do snips <- S.get
                                             svg <- liftIO $ activate classes contents snips
                                             return svg
    | otherwise = return cb
makeDiagrams x = return x

activate cls cnt snips = do let lns  = lines cnt
                            let expr = if lns /= [] then head $ lines cnt else []
                            let snip = if lns /= [] then unlines $ tail $ lines cnt else []
                            mdia <- compileDiagram expr [] (snip:snips)
                            case mdia of 
                               Left s -> return $ RawBlock "html" s
                               Right s -> return $ RawBlock "html" 
                                  ("<img src=\"/hash/" ++ s ++ "\">")

compileDiagram :: String -> [(String,String)] -> [String] -> IO (Either String String)
compileDiagram expr attrs src = do
  localbook <- doesDirectoryExist "book"
  let path = (if localbook then "book/cache/" else "/root/book/cache/") 
  ensureDir "/tmp/"

  let bopts :: DB.BuildOpts SVG V2 Double
      bopts = DB.mkBuildOpts SVG zero (SVGOptions (mkWidth 600) Nothing "")
                & DB.snippets .~ src
                & DB.imports  .~
                [ "Diagrams.Prelude" 
                , "Diagrams.Backend.SVG"
                ]
                & DB.pragmas .~ ["NoMonomorphismRestriction, DeriveDataTypeable"]
                & DB.diaExpr .~ expr
                & DB.postProcess .~ (pad 1.1 . centerXY)
                & DB.decideRegen .~ (DB.hashedRegenerate (\hash opts' -> opts') path)

  res <- DB.buildDiagram bopts

  case res of
    DB.ParseErr err    -> do
      hPutStrLn stderr ("\nError while parsing\n" ++ err)
      hPutStrLn stderr err
      return $ Left $ "Error while parsing: " ++ err

    DB.InterpErr ierr  -> do
      hPutStrLn stderr ("\nError while interpreting\n")
      hPutStrLn stderr (DB.ppInterpError ierr)
      return $ Left ("Error while interpreting: " ++ DB.ppInterpError ierr)

    DB.Skipped hash    -> do
      hPutStr stderr "."
      hFlush stderr
      --will eventually need to return not just the fil
      return $ Right (DB.hashToHexStr hash <.> ".svg")

    DB.OK hash out -> do
      hPutStr stderr "O"
      hFlush stderr
      let file = mkFile (DB.hashToHexStr hash)
      renderToFile file out
      return $ Right (DB.hashToHexStr hash <.> ".svg")

 where
  mkFile base = "/home/graham/projects/CarnapPrime/Carnap-Server/book/cache/" </> base <.> ".svg"
  ensureDir = createDirectoryIfMissing True 
