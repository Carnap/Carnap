{-#LANGUAGE OverloadedStrings #-}
module Filter.Diagrams (makeDiagrams)
where

import           Prelude
import           Control.Monad                   (when)
import           Data.Char                       (toLower)
import           Data.List                       (delete, tails)
import           Lucid
import           Control.Lens ((.~), (&))
--import           Diagrams.Backend.Cairo
--import           Diagrams.Backend.Cairo.Internal
import           Diagrams.Backend.SVG
import           Diagrams.TwoD.Size
import qualified Diagrams.Builder                as DB
import           Diagrams.Prelude                (centerXY, pad, (&), (.~))
--import           Diagrams.Size                   (dims)
import           Linear                          (V2 (..), zero)
import           System.Directory                (createDirectoryIfMissing)
import           System.FilePath                 ((<.>), (</>))
import           System.IO
import           Text.Pandoc.Definition


makeDiagrams :: Block -> IO (Block)
makeDiagrams cb@(CodeBlock (_,classes,_) contents)
    | "diagram" `elem` classes = do svg <- activate classes contents
                                    return $ Div ("",[],[]) [svg]
    | otherwise = return cb
makeDiagrams x = return x

activate cls cnt = do mdia <- compileDiagram cnt [] ""
                      case mdia of 
                         Left s -> return $ RawBlock "html" s
                         Right s -> return $ RawBlock "html" 
                            ("<img src=\"/hash/" ++ s ++ "\">")

compileDiagram :: String -> [(String,String)] -> String -> IO (Either String String)
compileDiagram expr attrs src = do
  ensureDir "/tmp/"

  let bopts :: DB.BuildOpts SVG V2 Double
      bopts = DB.mkBuildOpts SVG zero (SVGOptions (mkWidth 250) Nothing "")
                & DB.snippets .~ [src]
                & DB.imports  .~
                [ "Diagrams.Prelude" 
                , "Diagrams.Backend.SVG"
                ]
                --   [ "Diagrams.TwoD.Types"      -- WHY IS THIS NECESSARY =(
                --   , "Diagrams.Core.Points"
                --       -- GHC 7.2 bug?  need  V (Point R2) = R2  (see #65)
                --   , "Diagrams.Backend.SVG"
                --   , "Graphics.SVGFonts"
                --   , "Data.Typeable"
                --   ]
                & DB.pragmas .~ ["NoMonomorphismRestriction, DeriveDataTypeable"]
                & DB.diaExpr .~ expr
                & DB.postProcess .~ (pad 1.1 . centerXY)
                & DB.decideRegen .~ (DB.hashedRegenerate (\hash opts' -> opts') "/root/book/cache/")

  res <- DB.buildDiagram bopts

  case res of
    DB.ParseErr err    -> do
      hPutStrLn stderr ("\nError while parsing\n" ++ src)
      hPutStrLn stderr err
      return $ Left "Error while parsing: "

    DB.InterpErr ierr  -> do
      hPutStrLn stderr ("\nError while interpreting\n" ++ src)
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
