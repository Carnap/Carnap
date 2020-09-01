{-#LANGUAGE OverloadedStrings #-}
module Filter.Diagrams (makeDiagrams)
where

import           Prelude
import           Control.Monad.IO.Class          (liftIO)
import           Control.Monad.State.Lazy as S   (StateT, get, modify)
import           Graphics.Svg.Core (renderToFile)
import           Control.Lens ((.~), (&))
import qualified Data.Text as T
import           Diagrams.Backend.SVG
import           Diagrams.TwoD.Size
import qualified Diagrams.Builder                as DB
import           Diagrams.Prelude                (centerXY, pad)
import           Linear                          (V2 (..), zero)
import           System.Directory                (createDirectoryIfMissing)
import           System.FilePath                 ((<.>), (</>))
import           System.IO
import           Text.Pandoc.Definition


makeDiagrams :: FilePath -> Block -> StateT [T.Text] IO (Block)
makeDiagrams path cb@(CodeBlock (_,classes,_) contents)
    | "diagram" `elem` classes = if "snip" `elem` classes
                                     then do S.modify (\x -> contents:x)
                                             return $ RawBlock "html" ""
                                     else do snips <- S.get
                                             svg <- liftIO $ activate path classes contents snips
                                             return svg
    | otherwise = return cb
makeDiagrams _ x = return x

activate :: FilePath -> p -> T.Text -> [T.Text] -> IO Block
activate path _ cnt snips =
        do let lns  = T.lines cnt
           let expr = if lns /= [] then head $ T.lines cnt else ""
           let snip = if lns /= [] then T.unlines $ tail $ T.lines cnt else ""
           mdia <- compileDiagram path expr [] (snip:snips)
           case mdia of
              Left s -> return $ RawBlock "html" $ T.pack s
              Right s -> return $ RawBlock "html" $ T.pack
                 ("<img src=\"/hash/" ++ s ++ "\">")

compileDiagram :: FilePath -> T.Text -> [(String,String)] -> [T.Text] -> IO (Either String String)
compileDiagram path expr _ src = do
  ensureDir "/tmp/"

  let bopts :: DB.BuildOpts SVG V2 Double
      bopts = DB.mkBuildOpts SVG zero
                ( SVGOptions
                    { _size = (mkWidth 600)
                    , _svgDefinitions = Nothing
                    , _idPrefix = ""
                    , _svgAttributes = []
                    , _generateDoctype = False
                    }
                )
                & DB.snippets .~ (map T.unpack src)
                & DB.imports  .~
                [ "Diagrams.Prelude"
                , "Diagrams.Backend.SVG"
                ]
                & DB.pragmas .~ ["NoMonomorphismRestriction, DeriveDataTypeable"]
                & DB.diaExpr .~ (T.unpack expr)
                & DB.postProcess .~ (pad 1.1 . centerXY)
                & DB.decideRegen .~ (DB.hashedRegenerate (\_ opts' -> opts') (path </> "cache/") )

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
  mkFile base = path </> "cache" </> base <.> ".svg"
  ensureDir = createDirectoryIfMissing True
