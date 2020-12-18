{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.RenderFormulas (renderFormulasAction) where

import Lib
import Data.Map as M
import GHCJS.DOM.Element
import Control.Monad (mplus)
import Text.Parsec
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys)
import Carnap.Languages.ModalPropositional.Logic (ofModalPropSys)
import Carnap.Languages.PureSecondOrder.Logic (ofSecondOrderSys) 
import Carnap.Languages.SetTheory.Logic (ofSetTheorySys)
import Carnap.Languages.ModalFirstOrder.Logic (hardegreeMPLCalc)

renderFormulasAction = initElements (\w dom -> getListOfElementsByTag dom "code") rewriteFormula

rewriteFormula w Nothing = return ()
rewriteFormula w (Just e) = do datamap <- getCarnapDataMap e
                               case M.lookup "render-system" datamap of
                                   Nothing -> return ()
                                   Just system -> do Just text <- getInnerHTML e :: IO (Maybe String)
                                                     setInnerHTML e (Just $ parseWith system (decodeHtml text))
    where parseWith sys text = maybe "Error - No Such System" id $ ((\it -> tryParse it text) `ofPropSys` sys)
                                     `mplus` ((\it -> tryParse it text) `ofFOLSys` sys)
                                     `mplus` ((\it -> tryParse it text) `ofSecondOrderSys` sys)
                                     `mplus` ((\it -> tryParse it text) `ofSetTheorySys` sys)
                                     `mplus` ((\it -> tryParse it text) `ofModalPropSys` sys)
          tryParse calc text = case parse (ndParseForm calc <* eof) "" text of
                                  Left e1 -> case parse (ndParseSeq calc <* eof) "" text of
                                                Left e2 -> "couldn't parse as formula (" ++ show e1 
                                                            ++ ") or sequent (" ++ show e2
                                                            ++ ")"
                                                Right seq -> ndNotation calc . show $ seq
                                  Right f -> ndNotation calc . show $ f
