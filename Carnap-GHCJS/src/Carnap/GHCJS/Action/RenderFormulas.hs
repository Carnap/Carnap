{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.RenderFormulas (renderFormulasAction) where

import Lib
import Data.Map as M
import GHCJS.DOM.Element
import Control.Monad (mplus)
import Text.Parsec
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys, ofFOLTreeSys)
import Carnap.Languages.DefiniteDescription.Logic.Gamut (ofDefiniteDescSys)
import Carnap.Languages.ModalPropositional.Logic (ofModalPropSys)
import Carnap.Languages.PureSecondOrder.Logic (ofSecondOrderSys) 
import Carnap.Languages.SetTheory.Logic (ofSetTheorySys, ofSetTheoryTreeSys)
import Carnap.Languages.Arithmetic.Logic (ofArithmeticTreeSys)
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
                                     `mplus` ((\it -> tryParse it text) `ofDefiniteDescSys` sys)
                                     `mplus` ((\it -> tryParse it text) `ofModalPropSys` sys)
                                     `mplus` ((\it -> tryParseTree it text) `ofArithmeticTreeSys` sys)
                                     `mplus` ((\it -> tryParseTree it text) `ofSetTheoryTreeSys` sys)
                                     `mplus` ((\it -> tryParseTree it text) `ofFOLTreeSys` sys)
          tryParse calc text = case parse (ndParseForm calc <* eof) "" text of
                                  Left e1 -> case parse (ndParseSeq calc <* eof) "" text of
                                                Left e2 -> failMsg e1 e2
                                                Right seq -> ndNotation calc . show $ seq
                                  Right f -> ndNotation calc . show $ f
          tryParseTree calc text = case parse (tbParseForm calc <* eof) "" text of
                                     Left e1 -> case parse (parseSeqOver (tbParseForm calc) <* eof) "" text of
                                                   Left e2 -> failMsg e1 e2
                                                   Right seq -> tbNotation calc . show $ seq
                                     Right f -> tbNotation calc . show $ f
          failMsg e1 e2 = "couldn't parse as formula (" ++ show e1 ++ ") or sequent (" ++ show e2 ++ ")"
