module Filter.RenderFormulas (renderFormulas) where

import Text.Pandoc
import Text.Pandoc.Walk (walk)
import Prelude

renderFormulas :: Block -> Block
renderFormulas = walk renderFormula

renderFormula :: Inline -> Inline
renderFormula (Code (id,classes,attrs) txt) = Code (id,classes,map rewrite attrs) txt 
    where rewrite ("system",y) = ("data-carnap-render-system",y)
          rewrite x = x
renderFormula x = x
