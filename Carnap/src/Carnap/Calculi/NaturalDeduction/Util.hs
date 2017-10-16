module Carnap.Calculi.NaturalDeduction.Util where

import Carnap.Calculi.NaturalDeduction.Syntax
import Text.Parsec
import Data.Map (Map,(!),keys)

parseRuleTable :: Map String (Parsec String u [r]) -> (Parsec String u [r])
parseRuleTable m = do r <- choice (map (try . string) (keys m))
                      m ! r
