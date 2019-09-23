module Carnap.Calculi.Tableau.Data where

import Carnap.Core.Data.Types
import Carnap.Languages.ClassicalSequent.Syntax
import Data.Tree
import Text.Parsec



--a TreeForm is a formula within a truth tree, labeled by its row and whether it is resolved.
data TreeForm lex sem = TreeForm
           { treeForm :: FixLang lex sem
           , treeFormRow :: Int
           , treeFormResolved :: Bool
           }


--A tree node is a node in a truth tree, labeled by the rule used to create it.
data TreeNode lex sem rule = TreeNode 
           { treeNodeForms :: [TreeForm lex sem] 
           , treeNodeRule :: Maybe rule
           }


--A truth tree is a rose tree of TreeNodes.
type TruthTree lex sem rule = Tree (TreeNode lex sem rule)

data TableauNode lex sem rule = TableauNode
           { tableauNodeSeq :: ClassicalSequentOver lex (Sequent sem)
           , tableauNodeTarget :: Maybe (FixLang lex sem)
           , tableauNodeRule :: Maybe rule
           --this is the rule that develops the node, not the rule that the node is developed by.
           }

type Tableau lex sem rule = Tree (TableauNode lex sem rule)

data TreeFeedbackNode = Correct | Feedback String | Waiting | ParseErrorMsg String 
    deriving (Eq)

type TreeFeedback = Tree TreeFeedbackNode

data TableauCalc lex sem rule = TableauCalc 
           { tbParseForm :: Parsec String () (FixLang lex sem)
           , tbParseRule :: Parsec String () rule
           --possibly some other stuff here
           }
