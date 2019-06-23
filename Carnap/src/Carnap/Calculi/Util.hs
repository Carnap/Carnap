{-#LANGUAGE KindSignatures, GADTs, FlexibleContexts #-}
module Carnap.Calculi.Util where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.Huet
import Carnap.Core.Unification.ACUI
import Carnap.Languages.ClassicalSequent.Syntax
import Control.Monad.State
import Text.Parsec (ParseError)

data ProofErrorMessage :: ((* -> *) -> * -> *) -> * where
        NoParse :: ParseError -> Int -> ProofErrorMessage lex
        NoUnify :: [[Equation (ClassicalSequentOver lex)]]  -> Int -> ProofErrorMessage lex
        GenericError :: String -> Int -> ProofErrorMessage lex
        NoResult :: Int -> ProofErrorMessage lex --meant for blanks

-- TODO These should be combined into a lens

lineNoOfError (NoParse _ n) = n
lineNoOfError (NoUnify _ n) = n
lineNoOfError (GenericError _ n) = n
lineNoOfError (NoResult n) = n

renumber :: Int -> ProofErrorMessage lex -> ProofErrorMessage lex
renumber m (NoParse x n) = NoParse x m
renumber m (NoUnify x n) = NoUnify x m
renumber m (GenericError s n) = GenericError s m
renumber m (NoResult n) = NoResult m

fosolve :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) =>  [Equation (ClassicalSequentOver lex)] -> Either (ProofErrorMessage lex) [Equation (ClassicalSequentOver lex)]
fosolve eqs = case evalState (foUnifySys (const False) eqs) (0 :: Int) of 
                [] -> Left $ NoUnify [eqs] 0
                [s] -> Right s

hosolve :: 
    ( HigherOrder (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) => [Equation (ClassicalSequentOver lex)] -> Either (ProofErrorMessage lex) [[Equation (ClassicalSequentOver lex)]]
hosolve eqs = case evalState (huetUnifySys (const False) eqs) (0 :: Int) of
                    [] -> Left $ NoUnify [eqs] 0
                    subs -> Right subs

acuisolve :: 
    ( ACUI (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) => [Equation (ClassicalSequentOver lex)] -> Either (ProofErrorMessage lex) [[Equation (ClassicalSequentOver lex)]]
acuisolve eqs = 
        case evalState (acuiUnifySys (const False) eqs) (0 :: Int) of
          [] -> Left $ NoUnify [eqs] 0
          subs -> Right subs
