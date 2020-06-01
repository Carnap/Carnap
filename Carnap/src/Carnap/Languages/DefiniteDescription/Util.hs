{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, ConstraintKinds #-}
module Carnap.Languages.DefiniteDescription.Util where

import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Util
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Util
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Util
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Control.Monad.State
import Control.Lens
import Data.Typeable (Typeable)
import Data.Maybe
import Data.List

cleanDesc :: (FirstOrderTransformable lex, PrismDefiniteDesc lex Bool Int) => 
    FixLang lex (Form Bool) -> State [FixLang lex (Form Bool)] (FixLang lex (Form Bool))
cleanDesc f = if noDescs f 
                  then return f
                  else do f' <- traverseOf termsOf makeConstant f
                          cleanDesc f'
    where noDescs :: (FirstOrderTransformable lex, PrismDefiniteDesc lex Bool Int) => FixLang lex (Form Bool) -> Bool
          noDescs t = null (toListOf (termsOf . unaryOpPrismOn _desc') t)
          makeConstant :: (FirstOrderTransformable lex, PrismDefiniteDesc lex Bool Int) => FixLang lex (Term Int) 
            -> State [FixLang lex (Form Bool)] (FixLang lex (Term Int))
          makeConstant t = case t ^? (unaryOpPrismOn _desc') of
                               --we replace with constants from the bottom
                               --up, starting with the descriptions that
                               --don't contain descriptions
                               Just (v,LLam f) | noDescs (f (static 0)) -> 
                                    do prevDescs <- get
                                       case findEquiv 0 (f (static 0)) prevDescs of 
                                            Just n -> return $ foVar ("desc-" ++ show n)
                                            Nothing -> do put (prevDescs ++ [toDenex $ f (static 0)]) 
                                                          return $ foVar ("desc-" ++ show (length prevDescs))
                               _ -> traverseOf termsOf makeConstant t
          _desc' :: (FirstOrderTransformable lex, PrismDefiniteDesc lex Bool Int) => Prism' (FixLang lex ((Term Int -> Form Bool) -> Term Int)) String
          _desc' = _desc
          findEquiv :: FirstOrderTransformable lex => Int -> FixLang lex (Form Bool) -> [FixLang lex (Form Bool)] -> Maybe Int
          findEquiv _ f [] = Nothing
          findEquiv n f (x:xs) | toDenex f `pnfEquiv` x = Just n
                               | otherwise = findEquiv (n + 1) f xs

descEquivPNF f g = uncurry pnfEquiv $ evalState generateDescs []
    where generateDescs = do f' <- cleanDesc f
                             g' <- cleanDesc g
                             return (f',g')
