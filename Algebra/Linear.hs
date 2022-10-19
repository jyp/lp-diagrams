{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, RebindableSyntax, DeriveFunctor #-}

module Algebra.Linear where

import Algebra.Classes
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Prelude hiding (Num(..),(/))

data LinFunc v c = Func (Map v c) c
  deriving (Functor,Show)
type Constraint v c = LinFunc v c


instance (AbelianAdditive c,Ord v) => Additive (LinFunc v c) where
  zero = Func zero zero
  Func f1 k1 + Func f2 k2 = Func (f1 + f2) (k1 + k2)

instance (Ord v, AbelianAdditive c, Group c) => Group (LinFunc v c) where
  negate = fmap negate

instance (Ord v,AbelianAdditive c) => AbelianAdditive (LinFunc v c) where

instance (Ord v,Ring c) => Scalable c (LinFunc v c) where
  s *^ Func f k = Func (s *^ f) (s * k)

clean :: (Eq v, Eq c, Ring c) => LinFunc v c -> LinFunc v c
clean (Func f k) = Func (M.fromAscList $ filter ((/=0) . snd) $ M.assocs f) k

var :: Ring c => v -> LinFunc v c
var v = Func (M.singleton v 1) 0
