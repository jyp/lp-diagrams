{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, RebindableSyntax, DeriveFunctor #-}
module Algebra.Linear.GaussianElimination (linSolve) where

import Prelude hiding (Num(..),(/))
import Algebra.Classes
import qualified Data.Map.Strict as M
import Data.Maybe
import Algebra.Linear

gaussianElim :: (Ord v,Eq c,Field c) => [Constraint v c] -> [(v,LinFunc v c)]
gaussianElim [] = []
gaussianElim (co@(Func f k):cos) = case M.minViewWithKey f of
  Nothing -> if k == 0 then gaussianElim cos
             else error "gaussianElim: unsatisfiable"
  Just ((_,0),_) -> error "gaussianElim: invariant not respected"
  Just ((v,c),_) -> (v,clean $ var v - co') : gaussianElim (fmap t cos)
    where co' = (1/c) *^ co
          t co2@(Func m _) = case (M.lookup v m) of
            Nothing -> co2
            Just cv -> clean (co2 - cv *^ co')

substitution :: (Ord v,Ring c, Eq c) => [(v,LinFunc v c)] -> [(v,LinFunc v c)]
substitution [] = []
substitution ((v,f):vfs) = (v,f) : substitution [(v',subst v f f') | (v',f') <- vfs]

subst :: (Eq scalar, Ord v, Ring scalar) => v -> LinFunc v scalar -> LinFunc v scalar -> LinFunc v scalar
subst v f f'@(Func m _) = clean $ f' - coef *^ var v + coef *^ f
  where coef = fromMaybe 0 (M.lookup v m)


linSolve :: (Eq c, Ord v, Field c) => [Constraint v c] -> [(v, LinFunc v c)]
linSolve = substitution . reverse . gaussianElim . fmap clean
