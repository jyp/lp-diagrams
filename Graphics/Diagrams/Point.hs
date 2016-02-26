{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RecursiveDo, TypeFamilies, OverloadedStrings, RecordWildCards,UndecidableInstances, PackageImports, TemplateHaskell, RankNTypes #-}

module Graphics.Diagrams.Point where

import Graphics.Diagrams.Core
import Data.Foldable
import Data.List (transpose)
import Prelude hiding (sum,mapM_,mapM,concatMap,maximum,minimum,Num(..),(/))
import Algebra.Classes

infix 4 .=.
----------------
-- Points
-- | A point in 2d space


type Point = Point' Expr

orthonorm :: Point -> Expr
orthonorm (Point x y) = absE x + absE y

{-


-- | Norm of a vector. Don't minimize this: the solver does not like functions
-- with non-continuous derivatives (at zero in this case).
norm :: Point' Expr -> Expr
norm p = sqrtE (sqNorm p)

normalize :: Point' Expr -> Point' Expr
normalize x = (one/norm x) *^ x

-- | Dot product
dotProd :: forall a. (Ring a) => Point' a -> Point' a -> a
dotProd (Point x y) (Point x' y') = x*x' + y*y'

-- | Squared norm of a vector
sqNorm :: forall a. (Ring a) => Point' a -> a
sqNorm p = dotProd p p
-}
-- | Rotate a vector 90 degres in the trigonometric direction.
rotate90 :: forall a. Group a => Point' a -> Point' a
rotate90 (Point x y) = Point (negate y) x

-- | Rotate a vector 180 degres
rotate180 :: forall a. Group a => Point' a -> Point' a
rotate180 = rotate90 . rotate90

xdiff,ydiff :: Point -> Point -> Expr
xdiff p q = xpart (q - p)
ydiff p q = ypart (q - p)

-----------------
-- Point constraints

(.=.),northOf,southOf,westOf,eastOf :: Monad m => Point -> Point -> Diagram lab m ()
Point x1 y1 .=. Point x2 y2 = do
  x1 === x2
  y1 === y2

northOf (Point _ y1) (Point _ y2) = y2 <== y1
southOf = flip northOf
westOf (Point x1 _) (Point x2 _) = x1 <== x2
eastOf = flip westOf

alignHoriz,alignVert :: Monad m => [Point] -> Diagram lab m ()
alignHoriz = align ypart
alignVert = align xpart

align :: Monad m => (a -> Expr) -> [a] -> Diagram lab m ()
align _ [] = return ()
align f (p:ps) = forM_ ps $ \p' -> f p === f p'

alignMatrix :: Monad m => [[Point]] -> Diagram lab m ()
alignMatrix ls = do
  forM_ ls alignHoriz
  forM_ (transpose ls) alignVert
