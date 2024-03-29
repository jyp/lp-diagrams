{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RecursiveDo, TypeFamilies, OverloadedStrings, RecordWildCards,UndecidableInstances, PackageImports, TemplateHaskell #-}

module Graphics.Diagrams.Path where

import Graphics.Diagrams.Core
import Graphics.Diagrams.Point
import Data.Foldable
import Graphics.Typography.Geometry.Bezier
import Data.List (sort)
import Data.Maybe (listToMaybe)
import Prelude hiding (sum,mapM_,mapM,concatMap,maximum,minimum,Num(..),(/),sqrt)
import qualified Data.Vector.Unboxed as V
import Algebra.Polynomials.Bernstein (restriction,Bernsteinp(..))
import Control.Lens (over, set, view)
import Control.Monad.Reader (local)
import Algebra.Classes

toBeziers :: FrozenPath -> [Curve]
toBeziers EmptyPath = []
toBeziers (Path start ss) | not (null ss) &&
                            isCycle (last ss) = toBeziers' start (init ss ++ [StraightTo start])
                          | otherwise = toBeziers' start ss

curveSegment :: FrozenPoint
                  -> FrozenPoint -> FrozenPoint -> FrozenPoint -> Curve
curveSegment (Point xa ya) (Point xb yb) (Point xc yc) (Point xd yd) = bezier3 xa ya xb yb xc yc xd yd

lineSegment :: Point' Double -> Point' Double -> Curve
lineSegment (Point xa ya) (Point xb yb) = line xa ya xb yb

-- | Convert a Path into a Curve
toBeziers' :: FrozenPoint -> [Frozen Segment] -> [Curve]
toBeziers' _ [] = []
toBeziers' start (StraightTo next:ss) = curveSegment start mid mid next : toBeziers' next ss
  where mid = avg [start, next]
toBeziers' p (CurveTo c d q:ss) = curveSegment p c d q : toBeziers' q ss

-- | Convert a Curve into a Path
fromBeziers :: [Curve] -> FrozenPath
fromBeziers [] = EmptyPath
fromBeziers (Bezier cx cy t0 t1:bs) = case map toPt $ V.foldr (:) [] cxy of
      [p,c,d,q] -> Path p (CurveTo c d q:rest)
      [p,q] -> Path p (StraightTo q:rest)
  where [cx',cy'] = map (\c -> coefs $ restriction c t0 t1) [cx,cy]
        cxy = V.zip cx' cy'
        toPt (x,y) = Point x y
        rest = pathSegments (fromBeziers bs)

pathSegments :: Path' t -> [Segment t]
pathSegments EmptyPath = []
pathSegments (Path _ ss) = ss

isCycle :: Segment t -> Bool
isCycle Cycle = True
isCycle _  = False

-- | @clipOne c0 cs@ return the part of c0 from its start to the point where it
-- intersects any element of cs.
clipOne :: Curve -> [Curve] -> Maybe Curve
clipOne b cutter = fmap firstPart $ listToMaybe $ sort $ concatMap (inter b) cutter
  where firstPart t = fst $ splitBezier b t
        splitBezier (Bezier cx cy t0 t1) (u,v,_,_) = (Bezier cx cy t0 u, Bezier cx cy v t1)

-- | @cutAfter path area@ cuts the path after its first intersection with the @area@.
cutAfter', cutBefore' :: [Curve] -> [Curve] -> [Curve]
cutAfter' [] _cutter = []
cutAfter' (b:bs) cutter = case clipOne b cutter of
  Nothing -> b:cutAfter' bs cutter
  Just b' -> [b']

-- | Reverse a bezier curve
revBeziers :: [Curve] -> [Curve]
revBeziers = reverse . map rev
  where rev (Bezier cx cy t0 t1) = Bezier (revBernstein cx) (revBernstein cy) (1-t1) (1-t0)
        revBernstein (Bernsteinp n c) = Bernsteinp n (V.reverse c)

cutBefore' pth area = revBeziers $ cutAfter' (revBeziers pth) area

onBeziers :: ([Curve] -> [Curve] -> [Curve])
             -> FrozenPath -> FrozenPath -> FrozenPath
onBeziers op p' q' = fromBeziers $ op (toBeziers p') (toBeziers q')


cutAfter :: FrozenPath -> FrozenPath -> FrozenPath
cutAfter = onBeziers cutAfter'

cutBefore :: FrozenPath -> FrozenPath -> FrozenPath
cutBefore = onBeziers cutBefore'

-----------------
-- Paths


type Path = Path' Expr

polyline :: [Point] -> Path
polyline [] = EmptyPath
polyline (x:xs) = Path x (map StraightTo xs)

polygon :: [Point] -> Path
polygon [] = EmptyPath
polygon (x:xs) = Path x (map StraightTo xs ++ [Cycle])


-- | Circle approximated with 4 cubic bezier curves
circlePath :: Point -> Expr -> Path
circlePath center r =
  Path (pt r zero)
  [CurveTo (pt r k) (pt k r) (pt zero r),
   CurveTo (pt (negate k) r) (pt (negate r) k) (pt (negate r) zero),
   CurveTo (pt (negate r) (negate k)) (pt (negate k) (negate r)) (pt zero (negate r)),
   CurveTo (pt k (negate r)) (pt r (negate k)) (pt r zero),
   Cycle]
 where k1 :: Double
       k1 = fromInteger 4 * (sqrt (fromInteger 2) - (fromInteger 1)) / fromInteger 3
       k = k1 *^ r
       pt x y = center + (Point x y)

roundedRectanglePath :: Expr -> Point -> Point -> Path
roundedRectanglePath r (Point x1 y1) (Point x2 y2) =
  Path (Point x1 (y1-r))
  [
    CurveTo (Point x1 (y1-k) ) (Point (x1+k) y1) (Point (x1+r) y1),
    StraightTo (Point (x2-r) y1),
    CurveTo (Point (x2-k) y1) (Point x2 (y1-k)) (Point x2 (y1-r)),
    StraightTo (Point x2 (y2+r)),
    CurveTo (Point x2 (y2+k)) (Point (x2-k) y2) (Point (x2-r) y2),
    StraightTo (Point (x1+r) (y2)),
    CurveTo (Point (x1+k) y2) (Point (x1) (y2+k)) (Point x1 (y2+r)),
    Cycle
  ]
  where k1 :: Double
        k1 = fromInteger 4 * (sqrt (fromInteger 2) - (fromInteger 1)) / fromInteger 3
        k0 = k1 *^ r
        k = r - k0


path :: Monad m => Path -> Diagram lab m ()
path p = do
  options <- view diaPathOptions
  tracePath' <- view (diaBackend . tracePath)
  freeze p (tracePath' options)

frozenPath' :: Monad m => FrozenPath -> Diagram lab m ()
frozenPath' p = do
  options <- view diaPathOptions
  tracePath' <- view (diaBackend . tracePath)
  freeze [] $ \_ -> tracePath' options p

stroke :: Monad m => Color -> Diagram lab m a -> Diagram lab m a
stroke color = using (outline color)

draw :: Monad m => Diagram lab m a -> Diagram lab m a
draw = stroke "black"

noDraw :: Monad m => Diagram lab m a -> Diagram lab m a
noDraw = using (set drawColor Nothing . set fillColor Nothing)

noOutline :: PathOptions -> PathOptions
noOutline = set drawColor Nothing

outline :: Color -> PathOptions -> PathOptions
outline color = set drawColor (Just color)

fill :: Color -> PathOptions -> PathOptions
fill color = set fillColor (Just color)

zigzagDecoration :: PathOptions -> PathOptions
zigzagDecoration = set decoration (Decoration "zigzag")

using :: Monad m => (PathOptions -> PathOptions) -> Diagram lab m a -> Diagram lab m a
using f = local (over diaPathOptions f)

ultraThin, veryThin, thin, semiThick, thick, veryThick, ultraThick :: Constant
ultraThin = 0.1
veryThin = 0.2
thin = 0.4
semiThick = 0.6
thick = 0.8
veryThick = 1.2
ultraThick = 1.6

solid, dotted, denselyDotted, looselyDotted, dashed, denselyDashed,
  looselyDashed, dashDotted, denselyDashdotted, looselyDashdotted :: PathOptions -> PathOptions
solid             o@PathOptions{..} = o { _dashPattern = [] }
dotted            o@PathOptions{..} = o { _dashPattern = [(_lineWidth,2)] }
denselyDotted     o@PathOptions{..} = o { _dashPattern = [(_lineWidth, 1)] }
looselyDotted     o@PathOptions{..} = o { _dashPattern = [(_lineWidth, 4)] }
dashed            o@PathOptions{..} = o { _dashPattern = [(3, 3)] }
denselyDashed     o@PathOptions{..} = o { _dashPattern = [(3, 2)] }
looselyDashed     o@PathOptions{..} = o { _dashPattern = [(3, 6)] }
dashDotted        o@PathOptions{..} = o { _dashPattern = [(3, 2), (_lineWidth, 2)] }
denselyDashdotted o@PathOptions{..} = o { _dashPattern = [(3, 1), (_lineWidth, 1)] }
looselyDashdotted o@PathOptions{..} = o { _dashPattern = [(3, 4), (_lineWidth, 4)] }
