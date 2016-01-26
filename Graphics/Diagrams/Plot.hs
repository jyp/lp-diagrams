{-# LANGUAGE FlexibleContexts, RankNTypes, DeriveFunctor #-}
module Graphics.Diagrams.Plot where

import Graphics.Diagrams.Core
import Graphics.Diagrams.Path
import Graphics.Diagrams.Object
import Graphics.Diagrams.Point
import Control.Monad (forM_,when)
import Algebra.Classes
import Prelude hiding (Num(..),(/))

type Vec2 = Point'
type Transform a = Iso a Constant

-- | Generic axis rendering. @axisGen origin target anchor labels@
-- traces an axis from origin to target, attaching the labels at
-- anchor.
axisGen :: Monad m => Point -> Point -> Anchor -> [(Constant,lab)] -> Diagram lab m ()
axisGen origin target anch labels = do
  draw {- using (set endTip ToTip) -} $ path $ polyline [origin,target]
  when (not $ null $ labels) $ do
    forM_ labels $ \(p,txt) -> do
      l0 <- label "axis" txt
      let l = extend (constant 3) l0
      draw $ path $ polyline [l0 # anch, l # anch]
      l # anch .=. Point (lint p (xpart origin) (xpart target))
                         (lint p (ypart origin) (ypart target))

-- | @scale minx maxx@ maps the interval [minx,maxx] to [0,1]
scale :: forall b. Field b => b -> b -> Iso b b
scale minx maxx = Iso (\x -> (x - minx) / (maxx - minx))
                      (\x -> x * (maxx - minx) + minx)

-- | Make a number of steps
mkSteps :: Transform a -> ShowFct lab a -> [a] -> [(Constant,lab)]
mkSteps tx showFct xs = zip (map (forward tx) xs) (map showFct xs)

-- | render an horizontal axis on the given box
hAxis :: Monad m => Box -> [(Constant, lab)] -> Diagram lab m ()
hAxis bx = axisGen (bx # SW) (bx # SE) N

-- | render a vertical axis on the given box
vAxis :: Monad m => Box -> [(Constant, lab)] -> Diagram lab m ()
vAxis bx = axisGen (bx # SW) (bx # NW) E

-- | Draw axes. Coordinates in the [0,1] fit the box.
axes :: Monad m => Box -> Vec2 [(Constant, lab)] -> Diagram lab m ()
axes bx zs = d1 >> d2
  where Point d1 d2 = (Point hAxis vAxis) <*> pure bx <*> zs

-- | Multiply the vector (origin --> target) by p.
lint :: Constant -> Expr -> Expr -> Expr
lint p origin target = (p*-(target-origin)) + origin

-- | Draw a scatterplot in the given box.
-- Input data in the [0,1] interval fits the box.
scatterPlot :: Monad m => PlotCanvas a -> [Vec2 a] -> Diagram lab m ()
scatterPlot (bx,xform) input = forM_ (map (forward <$> xform <*>) input) $ \z -> do
  pt <- using (fill "black") $ circle "plotMark"
  width pt === constant 3
  pt # Center .=. interpBox bx z

interpBox :: Object -> Point' Constant -> Point' Expr
interpBox bx z = lint <$> z <*> bx#SW <*> bx#NE

-- | @functionPlot c n f@.
-- Plot the function @f@ on the canvas @c@, using @n@ steps (precision).

functionPlot :: Monad m => Show a => PlotCanvas a -> Int -> (a -> a) -> Diagram lab m ()
functionPlot (bx,Point tx ty) nsteps f = draw $ path $ polyline points
  where points = do
           step <- [0..nsteps]
           let xi :: Double
               xi = fromIntegral step / fromIntegral nsteps
               x = backward tx xi
               y = f x
               yi = forward ty y
           return $ interpBox bx (Point xi yi)

data Iso a b = Iso {forward :: a -> b, backward :: b -> a}

after :: Iso b c -> Iso a b -> Iso a c
(Iso f g) `after` (Iso h i) = Iso (f . h) (i . g)

axisMarks :: a -> a -> Iso a Constant -> (a,[a],a)
axisMarks lo hi trans = (u lo',(map u [lo'..hi']),u hi')
  where u = backward trans
        t = forward trans
        lo' = fromIntegral $ (floor (t lo) :: Integer)
        hi' = fromIntegral $ (ceiling (t hi) :: Integer)

logAxis :: Constant -> Transform Constant
logAxis base = Iso t u
     where t x = log x / log base
           u x = base ** x

simplLinAxis :: Constant -> Transform Constant
simplLinAxis step = Iso (/step) (*step)

type ShowFct lab a = a -> lab

mkAxes :: Vec2 (Transform a) -> Vec2 a -> Vec2 a -> (Vec2 [a], Vec2 (Transform a))
mkAxes axesXform lows highs = (mrks <$> axisInfo,
                               after <$> (scale <$> minz <*> maxz) <*> axesXform)
  where axisInfo = axisMarks <$> lows <*> highs <*> axesXform
        minz = t <*> (lo <$> axisInfo)
        maxz = t <*> (hi <$> axisInfo)
        t = forward <$> axesXform
        lo (x,_,_) = x
        mrks (_,x,_) = x
        hi (_,_,x) = x

type PlotCanvas a = (Box, Vec2 (Transform a))

preparePlot :: Monad m => Vec2 (ShowFct lab a) -> Vec2 (Transform a) -> Vec2 a -> Vec2 a -> Diagram lab m (PlotCanvas a)
preparePlot showFct axesXform lo hi = do
  bx <- box "plotFrame"
  axes bx marks
  return (bx,xform)
  where marks = mkSteps <$> xform <*> showFct <*> marks0
        (marks0,xform) = mkAxes axesXform lo hi

-- | Draw a 2D scatter plot, given an axis specification and a data
-- set
simplePlot :: (Ord a, Monad m) => Vec2 (ShowFct lab a) -> Vec2 (Transform a) -> [Vec2 a] -> Diagram lab m (PlotCanvas a)
simplePlot showFct axesXform input = do
  canvas <- preparePlot showFct axesXform (minimum <$> input') (maximum <$> input')
  scatterPlot canvas input
  return canvas
  where input' = sequenceA input
