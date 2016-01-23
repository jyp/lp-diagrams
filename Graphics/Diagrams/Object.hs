{-# LANGUAGE DataKinds, KindSignatures, OverloadedStrings, EmptyDataDecls, MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, GADTs, LambdaCase, RecordWildCards   #-}

module Graphics.Diagrams.Object where

import Graphics.Diagrams.Path
import Graphics.Diagrams.Point
import Graphics.Diagrams.Core
import Control.Monad
import Control.Lens (set,view)
import Algebra.Classes
import Prelude hiding (Num(..))

data Anchor = Center | N | NW | W | SW | S | SE | E | NE | BaseW | Base | BaseE
  deriving Show

-- | Box-shaped object. (a subtype)
type Box = Object

type Anchorage = Anchor -> Point
data Object = Object {objectOutline :: Path, anchors :: Anchorage}


infix 8 #

(#) :: Object -> Anchor -> Point
(#) = anchors


-- | Horizontal distance between objects
hdist :: Object -> Object -> Expr
hdist x y = xpart (y # W - x # E)

-- | Vertical distance between objects
vdist :: Object -> Object -> Expr
vdist x y = ypart (y # S - x # N)

-- | Move the anchors (NSEW) by the given delta, outwards.
extend :: Expr -> Object -> Object
extend e Object{..} = Object{anchors = \a -> anchors a + shiftInDir a e,..}

-- | Makes a shift of size 'd' in the given direction.
shiftInDir :: Anchor -> Expr -> Point
shiftInDir N d = zero `Point` d
shiftInDir S d = zero `Point` negate d
shiftInDir W d = negate d `Point` zero
shiftInDir BaseW d = negate d `Point` zero
shiftInDir E d  = d `Point` zero
shiftInDir BaseE d  = d `Point` zero
shiftInDir NW d = negate d `Point` d
shiftInDir SE d = d `Point` negate d
shiftInDir SW d = negate d `Point` negate d
shiftInDir NE d = d `Point` d
shiftInDir _ _  = zero `Point` zero

-- | Make a label object. This is the text surrounded by 4
-- points of blank and a rectangle outline.

label :: Monad m => lab -> Diagram lab m Box
label txt = do
  l <- extend (constant 4) <$> rawLabel txt
  pathObject $ Object (polygon (map (l #) [NW,NE,SE,SW]))
                      (anchors l)

-- | Internal use.
pathObject :: Monad m => Object -> Diagram lab m Object
pathObject o@(Object p _) = path p >> return o

-- | Label a point by a given TeX expression, at the given anchor.
labelAt :: Monad m => lab -> Anchor -> Point -> Diagram lab m Box
labelAt labell anchor labeled  = do
  t <- label labell
  t # anchor .=. labeled
  return t

-- | A free point
point :: Monad m => Diagram lab m Object
point = do
  [x,y] <- newVars (replicate 2 ContVar)
  return $ Object EmptyPath (\_ -> Point x y)

-- | A point anchorage (similar to a box of zero width and height)
pointBox :: Monad m => Diagram lab m Object
pointBox = point

-- | A box. Anchors are aligned along a grid.
box :: Monad m => Diagram lab m Object
box = do
  [n,s,e,w,base,midx,midy] <- newVars (replicate 7 ContVar)
  n >== base
  base >== s
  w <== e

  midx === avg [w,e]
  midy === avg [n,s]
  let pt = flip Point
      anchors anch = case anch of
        NW     -> pt n    w
        N      -> pt n    midx
        NE     -> pt n    e
        E      -> pt midy e
        SE     -> pt s    e
        S      -> pt s    midx
        SW     -> pt s    w
        W      -> pt midy w
        Center -> pt midy midx
        Base   -> pt base midx
        BaseE  -> pt base e
        BaseW  -> pt base w
      objectOutline = polygon (map anchors [NW,NE,SE,SW])
  pathObject $ Object{..}


-- | A box of zero width
vrule :: Monad m => Diagram lab m Object
vrule = do
  o <- box
  align xpart [o # W, o #Center, o#E]
  return o

-- | A box of zero height
hrule :: Monad m => Diagram lab m Object
hrule = do
  o <- box
  height o === zero
  return o

height, width, ascent, descent :: Object -> Expr
height o = ypart (o # N - o # S)
width o = xpart (o # E - o # W)
ascent o = ypart (o # N - o # Base)
descent o = ypart (o # Base - o # S)

-- | Make one object fit (snugly) in the other.
fitsIn, fitsHorizontallyIn, fitsVerticallyIn
  :: (Monad m) => Object -> Object -> Diagram lab m ()
o `fitsVerticallyIn` o' = do
  let dyN = ypart $ o' # N - o # N
      dyS = ypart $ o # S - o' # S
  minimize dyN
  dyN >== zero
  minimize dyS
  dyS >== zero

o `fitsHorizontallyIn` o' = do
  let dyW = xpart $ o # W - o' # W
      dyE = xpart $ o' # E - o # E
  minimize dyW
  dyW >== zero
  minimize dyE
  dyE >== zero

a `fitsIn` b = do
  a `fitsHorizontallyIn` b
  a `fitsVerticallyIn` b

-- | A circle
circle :: Monad m => Diagram lab m Object
circle = do
  bx <- noDraw box
  width bx === height bx
  let radius = 0.5 *- width bx
      p = circlePath (bx # Center) radius
  pathObject $ Object p (anchors bx)

traceBox :: (Monad m) => Color -> Object -> Diagram lab m ()
traceBox c l = do
  stroke c $ path $ polygon (map (l #) [NW,NE,SE,SW])
  -- TODO: draw the baseline, etc.

-- | Typeset a piece of text and return its bounding box as an object. Probably,
-- use 'label' instead.
rawLabel :: Monad m => lab -> Diagram lab m Object
rawLabel t = do
  l <- noDraw box
  -- traceAnchorage "red" l
  BoxSpec wid h desc <- drawText (l # NW) t

  width   l === constant wid
  descent l === constant desc
  height  l === constant (h + desc)
  return l

-- | A vector with an origin
data OVector = OVector { vectorOrigin, vectorMagnitude :: Point }

-- | Turn the orientation by 180 degrees
turn180 :: OVector -> OVector
turn180 (OVector p v) = OVector p (negate v)

data FList xs a where
  NIL :: FList '[] a
  (:%>) :: Functor t => t a -> FList fs a -> FList ('(:) t fs) a

infixr :%>

instance Functor (FList xs) where
  fmap _ NIL = NIL
  fmap f (x :%> xs) = fmap f x :%> fmap f xs

-- | Traces a straight edge between two objects.
-- A vector originated at the midpoint and pointing perpendicular to
-- the edge is returned.
edge :: Monad m => Object -> Object -> Diagram lab m OVector
edge source target = do
  let points@[a,b] = [source # Center,target # Center]
      link = polyline points
      targetArea = objectOutline target
      sourceArea = objectOutline source
  options <- view diaPathOptions
  tracePath' <- view (diaBackend . tracePath)
  freeze (link :%> sourceArea :%> targetArea :%> NIL) $ \(l' :%> sa' :%> ta' :%> NIL) -> do
       tracePath' options $ (l' `cutAfter` ta') `cutBefore` sa'
  return $ OVector (avg points) (rotate90 (b-a))

(.<.) :: Monad m => Point -> Point -> Diagram lab m ()
Point x1 y1 .<. Point x2 y2 = do
  x1 <== x2
  y1 <== y2

-- | Forces the point to be inside the (bounding box) of the object.
insideBox :: Monad m => Point -> Object -> Diagram lab m ()
insideBox p o = do
  (o # SW) .<. p
  p .<. (o # NE)

-- | @autoLabel o i@ Layouts the label object @o@ at the given incidence
-- vector.
autoLabelObj :: Monad m => Box -> OVector -> Diagram lab m ()
autoLabelObj lab (OVector pt norm) = do
  pt `insideBox` lab
  minimize =<< orthoDist (lab#Center) (pt + norm)

-- | @autoLabel o i@ Layouts the label object @o@ at the given incidence
-- vector.
autoLabel :: Monad m => lab -> OVector -> Diagram lab m ()
autoLabel lab i = do
  o <- label lab
  autoLabelObj o i

-- | @labeledEdge label source target@
labeledEdge :: Monad m => Object -> Object -> Box -> Diagram lab m ()
labeledEdge source target lab = autoLabelObj lab =<< edge source target

-------------------
-- Even higher-level primitives:

nodeDistance :: Expr
nodeDistance = constant 5

leftOf :: Monad m => Object -> Object -> Diagram lab m ()
a `leftOf` b = spread hdist nodeDistance [a,b]

topOf :: Monad m => Object -> Object -> Diagram lab m ()
a `topOf` b =  spread vdist nodeDistance [b,a]

-- | Spread a number of objects by *minimum* a given distance. example: @spread
-- hdist 30 ps@
spread :: Monad m => (t -> t -> Expr) -> Expr -> [t] -> Diagram lab m ()
spread f d (x:y:xs) = do
  f x y >== d
  minimize $ f x y
  spread f d (y:xs)
spread _ _ _ = return ()

-- | A node: a labeled circle
node :: Monad m => lab -> Diagram lab m Object
node lab = do
  l <- noDraw $ label lab
  c <- circle
  l `fitsIn` c
  l # Center .=. c # Center
  return c

-- | Draw an arrow between two objects
arrow :: Monad m => Object -> Object -> Diagram lab m OVector
arrow src trg = using (outline "black" . set endTip LatexTip) $ do
  edge src trg

-- | Bounding box of a number of anchored values
boundingBox :: (Monad m) => [Object] -> Diagram lab m Object
boundingBox os = do
  bx <- box
  mapM_ (`fitsIn` bx) os
  return bx
