{-# LANGUAGE DataKinds, KindSignatures, OverloadedStrings, EmptyDataDecls, MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, GADTs, LambdaCase, RecordWildCards   #-}

module Graphics.Diagrams.Object where

import Graphics.Diagrams.Path
import Graphics.Diagrams.Point
import Graphics.Diagrams.Core
import Control.Monad
import Control.Lens (set,view)
import Algebra.Classes hiding (normalize)
import Prelude hiding (Num(..),(/))
import Graphics.Diagrams.Shape


-- | Box-shaped object. (a subtype)
type Box = Object

data Object = Object { objectName :: !String
                     , objectOutline :: !Path
                     , anchors :: !Anchorage}


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

label :: Monad m => String -> lab -> Diagram lab m Box
label name txt = do
  l <- extend (constant 4) <$> rawLabel name txt
  pathObject $ Object
    name
    (polygon (map (l #) [NW,NE,SE,SW]))
    (anchors l)

-- | Internal use.
pathObject :: Monad m => Object -> Diagram lab m Object
pathObject o@(Object _ p _) = path p >> return o

-- | Label a point by a given TeX expression, at the given anchor.
labelAt :: Monad m => String -> lab -> Anchor -> Point -> Diagram lab m Box
labelAt name labell anchor labeled  = do
  t <- label name labell
  t # anchor .=. labeled
  return t

-- | A free point
point :: Monad m => String -> Diagram lab m Object
point name = do
  x <- newVar (name++".x"); y <- newVar (name++".y")
  return $ Object name EmptyPath (\_ -> Point x y)

-- -- | A free point
-- point' :: Monad m => Diagram lab m Object
-- point' = point "point"

-- | A box. Anchors are aligned along a grid.
boxAnchors :: Monad m => String -> Diagram lab m Anchorage
boxAnchors objectName = do
  let nv suff = newVar (objectName++"."++suff)
  n <- nv "north" ; s <- nv "south"; e <- nv "east"; w <- nv "west"; base <- nv "base"; midx <- nv "midx"; midy <- nv "midy"
  n >== base
  base >== s
  w <== e

  midx === avg [w,e]
  midy === avg [n,s]
  let pt = flip Point
  return $ \case
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


obj :: Monad m => Shape -> String -> Diagram lab m Object
obj shape objectName = do
  anchors <- boxAnchors objectName
  let objectOutline = shape anchors
  pathObject $ Object{..}


-- | A box of zero width
vrule :: Monad m => String -> Diagram lab m Object
vrule name = do
  o <- obj box name
  align xpart [o # W, o #Center, o#E]
  return o

-- | A box of zero height
hrule :: Monad m => String -> Diagram lab m Object
hrule name = do
  o <- obj box name
  height o === zero
  return o

height, width, ascent, descent :: Object -> Expr
height o = ypart (o # N - o # S)
width o = xpart (o # E - o # W)
ascent o = ypart (o # N - o # Base)
descent o = ypart (o # Base - o # S)


sloppyFitsHorizontallyIn :: Monad m => Object -> Object -> Diagram lab m ()
o `sloppyFitsHorizontallyIn` o' = do
  let dyW = xpart $ o # W - o' # W
      dyE = xpart $ o' # E - o # E
  dyW >== zero
  dyE >== zero

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


-- | Debug, by tracing the bounding box of the object in a certain color.
traceBox :: (Monad m) => Color -> Object -> Diagram lab m ()
traceBox c l = do
  stroke c $ path $ polygon (map (l #) [NW,NE,SE,SW])
  -- TODO: draw the baseline, etc.

-- | Typeset a piece of text and return its bounding box as an object. Probably,
-- use 'label' instead.
rawLabel :: Monad m => String -> lab -> Diagram lab m Object
rawLabel name t = do
  l <- noDraw (obj box name)
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
autoLabelObj lab (OVector pt v) = do
  -- let normalVector :: Point' Expr
  --     normalVector = v
  -- label must touch the point
  tighten 10 $ pt `insideBox` lab
  minimize (orthonorm (pt+v- lab#Center))
  -- go as far as possible in the normal direction
  -- maximize $ dotProd (((lab#Center) - pt)) normalVector
  -- don't stray away from the normal line
  -- minimize $ absE $ dotProd (((lab#Center) - pt)) (rotate90 normalVector)
  --

-- | @autoLabel o i@ Layouts the label object @o@ at the given incidence
-- vector.
autoLabel :: Monad m => String -> lab -> OVector -> Diagram lab m Object
autoLabel name lab i = do
  o <- label name lab
  autoLabelObj o i
  return o

-- | @labeledEdge label source target@
labeledEdge :: Monad m => Object -> Object -> Box -> Diagram lab m ()
labeledEdge source target lab = autoLabelObj lab =<< edge source target

-------------------
-- Even higher-level primitives:

nodeDistance :: Expr
nodeDistance = constant 5

leftOf, topOf, rightOf :: Monad m => Object -> Object -> Diagram lab m ()

a `leftOf` b = spread hdist nodeDistance [a,b]
a `topOf` b =  spread vdist nodeDistance [b,a]
rightOf = flip leftOf

-- | Spread a number of objects by *minimum* a given distance. example: @spread
-- hdist 30 ps@
spread :: Monad m => (t -> t -> Expr) -> Expr -> [t] -> Diagram lab m ()
spread f d (x:y:xs) = do
  f x y >== d
  minimize $ f x y
  spread f d (y:xs)
spread _ _ _ = return ()

-- | A node: a labeled object
node shape name lab = do
  l <- noDraw $ label name lab
  c <- obj shape name
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
  bx <- obj box $ "boundingBox" ++ (show $ map objectName os)
  mapM_ (`fitsIn` bx) os
  return bx

noOverlap :: Monad m => Object -> Diagram lab m Object
noOverlap o = do
  registerNonOverlap (o#SW) (o#NE)
  return o
