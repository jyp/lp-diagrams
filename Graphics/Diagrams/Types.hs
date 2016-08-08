{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RecursiveDo, TypeFamilies, OverloadedStrings, RecordWildCards,UndecidableInstances, PackageImports, TemplateHaskell, RankNTypes, GADTs, DeriveFunctor, ScopedTypeVariables, ConstraintKinds, InstanceSigs #-}

module Graphics.Diagrams.Types where
import Algebra.Classes as AC
import Prelude hiding (sum,mapM_,mapM,concatMap,Num(..),(/),fromRational,recip,(/))
import Data.Traversable (foldMapDefault,fmapDefault)
import Control.Lens hiding (element)

type Constant = Double

type Frozen x = x Constant
type FrozenPoint = Frozen Point'
type FrozenPath = Frozen Path'


------------------------------
-- Abstract algebra additions.
square :: forall a. Multiplicative a => a -> a
square x = x*x

(*-) :: Module Constant a => Constant -> a -> a
(*-) = (*^)
infixr 7 *-

-- | Average
avg :: Module Constant a => [a] -> a
avg xs = (one/fromIntegral (length xs)::Constant) *^ add xs

------------
-- Types

data Pair a = Pair {pairFst :: a, pairSnd :: a}
  deriving (Functor)

instance Show a => Show (Pair a) where
  show (Pair x y) = show (x,y)

data Point' a = Point {xpart :: a, ypart :: a}
  deriving (Eq,Show,Functor)

instance Module k a => Module k (Point' a) where
  (*^) scalar = fmap (scalar *^)

instance Traversable Point' where
  traverse f (Point x y) = Point <$> f x <*> f y

instance Foldable Point' where
  foldMap = foldMapDefault

instance Applicative Point' where
  pure x = Point x x
  Point f g <*> Point x y = Point (f x) (g y)

instance Additive a => Additive (Point' a) where
  zero = Point zero zero
  Point x1 y1 + Point x2 y2 = Point (x1 + x2) (y1 + y2)

instance AbelianAdditive v => AbelianAdditive (Point' v) where

instance Group v => Group (Point' v) where
  negate (Point x y) = Point (negate x) (negate y)
  Point x1 y1 - Point x2 y2 = Point (x1 - x2) (y1 - y2)



data Segment v = CurveTo (Point' v) (Point' v) (Point' v)
                   | StraightTo (Point' v)
                   | Cycle
                     -- Other things also supported by tikz:
                   --  Rounded (Maybe Constant)
                   --  HV point | VH point
  deriving (Show,Eq)
instance Functor Segment where
  fmap = fmapDefault

instance Foldable Segment where
  foldMap = foldMapDefault
instance Traversable Segment where
  traverse _ Cycle = pure Cycle
  traverse f (StraightTo p) = StraightTo <$> traverse f p
  traverse f (CurveTo c d q) = CurveTo <$> traverse f c <*> traverse f d <*> traverse f q


data Path' a
  = EmptyPath
  | Path {startingPoint :: Point' a
         ,segments :: [Segment a]}
  deriving Show
-- mapPoints :: (Point' a -> Point' b) -> Path' a -> Path' b
instance Functor Path' where
  fmap = fmapDefault

instance Foldable Path' where
  foldMap = foldMapDefault
instance Traversable Path' where
  traverse _ EmptyPath = pure EmptyPath
  traverse f (Path s ss) = Path <$> traverse f s <*> traverse (traverse f) ss


-- | Tikz decoration
newtype Decoration = Decoration String


-- | Tikz line tip
data LineTip = ToTip | CircleTip | NoTip | StealthTip | LatexTip | ReversedTip LineTip | BracketTip | ParensTip

-- | Tikz color
type Color = String

-- | Tikz line cap
data LineCap = ButtCap | RectCap | RoundCap

-- | Tikz line join
data LineJoin = MiterJoin | RoundJoin | BevelJoin

-- | Tikz dash pattern
type DashPattern = [(Constant,Constant)]

-- | Path drawing options
data PathOptions = PathOptions
                     {_drawColor :: Maybe Color
                     ,_fillColor :: Maybe Color
                     ,_lineWidth :: Constant
                     ,_startTip  :: LineTip
                     ,_endTip    :: LineTip
                     ,_lineCap   :: LineCap
                     ,_lineJoin  :: LineJoin
                     ,_dashPattern :: DashPattern
                     ,_decoration :: Decoration
                     }
$(makeLenses ''PathOptions)

-- | Size of a box, in points. boxDepth is how far the baseline is
-- from the bottom. boxHeight is how far the baseline is from the top.
-- (These are TeX meanings)
data BoxSpec = BoxSpec {boxWidth, boxHeight, boxDepth :: Double}
             deriving (Show)

nilBoxSpec :: BoxSpec
nilBoxSpec = BoxSpec 0 0 0

data Backend lab m =
                 Backend {_tracePath :: PathOptions -> FrozenPath -> m ()
                         ,_traceLabel :: forall location (x :: * -> *). Monad x =>
                                                 (location -> (FrozenPoint -> m ()) -> x ()) -> -- freezer
                                                 (forall a. m a -> x a) -> -- embedder
                                                 location ->
                                                 lab -> -- label specification
                                                 x BoxSpec
                         }

tracePath :: Lens' (Backend lab m) (PathOptions -> FrozenPath -> m ())
tracePath f (Backend tp tl) = fmap (\x -> Backend x tl) (f tp)

data Env lab m = Env {_diaTightness :: Rational -- ^ Multiplicator to minimize constraints
                     ,_diaPathOptions :: PathOptions
                     ,_diaBackend :: Backend lab m}

$(makeLenses ''Env)

defaultPathOptions :: PathOptions
defaultPathOptions = PathOptions
  {_drawColor = Nothing
  ,_fillColor = Nothing
  ,_lineWidth = 0.4
  ,_startTip  = NoTip
  ,_endTip    = NoTip
  ,_lineCap   = ButtCap
  ,_lineJoin  = MiterJoin
  ,_dashPattern = []
  ,_decoration = Decoration ""
  }
