{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RecursiveDo, TypeFamilies, OverloadedStrings, RecordWildCards,UndecidableInstances, PackageImports, TemplateHaskell, RankNTypes, GADTs, ImpredicativeTypes #-}

module Graphics.Diagrams.Core (module Graphics.Diagrams.Core) where
import Control.Monad.LPMonad
import Prelude hiding (sum,mapM_,mapM,concatMap,Num(..),(/))
import Control.Monad.RWS hiding (forM,forM_,mapM_,mapM)
import Data.LinearProgram
import Data.LinearProgram.Common as Graphics.Diagrams.Core (VarKind(..))
import Data.LinearProgram.LinExpr
import Data.Map (Map)
import qualified Data.Map as M
import Control.Lens hiding (element)
import Data.Traversable
import Data.Foldable
import System.IO.Unsafe

type LPState = LP Var Constant

-- | Solution of the linear programming problem
type Solution = Map Var Double


type Constant = Double

-- | Expressions are linear functions of the variables
type Expr = LinExpr Var Constant

data Point' a = Point {xpart :: a, ypart :: a}
  deriving (Eq,Show)

instance Traversable Point' where
  traverse f (Point x y) = Point <$> f x <*> f y

instance Foldable Point' where
  foldMap = foldMapDefault

instance Functor Point' where
  fmap = fmapDefault

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

instance Module Constant v => Module Constant (Point' v) where
  k *^ Point x y = Point (k *^ x) (k *^ y)

type Frozen x = x Constant
type FrozenPoint = Frozen Point'
type FrozenPath = Frozen Path'


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

$(makeLenses ''Backend)

data Env lab m = Env {_diaTightness :: Constant -- ^ Multiplicator to minimize constraints
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

-- | Some action to perform after a solution has been found.
data Freeze m where
  Freeze :: forall t m. Functor t => (t Constant -> m ()) -> t Expr -> Freeze m

newtype Diagram lab m a = Dia (RWST (Env lab m) [Freeze m] (Var,LPState) m a)
  deriving (Monad, Applicative, Functor, MonadReader (Env lab m), MonadWriter [Freeze m])

-- | @freeze x f@ performs @f@ on the frozen value of @x@.
freeze :: (Functor t, Monad m) => t Expr -> (t Constant -> m ()) -> Diagram lab m ()
freeze x f = tell [Freeze (\y -> (f y)) x]

instance Monad m => MonadState LPState (Diagram lab m) where
  get = Dia $ snd <$> get
  put y = Dia $ do
    (x,_) <- get
    put (x,y)

-------------
-- Diagrams


-- | Relax the optimisation functions by the given factor
relax :: Monad m => Constant -> Diagram lab m a -> Diagram lab m a
relax factor = tighten (1/factor)

-- | Tighten the optimisation functions by the given factor
tighten :: Monad m => Constant -> Diagram lab m a -> Diagram lab m a
tighten factor = local (over diaTightness (* factor))

--------------
-- Variables


newVar :: Monad m => Diagram lab m Expr
newVar = do
  [v] <- newVars [ContVar]
  return v

newVars :: Monad m => [VarKind] -> Diagram lab m [Expr]
newVars kinds = newVars' (zip kinds (repeat Free))

newVars' :: Monad m => [(VarKind,Bounds Constant)] -> Diagram lab m [Expr]
newVars' kinds = forM kinds $ \(k,b) -> do
  v <- rawNewVar
  setVarKind v k
  setVarBounds v b
  return $ variable v
 where rawNewVar :: Monad m => Diagram lab m Var
       rawNewVar = Dia $ do
         (Var x,y) <- get
         put $ (Var (x+1),y)
         return $ Var x


infix 4 <==,===,>==

----------------
-- Expressions

runDiagram :: Monad m => Backend lab m -> Diagram lab m a -> m a
runDiagram backend (Dia diag) = do
  (a,(_,problem),ds) <- runRWST diag (Env 1 defaultPathOptions backend)
                                        (Var 0,LP Min M.empty [] M.empty M.empty)
  let solution = case unsafePerformIO $ glpSolveVars simplexDefaults problem of
        (_retcode,Just (_objFunc,s)) -> s
        (retcode,Nothing) -> error $ "LP failed ret code = " ++ show retcode
  -- Raw Normal $ "%problem solved: " ++ show problem ++ "\n"
  forM_ ds (\(Freeze f x) -> f (fmap (valueIn solution) x))
  return a

-- | Value of an expression in the given solution
valueIn :: Solution -> Expr -> Double
valueIn sol (LinExpr m c) = sum (c:[scale * varValue v | (v,scale) <- M.assocs m])
 where varValue v = M.findWithDefault 0 v sol


-- | Embed a variable in an expression
variable :: Var -> Expr
variable v = LinExpr (M.singleton v 1) 0

-- | Embed a constant in an expression
constant :: Constant -> Expr
constant c = LinExpr M.empty c

(*-) :: Module Constant a => Constant -> a -> a
(*-) = (*^)
infixr 6 *-

-- | Average
avg :: Module Constant a => [a] -> a
avg xs = (1/fromIntegral (length xs)) *- add xs

-- | Absolute value, which can be MINIMIZED or put and upper bound on (but not
-- the other way around).
absoluteValue :: Monad m => Expr -> Diagram lab m Expr
absoluteValue x = do
  [t1,t2] <- newVars' [(ContVar,LBound 0),(ContVar,LBound 0)]
  t1 - t2 === x
  return $ t1 + t2

satAll :: Monad m => (Expr -> a -> Diagram lab m b) -> [a] -> Diagram lab m Expr
satAll p xs = do
  [m] <- newVars [ContVar]
  mapM_ (p m) xs
  return m

-- | Minimum or maximum of a list of expressions.
maximVar, minimVar :: Monad m => [Expr] -> Diagram lab m Expr
maximVar = satAll (>==)
minimVar = satAll (<==)

--------------
-- Expression constraints
(===), (>==), (<==) :: Expr -> Expr -> Monad m => Diagram lab m ()
e1 <== e2 = do
  let LinExpr f c = e1 - e2
  leqTo f (negate c)

(>==) = flip (<==)

e1 === e2 = do
  let LinExpr f c = e1 - e2
  equalTo f (negate c)

-- | minimize the distance between expressions
(=~=) :: Monad m => Expr -> Expr -> Diagram lab m ()
x =~= y = minimize =<< absoluteValue (x-y)

-------------------------
-- Expression objectives

minimize,maximize :: Monad m => Expr -> Diagram lab m ()
minimize (LinExpr x _) = do
  tightness <- view diaTightness
  addObjective (tightness *^ x)
maximize = minimize . negate


drawText :: Monad m => Point' Expr -> lab -> Diagram lab m BoxSpec
drawText point lab = do
  tl <- view (diaBackend . traceLabel)
  tl freeze diaRaw point lab

diaRaw :: Monad m => m a -> Diagram lab m a
diaRaw = Dia . lift
