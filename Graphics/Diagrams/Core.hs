{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RecursiveDo, TypeFamilies, OverloadedStrings, RecordWildCards,UndecidableInstances, PackageImports, TemplateHaskell, RankNTypes, GADTs, ImpredicativeTypes, DeriveFunctor, ScopedTypeVariables #-}

module Graphics.Diagrams.Core (module Graphics.Diagrams.Core) where
import Control.Monad.LPMonad
import Prelude hiding (sum,mapM_,mapM,concatMap,Num(..),(/))
import Control.Monad.RWS hiding (forM,forM_,mapM_,mapM)
import Data.LinearProgram
import Data.LinearProgram.Common as Graphics.Diagrams.Core (VarKind(..))
import Data.LinearProgram.LinExpr
import Data.Map (Map)
import qualified Data.Map.Strict as M
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
  deriving (Eq,Show,Functor)

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

data Pair a = Pair a a
  deriving (Functor)

instance Show a => Show (Pair a) where
  show (Pair x y) = show (x,y)

data DiagramState = DiagramState
  {_diaNextVar :: Var
  ,_diaLPState :: LPState
  ,_diaVarNames :: Map Var String
  ,_diaNoOverlaps :: [Pair (Point' Expr)]
  }

$(makeLenses ''DiagramState)

newtype Diagram lab m a = Dia {fromDia :: (RWST (Env lab m) [Freeze m] DiagramState m a)}
  deriving (Monad, Applicative, Functor, MonadReader (Env lab m), MonadWriter [Freeze m])

-- | @freeze x f@ performs @f@ on the frozen value of @x@.
freeze :: (Functor t, Monad m) => t Expr -> (t Constant -> m ()) -> Diagram lab m ()
freeze x f = tell [Freeze (\y -> (f y)) x]

instance Monad m => MonadState LPState (Diagram lab m) where
  get = Dia $ use diaLPState
  put y = Dia $ diaLPState .= y

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


newVar :: Monad m => String -> Diagram lab m Expr
newVar name = do
  [v] <- newVars [(name,ContVar)]
  return v

newVars :: Monad m => [(String,VarKind)] -> Diagram lab m [Expr]
newVars kinds = newVars' (zip kinds (repeat Free))

newVars' :: Monad m => [((String,VarKind),Bounds Constant)] -> Diagram lab m [Expr]
newVars' kinds = forM kinds $ \((name,k),b) -> do
  v <- rawNewVar name
  setVarKind v k
  setVarBounds v b
  return $ variable v
 where rawNewVar :: Monad m => String -> Diagram lab m Var
       rawNewVar name = Dia $ do
         Var x <- use diaNextVar
         diaNextVar .= Var (x+1)
         diaVarNames %= M.insert (Var x) name
         return $ Var x


infix 4 <==,===,>==

----------------
-- Expressions

runDiagram :: Monad m => Backend lab m -> Diagram lab m a -> m a
runDiagram backend (Dia diag) = do
  let env = Env 1 defaultPathOptions backend
  (a,finalState,ds) <- runRWST diag env $
    DiagramState (Var 0) (LP Min M.empty [] M.empty M.empty) (M.empty) []
  let problem0 = finalState ^. diaLPState
      solution0 = case unsafePerformIO $ glpSolveVars simplexDefaults problem0 of
        (_retcode,Just (_objFunc,s)) -> s
        (retcode,Nothing) -> error $ "LP failed ret code = " ++ show retcode
  (ovlDbg,finalState',_) <- runRWST (fromDia $ resolveNonOverlaps solution0) env finalState
  let problem1 = finalState' ^. diaLPState
      solution1 = case unsafePerformIO $ ({-putStrLn "ovlDbg: " >> print ovlDbg >> -}
        glpSolveVars simplexDefaults problem1) of
        (_retcode,Just (_objFunc,s)) -> s
        (retcode,Nothing) -> error $ "LP failed ret code = " ++ show retcode
  -- Raw Normal $ "%problem solved: " ++ show problem ++ "\n"
  forM_ ds (\(Freeze f x) -> f (fmap (valueIn solution1) x))
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
infixr 7 *-

-- | Average
avg :: Module Constant a => [a] -> a
avg xs = (1/fromIntegral (length xs)) *- add xs

-- | Absolute value, which can be MINIMIZED or put and upper bound on (but not
-- the other way around).
absoluteValue :: Monad m => Expr -> Diagram lab m Expr
absoluteValue x = do
  [t1,t2] <- newVars' [((("absoluteStack1",ContVar),LBound 0)),(("absoluteStack2",ContVar),LBound 0)]
  t1 - t2 === x
  return $ t1 + t2

satAll :: Monad m => String -> (Expr -> a -> Diagram lab m b) -> [a] -> Diagram lab m Expr
satAll name p xs = do
  [m] <- newVars [(name,ContVar)]
  mapM_ (p m) xs
  return m

-- | Minimum or maximum of a list of expressions.
maximVar, minimVar :: Monad m => [Expr] -> Diagram lab m Expr
maximVar = satAll "maximum of" (>==)
minimVar = satAll "minimum of" (<==)

--------------
-- Expression constraints
(===), (>==), (<==) :: Expr -> Expr -> Monad m => Diagram lab m ()
e1 <== e2 = do
  let LinExpr f c = e1 - e2
      isFalse = M.null f && c < 0
  when isFalse $ error "Diagrams.Core: inconsistent constraint!"
  constrName <- (\x y -> x ++ "<= " ++ y) <$> prettyExpr e1 <*> prettyExpr e2
  leqTo' constrName f (negate c)



prettyExpr :: Monad m => Expr -> Diagram lab m String
prettyExpr (LinExpr f k) = do
  vnames <- Dia (use diaVarNames)
  let vname n = case M.lookup n vnames of
        Nothing -> error ("prettyExpr: variable not found: " ++ show n)
        Just nm -> nm
  return $ prettySum ([prettyProd c (vname v) | (v,c) <- M.assocs f]  ++ [show k | k /= 0])
  where prettySum [] = "0"
        prettySum xs = foldr1 prettyPlus xs
        prettyPlus a ('-':b) = a ++ ('-':b)
        prettyPlus x y = x ++ "+" ++ y
        prettyProd 1 v = show v
        prettyProd (-1) v = '-' : show v
        prettyProd c v = show c ++ show v

(>==) = flip (<==)

e1 === e2 = do
  let LinExpr f c = e1 - e2
      isFalse = M.null f && c /= 0
  when isFalse $ error "Diagrams.Core: inconsistent constraint!"
  constrName <- (\x y -> x ++ " = " ++ y) <$> prettyExpr e1 <*> prettyExpr e2
  equalTo' constrName f (negate c)

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

--------------------------
-- Non-overlapping things

registerNonOverlap :: Monad m => Point' Expr -> Point' Expr -> Diagram lab m ()
registerNonOverlap nw se = Dia $ diaNoOverlaps %= (Pair nw se:)


-- resolveNonOverlaps :: Monad m => Solution -> Diagram lab m Bool
resolveNonOverlaps s = do
  noOvl <- Dia $ use diaNoOverlaps
  forM_ (allPairs noOvl) (\(pair :: Pair (Pair (Point' Expr))) -> do
    let frozenPair@(Pair bx1@(Pair nw1 _) bx2@(Pair nw2 _)) = fmap (fmap (fmap (valueIn s))) pair
        overlap = inters bx1 bx2
        doSomething = nonEmpty overlap
    when doSomething $ do
        let part :: forall a. Point' a -> a
            part = (if xpart overlap > ypart overlap then ypart else xpart)
            Pair (Pair _ p1) (Pair p2 _) = (if part nw1 < part nw2 then id else flipPair) pair
        part p1 <== part p2
    return ())
  where
    allPairs [] = []
    allPairs (x:xs) = [Pair x y | y <- xs] ++ allPairs xs
    inters (Pair p1 q1) (Pair p2 q2) = (max <$> q1 <*> q2) - (min <$> p1 <*> p2)
    nonEmpty (Point a b) = a > 0 && b > 0
    flipPair (Pair a b) = Pair b a
