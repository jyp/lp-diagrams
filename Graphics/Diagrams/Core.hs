{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RecursiveDo, TypeFamilies, OverloadedStrings, RecordWildCards,UndecidableInstances, PackageImports, TemplateHaskell, RankNTypes, GADTs, ImpredicativeTypes, DeriveFunctor, ScopedTypeVariables, ConstraintKinds #-}

module Graphics.Diagrams.Core (
  module Graphics.Diagrams.Types,
  Expr, constant, newVars,
  minimize, maximize,
  (===), (>==), (<==), (=~=),
  GExpr,
  minimize', maximize',
  fromLinear,
  Diagram(..), runDiagram,
  drawText,
  freeze, relax, tighten,
  registerNonOverlap
  ) where

import Prelude hiding (sum,mapM_,mapM,concatMap,Num(..),(/),fromRational,recip,(/))
import Control.Monad.RWS hiding (forM,forM_,mapM_,mapM)
import Algebra.Classes as AC
import Algebra.Linear as Linear
import Algebra.Linear.GaussianElimination
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Control.Lens hiding (element)
import Data.Traversable
import Data.Foldable
import System.IO.Unsafe
import Data.Vector (Vector,(!))
import qualified Data.Vector as V
import qualified Data.Vector.Storable as S
import Numeric.Optimization.Algorithms.HagerZhang05 hiding (optimize)
import qualified Numeric.Optimization.Algorithms.HagerZhang05 as HagerZhang05
import Algebra.AD as AD
import Graphics.Diagrams.Types


-- | Expressions are linear functions of the variables
type Expr = LinFunc Var Constant

newtype Var = Var Int
  deriving (Ord,Eq,Show,Enum)

-- | A non-linear expression.
type GExpr = E Var Constant

fromLinear :: Expr -> GExpr
fromLinear m = fromLinear' one m AD.var

fromLinear' :: forall a scalar. (Module scalar a) => a -> LinFunc Var scalar -> (Var -> a) -> a
fromLinear' unit (Func m c) f = c *^ unit + fromSum (M.foldMapWithKey (\v k -> AC.Sum (k *^ f v)) m)

substLinear :: Expr -> (Var -> Expr) -> Expr
substLinear = fromLinear' (Func M.empty 1)

rename :: (Var -> Var) -> Expr -> Expr
rename f e = substLinear e (Linear.var . f)


-- | Some action to perform after a solution has been found.
data Freeze m where
  Freeze :: forall t m. Functor t => (t Constant -> m ()) -> t Expr -> Freeze m

data Pair a = Pair a a
  deriving (Functor)

instance Show a => Show (Pair a) where
  show (Pair x y) = show (x,y)

data DiagramState = DiagramState
  {_diaNextVar :: Var
  ,_diaLinConstraints :: [Constraint Var Constant]
  ,_diaObjective :: GExpr
  ,_diaVarNames :: Map Var String
  ,_diaNoOverlaps :: [Pair (Point' GExpr)]
  }

$(makeLenses ''DiagramState)

newtype Diagram lab m a = Dia {fromDia :: (RWST (Env lab m) [Freeze m] DiagramState m a)}
  deriving (Monad, Applicative, Functor, MonadReader (Env lab m), MonadWriter [Freeze m], MonadState DiagramState)

-- | @freeze x f@ performs @f@ on the frozen value of @x@.
freeze :: (Functor t, Monad m) => t Expr -> (t Constant -> m ()) -> Diagram lab m ()
freeze x f = tell [Freeze (\y -> (f y)) x]


-------------
-- Diagrams


-- | Relax the optimisation functions by the given factor
relax :: Monad m => Rational -> Diagram lab m a -> Diagram lab m a
relax factor = tighten (one/factor)

-- | Tighten the optimisation functions by the given factor
tighten :: Monad m => Rational -> Diagram lab m a -> Diagram lab m a
tighten factor = local (over diaTightness (* factor))

--------------
-- Variables


newVar :: Monad m => String -> Diagram lab m Expr
newVar name = do
  [v] <- newVars [name]
  return v

newVars :: Monad m => [String] -> Diagram lab m [Expr]
newVars kinds = forM kinds $ \name -> do
  v <- rawNewVar name
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
runDiagram backend diag = do
  let env = Env one defaultPathOptions backend
  (a,finalState,ds) <- runRWST (fromDia $ do x<-diag;resolveNonOverlaps;return x) env $
    DiagramState (Var 0) [] zero (M.empty) []
  let reducedConstraints = M.fromList $ linSolve (finalState ^. diaLinConstraints)
      linSolvSubst v = case M.lookup v reducedConstraints of
        Nothing -> Linear.var v
        Just x -> x
      solvSubst = fromLinear . linSolvSubst
      maxVar =  finalState ^. diaNextVar
      freeVars = filter (\v -> M.notMember v reducedConstraints) [Var 0..maxVar]
      varsToFreeVars' :: Map Var Int
      varsToFreeVars' = M.fromList (zip freeVars [0..])
      freeVarsToVars :: V.Vector Var
      freeVarsToVars = V.fromList freeVars

      obj' :: GExpr
      obj' = AD.subst (finalState ^. diaObjective) solvSubst
      grad' rho = (y,fmap (\v -> M.findWithDefault zero v dy) freeVarsToVars)
         where D y dy = fromE obj' (\v -> maybe (error "not found") id (M.lookup v env') )
               env' = M.mapWithKey (\v i -> D (rho ! i) (M.singleton v 1)) varsToFreeVars'
      (solution,_result,_statistics) = unsafePerformIO $ do
       putStrLn $ "free vars: " ++ show freeVars
       putStrLn $ "reducedConstraints: " ++ show reducedConstraints
       putStrLn $ "optimizing ..."
       opt@(s,_,_) <- HagerZhang05.optimize
        defaultParameters {verbose = VeryVerbose}
        0.01
        (V.replicate (length freeVars) 0)
        (VFunction (fst . grad')) (VGradient (snd . grad')) (Just (VCombined grad'))
       putStrLn $ "done: "  ++ show (grad' (S.convert s))
       return opt
      solution' = fmap (solution S.!) varsToFreeVars'
      fullSolution = M.union solution' (fmap (valueIn solution') reducedConstraints)

  forM_ ds (\(Freeze f x) -> f (fmap (valueIn fullSolution) x))
  return a


valueIn :: Map Var Double -> Expr -> Double
valueIn sol f = fromLinear' one f (\v -> M.findWithDefault 0 v sol)

-- | Embed a variable in an expression
variable :: Var -> Expr
variable v = Func (M.singleton v 1) 0

-- | Embed a constant in an expression
constant :: Constant -> Expr
constant c = Func M.empty c

satAll :: Monad m => String -> (Expr -> a -> Diagram lab m b) -> [a] -> Diagram lab m Expr
satAll name p xs = do
  [m] <- newVars [(name)]
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
  let Func f c = e1 - e2
      isFalse = M.null f && c < 0
  when isFalse $ error "Diagrams.Core: inconsistent constraint!"
  minimize' $ E $ \s ->
    let [v1,v2] = map (($ s) . fromE . fromLinear) [e1,e2]
    in if v1 <= v2 then zero else square (square (v2-v1))

prettyExpr :: Monad m => Expr -> Diagram lab m String
prettyExpr (Func f k) = do
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
  constrName <- (\x y -> x ++ " = " ++ y) <$> prettyExpr e1 <*> prettyExpr e2
  diaLinConstraints %= (e1 - e2 :)

-- | minimize the distance between expressions
(=~=) :: Monad m => GExpr -> GExpr -> Diagram lab m ()
x =~= y = minimize' $ square (x-y)

-------------------------
-- Expression objectives

minimize,maximize :: Monad m => Expr -> Diagram lab m ()
minimize = minimize' . fromLinear
maximize = minimize . negate

minimize',maximize' :: Monad m => GExpr -> Diagram lab m ()
maximize' = minimize' . negate
minimize' f = do
  tightness <- view diaTightness
  diaObjective %= \o -> (fromRational tightness::Double) *^ f + o


drawText :: Monad m => Point' Expr -> lab -> Diagram lab m BoxSpec
drawText point lab = do
  tl <- view (diaBackend . traceLabel)
  tl freeze diaRaw point lab

diaRaw :: Monad m => m a -> Diagram lab m a
diaRaw = Dia . lift

--------------------------
-- Non-overlapping things

registerNonOverlap :: Monad m => Point' Expr -> Point' Expr -> Diagram lab m ()
registerNonOverlap nw se = Dia $ diaNoOverlaps %= (Pair (fromLinear <$> nw) (fromLinear <$>  se):)

surface :: forall a. Multiplicative a => Point' a -> a
surface (Point x y) = x*y

resolveNonOverlaps :: Monad m => Diagram lab m ()
resolveNonOverlaps = do
  noOvl <- Dia $ use diaNoOverlaps
  minimize' $ E $ \s ->
    add $ do
      pair <- allPairs noOvl
      let (Pair bx1 bx2) = fmap (fmap (fmap (($ s) . fromE))) pair
          overlap = inters bx1 bx2
      return $ if nonEmpty overlap then (square $ surface overlap) else zero
    where
      allPairs [] = []
      allPairs (x:xs) = [Pair x y | y <- xs] ++ allPairs xs
      inters (Pair p1 q1) (Pair p2 q2) = (min <$> q1 <*> q2) - (max <$> p1 <*> p2)
      nonEmpty (Point a b) = a > zero && b > zero
