{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RecursiveDo, TypeFamilies, OverloadedStrings, RecordWildCards,UndecidableInstances, PackageImports, TemplateHaskell, RankNTypes, GADTs, ImpredicativeTypes, DeriveFunctor, ScopedTypeVariables, ConstraintKinds #-}

module Graphics.Diagrams.Core (
  module Graphics.Diagrams.Types,
  Expr, constant, sqrtE, newVars,
  minimize, maximize,
  (===), (>==), (<==), (=~=),
  Diagram(..), runDiagram,
  drawText,
  freeze, relax, tighten,
  registerNonOverlap
  ) where

import Prelude hiding (sum,mapM_,mapM,concatMap,Num(..),(/),fromRational,recip,(/))
import qualified Prelude
import Control.Monad.RWS hiding (forM,forM_,mapM_,mapM)
import Algebra.Classes as AC
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Control.Lens hiding (element)
import Data.Traversable
import Data.Foldable
import System.IO.Unsafe
import Graphics.Diagrams.Types
import Data.SBV hiding (minimize,maximize,(===))
import qualified Data.SBV

-- | Expressions are linear functions of the variables
type SBVEnv = Map Var (SConstant)

type SConstant = SBV AlgReal

newtype Var = Var Int
  deriving (Ord,Eq,Show,Enum)

instance IsDouble Constant where
  fromDouble = id

instance IsDouble (SConstant) where
  fromDouble = fromSDouble sRNE . literal

-- | A non-linear expression.
newtype R env y = R {fromR :: env -> y}
  deriving Functor
instance Applicative (R env) where
  pure x = R (\_ -> x)
  R f <*> R x = R (\rho -> (f rho) (x rho))
liftA2 :: forall (f :: * -> *) a b a1.
            Applicative f =>
            (a1 -> a -> b) -> f a1 -> f a -> f b
liftA2 f x y = f <$> x <*> y
instance IsDouble x => IsDouble (R env x) where
  fromDouble x = pure (fromDouble x)
instance Additive x => Additive (R env x) where
  zero = pure zero
  (+) = liftA2 (+)
instance Multiplicative x => Multiplicative (R env x) where
  one = pure one
  (*) = liftA2 (*)
instance Division x => Division (R env x) where
  recip = fmap recip
  (/) = liftA2 (/)
instance AbelianAdditive x => AbelianAdditive (R env x)
instance Ring x => Ring (R env x) where
  fromInteger x = pure (fromInteger x)
instance Field x => Field (R env x) where
  fromRational x = pure (fromRational x)
instance Group x => Group (R env x) where
  negate = fmap negate
  (-) = liftA2 (-)
instance Multiplicative (SConstant) where
  (*) = (Prelude.*)
  one = 1
instance Division (SConstant) where
  (/) = (Prelude./)
instance Additive (SConstant) where
  (+) = (Prelude.+)
  zero = 0
instance AbelianAdditive (SConstant)
instance Field (SConstant)
instance Ring (SConstant)
instance Group (SConstant) where
  (-) = (Prelude.-)
  negate = Prelude.negate

sqrtE :: Expr -> Expr
sqrtE f = E (R (\rho -> id {- fixme ! -} (fromR (fromE f) rho)))

type Constraint = R SBVEnv (SBV Bool)
newtype Expr = E {fromE :: forall x. (Field x,IsDouble x,Prelude.Num x) => R (Map Var x) x}

class IsDouble d where
  fromDouble :: Double -> d

instance Additive Expr where
  zero = E zero
  E x + E y = E (x+y)
instance Group Expr where
  E x - E y = E (x-y)
instance Multiplicative Expr where
  one = E one
  E x * E y = E (x*y)
instance Division Expr where
  E x / E y = E (x/y)
instance AbelianAdditive Expr
instance Ring Expr
instance Field Expr
instance Module Rational Expr where
  k *^ E x = E (fromRational k*x)
instance Module Constant Expr where
  k *^ E x = E (fromDouble k*x)
instance Module Expr Expr where
  (*^) = (*)

-- | Some action to perform after a solution has been found.
data Freeze m where
  Freeze :: forall t m. Functor t => (t Constant -> m ()) -> t Expr -> Freeze m

data DiagramState = DiagramState
  {_diaNextVar :: Var
  ,_diaLinConstraints :: [Constraint]
  ,_diaObjective :: Expr
  ,_diaVarNames :: Map Var String
  ,_diaNoOverlaps :: [Pair (Point' Expr)]
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
  (a,finalState,ds) <- runRWST (fromDia $ do x<-diag;{-resolveNonOverlaps-};return x) env $
    DiagramState (Var 0) [] zero (M.empty) []
  let Var maxVar =  finalState ^. diaNextVar
      mkEnv :: [a] -> Map Var a
      mkEnv xs = M.fromList $ zip [Var 0..] xs
      obj :: [SConstant] -> SConstant
      obj rho = (fromR (fromE (finalState ^. diaObjective))) (mkEnv rho)
      constr :: [SConstant] -> SBV Bool
      constr rho = bAll id (map (\(R f) -> f rho') (finalState ^. diaLinConstraints))
        where rho'= mkEnv rho
      solution = unsafePerformIO $ do
       msol <- Data.SBV.minimize (Iterative True) obj maxVar  constr
       case msol of
         Just xs -> return $ fmap (fromRational . toRational) $ mkEnv xs

  forM_ ds (\(Freeze f x) -> f (fmap (\(E (R g)) -> g solution) x))
  return a


-- | Embed a variable in an expression
variable :: Var -> Expr
variable v = E (R $ \rho -> M.findWithDefault (error "variable not found in env") v rho)

-- | Embed a constant in an expression
constant :: Double -> Expr
constant c = E (R $ \_ -> fromDouble c)

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
E (R e1) <== (E (R e2)) = diaLinConstraints %= (R (\rho -> e1 rho .<= e2 rho ):)


(>==) = flip (<==)

E (R e1) === (E (R e2)) = diaLinConstraints %= (R (\rho -> e1 rho .== e2 rho ):)

-- | minimize the distance between expressions
(=~=) :: Monad m => Expr -> Expr -> Diagram lab m ()
x =~= y = minimize $ square (x-y)

-------------------------
-- Expression objectives


minimize,maximize :: Monad m => Expr -> Diagram lab m ()
maximize = minimize . negate
minimize f = do
  tightness <- view diaTightness
  diaObjective %= \o -> tightness *^ f + o


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

{-
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
-}
