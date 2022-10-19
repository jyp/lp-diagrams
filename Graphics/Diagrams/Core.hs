{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, RecursiveDo, TypeFamilies, OverloadedStrings, RecordWildCards,UndecidableInstances, PackageImports, TemplateHaskell, RankNTypes, GADTs, DeriveFunctor, ScopedTypeVariables, ConstraintKinds, OverloadedStrings #-}

module Graphics.Diagrams.Core (
  module Graphics.Diagrams.Types,
  Expr, constant, absE, newVar,
  minimize, maximize,
  (===), (>==), (<==), (=~=),
  Diagram(..), runDiagram,
  drawText,
  freeze, relax, tighten,
  registerNonOverlap
  ) where

import Prelude hiding (sum,mapM_,mapM,concatMap,Num(..),(/),fromRational,recip,(/),fail)
import qualified Prelude
import Control.Monad.RWS hiding (forM,forM_,mapM_,mapM,fail)
import Control.Monad.Fail
import Algebra.Classes as AC
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Control.Lens hiding (element)
import Data.Foldable
import System.IO.Unsafe
import Graphics.Diagrams.Types
import Data.List (isPrefixOf,intercalate)
import Data.String
import System.Process
import SMT.Model
import Numeric (showFFloat)

-- | Expressions are linear functions of the variables

newtype Var = Var Int
  deriving (Ord,Eq,Show,Enum)

class IsDouble a where
  fromDouble :: Double -> a
  -- sqrtE :: a -> a
  absE :: a -> a

instance IsDouble Constant where
  fromDouble = id
  -- sqrtE = sqrt
  absE = Prelude.abs

-- | S-Expression represented as strings
newtype SExpr = S {fromS :: String}

-- Generic environment
newtype R env y = R {_fromR :: env -> y}
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
  -- sqrtE = fmap sqrtE
  absE = fmap absE
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
instance Ring x => Scalable (R env x) (R env x) where
  (*^) = (*)
instance Ring x => Ring (R env x) where
  fromInteger x = pure (fromInteger x)
instance Field x => Field (R env x) where
  fromRational x = pure (fromRational x)
instance Group x => Group (R env x) where
  negate = fmap negate
  (-) = liftA2 (-)

newtype Expr = E {_fromE :: forall x. (Field x,IsDouble x) => R (Var -> x) x}

instance Additive Expr where
  zero = E zero
  E x + E y = E (x+y)
instance Group Expr where
  E x - E y = E (x-y)
-- Not a decidable theory: avoid.
-- instance Multiplicative Expr where
--   one = E one
--   E x * E y = E (x*y)
-- instance Division Expr where
--   E x / E y = E (x/y)
-- instance Ring Expr
-- instance Field Expr
-- instance Module Expr Expr where
--   (*^) = (*)
instance AbelianAdditive Expr
instance Scalable Rational Expr where
  k *^ E x = E (fromRational k*x)
instance Scalable Constant Expr where
  k *^ E x = E (fromDouble k*x)

-- | Some action to perform after a solution has been found.
data Freeze m where
  Freeze :: forall t m. Functor t => (t Constant -> m ()) -> t Expr -> Freeze m

type Constraint = SExpr

data DiagramState = DiagramState
  {_diaNextVar :: Var  -- ^ next var to allocate
  ,_diaConstraints :: [Constraint]
  ,_diaObjective :: Expr -- ^ objective function
  ,_diaVarNames :: Map Var String
  ,_diaNoOverlaps :: [Pair (Point' Expr)]
  }

$(makeLenses ''DiagramState)

newtype Diagram lab m a = Dia {fromDia :: RWST (Env lab m) [Freeze m] DiagramState m a}
  deriving (Monad, Applicative, Functor, MonadReader (Env lab m), MonadWriter [Freeze m], MonadState DiagramState)

instance MonadFail m => MonadFail (Diagram lab m) where
  fail msg = Dia (fail msg)

-- | @freeze x f@ performs @f@ on the frozen value of @x@.
freeze :: (Functor t, Monad m) => t Expr -> (t Constant -> m ()) -> Diagram lab m ()
freeze x f = tell [Freeze (\y -> (f y)) x]


-------------
-- Diagrams


runDiagram :: Monad m => Backend lab m -> Diagram lab m a -> m a
runDiagram backend diag = do
  let env = Env one defaultPathOptions backend
  (a,finalState,ds) <- runRWST (fromDia $ do x<-diag;resolveNonOverlaps;return x) env $
    DiagramState (Var 0) [] zero M.empty []
  let maxVar =  finalState ^. diaNextVar
      decls = [sexp ["declare-const", smtVar x, "Real"] | x <- [Var 0 .. maxVar]]
      constrs = intercalate "\n" $ map fromS $
        decls ++
        (unop "assert" <$> (finalState ^. diaConstraints)) ++
        [ unop "minimize" (renderExpr (finalState ^. diaObjective)),
          sexp ["check-sat"],
          sexp ["get-model"]
        ]
      solution = unsafePerformIO $ do
        writeFile "problem.smt2" $ constrs
        _exitCode <- system "z3 -smt2 problem.smt2 > result.smt2"
        res <- readFile "result.smt2"
        let resLines = lines res
        case resLines of
          ("sat":ls) -> do
            case readModel (unlines ls) of
              Right model -> return $ M.fromList model
              Left err -> do print err
                             error "runDiagram: failed to parse output model"
          _ -> error "runDiagram: z3 could not find a solution? check result.smt2"
      lkMod m (Var v) = M.findWithDefault
        (error ("variable not in model x" ++ show v))
        ("x"++show v) m

  forM_ ds (\(Freeze f x) -> f (fmap (\(E (R g)) -> g (lkMod solution)) x))
  return a

-- | Relax the optimisation functions by the given factor
relax :: Monad m => Rational -> Diagram lab m a -> Diagram lab m a
relax factor = tighten (recip factor)

-- | Tighten the optimisation functions by the given factor
tighten :: Monad m => Rational -> Diagram lab m a -> Diagram lab m a
tighten factor = local (over diaTightness (* factor))

--------------
-- Variables

newVar :: Monad m => String -> Diagram lab m Expr
newVar nm = do
  v <- rawNewVar nm
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


-- | Embed a variable in an expression
variable :: Var -> Expr
variable v = E (R $ \rho -> rho v)

-- | Embed a constant in an expression
constant :: Double -> Expr
constant c = E (R $ \_ -> fromDouble c)

satAll :: Monad m => String -> (Expr -> a -> Diagram lab m b) -> [a] -> Diagram lab m Expr
satAll name p xs = do
  m <- newVar name
  mapM_ (p m) xs
  return m

-- | Minimum or maximum of a list of expressions.
maximVar, minimVar :: Monad m => [Expr] -> Diagram lab m Expr
maximVar = satAll "maximum of" (>==)
minimVar = satAll "minimum of" (<==)

--------------
-- Expression constraints

(===), (>==), (<==) :: Monad m => Expr -> Expr -> Diagram lab m ()
e1 <== e2 = assert (e1 .<= e2)
(>==) = flip (<==)
e1 === e2 = assert (e1 .== e2)

-- | minimize the distance between expressions
(=~=) :: Monad m => Expr -> Expr -> Diagram lab m ()
x =~= y = minimize $ absE (x-y)

-------------------------
-- Expression objectives


minimize,maximize :: Monad m => Expr -> Diagram lab m ()
maximize = minimize . negate
minimize f = do
  tightness <- view diaTightness
  diaObjective %= \o -> (tightness *^ f) + o


drawText :: Monad m => Point' Expr -> lab -> Diagram lab m BoxSpec
drawText point lab = do
  be <- view diaBackend
  case be of Backend _ tl -> tl freeze diaRaw point lab

diaRaw :: Monad m => m a -> Diagram lab m a
diaRaw = Dia . lift

--------------------------
-- Non-overlapping things

registerNonOverlap :: Monad m => Point' Expr -> Point' Expr -> Diagram lab m ()
registerNonOverlap nw se = Dia $ diaNoOverlaps %= (Pair nw se:)

allPairs :: forall a. [a] -> [Pair a]
allPairs [] = []
allPairs (x:xs) = [Pair x y | y <- xs] ++ allPairs xs

resolveNonOverlaps :: Monad m => Diagram lab m ()
resolveNonOverlaps = do
  noOvl <- Dia $ use diaNoOverlaps
  forM_ (allPairs noOvl) $ \p -> do
    assert (disj (ffmap xpart p) .|| disj (ffmap ypart p))
 where disj (Pair (Pair p1 q1) (Pair p2 q2)) = (q1 .<= p2) .|| (q2 .<= p1)
       ffmap f = fmap (fmap f)


---------------------------------
-- Constraint & SExpr utils

assert :: Monad m => SExpr -> Diagram lab m ()
assert x = diaConstraints %= (x:)

(.<=),(.==) :: Expr -> Expr -> Constraint
x .<= y = binop "<=" (renderExpr x) (renderExpr y)

x .== y = binop "=" (renderExpr x) (renderExpr y)

(.||) :: Constraint -> Constraint -> Constraint
(.||) = binop "or"

renderExpr :: Expr -> SExpr
renderExpr (E (R x)) = x smtVar

smtVar :: Var -> SExpr
smtVar (Var x) = S ("x" ++ show x)

parens :: forall a. IsString [a] => [a] -> [a]
parens x = "(" ++ x ++ ")"
sexp :: [SExpr] -> SExpr
sexp xs = S $ parens $ intercalate " " $ map fromS xs
binop :: String -> SExpr -> SExpr -> SExpr
binop s x y = sexp [S s,x,y]
unop :: String -> SExpr -> SExpr
unop s x = sexp [S s,x]
instance Multiplicative (SExpr) where
  (*) = binop "*"
  one = S "1"
instance Division (SExpr) where
  (/) = binop "/"
instance Additive (SExpr) where
  (+) = binop "+"
  zero = S "0"
instance AbelianAdditive (SExpr)
instance Field (SExpr)
instance Scalable SExpr SExpr where
  (*^) = (*)
instance Ring (SExpr)
instance Group (SExpr) where
  negate = unop "-"
  (-) = binop "-"
instance IsString SExpr where
  fromString = S

instance IsDouble Expr where
  fromDouble d = E (R $ \_ -> fromDouble d)
  -- sqrtE (E x) = E (sqrtE x)
  absE (E x) = E (absE x)

instance IsDouble SExpr where
  fromDouble x = S $ showFFloat Nothing x ""
  -- can't use 'show': z3 solver 4.4.1 does not understand scientific notation
  -- (eg. 4e-2)

  -- sqrtE x = binop "^" x "0.5"
  absE = unop "abs"
