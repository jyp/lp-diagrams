{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RebindableSyntax #-}
module Algebra.AD (D(..),E(..),subst,dVar,var,sqrtE) where

import Algebra.Classes hiding ((:+))
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Prelude hiding (Num(..),(/),fromRational,recip)
-- import Data.Vector as V
import Data.Function (on)

data AST v c = V v
  | AST v c :* AST v c
  | AST v c :+ AST v c
  | AST v c :- AST v c
  | K c

instance (Show v, Show c) => Show (AST v c) where
  showsPrec p (V v) = shows v
  showsPrec p (K c ) = shows c
  showsPrec p (x :+ y) = parens (p>2) (showsPrec 2 x . showString " + " . showsPrec 2 y)
  showsPrec p (x :* y) = parens (p>3) (showsPrec 3 x . showString " + " . showsPrec 3 y)

parens True x = showString "(" . x . showString ")"
parens False x = x

data D v c = D {dValue :: !c
               ,dDerivs :: !(Map v c)
               }
  deriving Show

dVar :: forall v c. Ring c => v -> c -> D v c
dVar v c = D c (M.singleton v 1)

var :: (Multiplicative c, Additive c, Ord v) => v -> E v c
var v = E $ \env -> env v

instance (Ord v,Additive c) => Additive (D v c) where
  zero = D zero zero
  D v1 d1 + D v2 d2 = D (v1 + v2) (d1 + d2)

instance (Ord v,Group c) => Group (D v c) where
  negate (D x d) = D (negate x) (negate d)
  D v1 d1 - D v2 d2 = D (v1 - v2) (d1 - d2)

instance Ord c => Ord (D v c) where
  compare = compare `on` dValue

instance Eq c => Eq (D v c) where
  (==) = (==) `on` dValue

instance (Ord v,Ring c) => Multiplicative (D v c) where
  one = D one zero
  D v1 d1 * D v2 d2 = D (v1 * v2) (v2 *^ d1 + v1 *^ d2)

instance (AbelianAdditive c,Ord v) => AbelianAdditive (D v c)
instance (Ord v,Ring c) => Module c (D v c) where
  k *^ D v d = D (k * v) (k *^ d)

instance (Ord v,Ring c) => Module (D v c) (D v c) where
  (*^) = (*)

instance (Ord v, Ring c) => Ring (D v c) where
  fromInteger k = D (fromInteger k) zero

newtype E v c = E {fromE :: (v -> D v c) -> D v c}

instance (Ord v,Additive c) => Additive (E v c) where
  zero = E (const zero)
  (+) = liftE2 (+)

instance (Ord v,Group c) => Group (E v c) where
  negate (E x) = E (negate . x)
  (-) = liftE2 (-)

instance (Ord v,Ring c) => Multiplicative (E v c) where
  one = E (const one)
  (*) = liftE2 (*)

instance (Ord v,Ring c) => AbelianAdditive (E v c)
instance (Ord v,Ring c) => Module c (E v c) where
  k *^ E x = E ((k *^) . x)

instance (Ord v,Ring c) => Module (E v c) (E v c) where
  (*^) = (*)

instance (Ord v, Ring c) => Ring (E v c) where
  fromInteger k = E (\ _ -> fromInteger k)

liftE2 :: forall t t1. (D t t1 -> D t t1 -> D t t1) -> E t t1 -> E t t1 -> E t t1
liftE2 f (E x) (E y) = E (\e -> f (x e) (y e))

liftE :: forall t t1. (D t t1 -> D t t1) -> E t t1 -> E t t1
liftE f (E x) = E (\e -> f (x e))

subst :: E v c -> (v -> E v c) -> E v c
subst (E p) f = E $ \k -> p (\a -> fromE (f a) k)

sqrtD :: (Ord v, Floating c, Field c) => D v c -> D v c
sqrtD (D v d) = D (sqrtv) ((0.5/sqrtv) *^ d)
  where sqrtv = sqrt v

sqrtE :: forall t t1. (Floating t1, Ord t, Field t1) => E t t1 -> E t t1
sqrtE = liftE sqrtD

instance (Field c,Ord v) => Division (D v c) where
  recip (D v d) = D (recip v) (negate (square iv) *^ d)
    where square x = x*x
          iv = recip v

instance (Field c,Ord v) => Division (E v c) where
  recip = liftE recip
  (/) = liftE2 (/)
