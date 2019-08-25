{-# LANGUAGE DisambiguateRecordFields, NamedFieldPuns, RecordWildCards, PostfixOperators, LiberalTypeSynonyms, TypeOperators, OverloadedStrings, PackageImports, ScopedTypeVariables #-}

module Graphics.Diagrams.DerivationTrees (
-- * Basics
module Data.Monoid,
module Data.LabeledTree,

-- * Derivation' building
-- axiom, rule, etc, aborted,
emptyDrv, haltDrv', delayPre,
dummy, rule, Derivation, Premise, Rule(..),

-- * Links
LineStyle,defaultLink,Link(..),

-- * Engine
derivationTreeDiag, delayD

) where

-- import DerivationTrees.Basics
import Control.Monad.Writer
import Data.LabeledTree
import Data.Monoid
import Graphics.Diagrams as D hiding (label)
import qualified Data.Tree as T
import Algebra.Classes
import Prelude hiding (Num(..))
------------------
--- Basics

type LineStyle = PathOptions -> PathOptions

data Link lab = Link {label :: lab, linkStyle :: LineStyle, steps :: Int}  -- ^ Regular link
              | Delayed -- ^ automatic delaying

defaultLink :: Monoid lab => Link lab
defaultLink = Link mempty (denselyDotted . outline "black")  0


-------------------

data Rule lab = Rule {ruleStyle :: LineStyle, delimiter :: lab, ruleLabel :: lab, conclusion :: lab}
--  deriving Show

type Premise lab = Link lab ::> Derivation lab
type Derivation lab = Tree (Link lab) (Rule lab)

--------------------------------------------------
-- Delay

depth :: forall lab t. Link lab ::> Tree (Link lab) t -> Int
depth (Link{steps} ::> Node _ ps) = 1 + steps + maximum (0 : map depth ps)

isDelayed :: Premise lab -> Bool
isDelayed (Delayed{} ::> _) = True
isDelayed _ = False

delayPre :: forall lab a. Int -> Link lab ::> a -> Link lab ::> a
delayPre s (Link {..} ::> j) = Link {steps = s, ..} ::> j

delayD :: Monoid lab => Derivation lab -> Derivation lab
delayD (Node r ps0) = Node r (map delayP ps)
    where ps = fmap (fmap delayD) ps0
          ps' = filter (not . isDelayed) ps
          delayP (Delayed ::> d) = defaultLink {steps = 1 + maximum (0 : map depth ps')} ::> d
          delayP p = p

----------------------------------------------------------
-- Diagramify

derivationTreeDiag :: Monad m => Derivation lab -> Diagram lab m ()
derivationTreeDiag d = do
  h <- newVar "height" -- the height of a layer in the tree.
  minimize h
  h >== constant 1
  tree@(T.Node (_,n,_) _) <- toDiagram h d
  forM_ (T.levels tree) $ \ls ->
    case ls of
      [] -> return ()
      (_:ls') -> forM_ (zip ls ls') $ \((_,_,l),(r,_,_)) ->
        (l + Point (constant 10) zero) `westOf` r
  let leftFringe = map head nonNilLevs
      rightFringe = map last nonNilLevs
      nonNilLevs = filter (not . null) $ T.levels tree
  leftMost <- newVar "leftMost"; rightMost <- newVar "rightMost" 
  forM_ leftFringe $ \(p,_,_) ->
    leftMost <== xpart p
  forM_ rightFringe $ \(_,_,p) ->
    xpart p <== rightMost
  tighten 10 $ minimize $ (rightMost - leftMost)
  n # Center .=. zero

toDiagPart :: Monad m => Expr -> Premise lab -> Diagram lab m (T.Tree (Point,Object,Point))
toDiagPart layerHeight (Link{..} ::> rul)
  | steps == 0 = toDiagram layerHeight rul
  | otherwise = do
    above@(T.Node (_,concl,_) _) <- toDiagram layerHeight rul
    ptObj <- vrule "ptObj"
    let pt = ptObj # S
    pt `eastOf` (concl # W)
    pt `westOf` (concl # E)
    (xpart pt) =~= (xpart (concl # Center))
    let top = ypart (concl # S)
    ypart pt + (fromIntegral steps *- layerHeight) === top
    using linkStyle $ path $ polyline [ptObj # Base,Point (xpart pt) top]
    let embedPt 1 x = T.Node (concl # W,ptObj,concl # E) [x]
        embedPt n x = T.Node (pt,ptObj,pt) [embedPt (n-1) x]
    return $ embedPt steps above

-- | @chainBases distance objects@
-- - Ensures that all the objects have the same baseline.
-- - Separates the objects by the given distance
-- - Returns an object encompassing the group, with a the baseline set correctly.
-- - Returns the average distance between the objects

chainBases :: Monad m => Expr -> [Object] -> Diagram lab m (Object,Expr)
chainBases _ [] = do
  o <- box "empty"
  return (o,zero)
chainBases spacing ls = do
  grp <- box "grp"
  forM_ [Base,N,S] $ \ anch -> do
    D.align ypart $ map (# anch) (grp:ls)
  dxs <- forM (zip ls (tail ls)) $ \(x,y) -> do
    let dx = xdiff (x # E) (y # W)
    dx >== spacing
    return dx
  D.align xpart [grp # W,head ls # W]
  D.align xpart [grp # E,last ls # E]
  return (grp,avg dxs)

debug :: Monad m => m a -> m ()
debug x = return () 
-- debug x = x >> return ()

-- | Put object in a box of the same vertical extent, and baseline,
-- but whose height can be bigger.
relaxHeight :: (Monad m) => Object -> Diagram lab m Object
relaxHeight o = do
  b <- box "relaxed"
  debug $ traceBox "green" o
  D.align xpart [b#W,o#W]
  D.align xpart [b#E,o#E]
  D.align ypart [b#Base,o#Base]
  o `fitsVerticallyIn` b
  return b

toDiagram :: Monad m => Expr -> Derivation lab -> Diagram lab m (T.Tree (Point,Object,Point))
toDiagram layerHeight (Node Rule{..} premises) = do
  ps <- mapM (toDiagPart layerHeight) premises
  concl <- relaxHeight =<< extend (constant 1.5) <$> rawLabel "concl" conclusion
  debug $ traceBox "red" concl
  lab <- rawLabel "rulename" ruleLabel

  -- Grouping
  (psGrp,premisesDist) <- chainBases (constant 10) [p | T.Node (_,p,_) _ <- ps]
  debug $ using denselyDotted $ traceBox "blue" psGrp
  height psGrp === case ps of
                     [] -> zero
                     _ -> layerHeight

  -- Separation rule
  separ <- hrule "separation"
  separ # N .=. psGrp # S
  align ypart [concl # N,separ # S]
  minimize $ width separ
  psGrp `fitsHorizontallyIn` separ
  concl `sloppyFitsHorizontallyIn` separ

  -- rule label
  lab # BaseW .=. separ # E + Point (constant 3) (constant (negate 1))


  -- layout hints (not necessary for "correctness")
  let xd = xdiff (separ # W) (psGrp # W)
  xd   === xdiff (psGrp # E) (separ # E)
  relax 2 $ (2 *- xd) =~= premisesDist
  -- centering of conclusion
  (xpart (separ # Center) - xpart (concl # Center)) === zero
  -- minimize (xpart (separ # Center) - xpart (concl # Center)) -- does not produce the expected results with current z3 version

  -- draw the rule.
  using ruleStyle $ path $ polyline [separ # W,separ # E]
  return $ T.Node (separ # W, concl, lab # E) ps

-----------------------


rule :: Monoid lab => lab -> lab -> Rule lab
rule ruleLabel conclusion = Rule {delimiter = mempty, ruleStyle = outline "black", ..}

dummy :: Monoid lab => Rule lab
dummy = (rule mempty mempty) {ruleStyle = const defaultPathOptions}

emptyDrv :: forall k lab. Monoid lab => Tree k (Rule lab)
emptyDrv = Node dummy []

-- abortDrv (Node Rule {..} _) = Node Rule {ruleStyle = Waved, ..} []

-- | Used when the rest of the derivation is known.
haltDrv' :: forall lab. Monoid lab => lab -> Derivation lab -> Derivation lab
haltDrv' tex (Node r _) = Node r {ruleStyle = noOutline}
     [lnk {steps = 1, label = tex} ::> emptyDrv]
  where lnk :: Link lab
        lnk = defaultLink
