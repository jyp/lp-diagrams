{-# LANGUAGE DisambiguateRecordFields, NamedFieldPuns, RecordWildCards, PostfixOperators, LiberalTypeSynonyms, TypeOperators, OverloadedStrings, PackageImports, ScopedTypeVariables #-}

module Graphics.Diagrams.DerivationTrees (
-- * Basics
module Data.Monoid,
module Data.LabeledTree,

-- * Derivation' building
-- axiom, rule, etc, aborted,
emptyDrv, haltDrv',
dummy, rule, Derivation, Premise, Rule(..),

-- * Links
LineStyle,defaultLink,Link(..),

-- * Engine
derivationTreeDiag, delayD

) where

-- import DerivationTrees.Basics
import Data.LabeledTree
import Data.Monoid
import Control.Monad (forM, forM_)
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

data Rule lab = Rule {ruleStyle :: LineStyle, leftLabel, rightLabel :: Maybe lab,  conclusion :: lab}

type Premise lab = Link lab ::> Derivation lab
type Derivation lab = Tree (Link lab) (Rule lab)

--------------------------------------------------
-- Delay

depth :: forall lab t. Link lab ::> Tree (Link lab) t -> Int
depth (Link{steps} ::> Node _ ps) = 1 + steps + maximum (0 : map depth ps)

isDelayed :: Premise lab -> Bool
isDelayed (Delayed{} ::> _) = True
isDelayed _ = False

-- delayPre :: forall lab a. Int -> Link lab ::> a -> Link lab ::> a
-- delayPre s (Link {..} ::> j) = Link {steps = s, ..} ::> j

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
  tree@(T.Node (_,n,_) _) <- toDiagram d
  forM_ (T.levels tree) $ \level ->
    case level of
      [] -> return ()
      (_:level') ->do
        D.align ypart $ map (# Base) [concl | (_,concl,_) <- level ] -- make sure that baselines agree across each level throughout (otherwise, ugly)
        forM_ (zip level level') $ \((_,_,l),(r,_,_)) ->
          (l + Point (constant 8) zero) `westOf` r
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

treeConcl :: T.Tree (Point,Object,Point) -> Object
treeConcl (T.Node (_,concl,_) _) = concl

toDiagPart :: forall m lab. Monad m => Premise lab -> Diagram lab m (T.Tree (Point,Object,Point))
toDiagPart (Delayed ::> _) = error "first use delayD to get rid of Delay links"
toDiagPart (Link{..} ::> rul)
  | steps == 0 = toDiagram rul
  | otherwise = do
    linkObj <- vrule "linkObj"
    linkLab <- extend (constant 1.5) <$> rawLabel "link_label" label
    linkLab # W .=. linkObj # Center
    extend (constant 2) linkLab `sloppyFitsVerticallyIn` linkObj
    let pt = linkObj # S
    let embedPt :: Int -> Diagram lab m (T.Tree (Point,Object,Point))
        embedPt 1 = do
          above <- toDiagram rul
          let concl = treeConcl above
          linkObj `sloppyFitsHorizontallyIn` concl
          alignApproximately xpart ((# Center) <$> [linkObj, concl])
          align ypart [linkObj # N, concl # S]
          using linkStyle $ path $ polyline [linkObj # S,linkObj # N]
          return  (T.Node (concl # W,linkObj,concl # E) [above])
        embedPt n = do
          subObj <- point "subObj"
          subObj `sloppyFitsIn`linkObj
          nextAbove <- embedPt (n-1)
          (subObj # N) `southOf` (treeConcl nextAbove # S)
          return $ T.Node (pt,subObj,linkLab # E) [nextAbove]
    embedPt steps

-- | @chainBases distance objects@
-- - Ensures that all the objects have the same baseline.
-- - Separates the objects by the given distance
-- - Returns an object encompassing the group, with a the baseline set correctly.
-- - Returns the average distance between the objects

chainBases :: Monad m => Expr -> [Object] -> Diagram lab m (Object,Expr)
chainBases _ [] = do
  o <- obj box "empty"
  return (o,zero)
chainBases spacing ls = do
  grp <- obj box "grp"
  D.align ypart $ map (# Base) (grp:ls)
  forM_ ls $ \l -> do l `fitsVerticallyIn` grp

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

toDiagram :: Monad m => Derivation lab -> Diagram lab m (T.Tree (Point,Object,Point))
toDiagram (Node Rule{..} premises) = do
  ps <- mapM toDiagPart premises
  concl <- extend (constant 1.5) <$> rawLabel "concl" conclusion
  debug $ traceBox "red" concl

  -- Grouping
  (premisesGroup,premisesDist) <- chainBases (constant 10) [p | T.Node (_,p,_) _ <- ps]
  debug $ using denselyDotted $ traceBox "blue" premisesGroup

  -- Separation rule
  separ <- hrule "separation"
  align ypart [separ # N, premisesGroup # S]
  relax 10 $ alignApproximately xpart [separ # N, premisesGroup # S]
  align ypart [concl # N,separ # S]
  minimize $ width separ
  premisesGroup `fitsHorizontallyIn` separ
  concl `sloppyFitsHorizontallyIn` separ

  -- rule labels
  rightLab <-  forM rightLabel $ \l -> do
    l' <- rawLabel "rule_right" l
    l' # BaseW .=. separ # E + Point (constant 3) (constant (- 2))
    return l'
  leftLab <- forM leftLabel $ \l -> do
    l' <- rawLabel "rule_left" l
    l' # BaseE .=. separ # W + Point (constant (-3)) (constant (- 2))
    return l'


  -- layout hints (not necessary for "correctness")
  -- let xd = xdiff (separ # W) (premisesGroup # W)
  -- xd   === xdiff (premisesGroup # E) (separ # E)
  -- relax 2 $ (2 *- xd) =~= premisesDist
  -- try to center the conclusion:
  relax 10 $ alignApproximately xpart ((# Center) <$> [separ,concl])

  -- draw the rule line.
  using ruleStyle $ path $ polyline [separ # W,separ # E]
  return $ T.Node ((maybe separ id leftLab) # W, concl, (maybe separ id rightLab) # E) ps

-----------------------


rule :: Monoid lab => lab -> Rule lab
rule conclusion = Rule {ruleStyle = outline "black" ,
                        leftLabel = Nothing,
                        rightLabel = Nothing,
                        conclusion = conclusion}

dummy :: Monoid lab => Rule lab
dummy = (rule mempty) {ruleStyle = const defaultPathOptions}

emptyDrv :: forall k lab. Monoid lab => Tree k (Rule lab)
emptyDrv = Node dummy []

-- abortDrv (Node Rule {..} _) = Node Rule {ruleStyle = Waved, ..} []

-- | Used when the rest of the derivation is known.
haltDrv' :: forall lab. Monoid lab => lab -> Derivation lab -> Derivation lab
haltDrv' tex (Node r _) = Node r {ruleStyle = noOutline}
     [lnk {steps = 1, label = tex} ::> emptyDrv]
  where lnk :: Link lab
        lnk = defaultLink
