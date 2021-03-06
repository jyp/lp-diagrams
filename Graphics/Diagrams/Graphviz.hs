{-# LANGUAGE RecordWildCards, ScopedTypeVariables #-}
module Graphics.Diagrams.Graphviz (graph) where

import Graphics.Diagrams.Point as D
import Graphics.Diagrams.Object as D
import Graphics.Diagrams.Core as D
import Graphics.Diagrams.Shape as D
import Graphics.Diagrams.Path
import Data.GraphViz as G
import Data.GraphViz.Attributes.Complete as G
import Data.GraphViz.Parsing as G
import qualified Data.GraphViz.Types.Generalised as Gen
import Data.GraphViz.Commands.IO as G
import qualified Data.Text.Lazy as T
import System.IO.Unsafe (unsafePerformIO)
import Data.Foldable
import Control.Lens (set)
import Graphics.Typography.Geometry.Bezier (Curve)

graph :: (Monad m,PrintDotRepr g n, ParseDot n, PrintDot n) => (String -> lab) -> GraphvizCommand -> g n -> Diagram lab m ()
graph labFct cmd gr = graphToDiagram labFct $ layout cmd gr

layout :: (PrintDotRepr g n, ParseDot n, PrintDot n) => GraphvizCommand -> g n -> Gen.DotGraph n
layout command input = parseIt' $ unsafePerformIO $ graphvizWithHandle command input DotOutput hGetStrict

pos :: Attribute -> Maybe Pos
pos (Pos p) = Just p
pos _= Nothing

lpos :: Attribute -> Maybe G.Point
lpos (LPos p) = Just p
lpos _= Nothing

shapeA :: Attribute -> Maybe G.Shape
shapeA (Shape s) = Just s
shapeA _ = Nothing

widthA :: Attribute -> Maybe Double
widthA (Width s) = Just s
widthA _ = Nothing

labelA :: Attribute -> Maybe Label
labelA (Label l) = Just l
labelA _ = Nothing

arrowHeadA :: Attribute -> Maybe ArrowType
arrowHeadA (ArrowHead a) = Just a
arrowHeadA _ = Nothing

readAttr :: Monad m => (Attribute -> Maybe a) -> [Attribute] -> (a -> m ()) -> m ()
readAttr f as k = readAttr' f as k (return ())

readAttr' :: (Attribute -> Maybe a) -> [Attribute] -> (a -> k) -> k -> k
readAttr' f as k1 k2 = case [x | Just x <- map f as] of
  (x:_) -> k1 x
  _ -> k2


pt' :: G.Point -> Point' Double
pt' (G.Point x y _z _forced) = D.Point x y

pt :: G.Point -> Point' Expr
pt = fmap constant . pt'

diaSpline :: [FrozenPoint] -> [Graphics.Typography.Geometry.Bezier.Curve]
diaSpline (w:x:y:z:rest) = curveSegment w x y z:diaSpline (z:rest)
diaSpline _ = []

-- ToTip | CircleTip | NoTip | StealthTip | LatexTip | ReversedTip LineTip | BracketTip | ParensTip
tipTop :: LineTip -> ArrowType -> LineTip
tipTop _def (AType [(_,NoArrow)]) = NoTip
tipTop _def (AType [(_,Normal)]) = LatexTip
tipTop _def (AType [(_,DotArrow)]) = CircleTip
tipTop _def (AType [(_,Vee)]) = StealthTip
tipTop def _ = def

graphToDiagram :: forall l m n. Monad m => (String -> l) -> Gen.DotGraph n -> Diagram l m ()
graphToDiagram labFct (Gen.DotGraph _strict _directed _grIdent stmts) = do
  forM_ stmts $ \ stmt -> case stmt of
    (Gen.DE (DotEdge _from _to attrs)) -> do
      -- diaRaw $ tex $ "%Edge: " ++ show attrs ++ "\n"
      let toTip = readAttr' arrowHeadA attrs (tipTop ToTip) ToTip
      readAttr labelA attrs $ \(StrLabel l) ->
        readAttr lpos attrs $ \p ->
        renderLab l p
      readAttr pos attrs $ \(SplinePos splines) ->
        forM_ splines $ \Spline{..} -> do
          let mid = diaSpline $ map pt' splinePoints
          let beg = case (startPoint,splinePoints) of
                (Just p,q:_) -> [lineSegment (pt' p) (pt' q)]
                _ -> []
          let end = case (endPoint,reverse splinePoints) of
                (Just p,q:_) -> [lineSegment (pt' q) (pt' p)]
                _ -> []
          using (set endTip toTip) $
            draw $ frozenPath' $ fromBeziers (beg ++ mid ++ end)

    (Gen.DN (DotNode _nodeIdent attrs)) -> do
      -- diaRaw $ tex $ "%Node: " ++ show attrs ++ "\n"
      readAttr pos   attrs $ \(PointPos p) -> do
        readAttr labelA attrs $ \l -> do
          case l of
            StrLabel l -> renderLab l p
        readAttr widthA attrs $ \w ->
         readAttr shapeA attrs $ \s ->
          case s of
            Circle -> do
              draw $ path $ circlePath (pt p) (constant $ inch (w/2))
            _ -> return ()
    _ -> return ()
  where
  renderLab :: T.Text -> G.Point -> Diagram l m ()
  renderLab l p = do
    l' <- rawLabel "graphVizLab" $ labFct $ T.unpack $ l
    l' # D.Center .=. pt p


inch :: Num a => a -> a
inch x = 72 * x
