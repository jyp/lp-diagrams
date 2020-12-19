{-# LANGUAGE DataKinds, KindSignatures, OverloadedStrings, EmptyDataDecls, MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, GADTs, LambdaCase, RecordWildCards   #-}

module Graphics.Diagrams.Shape where

import Graphics.Diagrams.Path
import Graphics.Diagrams.Point
import Graphics.Diagrams.Core
import Algebra.Classes hiding (normalize)
import Prelude hiding (Num(..),(/))


type Anchorage = Anchor -> Point
data Anchor = Center | N | NW | W | SW | S | SE | E | NE | BaseW | Base | BaseE
  deriving Show

type Shape = Anchorage -> Path

box :: Shape
box anchors = polygon (map anchors [NW,NE,SE,SW])

circle :: Shape
circle anchors = circlePath (anchors Center) (0.5 *- xpart (anchors E - anchors W))

roundedBox :: Expr -> Shape
roundedBox rounding as = roundedRectanglePath rounding (as NW) (as SE)
