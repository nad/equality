------------------------------------------------------------------------
-- Safe modules that use --cubical-compatible, --erased-funext,
-- --erased-propext and --erased-quotients
------------------------------------------------------------------------

{-# OPTIONS
      --safe --cubical-compatible --erased-funext --erased-propext
      --erased-quotients #-}

module README.Safe.Cubical-compatible.Quotients where

-- Agda's primitive set quotients with erased higher constructors,
-- along with function and propositional extensionality.

import Quotient.Erased.Primitive

-- Finite sets, implemented using red-black trees.

import Tree.Red-black.Set
