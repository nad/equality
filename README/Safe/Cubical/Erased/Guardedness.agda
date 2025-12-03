------------------------------------------------------------------------
-- Safe modules that use --erased-cubical and --guardedness
------------------------------------------------------------------------

{-# OPTIONS --safe --erased-cubical --guardedness #-}

module README.Safe.Cubical.Erased.Guardedness where

-- Conatural numbers defined using --guardedness rather than
-- --sized-types.

import Conat.Guardedness

-- M-types for indexed containers, defined coinductively (in Cubical
-- Agda).

import Container.Indexed.Variant.M.Codata
import Container.Indexed.M.Codata
