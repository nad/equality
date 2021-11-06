------------------------------------------------------------------------
-- Safe modules that use --erased-cubical and --guardedness
------------------------------------------------------------------------

{-# OPTIONS --safe --erased-cubical --guardedness #-}

module README.Safe.Cubical.Erased.Guardedness where

-- M-types for indexed containers, defined coinductively (in Cubical
-- Agda).

import Container.Indexed.Variant.M.Codata
import Container.Indexed.M.Codata
