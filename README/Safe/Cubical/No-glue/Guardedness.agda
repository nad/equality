------------------------------------------------------------------------
-- Safe modules that use --cubical=no-glue and --guardedness
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical=no-glue --guardedness #-}

module README.Safe.Cubical.No-glue.Guardedness where

-- Conatural numbers defined using --guardedness rather than
-- --sized-types.

import Conat.Guardedness

-- M-types for indexed containers, defined coinductively (in Cubical
-- Agda).

import Container.Indexed.Variant.M.Codata
import Container.Indexed.M.Codata
