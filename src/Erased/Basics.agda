------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

-- This module contains some basic definitions with few dependencies
-- (in particular, not Function-universe) that do not rely on
-- equality. See Erased and other modules under Erased for more
-- definitions. The definitions below are reexported from Erased.

{-# OPTIONS --without-K --safe #-}

module Erased.Basics where

open import Prelude

private
  variable
    a : Level

-- Erased A is like A, but the values are (supposed to be) erased at
-- run-time.

record Erased (@0 A : Type a) : Type a where
  constructor [_]
  field
    @0 erased : A

open Erased public

-- A variant of [_] that does not take an erased argument.

[_]→ : {@0 A : Type a} → A → Erased A
[ x ]→ = [ x ]
