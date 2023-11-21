------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

-- This module contains some basic definitions with few dependencies
-- (in particular, not Function-universe) that do not rely on
-- equality. See Erased and other modules under Erased for more
-- definitions. The definitions below are reexported from
-- Erased.Level-1.

{-# OPTIONS --cubical-compatible --safe #-}

module Erased.Basics where

open import Prelude

private
  variable
    a p q : Level

-- Erased A is like A, but the values are (supposed to be) erased at
-- run-time.

record Erased (@0 A : Type a) : Type a where
  no-eta-equality
  pattern
  constructor [_]
  field
    @0 erased : A

open Erased public

-- A variant of [_] that does not take an erased argument.

[_]→ : {@0 A : Type a} → A → Erased A
[ x ]→ = [ x ]

-- A variant of [_]→.

[_∣_]→ : (@0 A : Type a) → A → Erased A
[_∣_]→ _ = [_]→

-- A type A is stable if Erased A implies A.

Stable : Type a → Type a
Stable A = Erased A → A

-- Erased preserves dependent functions.

map :
  {@0 A : Type a} {@0 P : A → Type p} →
  @0 ((x : A) → P x) → (x : Erased A) → Erased (P (erased x))
map f x = [ f (erased x) ]

-- A binary variant of map.

zip :
  {@0 A : Type a} {@0 P : A → Type p} {@0 Q : {x : A} → P x → Type q} →
  @0 ((x : A) (p : P x) → Q p) →
  (([ x ]) : Erased A) (([ p ]) : Erased (P x)) → Erased (Q p)
zip f x p = [ f (erased x) (erased p) ]
