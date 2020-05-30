------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

-- This module contains some basic definitions with few dependencies
-- (in particular, not Function-universe). See Erased and other
-- modules under Erased for more definitions. The definitions below
-- are reexported from Erased.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Erased.Basics
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Equivalence eq using (Is-equivalence)

private
  variable
    a : Level

-- Erased A is like A, but the values are (supposed to be) erased at
-- run-time.

record Erased (@0 A : Set a) : Set a where
  constructor [_]
  field
    @0 erased : A

open Erased public

-- A variant of [_] that does not take an erased argument.

[_]→ : {@0 A : Set a} → A → Erased A
[ x ]→ = [ x ]

-- An axiomatisation for []-cong.

record []-cong-axiomatisation a : Set (lsuc a) where
  field
    []-cong :
      {@0 A : Set a} {@0 x y : A} →
      Erased (x ≡ y) → [ x ] ≡ [ y ]
    []-cong-equivalence :
       {@0 A : Set a} {@0 x y : A} →
       Is-equivalence ([]-cong {x = x} {y = y})
    []-cong-[refl] :
      {A : Set a} {x : A} →
      []-cong [ refl x ] ≡ refl [ x ]
