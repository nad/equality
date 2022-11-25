------------------------------------------------------------------------
-- An axiomatisation for []-cong
------------------------------------------------------------------------

-- The definitions below are reexported from Erased.Level-1.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Erased.Box-cong-axiomatisation
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Erased.Basics
open import Prelude

open import Equivalence eq using (Is-equivalence)

-- An axiomatisation for []-cong.

record []-cong-axiomatisation a : Type (lsuc a) where
  field
    []-cong :
      {@0 A : Type a} {@0 x y : A} →
      Erased (x ≡ y) → [ x ] ≡ [ y ]
    []-cong-[refl] :
      {@0 A : Type a} {@0 x : A} →
      []-cong [ refl x ] ≡ refl [ x ]
