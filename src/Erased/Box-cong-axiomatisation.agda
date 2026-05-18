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

-- An axiomatisation of "unlimited erased matches are allowed for
-- identity types" (for certain universe levels).

@0 Unlimited-erased-matches : (a p : Level) → Type (lsuc (a ⊔ p))
Unlimited-erased-matches a p =
  ∃ λ (J : {@0 A : Type a} {@0 x y : A}
           (@0 P : ∀ {y} → x ≡ y → Type p) →
           P (refl x) → (@0 x≡y : x ≡ y) → P x≡y) →
    {@0 A : Type a} {@0 x : A}
    (@0 P : {y : A} → x ≡ y → Type p) {r : P (refl x)} →
    J P r (refl x) ≡ r
