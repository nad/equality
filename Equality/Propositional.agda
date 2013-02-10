------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality.Propositional where

open import Equality
open import Logical-equivalence hiding (_∘_)
open import Prelude

------------------------------------------------------------------------
-- Equality

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

private

  refl′ : ∀ {a} {A : Set a} (x : A) → x ≡ x
  refl′ x = refl

  elim : ∀ {a p} {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
         (∀ x → P (refl′ x)) →
         ∀ {x y} (x≡y : x ≡ y) → P x≡y
  elim P r refl = r _

  elim-refl : ∀ {a p} {A : Set a} (P : {x y : A} → x ≡ y → Set p)
              (r : ∀ x → P (refl′ x)) {x} →
              elim P r (refl′ x) ≡ r x
  elim-refl P r = refl

------------------------------------------------------------------------
-- Various derived definitions and properties

reflexive : ∀ ℓ → Reflexive ℓ
reflexive _ = record
  { _≡_  = _≡_
  ; refl = refl′
  }

equality-with-J : ∀ {a p} → Equality-with-J a p reflexive
equality-with-J = record
  { elim      = elim
  ; elim-refl = elim-refl
  }

open Derived-definitions-and-properties equality-with-J public
  hiding (_≡_; refl)
