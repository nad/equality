------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality.Propositional where

open import Equality
open import Equivalence hiding (_∘_)
open import Prelude

------------------------------------------------------------------------
-- Equality

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

private

  refl′ : {A : Set} (x : A) → x ≡ x
  refl′ x = refl

  elim : {A : Set} (P : {x y : A} → x ≡ y → Set) →
         (∀ x → P (refl′ x)) →
         ∀ {x y} (x≡y : x ≡ y) → P x≡y
  elim P r refl = r _

  elim-refl : ∀ {A : Set} (P : {x y : A} → x ≡ y → Set)
              (r : ∀ x → P (refl′ x)) {x} →
              elim P r (refl′ x) ≡ r x
  elim-refl P r = refl

------------------------------------------------------------------------
-- Various derived definitions and properties

reflexive : Reflexive
reflexive = record
  { _≡_  = _≡_
  ; refl = refl′
  }

equality-with-J : Equality-with-J reflexive
equality-with-J = record
  { elim      = elim
  ; elim-refl = elim-refl
  }

open Derived-definitions-and-properties equality-with-J public
  hiding (_≡_; refl)
