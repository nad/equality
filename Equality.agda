------------------------------------------------------------------------
-- Propositional equality, defined with an abstract (non-computing)
-- eliminator
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality where

open import Equality.Axiomatisations
open import Equivalence hiding (_∘_)
open import Prelude

------------------------------------------------------------------------
-- Concrete definition of equality

-- This definition is kept abstract because I might later want to
-- replace it with a definition where elim P r (refl x) does not
-- compute to r x.

abstract

  infix 4 _≡_

  data _≡_ {A : Set} : A → A → Set where
    refl′ : ∀ x → x ≡ x

  refl : {A : Set} (x : A) → x ≡ x
  refl = refl′

  elim : {A : Set} (P : {x y : A} → x ≡ y → Set) →
         (∀ x → P (refl x)) →
         ∀ {x y} (x≡y : x ≡ y) → P x≡y
  elim P r (refl′ x) = r x

  elim-refl : ∀ {A : Set} (P : {x y : A} → x ≡ y → Set)
              (r : ∀ x → P (refl x)) {x} →
              elim P r (refl x) ≡ r x
  elim-refl P r = refl _

------------------------------------------------------------------------
-- Various derived definitions and properties

private

  reflexive : Reflexive
  reflexive = record
    { _≡_  = _≡_
    ; refl = refl
    }

  equality-with-J : Equality-with-J reflexive
  equality-with-J = record
    { elim      = elim
    ; elim-refl = elim-refl
    }

open Derived-definitions-and-properties equality-with-J public
  hiding (_≡_; refl; elim; elim-refl)
