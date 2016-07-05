------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Equality.Propositional where

open import Equality
open import Logical-equivalence hiding (_∘_)
open import Prelude

------------------------------------------------------------------------
-- Equality

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

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

reflexive-relation : ∀ ℓ → Reflexive-relation ℓ
Reflexive-relation._≡_  (reflexive-relation _) = _≡_
Reflexive-relation.refl (reflexive-relation _) = refl′

equality-with-J : ∀ {a p} → Equality-with-J a p reflexive-relation
Equality-with-J.elim      equality-with-J = elim
Equality-with-J.elim-refl equality-with-J = elim-refl

open Derived-definitions-and-properties equality-with-J public
  hiding (_≡_; refl)
