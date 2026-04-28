------------------------------------------------------------------------
-- Vectors for which the element types depend on the position, defined
-- using a recursive function
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec.Dependent
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Equality.Decision-procedures eq
import Equivalence.Erased eq as EEq
open import Erased.Level-1 eq
open import Extensionality eq
open import Function-universe eq hiding (_∘_)

open import Vec.Dependent.Basics eq public

private variable
  p : Level
  A : Type _
  P : A → Type _
  n : ℕ

------------------------------------------------------------------------
-- Decidable equality

-- Equality is decidable for Vec n P, given a certain assumption.

decidable-equality :
  ((i : Fin n) → Decidable-equality (P i)) →
  Decidable-equality (Vec n P)
decidable-equality {n = zero} _ _ _ =
  yes (refl _)
decidable-equality {n = suc _} dec =
  Σ.Dec._≟_ (dec fzero) (decidable-equality (dec ∘ fsuc))

-- Erased equality is decidable for Vec n P, given a certain
-- assumption.

decidable-erased-equality :
  ((i : Fin n) → Decidable-erased-equality (P i)) →
  Decidable-erased-equality (Vec n P)
decidable-erased-equality {n = zero} _ _ _ =
  yes [ refl _ ]
decidable-erased-equality {n = suc _} dec =
  decidable-erased⇒decidable-erased⇒×-decidable-erased
    (dec fzero) (decidable-erased-equality (dec ∘ fsuc))

-- Equality is decidable for ((i : Fin n) → P i), given a certain
-- assumption.

decidable-equality-Π-Fin :
  {P : Fin n → Type p} →
  Extensionality lzero p →
  ((i : Fin n) → Decidable-equality (P i)) →
  Decidable-equality ((i : Fin n) → P i)
decidable-equality-Π-Fin ext dec =
  Decidable-equality-cong _ (Vec≃Π {k = equivalence} ext)
    (decidable-equality dec)

-- Erased equality is decidable for ((i : Fin n) → P i), given a
-- certain assumption.

decidable-erased-equality-Π-Fin :
  {P : Fin n → Type p} →
  @0 Extensionality lzero p →
  ((i : Fin n) → Decidable-erased-equality (P i)) →
  Decidable-erased-equality ((i : Fin n) → P i)
decidable-erased-equality-Π-Fin ext dec =
  EEq.Decidable-erased-equality-map-≃ᴱ (Vec≃Π [ ext ])
    (decidable-erased-equality dec)
