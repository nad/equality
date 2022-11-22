------------------------------------------------------------------------
-- Code related to Squash that uses --erased-matches
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --prop --erased-matches #-}

open import Equality

module Squash.Erased-matches
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Erased.Basics as E using (Erased)
open import Prelude

open import Equivalence eq as Eq using (_≃_)
open import Modality.Basics eq
open import Squash eq

private variable
  a ℓ : Level
  A   : Type a

-- The squash modality commutes with Erased.

commutes-with-Erased : Modality.Commutes-with-Erased (modality {ℓ = ℓ})
commutes-with-Erased =
  _≃_.is-equivalence $
  Eq.↔→≃
    (λ x → ◯-Erased→Erased-◯ x)
    Erased-Squash→Squash-Erased
    (λ _ → refl _)
    (λ _ → refl _)
  where
  open Modality modality

  Erased-Squash→Squash′-Erased :
    E.Erased (Squash A) → Squash′ (E.Erased A)
  Erased-Squash→Squash′-Erased E.[ [ x ] ] = squash′ E.[ x ]

  Erased-Squash→Squash-Erased :
    E.Erased (Squash A) → Squash (E.Erased A)
  Erased-Squash→Squash-Erased x =
    squash (Erased-Squash→Squash′-Erased x)
