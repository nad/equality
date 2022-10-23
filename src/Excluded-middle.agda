------------------------------------------------------------------------
-- Excluded middle
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Excluded-middle
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Extensionality eq
open import H-level.Closure eq

-- Excluded middle (roughly as stated in the HoTT book).

Excluded-middle : (ℓ : Level) → Type (lsuc ℓ)
Excluded-middle p = {P : Type p} → Is-proposition P → Dec P

-- Excluded middle is pointwise propositional (assuming
-- extensionality).

Excluded-middle-propositional :
  ∀ {ℓ} →
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition (Excluded-middle ℓ)
Excluded-middle-propositional ext =
  implicit-Π-closure ext 1 λ _ →
  Π-closure (lower-extensionality _ lzero ext) 1 λ P-prop →
  Dec-closure-propositional (lower-extensionality _ _ ext) P-prop
