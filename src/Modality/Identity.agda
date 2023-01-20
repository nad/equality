------------------------------------------------------------------------
-- The identity modality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Modality.Identity
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Equivalence.Path-split eq
open import H-level eq as H-level
open import H-level.Closure eq
open import Modality.Basics eq

private
  variable
    ℓ ℓ′ : Level

------------------------------------------------------------------------
-- The identity modality

-- The identity modality.
--
-- This modality is taken from "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

Identity-modality : Modality ℓ
Identity-modality {ℓ} = λ where
    .◯       → id
    .η       → id
    .Modal _ → ↑ ℓ ⊤

    .Modal-propositional _ →
      H-level.mono₁ 0 (↑-closure 0 ⊤-contractible)

    .Modal-◯ → _

    .Modal-respects-≃ → _

    .extendable-along-η _ → ∞-extendable-along-id
  where
  open Modality

-- The identity modality is empty-modal.

empty-modal : Empty-modal (Identity-modality {ℓ = ℓ})
empty-modal = _

-- The identity modality is very modal.

very-modal : Very-modal (Identity-modality {ℓ = ℓ})
very-modal = _

-- The identity modality is topological.

topological : Topological (Identity-modality {ℓ = ℓ})
topological {ℓ} =
    ( ↑ ℓ ⊤
    , (λ _ → ↑ ℓ ⊤)
    , (λ _ → record { to = λ _ _ → ∞-extendable-along-id })
    )
  , (λ _ → H-level.mono₁ 0 (↑-closure 0 ⊤-contractible))

-- The identity modality is left exact.

left-exact : Left-exact (λ (A : Type ℓ) → A)
left-exact {A} {x} {y} =
  Contractible A        →⟨ H-level.⇒≡ 0 ⟩□
  Contractible (x ≡ y)  □

-- The identity modality is cotopological.

cotopological : Cotopological (λ (A : Type ℓ) → A)
cotopological = left-exact , (λ _ c → c)

-- The identity modality is accessibility-modal.

accessibility-modal :
  Modality.Accessibility-modal (Identity-modality {ℓ = ℓ})
accessibility-modal {ℓ} =
    (λ acc → Modal→Acc→Acc-[]◯-η _ id acc)
  , id
  where
  open Modality (Identity-modality {ℓ = ℓ})

-- The identity modality is W-modal.

w-modal : W-modal (Identity-modality {ℓ = ℓ})
w-modal _ = _
