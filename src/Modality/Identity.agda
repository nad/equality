------------------------------------------------------------------------
-- The identity modality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Modality.Identity
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Equivalence.Path-split eq
open import H-level eq as H-level
open import H-level.Closure eq
open import Modality.Basics eq
import Modality.Very-modal

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
Identity-modality {ℓ = ℓ} = λ where
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

private
  module VM {ℓ = ℓ} =
    Modality.Very-modal
      eq
      (Identity-modality {ℓ = ℓ})
      (λ {A} → very-modal {A = A})

-- The identity modality is topological (for every universe level).

topological : Topological ℓ′ (Identity-modality {ℓ = ℓ})
topological {ℓ′ = ℓ′} =
    ( ↑ ℓ′ ⊤
    , (λ _ → ↑ ℓ′ ⊤)
    , (λ _ → record { to = λ _ _ → ∞-extendable-along-id })
    )
  , (λ _ → H-level.mono₁ 0 (↑-closure 0 ⊤-contractible))

-- The identity modality is left exact.

left-exact : Left-exact (λ (A : Type ℓ) → A)
left-exact = VM.left-exact

-- The identity modality is left exact.

left-exact-η-cong :
  Modality.Left-exact-η-cong (Identity-modality {ℓ = ℓ})
left-exact-η-cong = VM.left-exact-η-cong

-- The identity modality is accessibility-modal.

accessibility-modal :
  Modality.Accessibility-modal (Identity-modality {ℓ = ℓ})
accessibility-modal {ℓ = ℓ} =
    (λ acc → Modal→Acc→Acc-[]◯-η _ id acc)
  , id
  where
  open Modality (Identity-modality {ℓ = ℓ})
