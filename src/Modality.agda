------------------------------------------------------------------------
-- Idempotent monadic modalities
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Modality
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

import Equivalence.Erased.Contractible-preimages eq as ECP
open import Extensionality eq
open import H-level eq
open import H-level.Closure eq
import Modality.Very-modal eq as VM

private
  variable
    a : Level
    A : Type a
    f : A

open import Modality.Basics eq public

-- In erased contexts ◯ -Connectedᴱ A is propositional (assuming
-- function extensionality).

@0 Connectedᴱ-propositional :
  Extensionality a a →
  (◯ : Type a → Type a) →
  Is-proposition (◯ -Connectedᴱ A)
Connectedᴱ-propositional ext _ = ECP.Contractibleᴱ-propositional ext

-- In erased contexts ◯ -Connected-→ᴱ f is propositional (assuming
-- function extensionality).

@0 Connected-→ᴱ-propositional :
  Extensionality a a →
  (◯ : Type a → Type a) →
  Is-proposition (◯ -Connected-→ᴱ f)
Connected-→ᴱ-propositional ext ◯ =
  Π-closure ext 1 λ _ →
  Connectedᴱ-propositional ext ◯

-- Very-modal M is propositional (assuming function extensionality).

Very-modal-propositional :
  Extensionality (lsuc a) a →
  (M : Modality a) →
  Is-proposition (Very-modal M)
Very-modal-propositional ext M =
  [inhabited⇒+]⇒+ {A = Very-modal M} 0 λ very-modal →
  let open VM M very-modal in
  implicit-Π-closure ext 1 λ _ →
  Left-exact-η-cong→H-level→H-level-◯ left-exact-η-cong 1 $
  Modal-propositional ext′
  where
  open Modality M

  ext′ = lower-extensionality _ lzero ext
