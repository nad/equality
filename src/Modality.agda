------------------------------------------------------------------------
-- Idempotent monadic modalities
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Modality
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import H-level eq
open import H-level.Closure eq
import Modality.Very-modal eq as VM

private
  variable
    a : Level

open import Modality.Basics eq public

-- Very-modal M is propositional (assuming function extensionality).

Very-modal-propositional :
  {M : Modality a} →
  Extensionality (lsuc a) a →
  Is-proposition (Very-modal M)
Very-modal-propositional {M = M} ext =
  [inhabited⇒+]⇒+ {A = Very-modal M} 0 λ very-modal →
  let open VM M very-modal in
  implicit-Π-closure ext 1 λ _ →
  H-level→H-level-◯ 1 $
  Is-modal-propositional ext′
  where
  open Modality M

  ext′ = lower-extensionality _ lzero ext
