------------------------------------------------------------------------
-- Idempotent monadic modalities
------------------------------------------------------------------------

-- Unless otherwise noted this code is based on "Modalities in
-- Homotopy Type Theory" by Rijke, Shulman and Spitters, and/or (some
-- version of) the corresponding Coq code.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Modality
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equivalence eq using (_≃_; Is-equivalence)
open import Equivalence.Path-split eq using (Is-∞-extendable-along-[_])

private
  variable
    a p : Level
    A B : Type a
    P   : A → Type p

-- The Coq code accompanying "Modalities in Homotopy Type Theory" uses
-- a somewhat different definition of reflective subuniverses than the
-- paper:
-- * The definition has been adapted to Coq's notion of universe
--   polymorphism.
-- * The proof showing that the modality predicate is propositional is
--   allowed to make use of function extensionality for arbitrary
--   universe levels.
-- * One extra property is assumed: if A and B are equivalent and A is
--   modal, then B is modal.
-- * The property stating that λ (f : ◯ A → B) → f ∘ η is an
--   equivalence for all types A and modal types B is replaced by a
--   property that is intended to avoid uses of extensionality. This
--   property is stated using Is-∞-extendable-along-[_].
-- (This refers to one version of the code, which seems to have
-- changed since I first looked at it.)
--
-- Here is a definition of Σ-closed reflective subuniverses that is
-- based on the definition of reflective subuniverses in (one version
-- of) the Coq code of Rijke et al. Note that Is-modal-propositional
-- is only given access to function extensionality for a given
-- universe level.

record Σ-closed-reflective-subuniverse a : Type (lsuc a) where
  field
    ◯        : Type a → Type a
    η        : A → ◯ A
    Is-modal : Type a → Type a

    Is-modal-propositional :
      Extensionality a a →
      Is-proposition (Is-modal A)

    Is-modal-◯ : Is-modal (◯ A)

    Is-modal-respects-≃ : A ≃ B → Is-modal A → Is-modal B

    extendable-along-η :
      Is-modal B → Is-∞-extendable-along-[ η ] (λ (_ : ◯ A) → B)

    Σ-closed : Is-modal A → (∀ x → Is-modal (P x)) → Is-modal (Σ A P)

-- The following is a definition of "uniquely eliminating modality"
-- based on that in "Modalities in Homotopy Type Theory".

record Uniquely-eliminating-modality a : Type (lsuc a) where
  field
    ◯                    : Type a → Type a
    η                    : A → ◯ A
    uniquely-eliminating :
      Is-equivalence (λ (f : (x : ◯ A) → ◯ (P x)) → f ∘ η)

-- The following is a definition of "modality" based on that in (one
-- version of) the Coq code accompanying "Modalities in Homotopy Type
-- Theory".
--
-- One difference is that in the Coq code the proof showing that the
-- modality predicate is propositional is allowed to make use of
-- function extensionality for arbitrary universe levels.

record Modality a : Type (lsuc a) where
  field
    ◯        : Type a → Type a
    η        : A → ◯ A
    Is-modal : Type a → Type a

    Is-modal-propositional :
      Extensionality a a →
      Is-proposition (Is-modal A)

    Is-modal-◯ : Is-modal (◯ A)

    Is-modal-respects-≃ : A ≃ B → Is-modal A → Is-modal B

    extendable-along-η :
      {P : ◯ A → Type a} →
      (∀ x → Is-modal (P x)) →
      Is-∞-extendable-along-[ η ] P

-- A definition of what it means for a modality to be left exact,
-- based on Theorem 3.1 (i) in "Modalities in Homotopy Type Theory".

Left-exact : (Type a → Type a) → Type (lsuc a)
Left-exact {a = a} ◯ =
  {A : Type a} {x y : A} →
  Contractible (◯ A) → Contractible (◯ (x ≡ y))

-- Left-exact ◯ is propositional (assuming function extensionality).

Left-exact-propositional :
  {◯ : Type a → Type a} →
  Extensionality (lsuc a) a →
  Is-proposition (Left-exact ◯)
Left-exact-propositional ext =
  implicit-Π-closure ext  1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  implicit-Π-closure ext′ 1 λ _ →
  Π-closure ext′ 1 λ _ →
  H-level-propositional ext′ 0
  where
  ext′ = lower-extensionality _ lzero ext

-- A definition of what it means for a modality to be accessible (for
-- a certain universe level).
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory".

Accessible : (ℓ : Level) → Modality a → Type (lsuc (a ⊔ ℓ))
Accessible {a = a} ℓ M =
  ∃ λ (I : Type ℓ) →
  ∃ λ (P : I → Type ℓ) →
    (A : Type a) →
    Is-modal A ⇔
    ∀ i →
    Is-∞-extendable-along-[ (λ (_ : P i) → lift tt) ]
      (λ (_ : ↑ ℓ ⊤) → A)
  where
  open Modality M

-- A definition of what it means for a modality to be topological (for
-- a certain universe level).
--
-- This definition is based on (one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory".

Topological : (ℓ : Level) → Modality a → Type (lsuc (a ⊔ ℓ))
Topological {a = a} ℓ M =
  ∃ λ ((_ , P , _) : Accessible ℓ M) →
    ∀ i → Is-proposition (P i)
