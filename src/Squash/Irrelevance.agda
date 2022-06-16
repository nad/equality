------------------------------------------------------------------------
-- Squashing using irrelevance (with irrelevant projections)
------------------------------------------------------------------------

{-# OPTIONS --without-K --irrelevant-projections #-}

open import Equality

module Squash.Irrelevance
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
import Modality.Empty-modal
open import Prelude

open import Equivalence eq using (_≃_)
open import Equivalence.Path-split eq
  using (Is-∞-extendable-along-[_])
open import Extensionality eq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Modality.Basics eq
import Modality.Very-modal eq as VM
open import Monad eq

private
  variable
    a ℓ : Level
    A B : Type a

------------------------------------------------------------------------
-- The squash type

-- Any two elements of type Squash A are definitionally equal.

record Squash (A : Type a) : Type a where
  constructor [_]
  field
    .squashed : A

private

  -- A unit test.

  test : [ 4 ] ∷ [ 5 ] ∷ [] ≡ [ 3 ] ∷ [ 9 ] ∷ []
  test = refl _

-- Squashed types are propositions.

Squash-propositional : Is-proposition (Squash A)
Squash-propositional = λ _ _ → refl _

------------------------------------------------------------------------
-- Squash is a monad

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : Squash A → (A → Squash B) → Squash B
[ x ] >>=′ f = [ Squash.squashed (f x) ]

instance

  -- Squash is a monad.

  raw-monad : Raw-monad {c = ℓ} Squash
  Raw-monad.return raw-monad x = [ x ]
  Raw-monad._>>=_  raw-monad   = _>>=′_

  monad : Monad {c = ℓ} Squash
  Monad.raw-monad      monad = raw-monad
  Monad.left-identity  monad = λ _ _ → refl _
  Monad.right-identity monad = λ _ → refl _
  Monad.associativity  monad = λ _ _ _ → refl _

------------------------------------------------------------------------
-- Squash is a modality

-- A type A is stable if Squash A implies A.

Stable : Type a → Type a
Stable A = Squash A → A

-- Squash is a modality with λ x → [ x ] as the unit. A type is modal
-- if it is a stable proposition.

modality : Modality ℓ
modality {ℓ = ℓ} = λ where
    .Modality.◯                   → Squash
    .Modality.η x                 → [ x ]
    .Modality.Modal               → Modal
    .Modality.Modal-propositional → prop
    .Modality.Modal-◯             → Modal-Squash
    .Modality.Modal-respects-≃    → resp
    .Modality.extendable-along-η  → extendable
  where
  Modal : Type ℓ → Type ℓ
  Modal A = Stable A × Is-proposition A

  Modal-Squash : Modal (Squash A)
  Modal-Squash = _>>= id , Squash-propositional

  prop :
    {A : Type ℓ} →
    Extensionality ℓ ℓ →
    Is-proposition (Stable A × Is-proposition A)
  prop ext =
    [inhabited⇒+]⇒+ 0 λ (_ , prop) →
    ×-closure 1
      (Π-closure ext 1 λ _ → prop)
      (H-level-propositional ext 1)

  resp : A ≃ B → Modal A → Modal B
  resp {A = A} {B = B} A≃B =
    Stable A × Is-proposition A  →⟨ →-cong-→ (_>>= λ x → [ _≃_.from A≃B x ]) (_≃_.to A≃B)
                                      ×-cong
                                    H-level-cong _ 1 A≃B ⟩□
    Stable B × Is-proposition B  □

  Modal→Separated : {x y : A} → Modal A → Modal (x ≡ y)
  Modal→Separated {A = A} {x = x} {y = y} (s , prop) =
      (Squash (x ≡ y)        →⟨ const prop ⟩
       Is-proposition A      →⟨ +⇒≡ ⟩
       Contractible (x ≡ y)  →⟨ proj₁ ⟩□
       x ≡ y                 □)
    , ⇒≡ 1 prop

  extendable :
    {A : Type ℓ} {P : Squash A → Type ℓ} →
    (∀ x → Modal (P x)) →
    Is-∞-extendable-along-[ (λ x → [ x ]) ] P
  extendable                 _ zero    = _
  extendable {A = A} {P = P} m (suc n) =
      (λ f → (λ x → m x .proj₁ (lemma x f))
           , (λ x →
                m [ x ] .proj₁ (lemma [ x ] f)  ≡⟨ m [ x ] .proj₂ _ _ ⟩∎
                f x                             ∎))
    , (λ _ _ → extendable (Modal→Separated ∘ m) n)
    where
    lemma : (x : Squash A) → ((x : A) → P [ x ]) → Squash (P x)
    lemma [ x ] f = [ f x ]

-- The squash modality is empty-modal.

empty-modal : Empty-modal (modality {ℓ = ℓ})
empty-modal =
    (λ { [ () ] })
  , ⊥-propositional

private
  module EM {ℓ = ℓ} =
    Modality.Empty-modal eq (modality {ℓ = ℓ}) empty-modal

-- The squash modality is not left exact.

not-left-exact : ¬ Left-exact (Squash {a = a})
not-left-exact =
  Empty-modal→Is-proposition-◯→¬-Left-exact
    empty-modal Squash-propositional
  where
  open Modality modality

-- The squash modality is not very modal.

not-very-modal : ¬ Very-modal (modality {ℓ = ℓ})
not-very-modal =
  Very-modal modality  →⟨ VM.left-exact modality ⟩
  Left-exact Squash    →⟨ not-left-exact ⟩□
  ⊥                    □

-- The squash modality is not accessibility-modal.

not-accessibility-modal :
  ¬ Modality.Accessibility-modal (modality {ℓ = ℓ})
not-accessibility-modal =
  Is-proposition-◯→¬-Accessibility-modal Squash-propositional
  where
  open Modality modality
