------------------------------------------------------------------------
-- Finite sets, implemented using red-black trees
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
import Extensionality
open import Prelude
import Quotient.Erased.Axiomatised
import Total-order.Erased
import Univalence-axiom

module Tree.Red-black.Set
  {e⁺}
  (eq : ∀ {a p} → Equality-with-J a p e⁺)
  (open Extensionality eq)
  (open Quotient.Erased.Axiomatised eq)
  (open Total-order.Erased eq)
  (open Univalence-axiom eq)
  -- The code is parametrised by an implementation of quotients.
  (quot : Quotientᴱ)
  {a o}
  -- It is assumed that function and propositional extensionality hold.
  (@0 ext      : Extensionality (lsuc (a ⊔ o)) (lsuc (a ⊔ o)))
  (@0 prop-ext : Propositional-extensionality (a ⊔ o))
  -- The carrier type.
  {A : Type a}
  -- The carrier type is assumed to be totally ordered.
  (O : Total-order A o)
  where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)

open import Equivalence eq using (_≃_)
open import Equivalence.Erased eq using (_≃ᴱ_)
open import Erased.Level-1 eq as Erased
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq hiding (Set)
open import H-level.Closure eq
open import H-level.Truncation.Propositional.Erased.Axiomatised eq
open import Tree.Red-black eq as T hiding (_∈_; member?; empty; insert)

private
  module @0 BC {a} =
    Erased.[]-cong₁ (erased-instance-of-[]-cong-axiomatisation {a = a})
  open module Q  = Quotientᴱ quot renaming ([_] to [_]Q)
  open module Tr = Truncationᴱ Q.truncation

private variable
  x y : A

------------------------------------------------------------------------
-- Sets

opaque

  -- Finite sets.
  --
  -- The implementation uses red-black trees quotiented by set
  -- equivalence.

  Set : Type (a ⊔ o)
  Set = Tree⁻ O /ᴱ (λ t₁ t₂ → ∀ z → z ∈⁻ t₁ ⇔ z ∈⁻ t₂)

private variable
  xs : Set

------------------------------------------------------------------------
-- Set membership

private opaque
  unfolding Set

  -- Set membership.

  Membership :
    A → Set → ∃ λ (B : Type (a ⊔ o)) → Erased (Is-proposition B)
  Membership x = Q.rec λ where
    .is-setʳ →
      Is-set-∃-Erased-Is-proposition ext prop-ext
    .[]ʳ t →
      ∥ x ∈⁻ t ∥ᴱ , [ truncation-is-proposition ]
    .[]-respects-relationʳ {x = xs} {y = ys} →
      (∀ z → z ∈⁻ xs ⇔ z ∈⁻ ys)                         →⟨ _$ x ⟩

      x ∈⁻ xs ⇔ x ∈⁻ ys                                 →⟨ ∥∥ᴱ-cong ⟩

      ∥ x ∈⁻ xs ∥ᴱ ⇔ ∥ x ∈⁻ ys ∥ᴱ                       →⟨ prop-ext truncation-is-proposition truncation-is-proposition ⟩

      ∥ x ∈⁻ xs ∥ᴱ ≡ ∥ x ∈⁻ ys ∥ᴱ                       ↔⟨ ignore-propositional-component
                                                             (BC.H-level-Erased 1
                                                                (H-level-propositional
                                                                   (lower-extensionality _ _ ext) 1)) ⟩
      (∥ x ∈⁻ xs ∥ᴱ , [ truncation-is-proposition ]) ≡
      (∥ x ∈⁻ ys ∥ᴱ , [ truncation-is-proposition ])    □

opaque
  unfolding Membership

  infix 4 _∈_

  -- Set membership.

  _∈_ : A → Set → Type (a ⊔ o)
  x ∈ xs = Membership x xs .proj₁

opaque
  unfolding _∈_

  -- Set membership is propositional.

  @0 ∈-propositional : Is-proposition (x ∈ xs)
  ∈-propositional = Membership _ _ .proj₂ .erased

------------------------------------------------------------------------
-- A membership test

opaque
  unfolding Set _∈_

  -- Does the element exist in the set?

  member? : (x : A) (xs : Set) → Dec-Erased (x ∈ xs)
  member? x = Q.elim-prop λ where
    .is-propositionʳ _ →
      BC.Is-proposition-Dec-Erased (lower-extensionality _ _ ext)
        ∈-propositional
    .[]ʳ t →
      Dec-Erased-map-∥∥ᴱ
        (∥ x ∈⁻ t ∥ᴱ  ↝⟨ ≡⇒↝ _ (cong proj₁ (sym Q.rec-[])) ⟩
         x ∈ [ t ]Q   □)
        (member?⁻ x t)

------------------------------------------------------------------------
-- The empty set

opaque
  unfolding Set

  -- The empty set.

  ∅ : Set
  ∅ = [ empty⁻ ]Q

opaque
  unfolding ∅ _∈_

  -- The empty set is empty.

  @0 ∉∅ : ¬ x ∈ ∅
  ∉∅ {x} =
    x ∈ [ empty⁻ ]Q   →⟨ ≡⇒↝ _ (cong proj₁ Q.rec-[]) ⟩
    ∥ x ∈⁻ empty⁻ ∥ᴱ  →⟨ (Tr.rec λ where
                            .truncation-is-propositionʳ →
                              ⊥-propositional
                            .∣∣ʳ →
                              ∉empty⁻) ⟩□
    ⊥                 □

------------------------------------------------------------------------
-- Insertion

opaque
  unfolding Set

  -- Inserts an element into the set.

  insert : A → Set → Set
  insert x =
    insert⁻ x Q./ᴱ-map λ xs ys →
      (∀ z → z ∈⁻ xs ⇔ z ∈⁻ ys)                      →⟨ (λ hyp z →

        z ∈⁻ insert⁻ x xs                                    ↝⟨ ∈⁻-insert⁻ ⟩
        z ≡ x ⊎ z ∈⁻ xs                                      ↝⟨ F.id ⊎-cong hyp z ⟩
        z ≡ x ⊎ z ∈⁻ ys                                      ↝⟨ inverse ∈⁻-insert⁻ ⟩□
        z ∈⁻ insert⁻ x ys                                    □) ⟩□

      (∀ z → z ∈⁻ insert⁻ x xs ⇔ z ∈⁻ insert⁻ x ys)  □

opaque
  unfolding Set _∈_ insert _/ᴱ-map_

  -- The value y is in insert x xs if and only if merely y is x or y
  -- is in xs.

  @0 ∈insert⇔ : y ∈ insert x xs ⇔ y ≡ x ∥⊎∥ᴱ y ∈ xs
  ∈insert⇔ {y} {x} {xs} =
    Q.elim-prop {P = λ xs → y ∈ insert x xs ⇔ y ≡ x ∥⊎∥ᴱ y ∈ xs}
      (λ where
         .is-propositionʳ _ →
           ⇔-closure (lower-extensionality _ _ ext) 1 ∈-propositional
             truncation-is-proposition
         .[]ʳ t →
           y ∈ insert x [ t ]Q     ↝⟨ ≡⇒↝ _ (cong (_∈_ _) Q.rec-[]) ⟩
           y ∈ [ insert⁻ x t ]Q    ↝⟨ ≡⇒↝ _ (cong proj₁ Q.rec-[]) ⟩
           ∥ y ∈⁻ insert⁻ x t ∥ᴱ   ↝⟨ _≃ᴱ_.logical-equivalence (∥∥ᴱ-cong-⇔ ∈⁻-insert⁻) ⟩
           y ≡ x ∥⊎∥ᴱ y ∈⁻ t       ↝⟨ _≃_.logical-equivalence truncate-right-∥⊎∥ᴱ ⟩
           y ≡ x ∥⊎∥ᴱ ∥ y ∈⁻ t ∥ᴱ  ↝⟨ ≡⇒↝ _ (cong (∥_∥ᴱ ∘ _⊎_ _ ∘ proj₁) (sym Q.rec-[])) ⟩□
           y ≡ x ∥⊎∥ᴱ y ∈ [ t ]Q   □)
      xs
