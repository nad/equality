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
  (@0 ext      : Extensionality (lsuc a) (lsuc a))
  (@0 prop-ext : Propositional-extensionality a)
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
import Tree.Red-black eq O as T

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
  Set = T.Tree /ᴱ (λ t₁ t₂ → ∀ z → z T.∈ t₁ ⇔ z T.∈ t₂)

private variable
  xs : Set

------------------------------------------------------------------------
-- Set membership

private opaque
  unfolding Set

  -- Set membership.

  Membership :
    A → Set → ∃ λ (B : Type a) → Erased (Is-proposition B)
  Membership x = Q.rec λ where
    .is-setʳ →
      Is-set-∃-Erased-Is-proposition ext prop-ext
    .[]ʳ t →
      (x T.∈ t) , [ T.∈-propositional ]
    .[]-respects-relationʳ {x = xs} {y = ys} →
      (∀ z → z T.∈ xs ⇔ z T.∈ ys)             →⟨ _$ x ⟩

      x T.∈ xs ⇔ x T.∈ ys                     →⟨ prop-ext T.∈-propositional T.∈-propositional ⟩

      (x T.∈ xs) ≡ (x T.∈ ys)                 ↔⟨ ignore-propositional-component
                                                   (BC.H-level-Erased 1
                                                      (H-level-propositional
                                                         (lower-extensionality _ _ ext) 1)) ⟩□
      ((x T.∈ xs) , [ T.∈-propositional ]) ≡
      ((x T.∈ ys) , [ T.∈-propositional ])    □

opaque
  unfolding Membership

  infix 4 _∈_

  -- Set membership.

  _∈_ : A → Set → Type a
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
      Dec-Erased-map
        (x T.∈ t     ↝⟨ ≡⇒↝ _ (cong proj₁ (sym Q.rec-[])) ⟩
         x ∈ [ t ]Q  □)
        (T.member? x t)

------------------------------------------------------------------------
-- The empty set

opaque
  unfolding Set

  -- The empty set.

  ∅ : Set
  ∅ = [ T.empty ]Q

opaque
  unfolding ∅ _∈_

  -- The empty set is empty.

  @0 ∉∅ : ¬ x ∈ ∅
  ∉∅ {x} =
    x ∈ [ T.empty ]Q  →⟨ ≡⇒↝ _ (cong proj₁ Q.rec-[]) ⟩
    x T.∈ T.empty     →⟨ T.∉empty ⟩□
    ⊥                 □

------------------------------------------------------------------------
-- Insertion

opaque
  unfolding Set

  -- Inserts an element into the set.

  insert : A → Set → Set
  insert x =
    T.insert x Q./ᴱ-map λ xs ys →
      (∀ z → z T.∈ xs ⇔ z T.∈ ys)                        →⟨ (λ hyp z →

        z T.∈ T.insert x xs                                    ↝⟨ T.∈-insert ⟩
        z ≡ x ⊎ z T.∈ xs                                       ↝⟨ F.id ⊎-cong hyp z ⟩
        z ≡ x ⊎ z T.∈ ys                                       ↝⟨ inverse T.∈-insert ⟩□
        z T.∈ T.insert x ys                                    □) ⟩□

      (∀ z → z T.∈ T.insert x xs ⇔ z T.∈ T.insert x ys)  □

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
           y ∈ insert x [ t ]Q      ↝⟨ ≡⇒↝ _ (cong (_∈_ _) Q.rec-[]) ⟩
           y ∈ [ T.insert x t ]Q    ↝⟨ ≡⇒↝ _ (cong proj₁ Q.rec-[]) ⟩
           y T.∈ T.insert x t       ↔⟨ inverse (∥∥ᴱ≃ T.∈-propositional) ⟩
           ∥ y T.∈ T.insert x t ∥ᴱ  ↝⟨ _≃ᴱ_.logical-equivalence (∥∥ᴱ-cong-⇔ T.∈-insert) ⟩
           y ≡ x ∥⊎∥ᴱ y T.∈ t       ↝⟨ ≡⇒↝ _ (cong (∥_∥ᴱ ∘ _⊎_ _ ∘ proj₁) (sym Q.rec-[])) ⟩□
           y ≡ x ∥⊎∥ᴱ y ∈ [ t ]Q    □)
      xs
