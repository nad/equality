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
  (open Univalence-axiom eq hiding (extensionality))
  -- The code is parametrised by an implementation of quotients.
  (quot : Quotientᴱ)
  {a o}
  -- It is assumed that function and propositional extensionality hold.
  (@0 ext      : Extensionality (lsuc a) (lsuc a ⊔ o))
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
  Set = T.Tree /ᴱ T._≈_

private variable
  xs xs₁ xs₂ : Set

opaque
  unfolding Set

  -- Set is a set.

  @0 Set-set : Is-set Set
  Set-set = Q./ᴱ-is-set

------------------------------------------------------------------------
-- Set membership

private opaque
  unfolding Set T._≈_

  -- Set membership.

  Membership :
    A → Set → ∃ λ (B : Type a) → Erased (Is-proposition B)
  Membership x = Q.rec λ where
    .is-setʳ →
      Is-set-∃-Erased-Is-proposition (lower-extensionality lzero o ext)
        prop-ext
    .[]ʳ t →
      (x T.∈ t) , [ T.∈-propositional ]
    .[]-respects-relationʳ {x = xs} {y = ys} →
      (∀ {z} → z T.∈ xs ⇔ z T.∈ ys)           →⟨ (λ xs≈ys → xs≈ys) ⟩

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

private opaque
  unfolding _∈_

  -- The type of ∈[].

  ∈[]-type : Type (lsuc a ⊔ o)
  ∈[]-type = ∀ {x t} → (x ∈ [ t ]Q) ≡ (x T.∈ t)

  -- A computation rule for _∈_.

  ∈[] : ∈[]-type
  ∈[] = cong proj₁ Q.rec-[]

opaque
  unfolding Set ∈[]

  -- Extensionality for sets.

  @0 extensionality : (∀ {x} → x ∈ xs₁ ⇔ x ∈ xs₂) → xs₁ ≡ xs₂
  extensionality =
    Q.elim-prop₂ (λ xs₁ xs₂ → (∀ {x} → x ∈ xs₁ ⇔ x ∈ xs₂) → xs₁ ≡ xs₂)
      (λ _ _ →
         Π-closure (lower-extensionality _ (lsuc a) ext) 1 λ _ →
         Set-set)
      (λ t₁ t₂ t₁≈t₂ →
         Q.[]-respects-relation λ {x} →
           x T.∈ t₁     ↝⟨ ≡⇒↝ _ (sym ∈[]) ⟩
           x ∈ [ t₁ ]Q  ↝⟨ t₁≈t₂ ⟩
           x ∈ [ t₂ ]Q  ↝⟨ ≡⇒↝ _ ∈[] ⟩□
           x T.∈ t₂     □)
      _ _

------------------------------------------------------------------------
-- A membership test

opaque
  unfolding ∈[]

  -- Does the element exist in the set?

  member? : (x : A) (xs : Set) → Dec-Erased (x ∈ xs)
  member? x = Q.elim-prop λ where
    .is-propositionʳ _ →
      BC.Is-proposition-Dec-Erased (lower-extensionality _ _ ext)
        ∈-propositional
    .[]ʳ t →
      Dec-Erased-map
        (x T.∈ t     ↝⟨ ≡⇒↝ _ (sym ∈[]) ⟩
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
  unfolding ∅ ∈[]

  -- The empty set is empty.

  @0 ∉∅ : ¬ x ∈ ∅
  ∉∅ {x} =
    x ∈ [ T.empty ]Q  →⟨ ≡⇒↝ _ ∈[] ⟩
    x T.∈ T.empty     →⟨ T.∉empty ⟩□
    ⊥                 □

------------------------------------------------------------------------
-- Insertion

opaque
  unfolding Set

  -- Inserts an element into the set.

  insert : A → Set → Set
  insert x =
    T.insert x Q./ᴱ-map λ _ _ → T.insert-respects-set-equivalence

opaque
  unfolding _/ᴱ-map_ insert ∈[]

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
           y ∈ [ T.insert x t ]Q    ↝⟨ ≡⇒↝ _ ∈[] ⟩
           y T.∈ T.insert x t       ↔⟨ inverse (∥∥ᴱ≃ T.∈-propositional) ⟩
           ∥ y T.∈ T.insert x t ∥ᴱ  ↝⟨ ∥∥ᴱ-cong T.∈-insert ⟩
           y ≡ x ∥⊎∥ᴱ y T.∈ t       ↝⟨ ≡⇒↝ _ (cong (∥_∥ᴱ ∘ _⊎_ _) (sym ∈[])) ⟩□
           y ≡ x ∥⊎∥ᴱ y ∈ [ t ]Q    □)
      xs
