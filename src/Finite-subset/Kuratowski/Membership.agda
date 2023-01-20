------------------------------------------------------------------------
-- A membership relation for Kuratowski finite subsets (defined using
-- non-erased univalence)
------------------------------------------------------------------------

-- Based on Frumin, Geuvers, Gondelman and van der Weide's "Finite
-- Sets in Homotopy Type Theory".

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Finite-subset.Kuratowski.Membership
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equivalence equality-with-J as Eq using (_≃_)
open import Finite-subset.Kuratowski eq
import Finite-subset.Listed eq as L
import Finite-subset.Listed.Membership eq as LM
open import Function-universe equality-with-J hiding (_∘_)
open import H-level.Truncation.Propositional eq using (∥_∥; _∥⊎∥_)

private
  variable
    a   : Level
    A   : Type a
    x y : A
    m n : ℕ

------------------------------------------------------------------------
-- Membership

-- Membership.

infix 4 _∈_

_∈_ : {A : Type a} → A → Finite-subset-of A → Type a
x ∈ y = x LM.∈ _≃_.from Listed≃Kuratowski y

-- Membership is propositional.

∈-propositional : ∀ y → Is-proposition (x ∈ y)
∈-propositional _ = LM.∈-propositional

-- A lemma characterising ∅.

∈∅≃ : (x ∈ ∅) ≃ ⊥₀
∈∅≃ = LM.∈[]≃

-- A lemma characterising singleton.

∈singleton≃ : (x ∈ singleton y) ≃ ∥ x ≡ y ∥
∈singleton≃ = LM.∈singleton≃

-- If x is a member of y, then x is a member of y ∪ z.

∈→∈∪ˡ : ∀ y z → x ∈ y → x ∈ y ∪ z
∈→∈∪ˡ {x} y z =
  x ∈ y                                                                 ↔⟨⟩
  x LM.∈ _≃_.from Listed≃Kuratowski y                                   ↝⟨ LM.∈→∈∪ˡ ⟩
  x LM.∈ _≃_.from Listed≃Kuratowski y L.∪ _≃_.from Listed≃Kuratowski z  ↔⟨⟩
  x LM.∈ _≃_.from Listed≃Kuratowski (y ∪ z)                             ↔⟨⟩
  x ∈ y ∪ z                                                             □

-- If x is a member of z, then x is a member of y ∪ z.

∈→∈∪ʳ : ∀ y z → x ∈ z → x ∈ y ∪ z
∈→∈∪ʳ {x} y z =
  x ∈ z                                                                 ↔⟨⟩
  x LM.∈ _≃_.from Listed≃Kuratowski z                                   ↝⟨ LM.∈→∈∪ʳ (_≃_.from Listed≃Kuratowski y) ⟩
  x LM.∈ _≃_.from Listed≃Kuratowski y L.∪ _≃_.from Listed≃Kuratowski z  ↔⟨⟩
  x ∈ y ∪ z                                                             □

-- Membership of a union of two subsets can be expressed in terms of
-- membership of the subsets.

∈∪≃ : ∀ y z → (x ∈ y ∪ z) ≃ (x ∈ y ∥⊎∥ x ∈ z)
∈∪≃ {x} y z =
  x ∈ y ∪ z                                                             ↔⟨⟩

  x LM.∈ _≃_.from Listed≃Kuratowski y L.∪ _≃_.from Listed≃Kuratowski z  ↝⟨ LM.∈∪≃ ⟩

  x LM.∈ _≃_.from Listed≃Kuratowski y ∥⊎∥
  x LM.∈ _≃_.from Listed≃Kuratowski z                                   ↔⟨⟩

  x ∈ y ∥⊎∥ x ∈ z                                                       □

-- If truncated equality is decidable, then membership is also
-- decidable.

member? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec (x ∈ y)
member? equal? x = LM.member? equal? x ∘ _≃_.from Listed≃Kuratowski

-- Subsets.

_⊆_ : {A : Type a} → Finite-subset-of A → Finite-subset-of A → Type a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- The subset property can be expressed using _∪_ and _≡_.

⊆≃∪≡ : (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {x} {y} =
  x ⊆ y                                                              ↝⟨ LM.⊆≃∪≡ (_≃_.from Listed≃Kuratowski x) ⟩

  _≃_.from Listed≃Kuratowski x L.∪ _≃_.from Listed≃Kuratowski y ≡
  _≃_.from Listed≃Kuratowski y                                       ↔⟨⟩

  _≃_.from Listed≃Kuratowski (x ∪ y) ≡ _≃_.from Listed≃Kuratowski y  ↝⟨ Eq.≃-≡ (inverse Listed≃Kuratowski) ⟩□

  x ∪ y ≡ y                                                          □

-- Extensionality.

extensionality :
  (x ≡ y) ≃ (∀ z → z ∈ x ⇔ z ∈ y)
extensionality {x} {y} =
  x ≡ y                                                        ↝⟨ inverse $ Eq.≃-≡ (inverse Listed≃Kuratowski) ⟩
  _≃_.from Listed≃Kuratowski x ≡ _≃_.from Listed≃Kuratowski y  ↝⟨ LM.extensionality ⟩□
  (∀ z → z ∈ x ⇔ z ∈ y)                                        □

------------------------------------------------------------------------
-- Size

-- Size.

infix 4 ∣_∣≡_

∣_∣≡_ : {A : Type a} → Finite-subset-of A → ℕ → Type a
∣ x ∣≡ n = LM.∣ _≃_.from Listed≃Kuratowski x ∣≡ n

-- The size predicate is propositional.

∣∣≡-propositional :
  (x : Finite-subset-of A) → Is-proposition (∣ x ∣≡ n)
∣∣≡-propositional = LM.∣∣≡-propositional ∘ _≃_.from Listed≃Kuratowski

-- Unit tests documenting some of the computational behaviour of
-- ∣_∣≡_.

_ : (∣ ∅ {A = A} ∣≡ n) ≡ ↑ _ (n ≡ 0)
_ = refl _

_ : ∀ {A : Type a} {x : A} {y} →
    (∣ singleton x ∪ y ∣≡ zero) ≡ (x ∈ y × ∣ y ∣≡ zero ⊎ ⊥)
_ = refl _

_ : (∣ singleton x ∪ y ∣≡ suc n) ≡
    (x ∈ y × ∣ y ∣≡ suc n ⊎ ¬ x ∈ y × ∣ y ∣≡ n)
_ = refl _

-- The size predicate is functional.

∣∣≡-functional :
  (x : Finite-subset-of A) → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n
∣∣≡-functional = LM.∣∣≡-functional ∘ _≃_.from Listed≃Kuratowski

-- If truncated equality is decidable, then one can compute the size
-- of a finite subset.

size :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : Finite-subset-of A) → ∃ λ n → ∣ x ∣≡ n
size equal? = LM.size equal? ∘ _≃_.from Listed≃Kuratowski
