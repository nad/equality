------------------------------------------------------------------------
-- Groupoids
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Groupoid
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Prelude hiding (id; _∘_)

-- Groupoids using _≡_ as the underlying equality.

record Groupoid o p : Set (lsuc (o ⊔ p)) where
  infix  8 _⁻¹
  infixr 7 _∘_
  infix  4 _∼_
  field
    Object : Set o
    _∼_    : Object → Object → Set p

    id  : ∀ {x} → x ∼ x
    _∘_ : ∀ {x y z} → y ∼ z → x ∼ y → x ∼ z
    _⁻¹ : ∀ {x y} → x ∼ y → y ∼ x

    left-identity  : ∀ {x y} (p : x ∼ y) → id ∘ p ≡ p
    right-identity : ∀ {x y} (p : x ∼ y) → p ∘ id ≡ p
    assoc          : ∀ {w x y z} (p : y ∼ z) (q : x ∼ y) (r : w ∼ x) →
                     p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    left-inverse   : ∀ {x y} (p : x ∼ y) → p ⁻¹ ∘ p ≡ id
    right-inverse  : ∀ {x y} (p : x ∼ y) → p ∘ p ⁻¹ ≡ id

  -- Note that this definition should perhaps contain more coherence
  -- properties: we have not assumed that _≡_ is proof-irrelevant.

  -- Some derived properties.

  abstract

    -- The identity is an identity for the inverse operator as well.

    identity : ∀ {x} → id {x = x} ⁻¹ ≡ id
    identity =
      id ⁻¹       ≡⟨ sym $ right-identity (id ⁻¹) ⟩
      id ⁻¹ ∘ id  ≡⟨ left-inverse id ⟩∎
      id          ∎

    -- The inverse operator is idempotent.

    idempotent : ∀ {x y} (p : x ∼ y) → p ⁻¹ ⁻¹ ≡ p
    idempotent p =
      p ⁻¹ ⁻¹               ≡⟨ sym $ right-identity (p ⁻¹ ⁻¹) ⟩
      p ⁻¹ ⁻¹ ∘ id          ≡⟨ sym $ cong (_∘_ (p ⁻¹ ⁻¹)) (left-inverse p) ⟩
      p ⁻¹ ⁻¹ ∘ (p ⁻¹ ∘ p)  ≡⟨ assoc _ _ _ ⟩
      (p ⁻¹ ⁻¹ ∘ p ⁻¹) ∘ p  ≡⟨ cong (λ q → q ∘ p) (left-inverse (p ⁻¹)) ⟩
      id ∘ p                ≡⟨ left-identity p ⟩∎
      p                     ∎
