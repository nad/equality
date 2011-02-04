------------------------------------------------------------------------
-- The equality can be turned into a groupoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

module Equality.Groupoid where

open import Equality
open import Equality.Tactic
open import Prelude hiding (id; _∘_)

------------------------------------------------------------------------
-- Groupoids

-- Using _≡_ as the underlying equality.

record Groupoid ℓ : Set (suc ℓ) where
  infix  8 _⁻¹
  infixr 7 _∘_
  infix  4 _∼_
  field
    Object : Set ℓ
    _∼_    : Object → Object → Set

    id  : ∀ {x} → x ∼ x
    _∘_ : ∀ {x y z} → y ∼ z → x ∼ y → x ∼ z
    _⁻¹ : ∀ {x y} → x ∼ y → y ∼ x

    left-identity  : ∀ {x y} (p : x ∼ y) → id ∘ p ≡ p
    right-identity : ∀ {x y} (p : x ∼ y) → p ∘ id ≡ p
    assoc          : ∀ {w x y z} (p : y ∼ z) (q : x ∼ y) (r : w ∼ x) →
                     p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    left-inverse   : ∀ {x y} (p : x ∼ y) → p ⁻¹ ∘ p ≡ id
    right-inverse  : ∀ {x y} (p : x ∼ y) → p ∘ p ⁻¹ ≡ id

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

------------------------------------------------------------------------
-- _≡_ comes with a groupoid structure

groupoid : {A : Set} → Groupoid zero
groupoid {A} = record
  { Object = A
  ; _∼_    = _≡_

  ; id  = refl _
  ; _∘_ = flip trans
  ; _⁻¹ = sym

  ; left-identity  = left-identity
  ; right-identity = right-identity
  ; assoc          = assoc
  ; left-inverse   = left-inverse
  ; right-inverse  = right-inverse
  }
  where
  abstract
    left-identity : ∀ {x y} (p : x ≡ y) → trans p (refl _) ≡ p
    left-identity p =
      prove 1 tt (λ p → Trans p Refl , p) (refl _)

    right-identity : ∀ {x y} (p : x ≡ y) → trans (refl _) p ≡ p
    right-identity p =
      prove 1 tt (λ p → Trans Refl p , p) (refl _)

    assoc : ∀ {w x y z} (p : y ≡ z) (q : x ≡ y) (r : w ≡ x) →
            trans (trans r q) p ≡ trans r (trans q p)
    assoc _ _ _ =
      prove 3 tt
        (λ p q r → Trans (Trans r q) p , Trans r (Trans q p))
        (refl _)

    left-inverse : ∀ {x y} (p : x ≡ y) → trans p (sym p) ≡ refl _
    left-inverse =
      elim (λ p → trans p (sym p) ≡ refl _)
           (λ _ → prove 0 tt (Trans Refl (Sym Refl) , Refl) (refl _))

    right-inverse : ∀ {x y} (p : x ≡ y) → trans (sym p) p ≡ refl _
    right-inverse =
      elim (λ p → trans (sym p) p ≡ refl _)
           (λ _ → prove 0 tt (Trans (Sym Refl) Refl , Refl) (refl _))
