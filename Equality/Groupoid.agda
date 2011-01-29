------------------------------------------------------------------------
-- The equality can be turned into a groupoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

module Equality.Groupoid {ℓ} where

open import Prelude hiding (id; _∘_)

------------------------------------------------------------------------
-- Groupoids

record Groupoid : Set (suc ℓ) where
  infix  8 _⁻¹
  infixr 7 _∘_
  infix  4 _∼_ _≡_
  field
    Object : Set ℓ
    _∼_    : Object → Object → Set ℓ
    _≡_    : ∀ {x y} → x ∼ y → x ∼ y → Set ℓ

    id  : ∀ {x} → x ∼ x
    _∘_ : ∀ {x y z} → y ∼ z → x ∼ y → x ∼ z
    _⁻¹ : ∀ {x y} → x ∼ y → y ∼ x

    left-identity  : ∀ {x y} (p : x ∼ y) → id ∘ p ≡ p
    right-identity : ∀ {x y} (p : x ∼ y) → p ∘ id ≡ p
    assoc          : ∀ {w x y z} (p : y ∼ z) (q : x ∼ y) (r : w ∼ x) →
                     p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    left-inverse   : ∀ {x y} (p : x ∼ y) → p ⁻¹ ∘ p ≡ id
    right-inverse  : ∀ {x y} (p : x ∼ y) → p ∘ p ⁻¹ ≡ id

------------------------------------------------------------------------
-- _≡_ comes with a groupoid structure

open import Equality
open import Equality.Tactic

groupoid : {A : Set ℓ} → Groupoid
groupoid {A} = record
  { Object = A
  ; _∼_    = _≡_
  ; _≡_    = _≡_

  ; id  = refl _
  ; _∘_ = flip trans
  ; _⁻¹ = sym

  ; left-identity  = λ p → prove (Trans (Lift p) Refl) (Lift p) (refl _)
  ; right-identity = λ p → prove (Trans Refl (Lift p)) (Lift p) (refl _)
  ; assoc          = λ p q r →
                       prove (Trans (Trans (Lift r) (Lift q)) (Lift p))
                             (Trans (Lift r) (Trans (Lift q) (Lift p)))
                             (refl _)
  ; left-inverse   = elim (λ p → trans p (sym p) ≡ refl _)
                          (λ _ → prove (Trans Refl (Sym Refl)) Refl
                                       (refl _))
  ; right-inverse  = elim (λ p → trans (sym p) p ≡ refl _)
                          (λ _ → prove (Trans (Sym Refl) Refl) Refl
                                       (refl _))
  }
