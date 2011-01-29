------------------------------------------------------------------------
-- Surjections
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

module Surjection {ℓ} where

open import Equality
open import Equivalence
  using (_⇔_; module _⇔_) renaming (_∘_ to _⊚_)

infix 4 _↠_

-- Surjections.

record _↠_ (From To : Set ℓ) : Set ℓ where
  field
    equivalence : From ⇔ To

  open _⇔_ equivalence

  field
    right-inverse-of : ∀ x → to (from x) ≡ x

  open _⇔_ equivalence public

-- _↠_ is a preorder.

id : ∀ {A} → A ↠ A
id = record
  { equivalence      = Equivalence.id
  ; right-inverse-of = refl
  }

infixr 9 _∘_

_∘_ : ∀ {A B C} → B ↠ C → A ↠ B → A ↠ C
f ∘ g = record
  { equivalence      = equivalence f ⊚ equivalence g
  ; right-inverse-of = λ x →
      to f (to g (from g (from f x)))  ≡⟨ cong (to f) (right-inverse-of g (from f x)) ⟩
      to f (from f x)                  ≡⟨ right-inverse-of f x ⟩∎
      x                                ∎
  } where open _↠_
