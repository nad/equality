------------------------------------------------------------------------
-- Surjections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Surjection where

open import Equality
open import Equivalence
  using (_⇔_; module _⇔_) renaming (_∘_ to _⊚_)

infix 4 _↠_

-- Surjections.

record _↠_ (From To : Set) : Set where
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
  ; right-inverse-of = to∘from
  }
  where
  open _↠_

  abstract
    to∘from = λ x →
      to f (to g (from g (from f x)))  ≡⟨ cong (to f) (right-inverse-of g (from f x)) ⟩
      to f (from f x)                  ≡⟨ right-inverse-of f x ⟩∎
      x                                ∎

-- "Equational" reasoning combinators.

infix  2 finally-↠
infixr 2 _↠⟨_⟩_

_↠⟨_⟩_ : ∀ A {B C} → A ↠ B → B ↠ C → A ↠ C
_ ↠⟨ A↠B ⟩ B↠C = B↠C ∘ A↠B

finally-↠ : ∀ A B → A ↠ B → A ↠ B
finally-↠ _ _ A↠B = A↠B

syntax finally-↠ A B A↠B = A ↠⟨ A↠B ⟩∎ B ∎
