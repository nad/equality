------------------------------------------------------------------------
-- Bijections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bijection where

open import Equality
import Equivalence
open import Surjection using (_↠_; module _↠_)

infix 4 _↔_

-- Bijections.

record _↔_ (From To : Set) : Set where
  field
    surjection : From ↠ To

  open _↠_ surjection

  field
    left-inverse-of : ∀ x → from (to x) ≡ x

  open _↠_ surjection public

-- _↔_ is an equivalence relation.

id : ∀ {A} → A ↔ A
id = record
  { surjection      = Surjection.id
  ; left-inverse-of = refl
  }

inverse : ∀ {A B} → A ↔ B → B ↔ A
inverse A↔B = record
  { surjection = record
    { equivalence      = Equivalence.inverse equivalence
    ; right-inverse-of = left-inverse-of
    }
  ; left-inverse-of = right-inverse-of
  } where open _↔_ A↔B

infixr 9 _∘_

_∘_ : ∀ {A B C} → B ↔ C → A ↔ B → A ↔ C
f ∘ g = record
  { surjection      = Surjection._∘_ (surjection f) (surjection g)
  ; left-inverse-of = from∘to
  }
  where
  open _↔_

  abstract
    from∘to = λ x →
      from g (from f (to f (to g x)))  ≡⟨ cong (from g) (left-inverse-of f (to g x)) ⟩
      from g (to g x)                  ≡⟨ left-inverse-of g x ⟩∎
      x                                ∎
