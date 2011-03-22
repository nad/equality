------------------------------------------------------------------------
-- Bijections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Bijection
  {reflexive} (eq : Equality-with-J reflexive) where

open Derived-definitions-and-properties eq
import Equivalence
import Injection; open Injection eq using (Injective; _↣_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
private
  module Surjection where
    import Surjection; open Surjection eq public
open Surjection using (_↠_; module _↠_)

------------------------------------------------------------------------
-- Bijections

infix 0 _↔_

record _↔_ (From To : Set) : Set where
  field
    surjection : From ↠ To

  open _↠_ surjection

  field
    left-inverse-of : ∀ x → from (to x) ≡ x

  injective : Injective to
  injective {x = x} {y = y} to-x≡to-y =
    x            ≡⟨ sym (left-inverse-of x) ⟩
    from (to x)  ≡⟨ cong from to-x≡to-y ⟩
    from (to y)  ≡⟨ left-inverse-of y ⟩∎
    y            ∎

  injection : From ↣ To
  injection = record
    { to        = to
    ; injective = injective
    }

  open _↠_ surjection public

------------------------------------------------------------------------
-- Equivalence

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

-- "Equational" reasoning combinators.

infix  0 finally-↔
infixr 0 _↔⟨_⟩_

_↔⟨_⟩_ : ∀ A {B C} → A ↔ B → B ↔ C → A ↔ C
_ ↔⟨ A↔B ⟩ B↔C = B↔C ∘ A↔B

finally-↔ : ∀ A B → A ↔ B → A ↔ B
finally-↔ _ _ A↔B = A↔B

syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩∎ B ∎
