------------------------------------------------------------------------
-- Injections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Injection
  {reflexive} (eq : Equality-with-J reflexive) where

open Derived-definitions-and-properties eq
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- Injections

-- The property of being injective.

Injective : {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

infix 0 _↣_

-- Injections.

record _↣_ (From To : Set) : Set where
  field
    to        : From → To
    injective : Injective to

------------------------------------------------------------------------
-- Preorder

-- _↣_ is a preorder.

id : ∀ {A} → A ↣ A
id = record
  { to        = P.id
  ; injective = P.id
  }

infixr 9 _∘_

_∘_ : ∀ {A B C} → B ↣ C → A ↣ B → A ↣ C
f ∘ g = record
  { to        = to′
  ; injective = injective′
  }
  where
  open _↣_

  to′ = to f ⊚ to g

  abstract
    injective′ : Injective to′
    injective′ = injective g ⊚ injective f

-- "Equational" reasoning combinators.

infix  0 finally-↣
infixr 0 _↣⟨_⟩_

_↣⟨_⟩_ : ∀ A {B C} → A ↣ B → B ↣ C → A ↣ C
_ ↣⟨ A↣B ⟩ B↣C = B↣C ∘ A↣B

finally-↣ : ∀ A B → A ↣ B → A ↣ B
finally-↣ _ _ A↣B = A↣B

syntax finally-↣ A B A↣B = A ↣⟨ A↣B ⟩∎ B ∎
