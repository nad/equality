------------------------------------------------------------------------
-- Injections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Injection
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- Injections

-- The property of being injective.

Injective : ∀ {a b} {A : Type a} {B : Type b} → (A → B) → Type (a ⊔ b)
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

infix 0 _↣_

-- Injections.

record _↣_ {f t} (From : Type f) (To : Type t) : Type (f ⊔ t) where
  field
    to        : From → To
    injective : Injective to

------------------------------------------------------------------------
-- Preorder

-- _↣_ is a preorder.

id : ∀ {a} {A : Type a} → A ↣ A
id = record
  { to        = P.id
  ; injective = P.id
  }

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
      B ↣ C → A ↣ B → A ↣ C
f ∘ g = record
  { to        = to′
  ; injective = injective′
  }
  where
  open _↣_

  to′ = to f ⊚ to g

  injective′ : Injective to′
  injective′ = injective g ⊚ injective f

-- "Equational" reasoning combinators.

infix  -1 finally-↣
infixr -2 step-↣

-- For an explanation of why step-↣ is defined in this way, see
-- Equality.step-≡.

step-↣ : ∀ {a b c} (A : Type a) {B : Type b} {C : Type c} →
         B ↣ C → A ↣ B → A ↣ C
step-↣ _ = _∘_

syntax step-↣ A B↣C A↣B = A ↣⟨ A↣B ⟩ B↣C

finally-↣ : ∀ {a b} (A : Type a) (B : Type b) → A ↣ B → A ↣ B
finally-↣ _ _ A↣B = A↣B

syntax finally-↣ A B A↣B = A ↣⟨ A↣B ⟩□ B □
