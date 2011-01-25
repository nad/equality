------------------------------------------------------------------------
-- Propositional equality, defined with an abstract (non-computing)
-- eliminator
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalent; module Equivalent)
open import Function.Inverse using (Inverse)
open import Function.Surjection using (Surjection)
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (¬_)

open import Equality.Axiomatisations

------------------------------------------------------------------------
-- Concrete definition of equality

abstract

  infix 4 _≡_

  -- Note that the implementation of _≡_ is kept abstract.

  data _≡_ {A : Set} : A → A → Set where
    refl′ : ∀ x → x ≡ x

  refl : {A : Set} (x : A) → x ≡ x
  refl = refl′

  elim : {A : Set} (P : {x y : A} → x ≡ y → Set) →
         (∀ x → P (refl x)) →
         ∀ {x y} (x≡y : x ≡ y) → P x≡y
  elim P r (refl′ x) = r x

  elim-refl : ∀ {A : Set} (P : {x y : A} → x ≡ y → Set)
              (r : ∀ x → P (refl x)) {x} →
              elim P r (refl x) ≡ r x
  elim-refl P r = refl _

private

  equality-with-J : Equality-with-J
  equality-with-J = record
    { _≡_       = _≡_
    ; refl      = refl
    ; elim      = elim
    ; elim-refl = elim-refl
    }

open Auxiliary _≡_ public
open Equality-with-J equality-with-J public
  using ( cong; cong-refl
        ; subst; subst-refl
        ; singleton-contractible
        )
open Equality-with-substitutivity-and-contractibility
       (Equivalent.to J⇔subst+contr ⟨$⟩ equality-with-J) public
  using ( sym; sym-refl
        ; trans; trans-refl-refl
        ; _≡⟨_⟩_; finally
        )

------------------------------------------------------------------------
-- More derived properties

-- Binary congruence.

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f {x} {y} {u} {v} x≡y u≡v =
  f x u  ≡⟨ cong (λ g → g u) (cong f x≡y) ⟩
  f y u  ≡⟨ cong (f y) u≡v ⟩∎
  f y v  ∎

-- The boolean true is not equal to false.

true≢false : ¬ true ≡ false
true≢false true≡false = subst (λ b → if b then ⊤ else ⊥) true≡false _

------------------------------------------------------------------------
-- Definitions related to the setoid machinery

-- The equality can be turned into a setoid.

setoid : Set → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = record
    { refl  = refl _
    ; sym   = sym
    ; trans = trans
    }
  }

-- Lifts ordinary functions to equality-preserving functions.

→-to-⟶ : {A B : Set} → (A → B) → setoid A ⟶ setoid B
→-to-⟶ f = record { _⟨$⟩_ = f; cong = cong f }

-- Some abbreviations: surjections and bijections.

infix 4 _↠_ _↔_

_↠_ : Set → Set → Set
A ↠ B = Surjection (setoid A) (setoid B)

_↔_ : Set → Set → Set
A ↔ B = Inverse (setoid A) (setoid B)

------------------------------------------------------------------------
-- The K rule and uniqueness of identity proofs

-- The K rule (without computational content).

K-rule : Set₁
K-rule = {A : Set} (P : {x : A} → x ≡ x → Set) →
         (∀ x → P (refl x)) →
         ∀ {x} (x≡x : x ≡ x) → P x≡x

-- Proof irrelevance (or maybe "data irrelevance", depending on what
-- the set is used for).

Proof-irrelevant : Set → Set
Proof-irrelevant A = (x y : A) → x ≡ y

-- Uniqueness of identity proofs (for a particular type).

Uniqueness-of-identity-proofs : Set → Set
Uniqueness-of-identity-proofs A =
  {x y : A} → Proof-irrelevant (x ≡ y)

-- The K rule is equivalent to uniqueness of identity proofs.

K⇔UIP : K-rule ⇔ (∀ {A} → Uniqueness-of-identity-proofs A)
K⇔UIP =
  equivalent
    (λ K {_} →
       elim (λ p → ∀ q → p ≡ q)
            (λ x → K (λ {x} p → refl x ≡ p) (λ x → refl (refl x))))
    (λ UIP P r {x} x≡x → subst P (UIP (refl x) x≡x) (r x))
