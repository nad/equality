------------------------------------------------------------------------
-- Propositional equality, defined with an abstract (non-computing)
-- eliminator
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality where

open import Equality.Axiomatisations
open import Equivalence
open import Prelude

------------------------------------------------------------------------
-- Concrete definition of equality

-- This definition is kept abstract because I might later want to
-- replace it with a definition where elim P r (refl x) does not
-- compute to r x.

abstract

  infix 4 _≡_

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

------------------------------------------------------------------------
-- Various derived definitions and properties

private

  reflexive : Reflexive
  reflexive = record
    { _≡_  = _≡_
    ; refl = refl
    }

  equality-with-J : Equality-with-J reflexive
  equality-with-J = record
    { elim      = elim
    ; elim-refl = elim-refl
    }

open Reflexive reflexive public
  using ( Contractible; Singleton
        ; Extensionality; Well-behaved-extensionality
        )
open Equality-with-J equality-with-J public
  using ( cong; cong-refl
        ; subst; subst-refl
        ; singleton-contractible
        )
open Equality-with-substitutivity-and-contractibility
       (_⇔_.to J⇔subst+contr equality-with-J) public
  using ( sym; sym-refl
        ; trans; trans-refl-refl
        ; _≡⟨_⟩_; finally
        )

-- Binary congruence.

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f {x} {y} {u} {v} x≡y u≡v =
  f x u  ≡⟨ cong (λ g → g u) (cong f x≡y) ⟩
  f y u  ≡⟨ cong (f y) u≡v ⟩∎
  f y v  ∎

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
