------------------------------------------------------------------------
-- Sets with decidable equality have unique identity proofs
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

-- Following a proof by Michael Hedberg ("A coherence theorem for
-- Martin-Löf's type theory", JFP 1998).

open import Equality

module Equality.Decidable-UIP
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
import Equality.Groupoid as Groupoid; open Groupoid eq
open import Prelude

-- Constant functions.

Constant : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Constant f = ∀ x y → f x ≡ f y

-- Left inverses.

_Left-inverse-of_ : ∀ {a b} {A : Set a} {B : Set b} →
                    (B → A) → (A → B) → Set a
g Left-inverse-of f = ∀ x → g (f x) ≡ x

abstract

  -- A set with a constant endofunction with a left inverse is proof
  -- irrelevant.

  irrelevant : ∀ {a} {A : Set a} →
               (f : ∃ λ (f : A → A) → Constant f) →
               (∃ λ g → g Left-inverse-of (proj₁ f)) →
               Proof-irrelevant A
  irrelevant (f , constant) (g , left-inverse) x y =
    x        ≡⟨ sym (left-inverse x) ⟩
    g (f x)  ≡⟨ cong g (constant x y) ⟩
    g (f y)  ≡⟨ left-inverse y ⟩∎
    y        ∎

  -- Endofunction families on _≡_ always have left inverses.

  left-inverse :
    ∀ {a} {A : Set a} (f : (x y : A) → x ≡ y → x ≡ y) →
    ∀ {x y} → ∃ λ g → g Left-inverse-of f x y
  left-inverse {A = A} f {x} {y} =
    (λ x≡y →
       x  ≡⟨ x≡y ⟩
       y  ≡⟨ sym (f y y (refl y)) ⟩∎
       y  ∎) ,
    elim (λ {x y} x≡y → trans (f x y x≡y) (sym (f y y (refl y))) ≡ x≡y)
         (λ _ → Groupoid.left-inverse (groupoid A) _)

  -- A set A has unique identity proofs if there is a family of
  -- constant endofunctions on _≡_ {A = A}.

  constant⇒UIP :
    ∀ {a} {A : Set a} →
    (f : ∀ x y → ∃ λ (f : x ≡ y → x ≡ y) → Constant f) →
    Uniqueness-of-identity-proofs A
  constant⇒UIP constant {x} {y} =
    irrelevant (constant x y)
               (left-inverse (λ x y → proj₁ $ constant x y))

  -- Sets which are decidable come with constant endofunctions.

  constant : ∀ {a} {A : Set a} → Dec A →
             ∃ λ (f : A → A) → Constant f
  constant (inj₁  x) = (const x , λ _ _ → refl x)
  constant (inj₂ ¬x) = (id      , λ _ → ⊥-elim ∘ ¬x)

  -- Sets with decidable equality have unique identity proofs.

  decidable⇒UIP : ∀ {a} {A : Set a} →
    Decidable-equality A → Uniqueness-of-identity-proofs A
  decidable⇒UIP dec = constant⇒UIP (λ x y → constant (dec x y))
