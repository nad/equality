------------------------------------------------------------------------
-- Sets with decidable equality have unique identity proofs
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Following a proof by Michael Hedberg ("A coherence theorem for
-- Martin-Löf's type theory", JFP 1998).

module Equality.Decidable-UIP where

open import Equality
open import Equality.Groupoid
open import Prelude

-- Constant functions.

Constant : {A B : Set} → (A → B) → Set
Constant f = ∀ x y → f x ≡ f y

-- Left inverses.

_Left-inverse-of_ : {A B : Set} → (B → A) → (A → B) → Set
g Left-inverse-of f = ∀ x → g (f x) ≡ x

abstract

  -- A set with a constant endofunction with a left inverse is proof
  -- irrelevant.

  irrelevant : {A : Set} →
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
    {A : Set} (f : (x y : A) → x ≡ y → x ≡ y) →
    ∀ {x y} → ∃ λ g → g Left-inverse-of f x y
  left-inverse f {x} {y} =
    (λ x≡y →
       x  ≡⟨ x≡y ⟩
       y  ≡⟨ sym (f y y (refl y)) ⟩∎
       y  ∎) ,
    elim (λ {x y} x≡y → trans (f x y x≡y) (sym (f y y (refl y))) ≡ x≡y)
         (λ _ → Groupoid.left-inverse (groupoid _) _)

  -- A set A has unique identity proofs if there is a family of
  -- constant endofunctions on _≡_ {A = A}.

  constant⇒UIP :
    {A : Set} →
    (f : ∀ x y → ∃ λ (f : x ≡ y → x ≡ y) → Constant f) →
    Uniqueness-of-identity-proofs A
  constant⇒UIP constant {x} {y} =
    irrelevant (constant x y)
               (left-inverse (λ x y → proj₁ $ constant x y))

  -- Sets which are decidable come with constant endofunctions.

  constant : {A : Set} → Dec A →
             ∃ λ (f : A → A) → Constant f
  constant (yes x) = (const x , λ _ _ → refl x)
  constant (no ¬x) = (id      , λ _ → ⊥-elim ∘ ¬x)

  -- Sets with decidable equality have unique identity proofs.

  decidable⇒UIP : {A : Set} →
    Decidable (_≡_ {A = A}) → Uniqueness-of-identity-proofs A
  decidable⇒UIP dec = constant⇒UIP (λ x y → constant (dec x y))
