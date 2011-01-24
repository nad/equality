------------------------------------------------------------------------
-- Decidable equalities are proof irrelevant
------------------------------------------------------------------------

-- Following a proof by Michael Hedberg ("A coherence theorem for
-- Martin-Löf's type theory", JFP 1998).

module Equality-without-K.Decidable-Irrelevant where

open import Data.Empty
open import Data.Product as Prod
open import Function
open import Relation.Binary using (Decidable)
open import Relation.Nullary

open import Equality-without-K
open import Equality-without-K.Groupoid
open import Equality-without-K.Tactic

-- Constant functions.

Constant : {A B : Set} → (A → B) → Set
Constant f = ∀ x y → f x ≡ f y

-- Left inverses.

_Left-inverse-of_ : {A B : Set} → (B → A) → (A → B) → Set
g Left-inverse-of f = ∀ x → g (f x) ≡ x

-- A set with a constant endofunction with a left inverse has a
-- trivial equality.

trivial-≡ : {A : Set} →
            (f : ∃ λ (f : A → A) → Constant f) →
            (∃ λ g → g Left-inverse-of (proj₁ f)) →
            Trivial-≡ A
trivial-≡ (f , constant) (g , left-inverse) x y =
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
       (λ _ → Groupoid.left-inverse groupoid _)

-- A set A has proof irrelevance if there is a family of constant
-- endofunctions on _≡_ {A = A}.

constant⇒irrelevant :
  {A : Set} →
  (f : ∀ x y → ∃ λ (f : x ≡ y → x ≡ y) → Constant f) →
  Proof-irrelevance A
constant⇒irrelevant constant {x} {y} =
  trivial-≡ (constant x y)
            (left-inverse (λ x y → proj₁ $ constant x y))

-- Sets which are decidable come with constant endofunctions.

constant : {A : Set} → Dec A →
           ∃ λ (f : A → A) → Constant f
constant (yes x) = (const x , λ _ _ → refl x)
constant (no ¬x) = (id      , λ _ → ⊥-elim ∘ ¬x)

-- Sets with decidable equality have proof irrelevance.

decidable⇒irrelevant :
  {A : Set} → Decidable (_≡_ {A = A}) → Proof-irrelevance A
decidable⇒irrelevant dec =
  constant⇒irrelevant (λ x y → constant (dec x y))
