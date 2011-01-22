------------------------------------------------------------------------
-- Decidable equalities are proof irrelevant
------------------------------------------------------------------------

-- Following a proof by Michael Hedberg ("A coherence theorem for
-- Martin-Löf's type theory", JFP 1998).

module Equality-without-K.Decidable-Irrelevant where

open import Data.Empty
open import Data.Product
open import Function
open import Relation.Binary using (Decidable)
open import Relation.Nullary

open import Equality-without-K
open import Equality-without-K.Tactic

-- Sets which are decidable come with constant endofunctions.

Constant : {A B : Set} → (A → B) → Set
Constant f = ∀ x y → f x ≡ f y

constant : {A : Set} → Dec A →
           ∃ λ (f : A → A) → Constant f
constant (yes x) = (const x , λ _ _ → refl x)
constant (no ¬x) = (id      , λ _ → ⊥-elim ∘ ¬x)

-- Endofunction families on _≡_ always have left inverses.

_Left-inverse-of_ : {A B : Set} → (B → A) → (A → B) → Set
g Left-inverse-of f = ∀ x → g (f x) ≡ x

left-inverse : {A : Set}
               (f : {x y : A} → x ≡ y → x ≡ y) →
               ∃ λ (g : {x y : A} → x ≡ y → x ≡ y) →
                 ∀ {x y} → g {x} {y} Left-inverse-of f
left-inverse f =
  (λ {x y} x≡y →
     x  ≡⟨ x≡y ⟩
     y  ≡⟨ sym (f (refl y)) ⟩∎
     y  ∎) ,
  λ {_} →
    elim (λ {x y} x≡y → trans (f x≡y) (sym (f (refl y))) ≡ x≡y)
         (λ _ → trans-symʳ _)

-- A set with a constant endofunction with a left inverse has a
-- trivial equality.

trivial-≡ : {A : Set} (f g : A → A) →
            Constant f → g Left-inverse-of f →
            Trivial-≡ A
trivial-≡ f g constant left-inverse x y =
  x        ≡⟨ sym (left-inverse x) ⟩
  g (f x)  ≡⟨ cong g (constant x y) ⟩
  g (f y)  ≡⟨ left-inverse y ⟩∎
  y        ∎

-- Decidable equalities are proof irrelevant.

decidable⇒irrelevant :
  {A : Set} → Decidable (_≡_ {A = A}) → Proof-irrelevance A
decidable⇒irrelevant dec {x} {y}
  with left-inverse (λ {x y} → proj₁ $ constant $ dec x y)
... | (g , g∘f) = trivial-≡ _ g (proj₂ $ constant $ dec x y) g∘f
