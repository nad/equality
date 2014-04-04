------------------------------------------------------------------------
-- Sets with decidable equality have unique identity proofs
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- The part up to "decidable⇒UIP" follows a proof by Michael Hedberg
-- ("A coherence theorem for Martin-Löf's type theory", JFP 1998).

open import Equality

module Equality.Decidable-UIP
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence using (module _⇔_)
open import H-level eq
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
         (λ _ → trans-symʳ _)

  -- A set A has unique identity proofs if there is a family of
  -- constant endofunctions on _≡_ {A = A}.

  constant⇒UIP :
    ∀ {a} {A : Set a} →
    ((x y : A) → ∃ λ (f : x ≡ y → x ≡ y) → Constant f) →
    Uniqueness-of-identity-proofs A
  constant⇒UIP constant {x} {y} =
    irrelevant (constant x y)
               (left-inverse (λ x y → proj₁ $ constant x y))

  -- Sets which are decidable come with constant endofunctions.

  decidable⇒constant : ∀ {a} {A : Set a} → Dec A →
                       ∃ λ (f : A → A) → Constant f
  decidable⇒constant (inj₁  x) = (const x , λ _ _ → refl x)
  decidable⇒constant (inj₂ ¬x) = (id      , λ _ → ⊥-elim ∘ ¬x)

  -- Sets with decidable equality have unique identity proofs.

  decidable⇒UIP : ∀ {a} {A : Set a} →
    Decidable-equality A → Uniqueness-of-identity-proofs A
  decidable⇒UIP dec =
    constant⇒UIP (λ x y → decidable⇒constant (dec x y))

  -- Types with decidable equality are sets.

  decidable⇒set : ∀ {a} {A : Set a} → Decidable-equality A → Is-set A
  decidable⇒set {A = A} dec =
    _⇔_.from {To = Uniqueness-of-identity-proofs A}
             set⇔UIP (decidable⇒UIP dec)

  -- Non-dependent functions with propositional domains are constant.

  propositional-domain⇒constant :
    ∀ {a b} {A : Set a} {B : Set b} →
    Is-proposition A → (f : A → B) → Constant f
  propositional-domain⇒constant A-prop f = λ x y →
    cong f (_⇔_.to propositional⇔irrelevant A-prop x y)

  -- If there is a propositional, reflexive relation on A, and related
  -- elements are equal, then A is a set.
  --
  -- (The statement of this lemma is one part of the statement of
  -- Theorem 7.2.2 in "Homotopy Type Theory: Univalent Foundations of
  -- Mathematics" (first edition).)

  propositional-identity⇒set :
    ∀ {a b} {A : Set a}
    (B : A → A → Set b) →
    (∀ x y → Is-proposition (B x y)) →
    (∀ x → B x x) →
    (∀ x y → B x y → x ≡ y) →
    Is-set A
  propositional-identity⇒set B B-prop B-refl f =
    _⇔_.from set⇔UIP $ constant⇒UIP λ x y →
      (λ eq → f x y (subst (B x) eq (B-refl x))) ,
      (λ _ _ → propositional-domain⇒constant (B-prop x y) (f x y) _ _)
