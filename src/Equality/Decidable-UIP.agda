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

-- Weakly constant functions.

Constant : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Constant f = ∀ x y → f x ≡ f y

-- Left inverses.

_Left-inverse-of_ : ∀ {a b} {A : Set a} {B : Set b} →
                    (B → A) → (A → B) → Set a
g Left-inverse-of f = ∀ x → g (f x) ≡ x

abstract

  -- A set with a constant endofunction with a left inverse is
  -- propositional.

  propositional : ∀ {a} {A : Set a} →
                  (f : ∃ λ (f : A → A) → Constant f) →
                  (∃ λ g → g Left-inverse-of (proj₁ f)) →
                  Is-proposition A
  propositional (f , constant) (g , left-inverse) x y =
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

  -- A type A is a set if there is a family of constant endofunctions
  -- on _≡_ {A = A}.

  constant⇒set :
    ∀ {a} {A : Set a} →
    ((x y : A) → ∃ λ (f : x ≡ y → x ≡ y) → Constant f) →
    Is-set A
  constant⇒set constant {x} {y} =
    propositional (constant x y)
                  (left-inverse (λ x y → proj₁ $ constant x y))

  -- Types which are "decided" come with constant endofunctions.

  decided⇒constant : ∀ {a} {A : Set a} → Dec A →
                     ∃ λ (f : A → A) → Constant f
  decided⇒constant (yes x) = (const x , λ _ _ → refl x)
  decided⇒constant (no ¬x) = (id      , λ _ → ⊥-elim ∘ ¬x)

  -- Types with decidable equality are sets.

  decidable⇒set : ∀ {a} {A : Set a} → Decidable-equality A → Is-set A
  decidable⇒set dec =
    constant⇒set (λ x y → decided⇒constant (dec x y))

  -- Non-dependent functions with propositional domains are constant.

  propositional-domain⇒constant :
    ∀ {a b} {A : Set a} {B : Set b} →
    Is-proposition A → (f : A → B) → Constant f
  propositional-domain⇒constant A-prop f = λ x y → cong f (A-prop x y)

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
    constant⇒set λ x y →
      (λ eq → f x y (subst (B x) eq (B-refl x))) ,
      (λ _ _ → propositional-domain⇒constant (B-prop x y) (f x y) _ _)

  -- The following two results come from "Generalizations of Hedberg's
  -- Theorem" by Kraus, Escardó, Coquand and Altenkirch.

  -- Proposition 3.

  cong-constant :
    ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {x} {x≡x : x ≡ x} →
    (c : Constant f) →
    cong f x≡x ≡ refl (f x)
  cong-constant {f = f} {x} {x≡x} c =
    cong f x≡x                   ≡⟨ elim (λ {x y} x≡y →
                                              cong f x≡y ≡ trans (sym (c x x)) (c x y))
                                         (λ x →
            cong f (refl x)                  ≡⟨ cong-refl _ ⟩
            refl (f x)                       ≡⟨ sym $ trans-symˡ _ ⟩∎
            trans (sym (c x x)) (c x x)      ∎)
                                         _ ⟩
    trans (sym (c x x)) (c x x)  ≡⟨ trans-symˡ _ ⟩∎
    refl (f x)                   ∎

  -- The "Fixed Point Lemma".

  fixpoint-lemma :
    ∀ {a} {A : Set a} →
    (f : A → A) →
    Constant f →
    Is-proposition (∃ λ x → f x ≡ x)
  fixpoint-lemma f constant (x , fx≡x) (y , fy≡y) =
      let x≡y = x    ≡⟨ sym fx≡x ⟩
                f x  ≡⟨ constant x y ⟩
                f y  ≡⟨ fy≡y ⟩∎
                y    ∎

          x≡x = x    ≡⟨ sym fx≡x ⟩
                f x  ≡⟨ subst (λ z → f z ≡ z) (sym x≡y) fy≡y ⟩∎
                x    ∎

          lemma =
            subst (λ z → f z ≡ z) x≡x fx≡x                       ≡⟨ subst-in-terms-of-trans-and-cong ⟩

            trans (sym (cong f x≡x)) (trans fx≡x (cong id x≡x))  ≡⟨ cong₂ (λ p q → trans (sym p) (trans _ q))
                                                                          (cong-constant constant) (sym $ cong-id _) ⟩
            trans (sym (refl (f x))) (trans fx≡x x≡x)            ≡⟨ cong (λ p → trans p (trans fx≡x x≡x)) sym-refl ⟩

            trans (refl (f x)) (trans fx≡x x≡x)                  ≡⟨ trans-reflˡ _ ⟩

            trans fx≡x x≡x                                       ≡⟨ sym $ trans-assoc _ _ _ ⟩

            trans (trans fx≡x (sym fx≡x))
                  (subst (λ z → f z ≡ z) (sym x≡y) fy≡y)         ≡⟨ cong (λ p → trans p (subst (λ z → f z ≡ z) (sym x≡y) fy≡y)) $
                                                                      trans-symʳ _ ⟩
            trans (refl (f x))
                  (subst (λ z → f z ≡ z) (sym x≡y) fy≡y)         ≡⟨ trans-reflˡ _ ⟩∎

            subst (λ z → f z ≡ z) (sym x≡y) fy≡y                 ∎
      in
      x , fx≡x                                  ≡⟨ Σ-≡,≡→≡ x≡x lemma ⟩
      x , subst (λ z → f z ≡ z) (sym x≡y) fy≡y  ≡⟨ sym $ Σ-≡,≡→≡ (sym x≡y) (refl _) ⟩∎
      y , fy≡y                                  ∎
