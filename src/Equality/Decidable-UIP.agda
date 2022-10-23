------------------------------------------------------------------------
-- Types with decidable equality have unique identity proofs, and
-- related results
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- The part up to "decidable⇒set" follows a proof by Michael Hedberg
-- ("A coherence theorem for Martin-Löf's type theory", JFP 1998).

open import Equality

module Equality.Decidable-UIP
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence using (module _⇔_)
open import H-level eq
open import Prelude

-- Weakly constant functions.

Constant : ∀ {a b} {A : Type a} {B : Type b} → (A → B) → Type (a ⊔ b)
Constant f = ∀ x y → f x ≡ f y

-- Left inverses.

_Left-inverse-of_ : ∀ {a b} {A : Type a} {B : Type b} →
                    (B → A) → (A → B) → Type a
g Left-inverse-of f = ∀ x → g (f x) ≡ x

abstract

  -- A set with a constant endofunction with a left inverse is a
  -- proposition.

  proposition : ∀ {a} {A : Type a} →
                (f : ∃ λ (f : A → A) → Constant f) →
                (∃ λ g → g Left-inverse-of (proj₁ f)) →
                Is-proposition A
  proposition (f , constant) (g , left-inverse) x y =
    x        ≡⟨ sym (left-inverse x) ⟩
    g (f x)  ≡⟨ cong g (constant x y) ⟩
    g (f y)  ≡⟨ left-inverse y ⟩∎
    y        ∎

  -- Endofunction families on _≡_ always have left inverses.

  left-inverse :
    ∀ {a} {A : Type a} (f : (x y : A) → x ≡ y → x ≡ y) →
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
    ∀ {a} {A : Type a} →
    ((x y : A) → ∃ λ (f : x ≡ y → x ≡ y) → Constant f) →
    Is-set A
  constant⇒set constant {x} {y} =
    proposition (constant x y)
                (left-inverse (λ x y → proj₁ $ constant x y))

  -- If it is known whether or not a type is inhabited, then one can
  -- define a constant endofunction for that type.

  decidable⇒constant : ∀ {a} {A : Type a} → Dec A →
                       ∃ λ (f : A → A) → Constant f
  decidable⇒constant (yes x) = (const x , λ _ _ → refl x)
  decidable⇒constant (no ¬x) = (id      , λ _ → ⊥-elim ∘ ¬x)

  -- Types with decidable equality are sets.

  decidable⇒set : ∀ {a} {A : Type a} → Decidable-equality A → Is-set A
  decidable⇒set dec =
    constant⇒set (λ x y → decidable⇒constant (dec x y))

  -- Non-dependent functions with propositional domains are constant.

  propositional-domain⇒constant :
    ∀ {a b} {A : Type a} {B : Type b} →
    Is-proposition A → (f : A → B) → Constant f
  propositional-domain⇒constant A-prop f = λ x y →
    cong f (A-prop x y)

  -- If there is a propositional, reflexive relation on A, and related
  -- elements are equal, then A is a set.
  --
  -- (The statement of this lemma is one part of the statement of
  -- Theorem 7.2.2 in "Homotopy Type Theory: Univalent Foundations of
  -- Mathematics" (first edition).)

  propositional-identity⇒set :
    ∀ {a b} {A : Type a}
    (B : A → A → Type b) →
    (∀ x y → Is-proposition (B x y)) →
    (∀ x → B x x) →
    (∀ x y → B x y → x ≡ y) →
    Is-set A
  propositional-identity⇒set B B-prop B-refl f =
    constant⇒set λ x y →
      (λ eq → f x y (subst (B x) eq (B-refl x))) ,
      (λ _ _ → propositional-domain⇒constant (B-prop x y) (f x y) _ _)

  -- The function cong {x = x} {y = y} takes (weakly) constant
  -- functions to constant functions.
  --
  -- This is Lemma 3.1 from van Doorn's "Constructing the
  -- Propositional Truncation using Non-recursive HITs".

  cong-preserves-Constant :
    ∀ {a b} {A : Type a} {B : Type b} {f : A → B} {x y : A} →
    Constant f → Constant (cong {x = x} {y = y} f)
  cong-preserves-Constant {f = f} {x = x} {y = y} c p q =
    cong f p                     ≡⟨ lemma p ⟩
    trans (sym (c x x)) (c x y)  ≡⟨ sym (lemma q) ⟩∎
    cong f q                     ∎
    where
    lemma : ∀ p → cong {x = x} {y = y} f p ≡ trans (sym (c x x)) (c x y)
    lemma = elim
      (λ {x y} p → cong {x = x} {y = y} f p ≡ trans (sym (c x x)) (c x y))
      (λ x →
         cong f (refl x)              ≡⟨ cong-refl _ ⟩
         refl (f x)                   ≡⟨ sym $ trans-symˡ _ ⟩∎
         trans (sym (c x x)) (c x x)  ∎)

  -- The following two results come from "Generalizations of Hedberg's
  -- Theorem" by Kraus, Escardó, Coquand and Altenkirch.

  -- Proposition 3.
  --
  -- (I proved this result using cong-preserves-Constant.)

  cong-constant :
    ∀ {a b} {A : Type a} {B : Type b} {f : A → B} {x} {x≡x : x ≡ x} →
    Constant f →
    cong f x≡x ≡ refl (f x)
  cong-constant {f = f} {x} {x≡x} c =
    cong f x≡x       ≡⟨ cong-preserves-Constant c _ _ ⟩
    cong f (refl x)  ≡⟨ cong-refl _ ⟩∎
    refl (f x)       ∎

  -- The "Fixed Point Lemma".

  fixpoint-lemma :
    ∀ {a} {A : Type a} →
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
