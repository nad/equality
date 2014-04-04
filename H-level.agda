------------------------------------------------------------------------
-- H-levels
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module H-level
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence hiding (id; _∘_)
open import Prelude
open import Surjection eq hiding (id; _∘_)

------------------------------------------------------------------------
-- H-levels

-- H-levels ("homotopy levels").

H-level : ℕ → ∀ {ℓ} → Set ℓ → Set ℓ
H-level zero    A = Contractible A
H-level (suc n) A = (x y : A) → H-level n (x ≡ y)

-- Some named levels.

Is-proposition : ∀ {ℓ} → Set ℓ → Set ℓ
Is-proposition = H-level 1

Is-set : ∀ {ℓ} → Set ℓ → Set ℓ
Is-set = H-level 2

-- Propositions are propositional types.

Proposition : (ℓ : Level) → Set (lsuc ℓ)
Proposition _ = ∃ Is-proposition

-- Types that are sets.

SET : (ℓ : Level) → Set (lsuc ℓ)
SET _ = ∃ Is-set

-- The underlying type.

Type : ∀ {ℓ} → SET ℓ → Set ℓ
Type A = proj₁ A

------------------------------------------------------------------------
-- General properties

abstract

  -- H-level is upwards closed in its first argument.

  mono₁ : ∀ {a} {A : Set a} n → H-level n A → H-level (1 + n) A
  mono₁         (suc n) h x y = mono₁ n (h x y)
  mono₁ {A = A} zero    h x y = (trivial x y , irr)
    where
    trivial : (x y : A) → x ≡ y
    trivial x y =
      x        ≡⟨ sym $ proj₂ h x ⟩
      proj₁ h  ≡⟨ proj₂ h y ⟩∎
      y        ∎

    irr : ∀ {x y} (x≡y : x ≡ y) → trivial x y ≡ x≡y
    irr = elim (λ {x y} x≡y → trivial x y ≡ x≡y)
               (λ x → trans-symˡ (proj₂ h x))

  mono : ∀ {a m n} {A : Set a} → m ≤ n → H-level m A → H-level n A
  mono ≤-refl               = id
  mono (≤-step {n = n} m≤n) = λ h → mono₁ n (mono m≤n h)

  -- If something is contractible given the assumption that it is
  -- inhabited, then it is propositional.

  [inhabited⇒contractible]⇒propositional :
    ∀ {a} {A : Set a} → (A → Contractible A) → Is-proposition A
  [inhabited⇒contractible]⇒propositional h x = mono₁ 0 (h x) x

  -- If something has h-level (1 + n) given the assumption that it is
  -- inhabited, then it has h-level (1 + n).

  [inhabited⇒+]⇒+ :
    ∀ {a} {A : Set a} n → (A → H-level (1 + n) A) → H-level (1 + n) A
  [inhabited⇒+]⇒+ n h x = h x x

  -- Being propositional is logically equivalent to having at most one
  -- element.

  propositional⇔irrelevant :
    ∀ {a} {A : Set a} → Is-proposition A ⇔ Proof-irrelevant A
  propositional⇔irrelevant {A} = record
    { to   = λ h x y → proj₁ (h x y)
    ; from = λ irr →
        [inhabited⇒contractible]⇒propositional (λ x → (x , irr x))
    }

  -- If a propositional type is inhabited, then it is contractible.

  propositional⇒inhabited⇒contractible :
    ∀ {a} {A : Set a} → Is-proposition A → A → Contractible A
  propositional⇒inhabited⇒contractible p x =
    (x , _⇔_.to propositional⇔irrelevant p x)

  -- Being a set is logically equivalent to having unique identity
  -- proofs. Note that this means that, assuming that Agda is
  -- consistent, I cannot prove (inside Agda) that there is any type
  -- whose minimal h-level is at least three.

  set⇔UIP : ∀ {a} {A : Set a} →
            Is-set A ⇔ Uniqueness-of-identity-proofs A
  set⇔UIP {A = A} = record
    { to   = λ h {x} {y} x≡y x≡y′ → proj₁ (h x y x≡y x≡y′)
    ; from = λ UIP x y →
        [inhabited⇒contractible]⇒propositional (λ x≡y → (x≡y , UIP x≡y))
    }

-- H-level n respects (split) surjections.

respects-surjection :
  ∀ {a b} {A : Set a} {B : Set b} →
  A ↠ B → ∀ n → H-level n A → H-level n B
respects-surjection A↠B zero (x , irr) = (to x , irr′)
  where
  open _↠_ A↠B

  abstract
    irr′ : ∀ y → to x ≡ y
    irr′ = λ y →
      to x         ≡⟨ cong to (irr (from y)) ⟩
      to (from y)  ≡⟨ right-inverse-of y ⟩∎
      y            ∎

respects-surjection A↠B (suc n) h = λ x y →
  respects-surjection (↠-≡ A↠B) n (h (from x) (from y))
  where open _↠_ A↠B
