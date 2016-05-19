------------------------------------------------------------------------
-- Some definitions related to and properties of natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Nat
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open Derived-definitions-and-properties eq

------------------------------------------------------------------------
-- Equality of natural numbers is decidable

-- Inhabited only for zero.

Zero : ℕ → Set
Zero zero    = ⊤
Zero (suc n) = ⊥

-- Predecessor (except if the argument is zero).

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

abstract

  -- Zero is not equal to the successor of any number.

  0≢+ : {n : ℕ} → zero ≢ suc n
  0≢+ 0≡+ = subst Zero 0≡+ tt

-- The suc constructor is cancellative.

cancel-suc : {m n : ℕ} → suc m ≡ suc n → m ≡ n
cancel-suc = cong pred

-- Equality of natural numbers is decidable.

_≟_ : Decidable-equality ℕ
zero  ≟ zero  = yes (refl _)
suc m ≟ suc n = ⊎-map (cong suc) (λ m≢n → m≢n ∘ cancel-suc) (m ≟ n)
zero  ≟ suc n = no 0≢+
suc m ≟ zero  = no (0≢+ ∘ sym)

------------------------------------------------------------------------
-- One property related to _+_

-- Addition is associative.

+-assoc : ∀ m {n o} → m + (n + o) ≡ (m + n) + o
+-assoc zero    = refl _
+-assoc (suc m) = cong suc (+-assoc m)

-- Zero is a right additive unit.

+-right-identity : ∀ {n} → n + 0 ≡ n
+-right-identity {zero}  = refl 0
+-right-identity {suc _} = cong suc +-right-identity

-- The successor constructor can be moved from one side of _+_ to the
-- other.

suc+≡+suc : ∀ m {n} → suc m + n ≡ m + suc n
suc+≡+suc zero    = refl _
suc+≡+suc (suc m) = cong suc (suc+≡+suc m)

-- Addition is commutative.

+-comm : ∀ m {n} → m + n ≡ n + m
+-comm zero        = sym +-right-identity
+-comm (suc m) {n} =
  suc (m + n)  ≡⟨ cong suc (+-comm m) ⟩
  suc (n + m)  ≡⟨ suc+≡+suc n ⟩∎
  n + suc m    ∎

------------------------------------------------------------------------
-- The usual ordering of the natural numbers, along with some
-- properties

-- The ordering.

infix 4 _≤_

data _≤_ (m n : ℕ) : Set where
  ≤-refl′ : m ≡ n → m ≤ n
  ≤-step′ : ∀ {k} → m ≤ k → suc k ≡ n → m ≤ n

-- Some abbreviations.

≤-refl : ∀ {n} → n ≤ n
≤-refl = ≤-refl′ (refl _)

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step m≤n = ≤-step′ m≤n (refl _)

-- _≤_ is transitive.

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans p (≤-refl′ eq)   = subst (_ ≤_) eq p
≤-trans p (≤-step′ q eq) = ≤-step′ (≤-trans p q) eq

-- Some simple lemmas.

zero≤ : ∀ n → zero ≤ n
zero≤ zero    = ≤-refl
zero≤ (suc n) = ≤-step (zero≤ n)

suc≤suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
suc≤suc (≤-refl′ eq)     = ≤-refl′ (cong suc eq)
suc≤suc (≤-step′ m≤n eq) = ≤-step′ (suc≤suc m≤n) (cong suc eq)

suc≤suc⁻¹ : ∀ {m n} → suc m ≤ suc n → m ≤ n
suc≤suc⁻¹ (≤-refl′ eq)   = ≤-refl′ (cancel-suc eq)
suc≤suc⁻¹ (≤-step′ p eq) =
  ≤-trans (≤-step ≤-refl) (subst (_ ≤_) (cancel-suc eq) p)

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero    n = zero≤ n
m≤m+n (suc m) n = suc≤suc (m≤m+n m n)

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m zero    = ≤-refl
m≤n+m m (suc n) = ≤-step (m≤n+m m n)

-- A decision procedure for _≤_.

_≤?_ : Decidable _≤_
zero  ≤? n     = inj₁ (zero≤ n)
suc m ≤? zero  = inj₂ λ { (≤-refl′ eq)   → 0≢+ (sym eq)
                        ; (≤-step′ _ eq) → 0≢+ (sym eq)
                        }
suc m ≤? suc n = ⊎-map suc≤suc (λ m≰n → m≰n ∘ suc≤suc⁻¹) (m ≤? n)

-- If m is not smaller than or equal to n, then n is smaller than or
-- equal to m.

≰→≥ : ∀ {m n} → ¬ m ≤ n → n ≤ m
≰→≥ {zero}  {zero}  _ = ≤-refl
≰→≥ {zero}  {suc n} p = ⊥-elim (p (zero≤ (suc n)))
≰→≥ {suc m} {zero}  p = zero≤ (suc m)
≰→≥ {suc m} {suc n} p = suc≤suc (≰→≥ (p ∘ suc≤suc))

-- _≤_ is total.

total : ∀ m n → m ≤ n ⊎ n ≤ m
total m n = ⊎-map id ≰→≥ (m ≤? n)
