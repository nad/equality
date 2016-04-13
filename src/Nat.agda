------------------------------------------------------------------------
-- Some definitions related to and properties of natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Nat where

open import Prelude

------------------------------------------------------------------------
-- Some properties related to _≤_

-- _≤_ is transitive.

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans p ≤-refl     = p
≤-trans p (≤-step q) = ≤-step (≤-trans p q)

-- Some simple lemmas.

zero≤ : ∀ n → zero ≤ n
zero≤ zero    = ≤-refl
zero≤ (suc n) = ≤-step (zero≤ n)

suc≤suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
suc≤suc ≤-refl       = ≤-refl
suc≤suc (≤-step m≤n) = ≤-step (suc≤suc m≤n)

suc≤suc⁻¹ : ∀ {m n} → suc m ≤ suc n → m ≤ n
suc≤suc⁻¹ ≤-refl     = ≤-refl
suc≤suc⁻¹ (≤-step p) = ≤-trans (≤-step ≤-refl) p

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero    n = zero≤ n
m≤m+n (suc m) n = suc≤suc (m≤m+n m n)

-- A decision procedure for _≤_.

_≤?_ : Decidable _≤_
zero  ≤? n     = inj₁ (zero≤ n)
suc m ≤? zero  = inj₂ (λ ())
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
