------------------------------------------------------------------------
-- Some decision procedures for equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality.Decision-procedures where

open import Prelude
open import Equality

-- The values true and false are distinct.

abstract

  true≢false : ¬ true ≡ false
  true≢false true≡false = subst T true≡false _

-- Equality of booleans is decidable.

_≟-Bool_ : Decidable (_≡_ {A = Bool})
true  ≟-Bool true  = yes (refl _)
false ≟-Bool false = yes (refl _)
true  ≟-Bool false = no  true≢false
false ≟-Bool true  = no  (true≢false ∘ sym)

-- Equality of natural numbers is decidable.

private

  Zero : ℕ → Set
  Zero zero    = ⊤
  Zero (suc n) = ⊥

  pred : ℕ → ℕ
  pred zero    = zero
  pred (suc n) = n

_≟-ℕ_ : Decidable (_≡_ {A = ℕ})
zero  ≟-ℕ zero  = yes (refl _)
suc m ≟-ℕ suc n with m ≟-ℕ n
... | yes m≡n = yes (cong suc m≡n)
... | no  m≢n = no (m≢n ∘ cong pred)
zero  ≟-ℕ suc n = no (flip (subst Zero) _)
suc m ≟-ℕ zero  = no (flip (subst Zero) _ ∘ sym)
