------------------------------------------------------------------------
-- An example showing how Container.Tree-sort can be used
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Container.Tree-sort.Example
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude using (ℕ; zero; suc; Bool; true; false)

open import Container eq
open import Container.List eq

-- Comparison function for natural numbers.

_≤_ : ℕ → ℕ → Bool
zero  ≤ _     = true
suc _ ≤ zero  = false
suc m ≤ suc n = m ≤ n

open import Container.Tree-sort eq _≤_

-- The sort function seems to return an ordered list.

ordered : sort (3 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
ordered = refl _

-- The sort function definitely returns a list which is bag equivalent
-- to the input. This property can be used to establish bag
-- equivalences between concrete lists.

a-bag-equivalence : 1 ∷ 2 ∷ 3 ∷ [] ≈-bag 3 ∷ 1 ∷ 2 ∷ []
a-bag-equivalence = sort≈ (3 ∷ 1 ∷ 2 ∷ [])
