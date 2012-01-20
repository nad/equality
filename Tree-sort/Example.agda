------------------------------------------------------------------------
-- An example showing how Tree-sort can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Tree-sort.Example where

open import Bag-equality
open import Equality.Propositional
open import Prelude hiding (_≤_)
import Tree-sort

-- Comparison function for natural numbers.

_≤_ : ℕ → ℕ → Bool
zero  ≤ _     = true
suc _ ≤ zero  = false
suc m ≤ suc n = m ≤ n

open Tree-sort _≤_

-- The sort function seems to return an ordered list.

ordered : sort (3 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
ordered = refl

-- The sort function definitely returns a list which is bag equal to
-- the input. This property can be used to establish bag equalities
-- between concrete lists.

a-bag-equality : 1 ∷ 2 ∷ 3 ∷ [] ≈-bag 3 ∷ 1 ∷ 2 ∷ []
a-bag-equality = sort≈ (3 ∷ 1 ∷ 2 ∷ [])
