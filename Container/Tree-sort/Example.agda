------------------------------------------------------------------------
-- An example showing how Container.Tree-sort can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container.Tree-sort.Example where

open import Container
open import Container.List
import Container.Tree-sort as Tree-sort
open import Equality.Propositional
open import Prelude using (ℕ; zero; suc; Bool; true; false)

-- Comparison function for natural numbers.

_≤_ : ℕ → ℕ → Bool
zero  ≤ _     = true
suc _ ≤ zero  = false
suc m ≤ suc n = m ≤ n

open Tree-sort _≤_

-- The sort function seems to return an ordered list.

ordered : sort (3 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
ordered = refl

-- The sort function definitely returns a list which is bag equivalent
-- to the input. This property can be used to establish bag
-- equivalences between concrete lists.

a-bag-equivalence : 1 ∷ 2 ∷ 3 ∷ [] ≈-bag 3 ∷ 1 ∷ 2 ∷ []
a-bag-equivalence = sort≈ (3 ∷ 1 ∷ 2 ∷ [])
