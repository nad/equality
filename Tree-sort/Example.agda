------------------------------------------------------------------------
-- Examples showing how Tree-sort can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Tree-sort.Example where

open import Equality.Propositional
open import Prelude
import Tree-sort

-- Comparison function for natural numbers.

compare : (m n : ℕ) → m ≤ n ⊎ n ≤ m
compare zero    _       = inj₁ (zero≤ _)
compare _       zero    = inj₂ (zero≤ _)
compare (suc m) (suc n) with compare m n
... | inj₁ m≤n = inj₁ (suc≤suc m≤n)
... | inj₂ n≤m = inj₂ (suc≤suc n≤m)

open Tree-sort _≤_ compare

-- The sort function returns ordered lists.

ordered : sort (3 ∷ 1 ∷ 2 ∷ []) ≡
          cons 1 (cons 2 (cons 3 (nil _) _) _) _
ordered = refl

-- The sort function returns a list which is bag equivalent to the
-- input. This property can be used to establish bag equivalences
-- between concrete lists.

a-bag-equivalence : 1 ∷ 2 ∷ 3 ∷ [] ≈-bag 3 ∷ 1 ∷ 2 ∷ []
a-bag-equivalence = sort≈ (3 ∷ 1 ∷ 2 ∷ [])
