------------------------------------------------------------------------
-- Examples showing how Tree-sort can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Tree-sort.Examples where

open import Bag-equivalence
open import Equality.Propositional
open import Prelude

-- Comparison functions for natural numbers.

compare : (m n : ℕ) → m ≤ n ⊎ n ≤ m
compare zero    _       = inj₁ (zero≤ _)
compare _       zero    = inj₂ (zero≤ _)
compare (suc m) (suc n) with compare m n
... | inj₁ m≤n = inj₁ (suc≤suc m≤n)
... | inj₂ n≤m = inj₂ (suc≤suc n≤m)

_≤?_ : ℕ → ℕ → Bool
m ≤? n with compare m n
... | inj₁ m≤n = true
... | inj₂ n<m = false

open import Tree-sort.Partial _≤?_ as P using ()
open import Tree-sort.Full _≤_ compare as F using (cons; nil)

-- The sort functions return ordered lists.

orderedP : P.tree-sort (3 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
orderedP = refl

orderedF : F.tree-sort (3 ∷ 1 ∷ 2 ∷ []) ≡
           cons 1 (cons 2 (cons 3 (nil _) _) _) _
orderedF = refl

-- The sort functions return lists which are bag equivalent to the
-- input. This property can be used to establish bag equivalences
-- between concrete lists.

a-bag-equivalenceP : 1 ∷ 2 ∷ 3 ∷ [] ≈-bag 3 ∷ 1 ∷ 2 ∷ []
a-bag-equivalenceP = P.tree-sort-permutes (3 ∷ 1 ∷ 2 ∷ [])

a-bag-equivalenceF : 1 ∷ 2 ∷ 3 ∷ [] ≈-bag 3 ∷ 1 ∷ 2 ∷ []
a-bag-equivalenceF = F.tree-sort-permutes (3 ∷ 1 ∷ 2 ∷ [])
