------------------------------------------------------------------------
-- Examples showing how Tree-sort can be used
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Tree-sort.Examples
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Bag-equivalence eq
import Nat eq as Nat

-- Comparison functions for natural numbers.

_≤?_ : ℕ → ℕ → Bool
m ≤? n with Nat.total m n
... | inj₁ m≤n = true
... | inj₂ n<m = false

import Tree-sort.Partial eq _≤?_ as P
open import Tree-sort.Full eq Nat._≤_ Nat.total as F using (cons; nil)

-- The sort functions return ordered lists.

orderedP : P.tree-sort (3 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
orderedP = refl _

orderedF : F.tree-sort (3 ∷ 1 ∷ 2 ∷ []) ≡
           cons 1 (cons 2 (cons 3 (nil _) _) _) _
orderedF = refl _

-- The sort functions return lists which are bag equivalent to the
-- input. This property can be used to establish bag equivalences
-- between concrete lists.

a-bag-equivalenceP : 1 ∷ 2 ∷ 3 ∷ [] ≈-bag 3 ∷ 1 ∷ 2 ∷ []
a-bag-equivalenceP = P.tree-sort-permutes (3 ∷ 1 ∷ 2 ∷ [])

a-bag-equivalenceF : 1 ∷ 2 ∷ 3 ∷ [] ≈-bag 3 ∷ 1 ∷ 2 ∷ []
a-bag-equivalenceF = F.tree-sort-permutes (3 ∷ 1 ∷ 2 ∷ [])
