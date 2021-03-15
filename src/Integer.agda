------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Integer
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq hiding (elim)

import Agda.Builtin.Int

open import Prelude renaming (_+_ to _⊕_)

open import Equivalence eq as Eq using (_≃_)
import Nat eq as Nat

open import Integer.Basics eq public

------------------------------------------------------------------------
-- An equivalence

-- An equivalence between ℤ and ℤ corresponding to the successor
-- function.

successor : ℤ ≃ ℤ
successor = Eq.↔→≃
  succ
  pred
  succ-pred
  pred-succ
  where
  succ : ℤ → ℤ
  succ (+ n)        = + suc n
  succ -[1+ zero  ] = + zero
  succ -[1+ suc n ] = -[1+ n ]

  pred : ℤ → ℤ
  pred (+ zero)  = -[1+ zero ]
  pred (+ suc n) = + n
  pred -[1+ n ]  = -[1+ suc n ]

  succ-pred : ∀ i → succ (pred i) ≡ i
  succ-pred (+ zero)  = refl _
  succ-pred (+ suc _) = refl _
  succ-pred -[1+ _ ]  = refl _

  pred-succ : ∀ i → pred (succ i) ≡ i
  pred-succ (+ _)        = refl _
  pred-succ -[1+ zero  ] = refl _
  pred-succ -[1+ suc _ ] = refl _

-- The forward direction of successor adds one to its input.

successor≡1+ : ∀ i → _≃_.to successor i ≡ + 1 + i
successor≡1+ (+ _)        = refl _
successor≡1+ -[1+ zero  ] = refl _
successor≡1+ -[1+ suc _ ] = refl _
