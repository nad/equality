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
open import H-level eq
open import H-level.Closure eq
import Nat eq as Nat

open import Integer.Basics eq public

private
  variable
    i : ℤ

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

------------------------------------------------------------------------
-- Positive, negative

-- The property of being positive.

Positive : ℤ → Type
Positive (+ zero)  = ⊥
Positive (+ suc _) = ⊤
Positive -[1+ _ ]  = ⊥

-- Positive is propositional.

Positive-propositional : Is-proposition (Positive i)
Positive-propositional {i = + zero}   = ⊥-propositional
Positive-propositional {i = + suc _}  = mono₁ 0 ⊤-contractible
Positive-propositional {i = -[1+ _ ]} = ⊥-propositional

-- The property of being negative.

Negative : ℤ → Type
Negative (+ _)    = ⊥
Negative -[1+ _ ] = ⊤

-- Negative is propositional.

Negative-propositional : Is-proposition (Negative i)
Negative-propositional {i = + _}      = ⊥-propositional
Negative-propositional {i = -[1+ _ ]} = mono₁ 0 ⊤-contractible

-- No integer is both positive and negative.

¬+- : Positive i → Negative i → ⊥₀
¬+- {i = + _}      _   neg = neg
¬+- {i = -[1+ _ ]} pos _   = pos

-- No integer is both positive and equal to zero.

¬+0 : Positive i → i ≡ + 0 → ⊥₀
¬+0 {i = + zero}   pos _  = pos
¬+0 {i = + suc _}  _   ≡0 = Nat.0≢+ $ sym $ +-cancellative ≡0
¬+0 {i = -[1+ _ ]} pos _  = pos

-- No integer is both negative and equal to zero.

¬-0 : Negative i → i ≡ + 0 → ⊥₀
¬-0 {i = + _}      neg _  = neg
¬-0 {i = -[1+ _ ]} _   ≡0 = +≢-[1+] $ sym ≡0

-- One can decide if an integer is negative, zero or positive.

-⊎0⊎+ : ∀ i → Negative i ⊎ i ≡ + 0 ⊎ Positive i
-⊎0⊎+ (+ zero)  = inj₂ (inj₁ (refl _))
-⊎0⊎+ (+ suc _) = inj₂ (inj₂ _)
-⊎0⊎+ -[1+ _ ]  = inj₁ _

-- If i and j are positive, then i + j is positive.

>0→>0→+>0 : ∀ i j → Positive i → Positive j → Positive (i + j)
>0→>0→+>0 (+ suc _) (+ suc _) _ _ = _

-- If i and j are negative, then i + j is negative.

<0→<0→+<0 : ∀ i j → Negative i → Negative j → Negative (i + j)
<0→<0→+<0 -[1+ _ ] -[1+ _ ] _ _ = _
