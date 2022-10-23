------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

-- This module contains some basic definitions with few dependencies
-- (in particular, not Groupoid). See Integer for more definitions.
-- The definitions below are reexported from Integer.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Integer.Basics
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

import Agda.Builtin.Int

open import Prelude renaming (_+_ to _⊕_)

open import Equality.Decidable-UIP eq
import Nat eq as Nat

-- Integers.

open Agda.Builtin.Int public
  using ()
  hiding (module Int)
  renaming (Int to ℤ; pos to +_; negsuc to -[1+_])

module ℤ where
  open Agda.Builtin.Int.Int public
    using ()
    renaming (pos to +_; negsuc to -[1+_])

private
  variable
    m n : ℕ

-- Turns natural numbers into the corresponding negative integers.

-[_] : ℕ → ℤ
-[ zero  ] = + 0
-[ suc n ] = -[1+ n ]

-- Negation.

infix 8 -_

-_ : ℤ → ℤ
- + n      = -[ n ]
- -[1+ n ] = + suc n

-- A helper function used to implement addition.

+_+-[1+_] : ℕ → ℕ → ℤ
+ m +-[1+ n ] =
  if m Nat.<= n then -[1+ n ∸ m ] else + (m ∸ suc n)

private

  -- An alternative implementation of +_+-[1+_].

  +_+-[1+_]′ : ℕ → ℕ → ℤ
  + zero  +-[1+ n     ]′ = -[1+ n ]
  + suc m +-[1+ zero  ]′ = + m
  + suc m +-[1+ suc n ]′ = + m +-[1+ n ]′

  -- The alternative implementation of +_+-[1+_] is not optimised (it
  -- does not use builtin functions), but it computes in the same way
  -- as +_+-[1+_].

  ++-[1+]≡++-[1+]′ : ∀ m n → + m +-[1+ n ] ≡ + m +-[1+ n ]′
  ++-[1+]≡++-[1+]′ zero    n       = refl _
  ++-[1+]≡++-[1+]′ (suc m) zero    = refl _
  ++-[1+]≡++-[1+]′ (suc m) (suc n) = ++-[1+]≡++-[1+]′ m n

-- Addition.

infixl 6 _+_

_+_ : ℤ → ℤ → ℤ
+ m      + + n      = + (m ⊕ n)
+ m      + -[1+ n ] = + m +-[1+ n ]
-[1+ m ] + + n      = + n +-[1+ m ]
-[1+ m ] + -[1+ n ] = -[1+ suc m ⊕ n ]

-- Subtraction.

infixl 6 _-_

_-_ : ℤ → ℤ → ℤ
i - j = i + - j

-- The +_ constructor is cancellative.

+-cancellative : + m ≡ + n → m ≡ n
+-cancellative = cong f
  where
  f : ℤ → ℕ
  f (+ n)    = n
  f -[1+ n ] = n

-- The -[1+_] constructor is cancellative.

-[1+]-cancellative : -[1+ m ] ≡ -[1+ n ] → m ≡ n
-[1+]-cancellative = cong f
  where
  f : ℤ → ℕ
  f (+ n)    = n
  f -[1+ n ] = n

-- Non-negative integers are not equal to negative integers.

+≢-[1+] : + m ≢ -[1+ n ]
+≢-[1+] +≡- = subst P +≡- tt
  where
  P : ℤ → Type
  P (+ n)    = ⊤
  P -[1+ n ] = ⊥

-- Non-positive integers are not equal to positive integers.

+[1+]≢- : + suc m ≢ -[ n ]
+[1+]≢- {n = zero}  = Nat.0≢+ ∘ sym ∘ +-cancellative
+[1+]≢- {n = suc _} = +≢-[1+]

-- Equality of integers is decidable.

infix 4 _≟_

_≟_ : Decidable-equality ℤ
+ m      ≟ + n      = ⊎-map (cong (+_)) (_∘ +-cancellative) (m Nat.≟ n)
+ m      ≟ -[1+ n ] = no +≢-[1+]
-[1+ m ] ≟ + n      = no (+≢-[1+] ∘ sym)
-[1+ m ] ≟ -[1+ n ] = ⊎-map (cong -[1+_]) (_∘ -[1+]-cancellative)
                        (m Nat.≟ n)

-- The integers form a set.

ℤ-set : Is-set ℤ
ℤ-set = decidable⇒set _≟_

-- Addition is commutative.

+-comm : ∀ i {j} → i + j ≡ j + i
+-comm (+ m)    {j = + _}      = cong (+_) $ Nat.+-comm m
+-comm (+ m)    {j = -[1+ _ ]} = refl _
+-comm -[1+ m ] {j = + _}      = refl _
+-comm -[1+ m ] {j = -[1+ _ ]} = cong (-[1+_] ∘ suc) $ Nat.+-comm m
