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

open import Equality.Decidable-UIP eq
open import Equivalence eq as Eq using (_≃_)
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
--
-- Note that this definition is not optimised.

+_+-[1+_] : ℕ → ℕ → ℤ
+ m +-[1+ n ] = case m Nat.≤⊎> n of λ where
  (inj₁ _) → -[1+ n ∸ m ]
  (inj₂ _) → + (m ∸ suc n)

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

-- Non-negative integers are not equal to negative integers.

+≢-[1+] : + m ≢ -[1+ n ]
+≢-[1+] +≡- = subst P +≡- tt
  where
  P : ℤ → Type
  P (+ n)    = ⊤
  P -[1+ n ] = ⊥

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
