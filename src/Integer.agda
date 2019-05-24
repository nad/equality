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
  P : ℤ → Set
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
