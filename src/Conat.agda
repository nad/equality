------------------------------------------------------------------------
-- Conatural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Conat where

open import Equality.Propositional
open import Prelude hiding (_+_; _∸_)

open import Function-universe equality-with-J hiding (_∘_)
open import Nat equality-with-J as Nat using (_≤_)

------------------------------------------------------------------------
-- The type

-- Conats.

mutual

  data Conat (i : Size) : Set where
    zero : Conat i
    suc  : Conat′ i → Conat i

  record Conat′ (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Conat j

open Conat′ public

------------------------------------------------------------------------
-- Bisimilarity

-- Bisimilarity is only defined for fully defined conatural numbers
-- (of size ∞).

mutual

  infix 4 [_]_∼_ [_]_∼′_

  data [_]_∼_ (i : Size) : Conat ∞ → Conat ∞ → Set where
    zero : [ i ] zero ∼ zero
    suc  : ∀ {m n} → [ i ] force m ∼′ force n → [ i ] suc m ∼ suc n

  record [_]_∼′_ (i : Size) (m n : Conat ∞) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] m ∼ n

open [_]_∼′_ public

-- Bisimilarity is an equivalence relation.

reflexive-∼ : ∀ {i} n → [ i ] n ∼ n
reflexive-∼ zero    = zero
reflexive-∼ (suc n) = suc λ { .force → reflexive-∼ (force n) }

symmetric-∼ : ∀ {i m n} → [ i ] m ∼ n → [ i ] n ∼ m
symmetric-∼ zero    = zero
symmetric-∼ (suc p) = suc λ { .force → symmetric-∼ (force p) }

transitive-∼ : ∀ {i m n o} → [ i ] m ∼ n → [ i ] n ∼ o → [ i ] m ∼ o
transitive-∼ zero    zero    = zero
transitive-∼ (suc p) (suc q) =
  suc λ { .force → transitive-∼ (force p) (force q) }

-- Equational reasoning combinators.

infix  -1 finally-∼ _∎∼
infixr -2 step-∼ _≡⟨⟩∼_

_∎∼ : ∀ {i} n → [ i ] n ∼ n
_∎∼ = reflexive-∼

-- For an explanation of why step-∼ is defined in this way, see
-- Equality.step-≡.

step-∼ : ∀ {i} m {n o} → [ i ] n ∼ o → [ i ] m ∼ n → [ i ] m ∼ o
step-∼ _ n∼o m∼n = transitive-∼ m∼n n∼o

syntax step-∼ m n∼o m∼n = m ∼⟨ m∼n ⟩ n∼o

_≡⟨⟩∼_ : ∀ {i} m {n} → [ i ] m ∼ n → [ i ] m ∼ n
_ ≡⟨⟩∼ m∼n = m∼n

finally-∼ : ∀ {i} m n → [ i ] m ∼ n → [ i ] m ∼ n
finally-∼ _ _ m∼n = m∼n

syntax finally-∼ m n m∼n = m ∼⟨ m∼n ⟩∎ n ∎∼

------------------------------------------------------------------------
-- Some operations

-- The largest conatural number.

infinity : ∀ {i} → Conat i
infinity = suc λ { .force → infinity }

-- Turns natural numbers into conatural numbers.

⌜_⌝ : ∀ {i} → ℕ → Conat i
⌜ zero  ⌝ = zero
⌜ suc n ⌝ = suc λ { .force → ⌜ n ⌝ }

-- ⌜_⌝ maps equal numbers to bisimilar numbers.

⌜⌝-cong : ∀ {i m n} → m ≡ n → [ i ] ⌜ m ⌝ ∼ ⌜ n ⌝
⌜⌝-cong refl = reflexive-∼ _

-- Truncated predecessor.

pred : Conat ∞ → Conat ∞
pred zero    = zero
pred (suc n) = force n

-- Addition.

infixl 6 _+_

_+_ : ∀ {i} → Conat i → Conat i → Conat i
zero  + n = n
suc m + n = suc λ { .force → force m + n }

-- Zero is a left and right identity of addition (up to bisimilarity).

+-left-identity : ∀ {i} n → [ i ] zero + n ∼ n
+-left-identity = reflexive-∼

+-right-identity : ∀ {i} n → [ i ] n + zero ∼ n
+-right-identity zero    = zero
+-right-identity (suc n) = suc λ { .force → +-right-identity (force n) }

-- Infinity is a left and right zero of addition (up to bisimilarity).

+-left-zero : ∀ {i n} → [ i ] infinity + n ∼ infinity
+-left-zero = suc λ { .force → +-left-zero }

+-right-zero : ∀ {i} n → [ i ] n + infinity ∼ infinity
+-right-zero zero    = reflexive-∼ _
+-right-zero (suc n) = suc λ { .force → +-right-zero (force n) }

-- Addition is associative.

+-assoc : ∀ m {n o i} → [ i ] m + (n + o) ∼ (m + n) + o
+-assoc zero    = reflexive-∼ _
+-assoc (suc m) = suc λ { .force → +-assoc (force m) }

mutual

  -- The successor constructor can be moved from one side of _+_ to the
  -- other.

  suc+∼+suc : ∀ {m n i} → [ i ] suc m + force n ∼ force m + suc n
  suc+∼+suc {m} {n} =
    suc m + force n            ∼⟨ (suc λ { .force → reflexive-∼ _ }) ⟩
    ⌜ 1 ⌝ + force m + force n  ∼⟨ 1++∼+suc _ ⟩∎
    force m + suc n            ∎∼

  1++∼+suc : ∀ m {n i} → [ i ] ⌜ 1 ⌝ + m + force n ∼ m + suc n
  1++∼+suc zero    = suc λ { .force → reflexive-∼ _ }
  1++∼+suc (suc _) = suc λ { .force → suc+∼+suc }

-- Addition is commutative.

+-comm : ∀ m {n i} → [ i ] m + n ∼ n + m
+-comm zero {n} =
  zero + n  ∼⟨ symmetric-∼ (+-right-identity _) ⟩∎
  n + zero  ∎∼
+-comm (suc m) {n} =
  suc m + n            ∼⟨ (suc λ { .force → +-comm (force m) }) ⟩
  ⌜ 1 ⌝ + n + force m  ∼⟨ 1++∼+suc _ ⟩∎
  n + suc m            ∎∼

-- Addition preserves bisimilarity.

infixl 6 _+-cong_

_+-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] m₁ + n₁ ∼ m₂ + n₂
zero  +-cong q = q
suc p +-cong q = suc λ { .force → force p +-cong q }

-- ⌜_⌝ is homomorphic with respect to addition.

⌜⌝-+ : ∀ m {n i} → [ i ] ⌜ m Prelude.+ n ⌝ ∼ ⌜ m ⌝ + ⌜ n ⌝
⌜⌝-+ zero    = reflexive-∼ _
⌜⌝-+ (suc m) = suc λ { .force → ⌜⌝-+ m }

-- Truncated subtraction of a natural number.

infixl 6 _∸_

_∸_ : Conat ∞ → ℕ → Conat ∞
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = force m ∸ n

-- Infinity is a left zero of _∸_ (up to bisimilarity).

∸-left-zero-infinity : ∀ {i} n → [ i ] infinity ∸ n ∼ infinity
∸-left-zero-infinity zero    = reflexive-∼ _
∸-left-zero-infinity (suc n) = ∸-left-zero-infinity n

-- Zero is a left zero of _∸_ (up to bisimilarity).

∸-left-zero-zero : ∀ {i} n → [ i ] zero ∸ n ∼ zero
∸-left-zero-zero zero    = reflexive-∼ _
∸-left-zero-zero (suc n) = reflexive-∼ _

-- Zero is a right identity of subtraction (up to bisimilarity).

∸-right-identity : ∀ {i} n → [ i ] n ∸ zero ∼ n
∸-right-identity = reflexive-∼

-- Subtraction preserves bisimilarity and equality.

infixl 6 _∸-cong_

_∸-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ ∞ ] m₁ ∼ m₂ → n₁ ≡ n₂ → [ i ] m₁ ∸ n₁ ∼ m₂ ∸ n₂
_∸-cong_ {n₁ = zero}  p       refl = p
_∸-cong_ {n₁ = suc _} zero    refl = reflexive-∼ _
_∸-cong_ {n₁ = suc n} (suc p) refl = force p ∸-cong (n ∎)

-- ⌜_⌝ is homomorphic with respect to subtraction.

⌜⌝-∸ : ∀ m n {i} → [ i ] ⌜ m Prelude.∸ n ⌝ ∼ ⌜ m ⌝ ∸ n
⌜⌝-∸ m       zero    = reflexive-∼ _
⌜⌝-∸ zero    (suc n) = reflexive-∼ _
⌜⌝-∸ (suc m) (suc n) = ⌜⌝-∸ m n

------------------------------------------------------------------------
-- Ordering

-- [ ∞ ] m ≤ n means that m is less than or equal to n.

mutual

  infix 4 [_]_≤_ [_]_≤′_

  data [_]_≤_ (i : Size) : Conat ∞ → Conat ∞ → Set where
    zero : ∀ {n} → [ i ] zero ≤ n
    suc  : ∀ {m n} → [ i ] force m ≤′ force n → [ i ] suc m ≤ suc n

  record [_]_≤′_ (i : Size) (m n : Conat ∞) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] m ≤ n

open [_]_≤′_ public

-- [ ∞ ] m < n means that m is less than n.

infix 4 [_]_<_

[_]_<_ : Size → Conat′ ∞ → Conat ∞ → Set
[ i ] m < n = [ i ] suc m ≤ n

-- An inversion lemma.

cancel-suc : ∀ {i m n} → [ i ] suc m ≤ suc n → [ i ] force m ≤′ force n
cancel-suc (suc p) = p

-- Every conatural number is less than or equal to infinity.

infix 4 _≤infinity

_≤infinity : ∀ {i} n → [ i ] n ≤ infinity
zero  ≤infinity = zero
suc n ≤infinity = suc λ { .force → force n ≤infinity }

-- No natural number is greater than or equal to infinity.

infinity≰⌜⌝ : ∀ n → ¬ [ ∞ ] infinity ≤ ⌜ n ⌝
infinity≰⌜⌝ zero    ()
infinity≰⌜⌝ (suc n) (suc p) = infinity≰⌜⌝ n (force p)

-- If a number is not bounded from above by any natural number, then
-- it is bisimilar to infinity.

¬≤⌜⌝→∼∞ : ∀ {i} m → (∀ n → ¬ [ ∞ ] m ≤ ⌜ n ⌝) → [ i ] m ∼ infinity
¬≤⌜⌝→∼∞ zero    zero≰ = ⊥-elim (zero≰ 0 zero)
¬≤⌜⌝→∼∞ (suc m) hyp   =
  suc λ { .force →
    ¬≤⌜⌝→∼∞ (force m) λ n →
      [ ∞ ] force m ≤ ⌜ n ⌝    ↝⟨ (λ p → suc λ { .force → p }) ⟩
      [ ∞ ] suc m ≤ ⌜ suc n ⌝  ↝⟨ hyp (suc n) ⟩□
      ⊥                        □ }

-- The ordering relation is a partial order (with respect to
-- bisimilarity).

reflexive-≤ : ∀ {i} n → [ i ] n ≤ n
reflexive-≤ zero    = zero
reflexive-≤ (suc n) = suc λ { .force → reflexive-≤ (force n) }

transitive-≤ : ∀ {i m n o} → [ i ] m ≤ n → [ i ] n ≤ o → [ i ] m ≤ o
transitive-≤ zero    _       = zero
transitive-≤ (suc p) (suc q) =
  suc λ { .force → transitive-≤ (force p) (force q) }

antisymmetric-≤ : ∀ {i m n} → [ i ] m ≤ n → [ i ] n ≤ m → [ i ] m ∼ n
antisymmetric-≤ zero    zero    = zero
antisymmetric-≤ (suc p) (suc q) =
  suc λ { .force → antisymmetric-≤ (force p) (force q) }

-- Bisimilarity is contained in the ordering relation.

∼→≤ : ∀ {i m n} → [ i ] m ∼ n → [ i ] m ≤ n
∼→≤ zero    = zero
∼→≤ (suc p) = suc λ { .force → ∼→≤ (force p) }

-- "Equational" reasoning combinators.

infix  -1 finally-≤ _∎≤
infixr -2 step-≤ step-∼≤ _≡⟨⟩≤_

_∎≤ : ∀ {i} n → [ i ] n ≤ n
_∎≤ = reflexive-≤

step-≤ : ∀ {i} m {n o} → [ i ] n ≤ o → [ i ] m ≤ n → [ i ] m ≤ o
step-≤ _ n≤o m≤n = transitive-≤ m≤n n≤o

syntax step-≤ m n≤o m≤n = m ≤⟨ m≤n ⟩ n≤o

step-∼≤ : ∀ {i} m {n o} → [ i ] n ≤ o → [ i ] m ∼ n → [ i ] m ≤ o
step-∼≤ _ n≤o m∼n = step-≤ _ n≤o (∼→≤ m∼n)

syntax step-∼≤ m n≤o m∼n = m ∼⟨ m∼n ⟩≤ n≤o

_≡⟨⟩≤_ : ∀ {i} m {n} → [ i ] m ≤ n → [ i ] m ≤ n
_ ≡⟨⟩≤ m≤n = m≤n

finally-≤ : ∀ {i} m n → [ i ] m ≤ n → [ i ] m ≤ n
finally-≤ _ _ m≤n = m≤n

syntax finally-≤ m n m≤n = m ≤⟨ m≤n ⟩∎ n ∎≤

-- The successor of a number is greater than or equal to the number.

≤suc : ∀ {i n} → [ i ] force n ≤ suc n
≤suc = helper _ refl
  where
  helper : ∀ {i} m {n} → m ≡ force n → [ i ] m ≤ suc n
  helper zero    _    = zero
  helper (suc m) 1+m≡ = suc λ { .force {j = j} →
                          subst ([ j ] _ ≤_) 1+m≡ ≤suc }

-- If a number is less than or equal to another, then it is also less
-- than or equal to the other's successor.

≤-step : ∀ {m n i} → [ i ] m ≤′ force n → [ i ] m ≤ suc n
≤-step {zero}      _ = zero
≤-step {suc m} {n} p = suc λ { .force →
  force m  ≤⟨ ≤suc ⟩
  suc m    ≤⟨ force p ⟩∎
  force n  ∎≤ }

-- If m is less than n, then m is less than or equal to n.

<→≤ : ∀ {i m n} → [ i ] m < n → [ i ] force m ≤ n
<→≤ (suc p) = ≤-step p

-- If you add something to a number, then you get something that is
-- greater than or equal to what you started with.

m≤n+m : ∀ {i m n} → [ i ] m ≤ n + m
m≤n+m {n = zero}  = reflexive-≤ _
m≤n+m {n = suc n} = ≤-step λ { .force → m≤n+m }

m≤m+n : ∀ {m n i} → [ i ] m ≤ m + n
m≤m+n {m} {n} =
  m      ≤⟨ m≤n+m ⟩
  n + m  ≤⟨ ∼→≤ (+-comm n) ⟩∎
  m + n  ∎≤

-- A limited form of associativity for _+_ and _∸_.

+-∸-assoc : ∀ {m n k i} →
            [ ∞ ] ⌜ k ⌝ ≤ n → [ i ] (m + n) ∸ k ∼ m + (n ∸ k)
+-∸-assoc {m} {n} {zero} zero =
  m + n ∸ 0    ≡⟨⟩∼
  m + n        ≡⟨⟩∼
  m + (n ∸ 0)  ∎∼
+-∸-assoc {m} {suc n} {suc k} (suc k≤n) =
  m + suc n ∸ suc k            ∼⟨ symmetric-∼ (1++∼+suc m) ∸-cong refl {x = suc k} ⟩
  ⌜ 1 ⌝ + m + force n ∸ suc k  ≡⟨⟩∼
  m + force n ∸ k              ∼⟨ +-∸-assoc (force k≤n) ⟩
  m + (force n ∸ k)            ≡⟨⟩∼
  m + (suc n ∸ suc k)          ∎∼

-- If you subtract a number and then add it again, then you get back
-- what you started with if the number is less than or equal to the
-- number that you started with.

∸+≡ : ∀ {m n i} → [ i ] ⌜ n ⌝ ≤ m → [ i ] (m ∸ n) + ⌜ n ⌝ ∼ m
∸+≡ {m} {zero} zero =
  m + zero  ∼⟨ +-right-identity _ ⟩∎
  m         ∎∼
∸+≡ {.suc m} {suc n} (suc p) =
  force m ∸ n + ⌜ suc n ⌝        ∼⟨ symmetric-∼ (1++∼+suc _) ⟩
  ⌜ 1 ⌝ + (force m ∸ n) + ⌜ n ⌝  ∼⟨ symmetric-∼ (+-assoc ⌜ 1 ⌝) ⟩
  ⌜ 1 ⌝ + (force m ∸ n + ⌜ n ⌝)  ∼⟨ (suc λ { .force → ∸+≡ (force p) }) ⟩
  ⌜ 1 ⌝ + force m                ∼⟨ (suc λ { .force → _ ∎∼ }) ⟩∎
  suc m                          ∎∼

-- Lemmas relating the ordering relation, subtraction and the
-- successor function.

∸suc≤→∸≤suc :
  ∀ {i} m n {o} →
  [ i ] m ∸ suc n ≤ force o → [ ssuc i ] m ∸ n ≤ suc o
∸suc≤→∸≤suc zero    zero    p = zero
∸suc≤→∸≤suc zero    (suc n) p = zero
∸suc≤→∸≤suc (suc m) zero    p = suc λ { .force → p }
∸suc≤→∸≤suc (suc m) (suc n) p = ∸suc≤→∸≤suc (force m) n p

∸≤suc→∸suc≤ :
  ∀ {i} {j : Size< i} m n {o} →
  [ i ] m ∸ n ≤ suc o → [ j ] m ∸ suc n ≤ force o
∸≤suc→∸suc≤ zero    zero    p       = zero
∸≤suc→∸suc≤ zero    (suc n) p       = zero
∸≤suc→∸suc≤ (suc m) zero    (suc p) = force p
∸≤suc→∸suc≤ (suc m) (suc n) p       = ∸≤suc→∸suc≤ (force m) n p

-- ⌜_⌝ is monotone.

⌜⌝-mono : ∀ {m n i} → m ≤ n → [ i ] ⌜ m ⌝ ≤ ⌜ n ⌝
⌜⌝-mono {zero}          m≤n = zero
⌜⌝-mono {suc _} {zero}  m≤n = ⊥-elim (Nat.≮0 _ m≤n)
⌜⌝-mono {suc _} {suc _} m≤n =
  suc λ { .force → ⌜⌝-mono (Nat.suc≤suc⁻¹ m≤n) }

-- If two natural numbers are related by [ ∞ ]_≤_, then they are also
-- related by _≤_.

⌜⌝-mono⁻¹ : ∀ {m n} → [ ∞ ] ⌜ m ⌝ ≤ ⌜ n ⌝ → m ≤ n
⌜⌝-mono⁻¹ {zero}          zero      = Nat.zero≤ _
⌜⌝-mono⁻¹ {suc _} {zero}  ()
⌜⌝-mono⁻¹ {suc _} {suc _} (suc m≤n) =
  Nat.suc≤suc (⌜⌝-mono⁻¹ (force m≤n))

-- The pred function is monotone.

pred-mono : ∀ {m n} → [ ∞ ] m ≤ n → [ ∞ ] pred m ≤ pred n
pred-mono zero    = zero
pred-mono (suc p) = force p

-- Addition is monotone.

infixl 6 _+-mono_

_+-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] m₁ + n₁ ≤ m₂ + n₂
_+-mono_ {m₁ = m₁} {m₂} {n₁} {n₂} zero q =
  zero + n₁  ≡⟨⟩≤
  n₁         ≤⟨ q ⟩
  n₂         ≤⟨ m≤n+m ⟩∎
  m₂ + n₂    ∎≤
suc p +-mono q = suc λ { .force → force p +-mono q }

------------------------------------------------------------------------
-- Minimum and maximum

-- The smallest number.

min : ∀ {i} → Conat i → Conat i → Conat i
min zero    n       = zero
min m       zero    = zero
min (suc m) (suc n) = suc λ { .force → min (force m) (force n) }

-- The largest number.

max : ∀ {i} → Conat i → Conat i → Conat i
max zero    n       = n
max m       zero    = m
max (suc m) (suc n) = suc λ { .force → max (force m) (force n) }

-- The minimum of two numbers is less than or equal to both of them.

min≤ˡ : ∀ {i} m n → [ i ] min m n ≤ m
min≤ˡ zero    _       = zero
min≤ˡ (suc _) zero    = zero
min≤ˡ (suc m) (suc n) = suc λ { .force → min≤ˡ (force m) (force n) }

min≤ʳ : ∀ {i} m n → [ i ] min m n ≤ n
min≤ʳ zero    _       = zero
min≤ʳ (suc _) zero    = zero
min≤ʳ (suc m) (suc n) = suc λ { .force → min≤ʳ (force m) (force n) }

-- The maximum of two numbers is greater than or equal to both of
-- them.

ˡ≤max : ∀ {i} m n → [ i ] m ≤ max m n
ˡ≤max zero    _       = zero
ˡ≤max (suc _) zero    = reflexive-≤ _
ˡ≤max (suc m) (suc n) = suc λ { .force → ˡ≤max (force m) (force n) }

ʳ≤max : ∀ {i} m n → [ i ] n ≤ max m n
ʳ≤max zero    _       = reflexive-≤ _
ʳ≤max (suc _) zero    = zero
ʳ≤max (suc m) (suc n) = suc λ { .force → ʳ≤max (force m) (force n) }

------------------------------------------------------------------------
-- Finite and infinite numbers

-- A number is finite if it is bisimilar to a natural number.

Finite : Conat ∞ → Set
Finite m = ∃ λ n → [ ∞ ] m ∼ ⌜ n ⌝

-- Numbers that are not finite are infinite.

Infinite : Conat ∞ → Set
Infinite n = ¬ Finite n

-- The value infinity is infinite.

Infinite-infinity : Infinite infinity
Infinite-infinity = uncurry λ n →
  [ ∞ ] infinity ∼ ⌜ n ⌝  ↝⟨ ∼→≤ ⟩
  [ ∞ ] infinity ≤ ⌜ n ⌝  ↝⟨ infinity≰⌜⌝ _ ⟩
  ⊥                       □

-- Infinite numbers are bisimilar to infinity.

Infinite→∼infinity : ∀ {n i} → Infinite n → [ i ] n ∼ infinity
Infinite→∼infinity {zero}  inf = ⊥-elim (inf (_ , zero))
Infinite→∼infinity {suc n} inf =
  suc λ { .force → Infinite→∼infinity (inf ∘ Σ-map suc suc′) }
  where
  suc′ : ∀ {m} → [ ∞ ] force n ∼ ⌜ m ⌝ → [ ∞ ] suc n ∼ ⌜ suc m ⌝
  suc′ p = suc λ { .force → p }

-- If m is bounded from above by some natural number, then m is
-- finite.

≤⌜⌝→Finite : ∀ {m n} → [ ∞ ] m ≤ ⌜ n ⌝ → Finite m
≤⌜⌝→Finite {.zero}  {zero}  zero      = zero , zero
≤⌜⌝→Finite {.zero}  {suc n} zero      = zero , zero
≤⌜⌝→Finite {.suc m} {suc n} (suc m≤n) =
  Σ-map suc (λ hyp → suc λ { .force → hyp }) (≤⌜⌝→Finite (force m≤n))