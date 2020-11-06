------------------------------------------------------------------------
-- Conatural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Equality

module Conat {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (_+_; _∸_; _*_)
open import Prelude.Size

open import Function-universe eq hiding (_∘_)
open import Nat eq as Nat using (_≤_)

------------------------------------------------------------------------
-- The type

-- Conats.

mutual

  data Conat (i : Size) : Type where
    zero : Conat i
    suc  : Conat′ i → Conat i

  record Conat′ (i : Size) : Type where
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

  data [_]_∼_ (i : Size) : Conat ∞ → Conat ∞ → Type where
    zero : [ i ] zero ∼ zero
    suc  : ∀ {m n} → [ i ] force m ∼′ force n → [ i ] suc m ∼ suc n

  record [_]_∼′_ (i : Size) (m n : Conat ∞) : Type where
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
infixr -2 step-∼ step-≡∼ _≡⟨⟩∼_

_∎∼ : ∀ {i} n → [ i ] n ∼ n
_∎∼ = reflexive-∼

-- For an explanation of why step-∼ is defined in this way, see
-- Equality.step-≡.

step-∼ : ∀ {i} m {n o} → [ i ] n ∼ o → [ i ] m ∼ n → [ i ] m ∼ o
step-∼ _ n∼o m∼n = transitive-∼ m∼n n∼o

syntax step-∼ m n∼o m∼n = m ∼⟨ m∼n ⟩ n∼o

step-≡∼ : ∀ {i} m {n o} → [ i ] n ∼ o → m ≡ n → [ i ] m ∼ o
step-≡∼ {i} _ n∼o m≡n = subst ([ i ]_∼ _) (sym m≡n) n∼o

syntax step-≡∼ m n∼o m≡n = m ≡⟨ m≡n ⟩∼ n∼o

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

mutual

  -- Turns natural numbers into conatural numbers.

  ⌜_⌝ : ∀ {i} → ℕ → Conat i
  ⌜ zero  ⌝ = zero
  ⌜ suc n ⌝ = suc ⌜ n ⌝′

  ⌜_⌝′ : ∀ {i} → ℕ → Conat′ i
  force ⌜ n ⌝′ = ⌜ n ⌝

-- ⌜_⌝ maps equal numbers to bisimilar numbers.

⌜⌝-cong : ∀ {i m n} → m ≡ n → [ i ] ⌜ m ⌝ ∼ ⌜ n ⌝
⌜⌝-cong {m = m} {n} m≡n =
  ⌜ m ⌝  ≡⟨ cong ⌜_⌝ m≡n ⟩∼
  ⌜ n ⌝  ∎∼

-- Truncated predecessor.

pred : ∀ {i} {j : Size< i} → Conat i → Conat j
pred zero    = zero
pred (suc n) = force n

-- The pred function preserves bisimilarity.

pred-cong :
  ∀ {n₁ n₂ i} {j : Size< i} →
  [ i ] n₁ ∼ n₂ → [ j ] pred n₁ ∼ pred n₂
pred-cong zero    = zero
pred-cong (suc p) = force p

-- ⌜_⌝ is homomorphic with respect to pred.

⌜⌝-pred : ∀ n {i} → [ i ] ⌜ Nat.pred n ⌝ ∼ pred ⌜ n ⌝
⌜⌝-pred zero    = zero   ∎∼
⌜⌝-pred (suc n) = ⌜ n ⌝  ∎∼

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
_∸-cong_ {m₁ = m₁} {m₂} {zero} {n₂} p eq =
  m₁         ∼⟨ p ⟩
  m₂         ≡⟨⟩∼
  m₂ ∸ zero  ≡⟨ cong (_ ∸_) eq ⟩∼
  m₂ ∸ n₂    ∎∼

_∸-cong_ {n₁ = suc n₁} {n₂} zero eq =
  zero           ≡⟨⟩∼
  zero ∸ suc n₁  ≡⟨ cong (_ ∸_) eq ⟩∼
  zero ∸ n₂      ∎∼

_∸-cong_ {n₁ = suc n₁} {n₂} (suc {m = m₁} {n = m₂} p) eq =
  force m₁ ∸ n₁    ∼⟨ force p ∸-cong refl n₁ ⟩
  force m₂ ∸ n₁    ≡⟨⟩∼
  suc m₂ ∸ suc n₁  ≡⟨ cong (_ ∸_) eq ⟩∼
  suc m₂ ∸ n₂      ∎∼

-- ⌜_⌝ is homomorphic with respect to subtraction.

⌜⌝-∸ : ∀ m n {i} → [ i ] ⌜ m Prelude.∸ n ⌝ ∼ ⌜ m ⌝ ∸ n
⌜⌝-∸ m       zero    = reflexive-∼ _
⌜⌝-∸ zero    (suc n) = reflexive-∼ _
⌜⌝-∸ (suc m) (suc n) = ⌜⌝-∸ m n

-- Multiplication.

infixl 7 _*_

_*_ : ∀ {i} → Conat i → Conat i → Conat i
zero  * n     = zero
m     * zero  = zero
suc m * suc n = suc λ { .force → n .force + m .force * suc n }

-- One is a left and right identity of multiplication (up to
-- bisimilarity).

*-left-identity : ∀ {i} n → [ i ] ⌜ 1 ⌝ * n ∼ n
*-left-identity zero    = reflexive-∼ _
*-left-identity (suc n) = suc λ { .force →
  n .force + zero  ∼⟨ +-right-identity _ ⟩
  n .force         ∎∼ }

*-right-identity : ∀ {i} n → [ i ] n * ⌜ 1 ⌝ ∼ n
*-right-identity zero    = reflexive-∼ _
*-right-identity (suc n) = suc λ { .force → *-right-identity _ }

-- Zero is a left and right zero of multiplication (up to
-- bisimilarity).

*-left-zero : ∀ {i n} → [ i ] zero * n ∼ zero
*-left-zero = reflexive-∼ _

*-right-zero : ∀ {i n} → [ i ] n * zero ∼ zero
*-right-zero {n = zero}  = reflexive-∼ _
*-right-zero {n = suc n} = reflexive-∼ _

-- An unfolding lemma for multiplication.

suc*∼+* : ∀ {m n i} → [ i ] suc m * n ∼ n + m .force * n
suc*∼+* {m} {zero}  =
  zero             ∼⟨ symmetric-∼ *-right-zero ⟩
  m .force * zero  ∎∼
suc*∼+* {m} {suc n} = suc λ { .force → reflexive-∼ _ }

-- Multiplication distributes over addition.

*-+-distribˡ : ∀ m {n o i} → [ i ] m * (n + o) ∼ m * n + m * o
*-+-distribˡ zero                = reflexive-∼ _
*-+-distribˡ (suc m) {zero}  {o} = reflexive-∼ _
*-+-distribˡ (suc m) {suc n} {o} = suc λ { .force →
  n .force + o + m .force * (suc n + o)               ∼⟨ (_ ∎∼) +-cong *-+-distribˡ (m .force) ⟩
  n .force + o + (m .force * suc n + m .force * o)    ∼⟨ symmetric-∼ (+-assoc (n .force)) ⟩
  n .force + (o + (m .force * suc n + m .force * o))  ∼⟨ (n .force ∎∼) +-cong +-assoc o ⟩
  n .force + ((o + m .force * suc n) + m .force * o)  ∼⟨ (n .force ∎∼) +-cong (+-comm o +-cong (_ ∎∼)) ⟩
  n .force + ((m .force * suc n + o) + m .force * o)  ∼⟨ (n .force ∎∼) +-cong symmetric-∼ (+-assoc (m .force * _)) ⟩
  n .force + (m .force * suc n + (o + m .force * o))  ∼⟨ +-assoc (n .force) ⟩
  n .force + m .force * suc n + (o + m .force * o)    ∼⟨ (n .force + _ ∎∼) +-cong symmetric-∼ suc*∼+* ⟩
  n .force + m .force * suc n + suc m * o             ∎∼ }

*-+-distribʳ : ∀ m {n o i} → [ i ] (m + n) * o ∼ m * o + n * o
*-+-distribʳ zero               = reflexive-∼ _
*-+-distribʳ (suc m) {n} {zero} =
  zero      ∼⟨ symmetric-∼ *-right-zero ⟩
  n * zero  ∎∼
*-+-distribʳ (suc m) {n} {suc o} = suc λ { .force →
  o .force + (m .force + n) * suc o          ∼⟨ (_ ∎∼) +-cong *-+-distribʳ (m .force) ⟩
  o .force + (m .force * suc o + n * suc o)  ∼⟨ +-assoc (o .force) ⟩
  o .force + m .force * suc o + n * suc o    ∎∼ }

-- Multiplication is associative.

*-assoc : ∀ m {n o i} → [ i ] m * (n * o) ∼ (m * n) * o
*-assoc zero                    = reflexive-∼ _
*-assoc (suc m) {zero}          = reflexive-∼ _
*-assoc (suc m) {suc n} {zero}  = reflexive-∼ _
*-assoc (suc m) {suc n} {suc o} = suc λ { .force →
  o .force + n .force * suc o + m .force * (suc n * suc o)    ∼⟨ symmetric-∼ (+-assoc (o .force)) ⟩
  o .force + (n .force * suc o + m .force * (suc n * suc o))  ∼⟨ (o .force ∎∼) +-cong ((_ ∎∼) +-cong *-assoc (m .force)) ⟩
  o .force + (n .force * suc o + (m .force * suc n) * suc o)  ∼⟨ (o .force ∎∼) +-cong symmetric-∼ (*-+-distribʳ (n .force)) ⟩
  o .force + (n .force + m .force * suc n) * suc o            ∎∼ }

-- Multiplication is commutative.

*-comm : ∀ m {n i} → [ i ] m * n ∼ n * m
*-comm zero {n} =
  zero      ∼⟨ symmetric-∼ *-right-zero ⟩
  n * zero  ∎∼
*-comm (suc m) {zero}  = reflexive-∼ _
*-comm (suc m) {suc n} = suc λ { .force →
  n .force + m .force * suc n                  ∼⟨ (_ ∎∼) +-cong *-comm (m .force) ⟩
  n .force + suc n * m .force                  ∼⟨ (n .force ∎∼) +-cong suc*∼+* ⟩
  n .force + (m .force + n .force * m .force)  ∼⟨ +-assoc (n .force) ⟩
  (n .force + m .force) + n .force * m .force  ∼⟨ +-comm (n .force) +-cong *-comm _ ⟩
  (m .force + n .force) + m .force * n .force  ∼⟨ symmetric-∼ (+-assoc (m .force)) ⟩
  m .force + (n .force + m .force * n .force)  ∼⟨ (m .force ∎∼) +-cong symmetric-∼ suc*∼+* ⟩
  m .force + suc m * n .force                  ∼⟨ (m .force ∎∼) +-cong *-comm (suc m) ⟩
  m .force + n .force * suc m                  ∎∼ }

-- An unfolding lemma for multiplication.

*suc∼+* : ∀ {m n i} → [ i ] m * suc n ∼ m + m * n .force
*suc∼+* {m} {n} =
  m * suc n         ∼⟨ *-comm _ ⟩
  suc n * m         ∼⟨ suc*∼+* ⟩
  m + n .force * m  ∼⟨ (_ ∎∼) +-cong *-comm (n .force) ⟩
  m + m * n .force  ∎∼

-- Multiplication preserves bisimilarity.

infixl 7 _*-cong_

_*-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] m₁ * n₁ ∼ m₂ * n₂
zero  *-cong _     = zero
suc p *-cong zero  = zero
suc p *-cong suc q = suc λ { .force →
  q .force +-cong p .force *-cong suc q }

-- ⌜_⌝ is homomorphic with respect to multiplication.

⌜⌝-* : ∀ m {n i} → [ i ] ⌜ m Prelude.* n ⌝ ∼ ⌜ m ⌝ * ⌜ n ⌝
⌜⌝-* zero        = reflexive-∼ _
⌜⌝-* (suc m) {n} =
  ⌜ n Prelude.+ m Prelude.* n ⌝  ∼⟨ ⌜⌝-+ n ⟩
  ⌜ n ⌝ + ⌜ m Prelude.* n ⌝      ∼⟨ reflexive-∼ _ +-cong ⌜⌝-* m ⟩
  ⌜ n ⌝ + ⌜ m ⌝ * ⌜ n ⌝          ∼⟨ symmetric-∼ suc*∼+* ⟩
  ⌜ suc m ⌝ * ⌜ n ⌝              ∎∼

------------------------------------------------------------------------
-- Ordering

-- [ ∞ ] m ≤ n means that m is less than or equal to n.

mutual

  infix 4 [_]_≤_ [_]_≤′_

  data [_]_≤_ (i : Size) : Conat ∞ → Conat ∞ → Type where
    zero : ∀ {n} → [ i ] zero ≤ n
    suc  : ∀ {m n} → [ i ] force m ≤′ force n → [ i ] suc m ≤ suc n

  record [_]_≤′_ (i : Size) (m n : Conat ∞) : Type where
    coinductive
    field
      force : {j : Size< i} → [ j ] m ≤ n

open [_]_≤′_ public

-- [ ∞ ] m < n means that m is less than n (if n is finite).

infix 4 [_]_<_

[_]_<_ : Size → Conat′ ∞ → Conat ∞ → Type
[ i ] m < n = [ i ] suc m ≤ n

-- Every conatural number is less than or equal to infinity.

infix 4 _≤infinity

_≤infinity : ∀ {i} n → [ i ] n ≤ infinity
zero  ≤infinity = zero
suc n ≤infinity = suc λ { .force → force n ≤infinity }

-- No natural number is greater than or equal to infinity.

infinity≰⌜⌝ : ∀ n → ¬ [ ∞ ] infinity ≤ ⌜ n ⌝
infinity≰⌜⌝ zero    ()
infinity≰⌜⌝ (suc n) (suc p) = infinity≰⌜⌝ n (force p)

-- No number is less than zero.

≮0 : ∀ {n i} → ¬ [ i ] n < zero
≮0 ()

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

-- The ordering relation respects the ordering relation
-- (contravariantly in the first argument).

infix 4 _≤-cong-≤_

_≤-cong-≤_ :
  ∀ {m m′ n n′ i} →
  [ i ] m′ ≤ m → [ i ] n ≤ n′ → [ i ] m ≤ n → [ i ] m′ ≤ n′
_≤-cong-≤_ {m} {m′} {n} {n′} m≥m′ n≤n′ m≤n =
  m′  ≤⟨ m≥m′ ⟩
  m   ≤⟨ m≤n ⟩
  n   ≤⟨ n≤n′ ⟩
  n′  ∎≤

-- A kind of preservation result for bisimilarity, ordering and
-- logical equivalence.

infix 4 _≤-cong-∼_

_≤-cong-∼_ :
  ∀ {m m′ n n′ i} →
  [ i ] m ∼ m′ → [ i ] n ∼ n′ → [ i ] m ≤ n ⇔ [ i ] m′ ≤ n′
m∼m′ ≤-cong-∼ n∼n′ = record
  { to   = ∼→≤ (symmetric-∼ m∼m′) ≤-cong-≤ ∼→≤ n∼n′
  ; from = ∼→≤ m∼m′ ≤-cong-≤ ∼→≤ (symmetric-∼ n∼n′)
  }

-- Some inversion lemmas.

cancel-suc-≤ :
  ∀ {i m n} → [ i ] suc m ≤ suc n → [ i ] force m ≤′ force n
cancel-suc-≤ (suc p) = p

cancel-pred-≤ :
  ∀ {m n i} →
  [ i ] ⌜ 1 ⌝ ≤ n →
  [ i ] pred m ≤′ pred n →
  [ i ] m ≤ n
cancel-pred-≤ {zero}  (suc _) = λ _ → zero
cancel-pred-≤ {suc _} (suc _) = suc

cancel-∸-suc-≤ :
  ∀ {m n o i} →
  [ ∞ ] ⌜ o ⌝′ < n →
  [ i ] m ∸ suc o ≤′ n ∸ suc o →
  [ i ] m ∸ o ≤ n ∸ o
cancel-∸-suc-≤ {zero} {n} {o} _ _ =
  zero ∸ o  ∼⟨ ∸-left-zero-zero o ⟩≤
  zero      ≤⟨ zero ⟩∎
  n ∸ o     ∎≤
cancel-∸-suc-≤ {suc _} {_}     {zero}  (suc _)   = suc
cancel-∸-suc-≤ {suc m} {suc n} {suc o} (suc o<n) =
  cancel-∸-suc-≤ (force o<n)

-- The successor of a number is greater than or equal to the number.

≤suc : ∀ {i n} → [ i ] force n ≤ suc n
≤suc = helper _ (refl _)
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

-- A form of associativity for _∸_.

∸-∸-assoc : ∀ {m} n {k i} → [ i ] (m ∸ n) ∸ k ∼ m ∸ (n Prelude.+ k)
∸-∸-assoc         zero            = _ ∎∼
∸-∸-assoc {zero}  (suc _) {zero}  = _ ∎∼
∸-∸-assoc {zero}  (suc _) {suc _} = _ ∎∼
∸-∸-assoc {suc _} (suc n)         = ∸-∸-assoc n

-- A limited form of associativity for _+_ and _∸_.

+-∸-assoc : ∀ {m n k i} →
            [ ∞ ] ⌜ k ⌝ ≤ n → [ i ] (m + n) ∸ k ∼ m + (n ∸ k)
+-∸-assoc {m} {n} {zero} zero =
  m + n ∸ 0    ≡⟨⟩∼
  m + n        ≡⟨⟩∼
  m + (n ∸ 0)  ∎∼
+-∸-assoc {m} {suc n} {suc k} (suc k≤n) =
  m + suc n ∸ suc k            ∼⟨ symmetric-∼ (1++∼+suc m) ∸-cong refl (suc k) ⟩
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

-- If you subtract a natural number and then add it again, then you
-- get something that is greater than or equal to what you started
-- with.

≤∸+ : ∀ m n {i} → [ i ] m ≤ (m ∸ n) + ⌜ n ⌝
≤∸+ m zero =
  m          ∼⟨ symmetric-∼ (+-right-identity _) ⟩≤
  m + ⌜ 0 ⌝  ∎≤
≤∸+ zero    (suc n) = zero
≤∸+ (suc m) (suc n) =
  suc m                          ≤⟨ (suc λ { .force → ≤∸+ (force m) n }) ⟩
  ⌜ 1 ⌝ + (force m ∸ n + ⌜ n ⌝)  ∼⟨ +-assoc ⌜ 1 ⌝ ⟩≤
  ⌜ 1 ⌝ + (force m ∸ n) + ⌜ n ⌝  ∼⟨ 1++∼+suc _ ⟩≤
  force m ∸ n + ⌜ suc n ⌝        ≡⟨⟩≤
  suc m ∸ suc n + ⌜ suc n ⌝      ∎≤

-- If you subtract something from a number you get a number that is
-- less than or equal to the one you started with.

∸≤ : ∀ {m} n {i} → [ i ] m ∸ n ≤ m
∸≤         zero    = _ ∎≤
∸≤ {zero}  (suc _) = _ ∎≤
∸≤ {suc m} (suc n) = ≤-step λ { .force → ∸≤ n }

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

-- One can decide whether a natural number is greater than or equal
-- to, or less than, any number.

≤⌜⌝⊎>⌜⌝ : ∀ {i} m n → [ i ] m ≤ ⌜ n ⌝ ⊎ [ i ] ⌜ n ⌝′ < m
≤⌜⌝⊎>⌜⌝ zero    _       = inj₁ zero
≤⌜⌝⊎>⌜⌝ (suc m) zero    = inj₂ (suc λ { .force → zero })
≤⌜⌝⊎>⌜⌝ (suc m) (suc n) =
  ⊎-map (λ (p : [ _ ] _ ≤ _) → suc λ { .force → p })
        (λ (p : [ _ ] _ < _) → suc λ { .force → p })
        (≤⌜⌝⊎>⌜⌝ (force m) n)

-- One can decide whether a natural number is less than or equal to,
-- or greater than, any number.

⌜⌝≤⊎⌜⌝> : ∀ {i} m n → [ i ] ⌜ m ⌝ ≤ n ⊎ [ i ] ⌜ 1 ⌝ + n ≤ ⌜ m ⌝
⌜⌝≤⊎⌜⌝> zero    _       = inj₁ zero
⌜⌝≤⊎⌜⌝> (suc m) zero    = inj₂ (suc λ { .force → zero })
⌜⌝≤⊎⌜⌝> (suc m) (suc n) =
  ⊎-map (λ (p : [ _ ] _ ≤ _) → suc λ { .force → p })
        (λ p                 → suc λ { .force → suc n            ≤⟨ (suc λ { .force → _ ∎≤ }) ⟩
                                                ⌜ 1 ⌝ + force n  ≤⟨ p ⟩∎
                                                ⌜ m ⌝            ∎≤ })
        (⌜⌝≤⊎⌜⌝> m (force n))

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

-- Subtraction is monotone in its first argument and antitone in its
-- second argument.

infixl 6 _∸-mono_

_∸-mono_ : ∀ {m₁ m₂ n₁ n₂ i} →
           [ ∞ ] m₁ ≤ m₂ → n₂ ≤ n₁ → [ i ] m₁ ∸ n₁ ≤ m₂ ∸ n₂
_∸-mono_              {n₁ = zero}   {zero}  p  _ = p
_∸-mono_              {n₁ = zero}   {suc _} _  q = ⊥-elim (Nat.≮0 _ q)
_∸-mono_ {zero}       {n₁ = suc n₁}         _  _ = zero
_∸-mono_ {suc _}  {zero}   {suc _}          () _
_∸-mono_ {suc m₁} {suc m₂} {suc n₁} {zero}  p  _ = force m₁ ∸ n₁  ≤⟨ ∸≤ n₁ ⟩
                                                   force m₁       ≤⟨ ≤suc ⟩
                                                   suc m₁         ≤⟨ p ⟩∎
                                                   suc m₂         ∎≤
_∸-mono_ {suc _}  {suc _}  {suc _}  {suc _} p  q =
  force (cancel-suc-≤ p) ∸-mono Nat.suc≤suc⁻¹ q

-- Multiplication is monotone.

infixl 7 _*-mono_

_*-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] m₁ * n₁ ≤ m₂ * n₂
zero  *-mono _     = zero
suc _ *-mono zero  = zero
suc p *-mono suc q = suc λ { .force →
  q .force +-mono p .force *-mono suc q  }

------------------------------------------------------------------------
-- Minimum and maximum

-- The smallest number.

min : ∀ {i} → Conat i → Conat i → Conat i
min zero    n       = zero
min m       zero    = zero
min (suc m) (suc n) = suc λ { .force → min (force m) (force n) }

-- The largest number.

max : ∀ {i} → Conat i → Conat i → Conat i
max zero    n = n
max (suc m) n = suc λ { .force → max (force m) (pred n) }

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
ˡ≤max zero    _ = zero
ˡ≤max (suc m) n = suc λ { .force → ˡ≤max (force m) (pred n) }

ʳ≤max : ∀ {i} m n → [ i ] n ≤ max m n
ʳ≤max zero    _       = reflexive-≤ _
ʳ≤max (suc _) zero    = zero
ʳ≤max (suc m) (suc n) = suc λ { .force → ʳ≤max (force m) (force n) }

-- The min and max functions preserve bisimilarity.

min-cong :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] min m₁ n₁ ∼ min m₂ n₂
min-cong zero    q       = zero
min-cong (suc p) zero    = zero
min-cong (suc p) (suc q) =
  suc λ { .force → min-cong (force p) (force q) }

max-cong :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] max m₁ n₁ ∼ max m₂ n₂
max-cong zero    q = q
max-cong (suc p) q =
  suc λ { .force → max-cong (force p) (pred-cong q) }

------------------------------------------------------------------------
-- Finite and infinite numbers

-- A number is finite if it is bisimilar to a natural number.

Finite : Conat ∞ → Type
Finite m = ∃ λ n → [ ∞ ] m ∼ ⌜ n ⌝

-- Numbers that are not finite are infinite.

Infinite : Conat ∞ → Type
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
  Σ-map suc (λ (hyp : [ _ ] _ ∼ _) → suc λ { .force → hyp })
    (≤⌜⌝→Finite (force m≤n))

------------------------------------------------------------------------
-- Functions and proofs related to addition of strictly positive
-- numbers

-- The function _⁺+_ adds two numbers, given that the first one is
-- positive. This fact allows the second number to have type Conat′ i,
-- rather than Conat i. This can be convenient in corecursive
-- definitions.

infixl 6 _⁺+_

_⁺+_ : ∀ {m i} → [ i ] ⌜ 1 ⌝ ≤ m → Conat′ i → Conat i
_⁺+_ {zero}  () _
_⁺+_ {suc m} _  n = suc λ { .force → force m + force n }

-- The definition of _⁺+_ is correct.

⁺+∼+ : ∀ {m i} (1≤m : [ ∞ ] ⌜ 1 ⌝ ≤ m) n →
       [ i ] 1≤m ⁺+ n ∼ m + force n
⁺+∼+ {zero}  () _
⁺+∼+ {suc _} _  _ = suc λ { .force → _ ∎∼ }

-- _⁺+_ preserves bisimilarity.

⁺+-cong :
  ∀ {m₁ m₂ n₁ n₂ i}
  (1≤m₁ : [ ∞ ] ⌜ 1 ⌝ ≤ m₁)
  (1≤m₂ : [ ∞ ] ⌜ 1 ⌝ ≤ m₂) →
  [ i ] m₁ ∼ m₂ →
  [ i ] force n₁ ∼′ force n₂ →
  [ i ] 1≤m₁ ⁺+ n₁ ∼ 1≤m₂ ⁺+ n₂
⁺+-cong {zero}          () _  _           _
⁺+-cong {suc _} {zero}  _  () _           _
⁺+-cong {suc _} {suc _} _  _  (suc m₁∼m₂) n₁∼n₂ =
  suc λ { .force → force m₁∼m₂ +-cong force n₁∼n₂ }

-- _⁺+_ is monotone.

⁺+-mono :
  ∀ {m₁ m₂ n₁ n₂ i}
  (1≤m₁ : [ ∞ ] ⌜ 1 ⌝ ≤ m₁)
  (1≤m₂ : [ ∞ ] ⌜ 1 ⌝ ≤ m₂) →
  [ i ] m₁ ≤ m₂ →
  [ i ] force n₁ ≤′ force n₂ →
  [ i ] 1≤m₁ ⁺+ n₁ ≤ 1≤m₂ ⁺+ n₂
⁺+-mono {zero}          () _  _           _
⁺+-mono {suc _} {zero}  _  () _           _
⁺+-mono {suc _} {suc _} _  _  (suc m₁∼m₂) n₁∼n₂ =
  suc λ { .force → force m₁∼m₂ +-mono force n₁∼n₂ }

-- Variants of _+-cong_ that can be used when one or more of the
-- numbers are known to be positive. With this information at hand it
-- suffices for some of the proofs to be "primed".

1≤+-cong :
  ∀ {m₁ m₂ n₁ n₂ i} →
  [ i ] ⌜ 1 ⌝ ≤ m₁ →
  [ i ] m₁ ∼ m₂ →
  [ i ] n₁ ∼′ n₂ →
  [ i ] m₁ + n₁ ∼ m₂ + n₂
1≤+-cong {zero}          () _           _
1≤+-cong {suc _} {zero}  _  ()          _
1≤+-cong {suc _} {suc _} _  (suc m₁∼m₂) n₁∼n₂ =
  suc λ { .force → force m₁∼m₂ +-cong force n₁∼n₂ }

+1≤-cong :
  ∀ {m₁ m₂ n₁ n₂ i} →
  [ i ] ⌜ 1 ⌝ ≤ n₁ →
  [ i ] m₁ ∼′ m₂ →
  [ i ] n₁ ∼ n₂ →
  [ i ] m₁ + n₁ ∼ m₂ + n₂
+1≤-cong {m₁} {m₂} {n₁} {n₂} 1≤n₁ m₁∼m₂ n₁∼n₂ =
  m₁ + n₁  ∼⟨ +-comm m₁ ⟩
  n₁ + m₁  ∼⟨ 1≤+-cong 1≤n₁ n₁∼n₂ m₁∼m₂ ⟩
  n₂ + m₂  ∼⟨ +-comm n₂ ⟩∎
  m₂ + n₂  ∎∼

1≤+1≤-cong :
  ∀ {m₁ m₂ n₁ n₂ i} →
  [ i ] ⌜ 1 ⌝ ≤ m₁ →
  [ i ] ⌜ 1 ⌝ ≤ n₂ →
  [ i ] m₁ ∼′ m₂ →
  [ i ] n₁ ∼′ n₂ →
  [ i ] m₁ + n₁ ∼ m₂ + n₂
1≤+1≤-cong {m₁} {m₂} {n₁} {n₂} 1≤m₁ 1≤n₂ m₁∼m₂ n₁∼n₂ =
  m₁ + n₁  ∼⟨ 1≤+-cong 1≤m₁ (_ ∎∼) n₁∼n₂ ⟩
  m₁ + n₂  ∼⟨ +1≤-cong 1≤n₂ m₁∼m₂ (_ ∎∼) ⟩∎
  m₂ + n₂  ∎∼

-- Variants of _+-mono_ that can be used when one or more of the
-- numbers are known to be positive. With this information at hand it
-- suffices for some of the proofs to be "primed".

1≤+-mono :
  ∀ {m₁ m₂ n₁ n₂ i} →
  [ i ] ⌜ 1 ⌝ ≤ m₁ →
  [ i ] m₁ ≤ m₂ →
  [ i ] n₁ ≤′ n₂ →
  [ i ] m₁ + n₁ ≤ m₂ + n₂
1≤+-mono {zero}          () _           _
1≤+-mono {suc _} {zero}  _  ()          _
1≤+-mono {suc _} {suc _} _  (suc m₁≤m₂) n₁≤n₂ =
  suc λ { .force → force m₁≤m₂ +-mono force n₁≤n₂ }

+1≤-mono :
  ∀ {m₁ m₂ n₁ n₂ i} →
  [ i ] ⌜ 1 ⌝ ≤ n₁ →
  [ i ] m₁ ≤′ m₂ →
  [ i ] n₁ ≤ n₂ →
  [ i ] m₁ + n₁ ≤ m₂ + n₂
+1≤-mono {m₁} {m₂} {n₁} {n₂} 1≤n₁ m₁≤m₂ n₁≤n₂ =
  m₁ + n₁  ∼⟨ +-comm m₁ ⟩≤
  n₁ + m₁  ≤⟨ 1≤+-mono 1≤n₁ n₁≤n₂ m₁≤m₂ ⟩
  n₂ + m₂  ∼⟨ +-comm n₂ ⟩≤
  m₂ + n₂  ∎≤

1≤+1≤-mono :
  ∀ {m₁ m₂ n₁ n₂ i} →
  [ i ] ⌜ 1 ⌝ ≤ m₁ →
  [ i ] ⌜ 1 ⌝ ≤ n₂ →
  [ i ] m₁ ≤′ m₂ →
  [ i ] n₁ ≤′ n₂ →
  [ i ] m₁ + n₁ ≤ m₂ + n₂
1≤+1≤-mono {m₁} {m₂} {n₁} {n₂} 1≤m₁ 1≤n₂ m₁≤m₂ n₁≤n₂ =
  m₁ + n₁  ≤⟨ 1≤+-mono 1≤m₁ (_ ∎≤) n₁≤n₂ ⟩
  m₁ + n₂  ≤⟨ +1≤-mono 1≤n₂ m₁≤m₂ (_ ∎≤) ⟩∎
  m₂ + n₂  ∎≤

------------------------------------------------------------------------
-- Some negative results

-- It is impossible to define a strengthening function that, for any
-- size i, takes strong bisimilarity of size i between 2 and 1 into
-- ordering of size ssuc i between 2 and 1.

no-strengthening-21 :
  ¬ (∀ {i} → [ i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝ → [ ssuc i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝)
no-strengthening-21 strengthen = contradiction ∞
  where
  2≁1 : ∀ i → ¬ [ i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝
  2≁1 i =
    [ i      ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝  ↝⟨ strengthen ⟩
    [ ssuc i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝  ↝⟨ (λ hyp → cancel-suc-≤ hyp .force) ⟩
    [ i      ] ⌜ 1 ⌝ ≤ ⌜ 0 ⌝  ↝⟨ ≮0 ⟩□
    ⊥                         □

  mutual

    2∼1 : ∀ i → [ i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝
    2∼1 i = suc λ { .force {j} → ⊥-elim (contradiction j) }

    contradiction : Size → ⊥
    contradiction i = 2≁1 i (2∼1 i)

-- It is impossible to define a strengthening function that, for any
-- size i, takes strong bisimilarity of size i between 2 and 1 into
-- strong bisimilarity of size ssuc i between 2 and 1.

no-strengthening-∼-21 :
  ¬ (∀ {i} → [ i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝ → [ ssuc i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝)
no-strengthening-∼-21 =
  (∀ {i} → [ i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝ → [ ssuc i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝)  ↝⟨ ∼→≤ ∘_ ⟩
  (∀ {i} → [ i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝ → [ ssuc i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝)  ↝⟨ no-strengthening-21 ⟩□
  ⊥                                                         □

-- It is impossible to define a strengthening function that, for any
-- size i, takes ordering of size i between 2 and 1 into ordering of
-- size ssuc i between 2 and 1.

no-strengthening-≤-21 :
  ¬ (∀ {i} → [ i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝ → [ ssuc i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝)
no-strengthening-≤-21 =
  (∀ {i} → [ i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝ → [ ssuc i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝)  ↝⟨ _∘ ∼→≤ ⟩
  (∀ {i} → [ i ] ⌜ 2 ⌝ ∼ ⌜ 1 ⌝ → [ ssuc i ] ⌜ 2 ⌝ ≤ ⌜ 1 ⌝)  ↝⟨ no-strengthening-21 ⟩□
  ⊥                                                         □
