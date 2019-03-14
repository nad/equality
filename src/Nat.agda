------------------------------------------------------------------------
-- Some definitions related to and properties of natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Nat
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open Derived-definitions-and-properties eq

------------------------------------------------------------------------
-- Equality of natural numbers is decidable

-- Inhabited only for zero.

Zero : ℕ → Set
Zero zero    = ⊤
Zero (suc n) = ⊥

-- Predecessor (except if the argument is zero).

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

abstract

  -- Zero is not equal to the successor of any number.

  0≢+ : {n : ℕ} → zero ≢ suc n
  0≢+ 0≡+ = subst Zero 0≡+ tt

-- The suc constructor is cancellative.

cancel-suc : {m n : ℕ} → suc m ≡ suc n → m ≡ n
cancel-suc = cong pred

-- Equality of natural numbers is decidable.

infix 4 _≟_

_≟_ : Decidable-equality ℕ
zero  ≟ zero  = yes (refl _)
suc m ≟ suc n = ⊎-map (cong suc) (λ m≢n → m≢n ∘ cancel-suc) (m ≟ n)
zero  ≟ suc n = no 0≢+
suc m ≟ zero  = no (0≢+ ∘ sym)

------------------------------------------------------------------------
-- Inequality

-- Inequality.

Distinct : ℕ → ℕ → Set
Distinct zero    zero    = ⊥
Distinct zero    (suc _) = ⊤
Distinct (suc _) zero    = ⊤
Distinct (suc m) (suc n) = Distinct m n

-- Distinct is pointwise logically equivalent to _≢_.

Distinct⇔≢ : {m n : ℕ} → Distinct m n ⇔ m ≢ n
Distinct⇔≢ = record { to = to _ _; from = from _ _ }
  where
  to : ∀ m n → Distinct m n → m ≢ n
  to zero    zero    ()
  to zero    (suc n) _   = 0≢+
  to (suc m) zero    _   = 0≢+ ∘ sym
  to (suc m) (suc n) m≢n = to m n m≢n ∘ cancel-suc

  from : ∀ m n → m ≢ n → Distinct m n
  from zero    zero    0≢0     = 0≢0 (refl 0)
  from zero    (suc n) _       = _
  from (suc m) zero    _       = _
  from (suc m) (suc n) 1+m≢1+n = from m n (1+m≢1+n ∘ cong suc)

-- Two natural numbers are either equal or distinct.

≡⊎Distinct : ∀ m n → m ≡ n ⊎ Distinct m n
≡⊎Distinct m n = ⊎-map id (_⇔_.from Distinct⇔≢) (m ≟ n)

------------------------------------------------------------------------
-- Properties related to _+_

-- Addition is associative.

+-assoc : ∀ m {n o} → m + (n + o) ≡ (m + n) + o
+-assoc zero    = refl _
+-assoc (suc m) = cong suc (+-assoc m)

-- Zero is a right additive unit.

+-right-identity : ∀ {n} → n + 0 ≡ n
+-right-identity {zero}  = refl 0
+-right-identity {suc _} = cong suc +-right-identity

-- The successor constructor can be moved from one side of _+_ to the
-- other.

suc+≡+suc : ∀ m {n} → suc m + n ≡ m + suc n
suc+≡+suc zero    = refl _
suc+≡+suc (suc m) = cong suc (suc+≡+suc m)

-- Addition is commutative.

+-comm : ∀ m {n} → m + n ≡ n + m
+-comm zero        = sym +-right-identity
+-comm (suc m) {n} =
  suc (m + n)  ≡⟨ cong suc (+-comm m) ⟩
  suc (n + m)  ≡⟨ suc+≡+suc n ⟩∎
  n + suc m    ∎

-- A number is not equal to a strictly larger number.

≢1+ : ∀ m {n} → ¬ m ≡ suc (m + n)
≢1+ zero    p = 0≢+ p
≢1+ (suc m) p = ≢1+ m (cancel-suc p)

------------------------------------------------------------------------
-- Properties related to _*_

-- Zero is a right zero for multiplication.

*-right-zero : ∀ n → n * 0 ≡ 0
*-right-zero zero    = refl 0
*-right-zero (suc n) = *-right-zero n

-- Multiplication is commutative.

*-comm : ∀ m {n} → m * n ≡ n * m
*-comm zero    {n}     = sym (*-right-zero n)
*-comm (suc m) {zero}  = *-right-zero m
*-comm (suc m) {suc n} =
  suc (n + m * suc n)    ≡⟨ cong (suc ∘ (n +_)) (*-comm m) ⟩
  suc (n + suc n * m)    ≡⟨⟩
  suc (n + (m + n * m))  ≡⟨ cong suc (+-assoc n) ⟩
  suc (n + m + n * m)    ≡⟨ cong₂ (λ x y → suc (x + y)) (+-comm n) (sym (*-comm m)) ⟩
  suc (m + n + m * n)    ≡⟨ cong suc (sym (+-assoc m)) ⟩
  suc (m + (n + m * n))  ≡⟨⟩
  suc (m + suc m * n)    ≡⟨ cong (suc ∘ (m +_)) (*-comm (suc m) {n}) ⟩∎
  suc (m + n * suc m)    ∎

-- One is a left identity for multiplication.

*-left-identity : ∀ {n} → 1 * n ≡ n
*-left-identity {n} =
  1 * n     ≡⟨⟩
  n + zero  ≡⟨ +-right-identity ⟩∎
  n         ∎

-- One is a right identity for multiplication.

*-right-identity : ∀ n → n * 1 ≡ n
*-right-identity n =
  n * 1 ≡⟨ *-comm n ⟩
  1 * n ≡⟨ *-left-identity ⟩∎
  n     ∎

-- Multiplication distributes from the left over addition.

*-+-distribˡ : ∀ m {n o} → m * (n + o) ≡ m * n + m * o
*-+-distribˡ zero            = refl _
*-+-distribˡ (suc m) {n} {o} =
  n + o + m * (n + o)        ≡⟨ cong ((n + o) +_) (*-+-distribˡ m) ⟩
  n + o + (m * n + m * o)    ≡⟨ sym (+-assoc n) ⟩
  n + (o + (m * n + m * o))  ≡⟨ cong (n +_) (+-assoc o) ⟩
  n + (o + m * n + m * o)    ≡⟨ cong ((n +_) ∘ (_+ m * o)) (+-comm o) ⟩
  n + (m * n + o + m * o)    ≡⟨ cong (n +_) (sym (+-assoc (m * _))) ⟩
  n + (m * n + (o + m * o))  ≡⟨ +-assoc n ⟩∎
  n + m * n + (o + m * o)    ∎

-- Multiplication distributes from the right over addition.

*-+-distribʳ : ∀ m {n o} → (m + n) * o ≡ m * o + n * o
*-+-distribʳ m {n} {o} =
  (m + n) * o    ≡⟨ *-comm (m + _) ⟩
  o * (m + n)    ≡⟨ *-+-distribˡ o ⟩
  o * m + o * n  ≡⟨ cong₂ _+_ (*-comm o) (*-comm o) ⟩∎
  m * o + n * o  ∎

------------------------------------------------------------------------
-- The usual ordering of the natural numbers, along with some
-- properties

-- The ordering.

infix 4 _≤_ _<_

data _≤_ (m n : ℕ) : Set where
  ≤-refl′ : m ≡ n → m ≤ n
  ≤-step′ : ∀ {k} → m ≤ k → suc k ≡ n → m ≤ n

-- Strict inequality.

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

-- Some abbreviations.

≤-refl : ∀ {n} → n ≤ n
≤-refl = ≤-refl′ (refl _)

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step m≤n = ≤-step′ m≤n (refl _)

-- _≤_ is transitive.

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans p (≤-refl′ eq)   = subst (_ ≤_) eq p
≤-trans p (≤-step′ q eq) = ≤-step′ (≤-trans p q) eq

-- If m is strictly less than n, then m is less than or equal to n.

<→≤ : ∀ {m n} → m < n → m ≤ n
<→≤ m<n = ≤-trans (≤-step ≤-refl) m<n

-- "Equational" reasoning combinators.

infix  -1 finally-≤ _∎≤
infixr -2 step-≤ step-≡≤ _≡⟨⟩≤_ step-< _<⟨⟩_

_∎≤ : ∀ n → n ≤ n
_ ∎≤ = ≤-refl

-- For an explanation of why step-≤, step-≡≤ and step-< are defined in
-- this way, see Equality.step-≡.

step-≤ : ∀ m {n o} → n ≤ o → m ≤ n → m ≤ o
step-≤ _ n≤o m≤n = ≤-trans m≤n n≤o

syntax step-≤ m n≤o m≤n = m ≤⟨ m≤n ⟩ n≤o

step-≡≤ : ∀ m {n o} → n ≤ o → m ≡ n → m ≤ o
step-≡≤ _ n≤o m≡n = subst (_≤ _) (sym m≡n) n≤o

syntax step-≡≤ m n≤o m≡n = m ≡⟨ m≡n ⟩≤ n≤o

_≡⟨⟩≤_ : ∀ m {n} → m ≤ n → m ≤ n
_ ≡⟨⟩≤ m≤n = m≤n

finally-≤ : ∀ m n → m ≤ n → m ≤ n
finally-≤ _ _ m≤n = m≤n

syntax finally-≤ m n m≤n = m ≤⟨ m≤n ⟩∎ n ∎≤

step-< : ∀ m {n o} → n ≤ o → m < n → m ≤ o
step-< m {n} {o} n≤o m<n =
  m  ≤⟨ <→≤ m<n ⟩
  n  ≤⟨ n≤o ⟩∎
  o  ∎≤

syntax step-< m n≤o m<n = m <⟨ m<n ⟩ n≤o

_<⟨⟩_ : ∀ m {n} → m < n → m ≤ n
_<⟨⟩_ _ = <→≤

-- Some simple lemmas.

zero≤ : ∀ n → zero ≤ n
zero≤ zero    = ≤-refl
zero≤ (suc n) = ≤-step (zero≤ n)

suc≤suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
suc≤suc (≤-refl′ eq)     = ≤-refl′ (cong suc eq)
suc≤suc (≤-step′ m≤n eq) = ≤-step′ (suc≤suc m≤n) (cong suc eq)

suc≤suc⁻¹ : ∀ {m n} → suc m ≤ suc n → m ≤ n
suc≤suc⁻¹ (≤-refl′ eq)   = ≤-refl′ (cancel-suc eq)
suc≤suc⁻¹ (≤-step′ p eq) =
  ≤-trans (≤-step ≤-refl) (subst (_ ≤_) (cancel-suc eq) p)

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero    n = zero≤ n
m≤m+n (suc m) n = suc≤suc (m≤m+n m n)

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m zero    = ≤-refl
m≤n+m m (suc n) = ≤-step (m≤n+m m n)

pred≤ : ∀ n → pred n ≤ n
pred≤ zero    = ≤-refl
pred≤ (suc _) = ≤-step ≤-refl

-- A decision procedure for _≤_.

infix 4 _≤?_

_≤?_ : Decidable _≤_
zero  ≤? n     = inj₁ (zero≤ n)
suc m ≤? zero  = inj₂ λ { (≤-refl′ eq)   → 0≢+ (sym eq)
                        ; (≤-step′ _ eq) → 0≢+ (sym eq)
                        }
suc m ≤? suc n = ⊎-map suc≤suc (λ m≰n → m≰n ∘ suc≤suc⁻¹) (m ≤? n)

-- If m is not less than or equal to n, then n is strictly less
-- than m.

≰→> : ∀ {m n} → ¬ m ≤ n → n < m
≰→> {zero}  {n}     p = ⊥-elim (p (zero≤ n))
≰→> {suc m} {zero}  p = suc≤suc (zero≤ m)
≰→> {suc m} {suc n} p = suc≤suc (≰→> (p ∘ suc≤suc))

-- If m is not less than or equal to n, then n is less than or
-- equal to m.

≰→≥ : ∀ {m n} → ¬ m ≤ n → n ≤ m
≰→≥ p = ≤-trans (≤-step ≤-refl) (≰→> p)

-- If m is less than or equal to n, but not equal to n, then m is
-- strictly less than n.

≤≢→< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤≢→< (≤-refl′ eq)     m≢m   = ⊥-elim (m≢m eq)
≤≢→< (≤-step′ m≤n eq) m≢1+n = subst (_ <_) eq (suc≤suc m≤n)

-- If m is less than or equal to n, then m is strictly less than n or
-- equal to n.

≤→<⊎≡ : ∀ {m n} → m ≤ n → m < n ⊎ m ≡ n
≤→<⊎≡         (≤-refl′ m≡n)               = inj₂ m≡n
≤→<⊎≡ {m} {n} (≤-step′ {k = k} m≤k 1+k≡n) = inj₁ (
  suc m  ≤⟨ suc≤suc m≤k ⟩
  suc k  ≡⟨ 1+k≡n ⟩≤
  n      ∎≤)

-- _≤_ is total.

total : ∀ m n → m ≤ n ⊎ n ≤ m
total m n = ⊎-map id ≰→≥ (m ≤? n)

-- A variant of total.

infix 4 _≤⊎>_

_≤⊎>_ : ∀ m n → m ≤ n ⊎ n < m
m ≤⊎> n = ⊎-map id ≰→> (m ≤? n)

-- Another variant of total.

infix 4 _<⊎≡⊎>_

_<⊎≡⊎>_ : ∀ m n → m < n ⊎ m ≡ n ⊎ n < m
m <⊎≡⊎> n = case m ≤⊎> n of λ where
  (inj₂ n<m) → inj₂ (inj₂ n<m)
  (inj₁ m≤n) → ⊎-map id inj₁ (≤→<⊎≡ m≤n)

-- A number is not strictly greater than a smaller (strictly or not)
-- number.

+≮ : ∀ m {n} → ¬ m + n < n
+≮ m {n}     (≤-refl′ q)           = ≢1+ n (n            ≡⟨ sym q ⟩
                                            suc (m + n)  ≡⟨ cong suc (+-comm m) ⟩∎
                                            suc (n + m)  ∎)
+≮ m {zero}  (≤-step′ {k = k} p q) = 0≢+ (0      ≡⟨ sym q ⟩∎
                                          suc k  ∎)
+≮ m {suc n} (≤-step′ {k = k} p q) = +≮ m {n} (suc m + n  ≡⟨ suc+≡+suc m ⟩≤
                                               m + suc n  <⟨ p ⟩
                                               k          ≡⟨ cancel-suc q ⟩≤
                                               n          ∎≤)

-- No number is strictly less than zero.

≮0 : ∀ n → ¬ n < zero
≮0 n = +≮ n ∘ subst (_< 0) (sym +-right-identity)

-- _<_ is irreflexive.

<-irreflexive : ∀ {n} → ¬ n < n
<-irreflexive = +≮ 0

-- If m is strictly less than n, then m is not equal to n.

<→≢ : ∀ {m n} → m < n → m ≢ n
<→≢ m<n m≡n = <-irreflexive (subst (_< _) m≡n m<n)

-- Antisymmetry.

≤-antisymmetric : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisymmetric         (≤-refl′ q₁)             _                        = q₁
≤-antisymmetric         _                        (≤-refl′ q₂)             = sym q₂
≤-antisymmetric {m} {n} (≤-step′ {k = k₁} p₁ q₁) (≤-step′ {k = k₂} p₂ q₂) =
  ⊥-elim (<-irreflexive (
    suc k₁  ≡⟨ q₁ ⟩≤
    n       ≤⟨ p₂ ⟩
    k₂      <⟨⟩
    suc k₂  ≡⟨ q₂ ⟩≤
    m       ≤⟨ p₁ ⟩
    k₁      ∎≤))

-- If n is less than or equal to pred n, then n is equal to zero.

≤pred→≡zero : ∀ {n} → n ≤ pred n → n ≡ zero
≤pred→≡zero {zero}  _   = refl _
≤pred→≡zero {suc n} n<n = ⊥-elim (+≮ 0 n<n)

-- The pred function is monotone.

pred-mono : ∀ {m n} → m ≤ n → pred m ≤ pred n
pred-mono         (≤-refl′ m≡n)               = ≤-refl′ (cong pred m≡n)
pred-mono {m} {n} (≤-step′ {k = k} m≤k 1+k≡n) =
  pred m  ≤⟨ pred-mono m≤k ⟩
  pred k  ≤⟨ pred≤ _ ⟩
  k       ≡⟨ cong pred 1+k≡n ⟩≤
  pred n  ∎≤

-- _+_ is monotone.

infixl 6 _+-mono_

_+-mono_ : ∀ {m₁ m₂ n₁ n₂} → m₁ ≤ m₂ → n₁ ≤ n₂ → m₁ + n₁ ≤ m₂ + n₂
_+-mono_ {m₁} {m₂} {n₁} {n₂} (≤-refl′ eq) q =
  m₁ + n₁  ≡⟨ cong (_+ _) eq ⟩≤
  m₂ + n₁  ≤⟨ lemma m₂ q ⟩∎
  m₂ + n₂  ∎≤
  where
  lemma : ∀ m {n k} → n ≤ k → m + n ≤ m + k
  lemma zero    p = p
  lemma (suc m) p = suc≤suc (lemma m p)
_+-mono_ {m₁} {m₂} {n₁} {n₂} (≤-step′ {k = k} p eq) q =
  m₁ + n₁     ≤⟨ p +-mono q ⟩
  k + n₂      ≤⟨ ≤-step (_ ∎≤) ⟩
  suc k + n₂  ≡⟨ cong (_+ _) eq ⟩≤
  m₂ + n₂     ∎≤

-- An eliminator corresponding to well-founded induction.

well-founded-elim :
  ∀ {p}
  (P : ℕ → Set p) →
  (∀ m → (∀ {n} → n < m → P n) → P m) →
  ∀ m → P m
well-founded-elim P p m = helper (suc m) ≤-refl
  where
  helper : ∀ m {n} → n < m → P n
  helper zero    n<0                           = ⊥-elim (≮0 _ n<0)
  helper (suc m) (≤-step′ {k = k} n<k 1+k≡1+m) =
    helper m (subst (_ <_) (cancel-suc 1+k≡1+m) n<k)
  helper (suc m) (≤-refl′ 1+n≡1+m) =
    subst P (sym (cancel-suc 1+n≡1+m)) (p m (helper m))

-- The accessibility relation for _<_.

data Acc (n : ℕ) : Set where
  acc : (∀ {m} → m < n → Acc m) → Acc n

-- Every natural number is accessible.

accessible : ∀ n → Acc n
accessible = well-founded-elim _ λ _ → acc

------------------------------------------------------------------------
-- An alternative definition of the ordering

-- The following ordering can be used to define a function by
-- recursion up to some bound (see the example below).

infix 4 _≤↑_

data _≤↑_ (m n : ℕ) : Set where
  ≤↑-refl : m ≡ n → m ≤↑ n
  ≤↑-step : suc m ≤↑ n → m ≤↑ n

-- The successor function preserves _≤↑_.

suc≤↑suc : ∀ {m n} → m ≤↑ n → suc m ≤↑ suc n
suc≤↑suc (≤↑-refl m≡n)    = ≤↑-refl (cong suc m≡n)
suc≤↑suc (≤↑-step 1+m≤↑n) = ≤↑-step (suc≤↑suc 1+m≤↑n)

-- Functions that convert between _≤_ and _≤↑_.

≤→≤↑ : ∀ {m n} → m ≤ n → m ≤↑ n
≤→≤↑ (≤-refl′ m≡n)               = ≤↑-refl m≡n
≤→≤↑ (≤-step′ {k = k} m≤k 1+k≡n) =
  subst (_ ≤↑_) 1+k≡n (≤↑-step (suc≤↑suc (≤→≤↑ m≤k)))

≤↑→≤ : ∀ {m n} → m ≤↑ n → m ≤ n
≤↑→≤ (≤↑-refl m≡n)    = ≤-refl′ m≡n
≤↑→≤ (≤↑-step 1+m≤↑n) = <→≤ (≤↑→≤ 1+m≤↑n)

private

  -- An example: The list up-to n consists of all natural numbers from
  -- 0 to n, inclusive.

  up-to : ℕ → List ℕ
  up-to bound = helper 0 (≤→≤↑ (zero≤ bound))
    where
    helper : ∀ n → n ≤↑ bound → List ℕ
    helper n (≤↑-refl _) = n ∷ []
    helper n (≤↑-step p) = n ∷ helper _ p

-- An eliminator wrapping up the technique used in the example above.

up-to-elim :
  ∀ {p}
  (P : ℕ → Set p) →
  ∀ n →
  P n →
  (∀ m → m < n → P (suc m) → P m) →
  P 0
up-to-elim P n Pn P<n = helper 0 (≤→≤↑ (zero≤ n))
  where
  helper : ∀ m → m ≤↑ n → P m
  helper m (≤↑-refl m≡n) = subst P (sym m≡n) Pn
  helper m (≤↑-step m<n) = P<n m (≤↑→≤ m<n) (helper (suc m) m<n)

private

  -- The example, expressed using the eliminator.

  up-to′ : ℕ → List ℕ
  up-to′ bound =
    up-to-elim (const _) bound (bound ∷ []) (λ n _ → n ∷_)

------------------------------------------------------------------------
-- Another alternative definition of the ordering

-- This ordering relation is defined by recursion on the numbers.

infix 4 _≤→_

_≤→_ : ℕ → ℕ → Set
zero  ≤→ _     = ⊤
suc m ≤→ zero  = ⊥
suc m ≤→ suc n = m ≤→ n

-- Functions that convert between _≤_ and _≤→_.

≤→≤→ : ∀ m n → m ≤ n → m ≤→ n
≤→≤→ zero    _       _ = _
≤→≤→ (suc m) zero    p = ≮0 _ p
≤→≤→ (suc m) (suc n) p = ≤→≤→ m n (suc≤suc⁻¹ p)

≤→→≤ : ∀ m n → m ≤→ n → m ≤ n
≤→→≤ zero    n       _  = zero≤ n
≤→→≤ (suc m) zero    ()
≤→→≤ (suc m) (suc n) p  = suc≤suc (≤→→≤ m n p)

------------------------------------------------------------------------
-- Properties related to _∸_

-- Zero is a left zero of truncated subtraction.

∸-left-zero : ∀ n → 0 ∸ n ≡ 0
∸-left-zero zero    = refl _
∸-left-zero (suc _) = refl _

-- A form of associativity for _∸_.

∸-∸-assoc : ∀ {m} n {k} → (m ∸ n) ∸ k ≡ m ∸ (n + k)
∸-∸-assoc         zero            = refl _
∸-∸-assoc {zero}  (suc _) {zero}  = refl _
∸-∸-assoc {zero}  (suc _) {suc _} = refl _
∸-∸-assoc {suc _} (suc n)         = ∸-∸-assoc n

-- A limited form of associativity for _+_ and _∸_.

+-∸-assoc : ∀ {m n k} → k ≤ n → (m + n) ∸ k ≡ m + (n ∸ k)
+-∸-assoc {m} {n} {zero} _ =
  m + n ∸ 0    ≡⟨⟩
  m + n        ≡⟨⟩
  m + (n ∸ 0)  ∎
+-∸-assoc {m} {zero}  {suc k} <0      = ⊥-elim (≮0 _ <0)
+-∸-assoc {m} {suc n} {suc k} 1+k≤1+n =
  m + suc n ∸ suc k    ≡⟨ cong (_∸ suc k) (sym (suc+≡+suc m)) ⟩
  suc m + n ∸ suc k    ≡⟨⟩
  m + n ∸ k            ≡⟨ +-∸-assoc (suc≤suc⁻¹ 1+k≤1+n) ⟩
  m + (n ∸ k)          ≡⟨⟩
  m + (suc n ∸ suc k)  ∎

-- A special case of +-∸-assoc.

∸≡suc∸suc : ∀ {m n} → n < m → m ∸ n ≡ suc (m ∸ suc n)
∸≡suc∸suc = +-∸-assoc

-- If you add a number and then subtract it again, then you get back
-- what you started with.

+∸≡ : ∀ {m} n → (m + n) ∸ n ≡ m
+∸≡ {m} zero =
  m + 0  ≡⟨ +-right-identity ⟩∎
  m      ∎
+∸≡ {zero}  (suc n) = +∸≡ n
+∸≡ {suc m} (suc n) =
  m + suc n ∸ n  ≡⟨ cong (_∸ n) (sym (suc+≡+suc m))  ⟩
  suc m + n ∸ n  ≡⟨ +∸≡ n ⟩∎
  suc m          ∎

-- If you subtract a number from itself, then the answer is zero.

∸≡0 : ∀ n → n ∸ n ≡ 0
∸≡0 = +∸≡

-- If you subtract a number and then add it again, then you get back
-- what you started with if the number is less than or equal to the
-- number that you started with.

∸+≡ : ∀ {m n} → n ≤ m → (m ∸ n) + n ≡ m
∸+≡ {m} {n} (≤-refl′ n≡m) =
  (m ∸ n) + n  ≡⟨ cong (λ n → m ∸ n + n) n≡m ⟩
  (m ∸ m) + m  ≡⟨ cong (_+ m) (∸≡0 m) ⟩
  0 + m        ≡⟨⟩
  m            ∎
∸+≡ {m} {n} (≤-step′ {k = k} n≤k 1+k≡m) =
  (m ∸ n) + n        ≡⟨ cong (λ m → m ∸ n + n) (sym 1+k≡m) ⟩
  (1 + k ∸ n) + n    ≡⟨ cong (_+ n) (∸≡suc∸suc (suc≤suc n≤k)) ⟩
  1 + ((k ∸ n) + n)  ≡⟨ cong (1 +_) (∸+≡ n≤k) ⟩
  1 + k              ≡⟨ 1+k≡m ⟩∎
  m                  ∎

-- If you subtract a number and then add it again, then you get
-- something that is greater than or equal to what you started with.

≤∸+ : ∀ m n → m ≤ (m ∸ n) + n
≤∸+ m zero =
  m      ≡⟨ sym +-right-identity ⟩≤
  m + 0  ∎≤
≤∸+ zero    (suc n) = zero≤ _
≤∸+ (suc m) (suc n) =
  suc m            ≤⟨ suc≤suc (≤∸+ m n) ⟩
  suc (m ∸ n + n)  ≡⟨ suc+≡+suc _ ⟩≤
  m ∸ n + suc n    ∎≤

-- If you subtract something from a number you get a number that is
-- less than or equal to the one you started with.

∸≤ : ∀ m n → m ∸ n ≤ m
∸≤ _       zero    = ≤-refl
∸≤ zero    (suc _) = ≤-refl
∸≤ (suc m) (suc n) = ≤-step (∸≤ m n)

-- _∸_ is monotone in its first argument and antitone in its second
-- argument.

infixl 6 _∸-mono_

_∸-mono_ : ∀ {m₁ m₂ n₁ n₂} → m₁ ≤ m₂ → n₂ ≤ n₁ → m₁ ∸ n₁ ≤ m₂ ∸ n₂
_∸-mono_              {n₁ = zero}   {zero}  p _ = p
_∸-mono_              {n₁ = zero}   {suc _} _ q = ⊥-elim (≮0 _ q)
_∸-mono_ {zero}       {n₁ = suc n₁}         _ _ = zero≤ _
_∸-mono_ {suc _}  {zero}   {suc _}          p _ = ⊥-elim (≮0 _ p)
_∸-mono_ {suc m₁} {suc m₂} {suc n₁} {zero}  p _ = m₁ ∸ n₁  ≤⟨ ∸≤ _ n₁ ⟩
                                                  m₁       ≤⟨ pred≤ _ ⟩
                                                  suc m₁   ≤⟨ p ⟩∎
                                                  suc m₂   ∎≤
_∸-mono_ {suc _}  {suc _}  {suc _}  {suc _} p q =
  suc≤suc⁻¹ p ∸-mono suc≤suc⁻¹ q

-- The predecessor function can be expressed using _∸_.

pred≡∸1 : ∀ n → pred n ≡ n ∸ 1
pred≡∸1 zero    = refl _
pred≡∸1 (suc _) = refl _

------------------------------------------------------------------------
-- Minimum and maximum

-- Minimum.

min : ℕ → ℕ → ℕ
min zero    n       = zero
min m       zero    = zero
min (suc m) (suc n) = suc (min m n)

-- Maximum.

max : ℕ → ℕ → ℕ
max zero    n       = n
max m       zero    = m
max (suc m) (suc n) = suc (max m n)

-- The min operation can be expressed using repeated truncated
-- subtraction.

min≡∸∸ : ∀ m n → min m n ≡ m ∸ (m ∸ n)
min≡∸∸ zero n =
  0            ≡⟨ sym (∸-left-zero (0 ∸ n)) ⟩∎
  0 ∸ (0 ∸ n)  ∎
min≡∸∸ (suc m) zero =
  0      ≡⟨ sym (∸≡0 m) ⟩∎
  m ∸ m  ∎
min≡∸∸ (suc m) (suc n) =
  suc (min m n)      ≡⟨ cong suc (min≡∸∸ m n) ⟩
  suc (m ∸ (m ∸ n))  ≡⟨ sym (+-∸-assoc (∸≤ _ n)) ⟩∎
  suc m ∸ (m ∸ n)    ∎

-- The max operation can be expressed using addition and truncated
-- subtraction.

max≡+∸ : ∀ m n → max m n ≡ m + (n ∸ m)
max≡+∸ zero    _       = refl _
max≡+∸ (suc m) zero    = suc m        ≡⟨ cong suc (sym +-right-identity) ⟩∎
                         suc (m + 0)  ∎
max≡+∸ (suc m) (suc n) = cong suc (max≡+∸ m n)

-- Given two numbers one is the minimum and the other is the maximum.

min-and-max :
  ∀ m n → min m n ≡ m × max m n ≡ n ⊎ min m n ≡ n × max m n ≡ m
min-and-max zero    _       = inj₁ (refl _ , refl _)
min-and-max (suc _) zero    = inj₂ (refl _ , refl _)
min-and-max (suc m) (suc n) =
  ⊎-map (Σ-map (cong suc) (cong suc))
        (Σ-map (cong suc) (cong suc))
        (min-and-max m n)

-- The min operation is idempotent.

min-idempotent : ∀ n → min n n ≡ n
min-idempotent n = case min-and-max n n of [ proj₁ , proj₁ ]

-- The max operation is idempotent.

max-idempotent : ∀ n → max n n ≡ n
max-idempotent n = case min-and-max n n of [ proj₂ , proj₂ ]

-- The min operation is commutative.

min-comm : ∀ m n → min m n ≡ min n m
min-comm zero    zero    = refl _
min-comm zero    (suc _) = refl _
min-comm (suc _) zero    = refl _
min-comm (suc m) (suc n) = cong suc (min-comm m n)

-- The max operation is commutative.

max-comm : ∀ m n → max m n ≡ max n m
max-comm zero    zero    = refl _
max-comm zero    (suc _) = refl _
max-comm (suc _) zero    = refl _
max-comm (suc m) (suc n) = cong suc (max-comm m n)

-- The minimum is less than or equal to both arguments.

min≤ˡ : ∀ m n → min m n ≤ m
min≤ˡ zero    _       = ≤-refl
min≤ˡ (suc _) zero    = zero≤ _
min≤ˡ (suc m) (suc n) = suc≤suc (min≤ˡ m n)

min≤ʳ : ∀ m n → min m n ≤ n
min≤ʳ m n =
  min m n  ≡⟨ min-comm _ _ ⟩≤
  min n m  ≤⟨ min≤ˡ _ _ ⟩∎
  n        ∎≤

-- The maximum is greater than or equal to both arguments.

ˡ≤max : ∀ m n → m ≤ max m n
ˡ≤max zero    _       = zero≤ _
ˡ≤max (suc _) zero    = ≤-refl
ˡ≤max (suc m) (suc n) = suc≤suc (ˡ≤max m n)

ʳ≤max : ∀ m n → n ≤ max m n
ʳ≤max m n =
  n        ≤⟨ ˡ≤max _ _ ⟩
  max n m  ≡⟨ max-comm n _ ⟩≤
  max m n  ∎≤

------------------------------------------------------------------------
-- Division by two

-- Division by two, rounded upwards.

⌈_/2⌉ : ℕ → ℕ
⌈ zero        /2⌉ = zero
⌈ suc zero    /2⌉ = suc zero
⌈ suc (suc n) /2⌉ = suc ⌈ n /2⌉

-- Division by two, rounded downwards.

⌊_/2⌋ : ℕ → ℕ
⌊ zero        /2⌋ = zero
⌊ suc zero    /2⌋ = zero
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

-- Some simple lemmas related to division by two.

⌈/2⌉+⌊/2⌋ : ∀ n → ⌈ n /2⌉ + ⌊ n /2⌋ ≡ n
⌈/2⌉+⌊/2⌋ zero          = refl _
⌈/2⌉+⌊/2⌋ (suc zero)    = refl _
⌈/2⌉+⌊/2⌋ (suc (suc n)) =
  suc ⌈ n /2⌉ + suc ⌊ n /2⌋      ≡⟨ cong suc (sym (suc+≡+suc _)) ⟩
  suc (suc (⌈ n /2⌉ + ⌊ n /2⌋))  ≡⟨ cong (suc ∘ suc) (⌈/2⌉+⌊/2⌋ n) ⟩∎
  suc (suc n)                    ∎

⌊/2⌋≤⌈/2⌉ : ∀ n → ⌊ n /2⌋ ≤ ⌈ n /2⌉
⌊/2⌋≤⌈/2⌉ zero          = ≤-refl
⌊/2⌋≤⌈/2⌉ (suc zero)    = zero≤ 1
⌊/2⌋≤⌈/2⌉ (suc (suc n)) = suc≤suc (⌊/2⌋≤⌈/2⌉ n)

⌈/2⌉≤ : ∀ n → ⌈ n /2⌉ ≤ n
⌈/2⌉≤ zero          = ≤-refl
⌈/2⌉≤ (suc zero)    = ≤-refl
⌈/2⌉≤ (suc (suc n)) =
  suc ⌈ n /2⌉  ≤⟨ suc≤suc (⌈/2⌉≤ n) ⟩
  suc n        ≤⟨ m≤n+m _ 1 ⟩∎
  suc (suc n)  ∎≤

⌈/2⌉< : ∀ n → ⌈ 2 + n /2⌉ < 2 + n
⌈/2⌉< n =
  2 + ⌈ n /2⌉  ≤⟨ ≤-refl +-mono ⌈/2⌉≤ n ⟩∎
  2 + n        ∎≤

⌊/2⌋< : ∀ n → ⌊ 1 + n /2⌋ < 1 + n
⌊/2⌋< zero    = ≤-refl
⌊/2⌋< (suc n) =
  2 + ⌊ n /2⌋  ≤⟨ ≤-refl +-mono ⌊/2⌋≤⌈/2⌉ n ⟩
  2 + ⌈ n /2⌉  ≤⟨ ⌈/2⌉< n ⟩∎
  2 + n        ∎≤
