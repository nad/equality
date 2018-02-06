------------------------------------------------------------------------
-- Some definitions related to and properties of natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Nat
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

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

_≟_ : Decidable-equality ℕ
zero  ≟ zero  = yes (refl _)
suc m ≟ suc n = ⊎-map (cong suc) (λ m≢n → m≢n ∘ cancel-suc) (m ≟ n)
zero  ≟ suc n = no 0≢+
suc m ≟ zero  = no (0≢+ ∘ sym)

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
  m      ≤⟨ ≤-step ≤-refl ⟩
  suc m  ≤⟨ m<n ⟩
  n      ≤⟨ n≤o ⟩∎
  o      ∎≤

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

-- A decision procedure for _≤_.

infix 4 _≤?_

_≤?_ : Decidable _≤_
zero  ≤? n     = inj₁ (zero≤ n)
suc m ≤? zero  = inj₂ λ { (≤-refl′ eq)   → 0≢+ (sym eq)
                        ; (≤-step′ _ eq) → 0≢+ (sym eq)
                        }
suc m ≤? suc n = ⊎-map suc≤suc (λ m≰n → m≰n ∘ suc≤suc⁻¹) (m ≤? n)

-- If m is not smaller than or equal to n, then n is strictly smaller
-- than m.

≰→> : ∀ {m n} → ¬ m ≤ n → n < m
≰→> {zero}  {n}     p = ⊥-elim (p (zero≤ n))
≰→> {suc m} {zero}  p = suc≤suc (zero≤ m)
≰→> {suc m} {suc n} p = suc≤suc (≰→> (p ∘ suc≤suc))

-- If m is not smaller than or equal to n, then n is smaller than or
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

≤⊎> : ∀ m n → m ≤ n ⊎ n < m
≤⊎> m n = ⊎-map id ≰→> (m ≤? n)

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

-- No number is strictly smaller than zero.

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

------------------------------------------------------------------------
-- Properties related to _∸_

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
