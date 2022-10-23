------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Integer {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude as P hiding (suc) renaming (_+_ to _⊕_; _*_ to _⊛_)

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq hiding (_∘_)
open import Group eq using (Group; Abelian)
open import H-level eq
open import H-level.Closure eq
import Nat eq as Nat

open import Integer.Basics eq public

private
  variable
    i j : ℤ

------------------------------------------------------------------------
-- Some lemmas

-- The sum of i and - i is zero.

+-right-inverse : ∀ i → i + - i ≡ + 0
+-right-inverse = λ where
    (+ zero)    → refl _
    (+ P.suc n) → lemma n
    -[1+ n ]    → lemma n
  where
  lemma : ∀ n → + P.suc n +-[1+ n ] ≡ + 0
  lemma n
    with P.suc n Nat.<= n | T[<=]↔≤ {m = P.suc n} {n = n}
  … | false | _  = cong (+_) $ Nat.∸≡0 n
  … | true  | eq = ⊥-elim $ Nat.<-irreflexive (_↔_.to eq _)

-- The sum of - i and i is zero.

+-left-inverse : ∀ i → - i + i ≡ + 0
+-left-inverse i =
  - i + i  ≡⟨ +-comm (- i) ⟩
  i + - i  ≡⟨ +-right-inverse i ⟩∎
  + 0      ∎

-- + 0 is a left identity for addition.

+-left-identity : + 0 + i ≡ i
+-left-identity {i = + _}      = refl _
+-left-identity {i = -[1+ _ ]} = refl _

-- + 0 is a right identity for addition.

+-right-identity : i + + 0 ≡ i
+-right-identity {i = + _}      = cong (+_) Nat.+-right-identity
+-right-identity {i = -[1+ _ ]} = refl _

-- Addition is associative.

+-assoc : ∀ i {j k} → i + (j + k) ≡ (i + j) + k
+-assoc = λ where
    (+ m) {j = + _} {k = + _} →
      cong (+_) $ Nat.+-assoc m
    -[1+ m ] {j = -[1+ n ]} {k = -[1+ o ]} →
      cong (-[1+_] ∘ P.suc)
        (m ⊕ P.suc (n ⊕ o)  ≡⟨ sym $ Nat.suc+≡+suc m ⟩
         P.suc m ⊕ (n ⊕ o)  ≡⟨ Nat.+-assoc (P.suc m) ⟩∎
         (P.suc m ⊕ n) ⊕ o  ∎)
    -[1+ m ] {j = + n} {k = + o} →
      sym $ ++-[1+]++ _ n _
    (+ m) {j = -[1+ n ]} {k = -[1+ o ]} →
      sym $ ++-[1+]+-[1+] m _ _
    (+ m) {j = + n} {k = -[1+ o ]} →
      lemma₁ m _ _
    (+ m) {j = -[1+ n ]} {k = + o} →
      lemma₂ m _ _
    -[1+ m ] {j = -[1+ n ]} {k = + o} →
      lemma₃ _ o _
    -[1+ m ] {j = + n} {k = -[1+ o ]} →
      lemma₄ _ n _
  where
  ++-[1+]++ : ∀ m n o → + n +-[1+ m ] + + o ≡ (+ (n ⊕ o) +-[1+ m ])
  ++-[1+]++ m         zero      o = refl _
  ++-[1+]++ zero      (P.suc n) o = refl _
  ++-[1+]++ (P.suc m) (P.suc n) o = ++-[1+]++ m n o

  ++-[1+]+-[1+] :
    ∀ m n o → + m +-[1+ n ] + -[1+ o ] ≡ (+ m +-[1+ 1 ⊕ n ⊕ o ])
  ++-[1+]+-[1+] zero      n         o = refl _
  ++-[1+]+-[1+] (P.suc m) zero      o = refl _
  ++-[1+]+-[1+] (P.suc m) (P.suc n) o = ++-[1+]+-[1+] m n o

  lemma₁ : ∀ m n o → + m + (+ n +-[1+ o ]) ≡ (+ m ⊕ n +-[1+ o ])
  lemma₁ m n o =
    + m + (+ n +-[1+ o ])  ≡⟨ +-comm (+ m) {j = + n +-[1+ o ]} ⟩
    (+ n +-[1+ o ]) + + m  ≡⟨ ++-[1+]++ _ n _ ⟩
    (+ n ⊕ m +-[1+ o ])    ≡⟨ cong +_+-[1+ o ] $ Nat.+-comm n ⟩∎
    (+ m ⊕ n +-[1+ o ])    ∎

  lemma₂ : ∀ m n o → + m + (+ n +-[1+ o ]) ≡ (+ m +-[1+ o ]) + + n
  lemma₂ m n o =
    + m + (+ n +-[1+ o ])  ≡⟨ lemma₁ m n o ⟩
    (+ m ⊕ n +-[1+ o ])    ≡⟨ sym $ ++-[1+]++ _ m _ ⟩∎
    (+ m +-[1+ o ]) + + n  ∎

  lemma₃ :
    ∀ m n o → -[1+ m ] + (+ n +-[1+ o ]) ≡ (+ n +-[1+ 1 ⊕ m ⊕ o ])
  lemma₃ m n o =
    -[1+ m ] + (+ n +-[1+ o ])  ≡⟨ +-comm -[1+ m ] {j = + n +-[1+ o ]} ⟩
    (+ n +-[1+ o ]) + -[1+ m ]  ≡⟨ ++-[1+]+-[1+] n o m ⟩
    (+ n +-[1+ 1 ⊕ o ⊕ m ])     ≡⟨ cong + n +-[1+_] $ cong (1 ⊕_) $ Nat.+-comm o ⟩∎
    (+ n +-[1+ 1 ⊕ m ⊕ o ])     ∎

  lemma₄ :
    ∀ m n o → -[1+ m ] + (+ n +-[1+ o ]) ≡ (+ n +-[1+ m ]) + -[1+ o ]
  lemma₄ m n o =
    -[1+ m ] + (+ n +-[1+ o ])  ≡⟨ lemma₃ m n o ⟩
    (+ n +-[1+ 1 ⊕ m ⊕ o ])     ≡⟨ sym $ ++-[1+]+-[1+] n _ _ ⟩∎
    (+ n +-[1+ m ]) + -[1+ o ]  ∎

------------------------------------------------------------------------
-- Successor and predecessor

-- The successor function.

suc : ℤ → ℤ
suc (+ n)          = + P.suc n
suc -[1+ zero ]    = + zero
suc -[1+ P.suc n ] = -[1+ n ]

-- The successor function adds one to its input.

suc≡1+ : ∀ i → suc i ≡ + 1 + i
suc≡1+ (+ _)          = refl _
suc≡1+ -[1+ zero ]    = refl _
suc≡1+ -[1+ P.suc _ ] = refl _

-- The predecessor function.

pred : ℤ → ℤ
pred (+ zero)    = -[1+ zero ]
pred (+ P.suc n) = + n
pred -[1+ n ]    = -[1+ P.suc n ]

-- The predecessor function adds minus one to its input.

pred≡-1+ : ∀ i → pred i ≡ -[ 1 ] + i
pred≡-1+ (+ zero)    = refl _
pred≡-1+ (+ P.suc _) = refl _
pred≡-1+ -[1+ _ ]    = refl _

-- An equivalence between ℤ and ℤ corresponding to the successor
-- function.

successor : ℤ ≃ ℤ
successor = Eq.↔→≃ suc pred suc-pred pred-suc
  where
  suc-pred : ∀ i → suc (pred i) ≡ i
  suc-pred (+ zero)    = refl _
  suc-pred (+ P.suc _) = refl _
  suc-pred -[1+ _ ]    = refl _

  pred-suc : ∀ i → pred (suc i) ≡ i
  pred-suc (+ _)          = refl _
  pred-suc -[1+ zero ]    = refl _
  pred-suc -[1+ P.suc _ ] = refl _

------------------------------------------------------------------------
-- Positive, negative

-- The property of being positive.

Positive : ℤ → Type
Positive (+ zero)    = ⊥
Positive (+ P.suc _) = ⊤
Positive -[1+ _ ]    = ⊥

-- Positive is propositional.

Positive-propositional : Is-proposition (Positive i)
Positive-propositional {i = + zero}    = ⊥-propositional
Positive-propositional {i = + P.suc _} = mono₁ 0 ⊤-contractible
Positive-propositional {i = -[1+ _ ]}  = ⊥-propositional

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
¬+0 {i = + zero}    pos _  = pos
¬+0 {i = + P.suc _} _   ≡0 = Nat.0≢+ $ sym $ +-cancellative ≡0
¬+0 {i = -[1+ _ ]}  pos _  = pos

-- No integer is both negative and equal to zero.

¬-0 : Negative i → i ≡ + 0 → ⊥₀
¬-0 {i = + _}      neg _  = neg
¬-0 {i = -[1+ _ ]} _   ≡0 = +≢-[1+] $ sym ≡0

-- One can decide if an integer is negative, zero or positive.

-⊎0⊎+ : ∀ i → Negative i ⊎ i ≡ + 0 ⊎ Positive i
-⊎0⊎+ (+ zero)    = inj₂ (inj₁ (refl _))
-⊎0⊎+ (+ P.suc _) = inj₂ (inj₂ _)
-⊎0⊎+ -[1+ _ ]    = inj₁ _

-- If i and j are positive, then i + j is positive.

>0→>0→+>0 : ∀ i j → Positive i → Positive j → Positive (i + j)
>0→>0→+>0 (+ P.suc _) (+ P.suc _) _ _ = _

-- If i and j are negative, then i + j is negative.

<0→<0→+<0 : ∀ i j → Negative i → Negative j → Negative (i + j)
<0→<0→+<0 -[1+ _ ] -[1+ _ ] _ _ = _

------------------------------------------------------------------------
-- The group of integers

-- The group of integers.

ℤ-group : Group lzero
ℤ-group .Group.Carrier          = ℤ
ℤ-group .Group.Carrier-is-set   = ℤ-set
ℤ-group .Group._∘_              = _+_
ℤ-group .Group.id               = + 0
ℤ-group .Group._⁻¹              = -_
ℤ-group .Group.left-identity _  = +-left-identity
ℤ-group .Group.right-identity _ = +-right-identity
ℤ-group .Group.assoc i _ _      = +-assoc i
ℤ-group .Group.right-inverse    = +-right-inverse
ℤ-group .Group.left-inverse     = +-left-inverse

-- The group of integers is abelian.

ℤ-abelian : Abelian ℤ-group
ℤ-abelian i _ = +-comm i

private
  module ℤG = Group ℤ-group
open ℤG public
  using ()
  renaming (_^+_ to infixl 7 _*+_;
            _^_  to infixl 7 _*_)

-- + 1 is a left identity for multiplication.

*-left-identity : ∀ i → + 1 * i ≡ i
*-left-identity = lemma
  where
  +lemma : ∀ n → + 1 *+ n ≡ + n
  +lemma zero      = refl _
  +lemma (P.suc n) =
    + 1 + (+ 1) *+ n  ≡⟨ cong (λ i → + 1 + i) $ +lemma n ⟩
    + 1 + + n         ≡⟨⟩
    + P.suc n         ∎

  -lemma : ∀ n → -[ 1 ] *+ n ≡ -[ n ]
  -lemma zero              = refl _
  -lemma (P.suc zero)      = refl _
  -lemma (P.suc (P.suc n)) =
    -[ 1 ] + -[ 1 ] *+ P.suc n  ≡⟨ cong (λ i → -[ 1 ] + i) $ -lemma (P.suc n) ⟩
    -[ 1 ] + -[ P.suc n ]       ≡⟨⟩
    -[ P.suc (P.suc n) ]        ∎

  lemma : ∀ i → + 1 * i ≡ i
  lemma (+ n)    = +lemma n
  lemma -[1+ n ] = -lemma (P.suc n)

-- _*+ n distributes over addition.

*+-distrib-+ : ∀ n → (i + j) *+ n ≡ i *+ n + j *+ n
*+-distrib-+ {i = i} n = ℤG.∘^+≡^+∘^+ (+-comm i) n

-- If a positive number is multiplied by a positive number, then
-- the result is positive.

>0→*+suc> : ∀ i m → Positive i → Positive (i *+ P.suc m)
>0→*+suc> i zero =
  Positive i          ↝⟨ subst Positive (sym $ ℤG.right-identity i) ⟩
  Positive (i + + 0)  ↔⟨⟩
  Positive (i *+ 1)   □
>0→*+suc> i (P.suc m) =
  Positive i                            ↝⟨ (λ p → p , >0→*+suc> i m p) ⟩
  Positive i × Positive (i *+ P.suc m)  ↝⟨ uncurry (>0→>0→+>0 i (i *+ P.suc m)) ⟩
  Positive (i + i *+ P.suc m)           ↔⟨⟩
  Positive (i *+ P.suc (P.suc m))       □

-- If a negative number is multiplied by a positive number, then
-- the result is negative.

<0→*+suc<0 : ∀ i m → Negative i → Negative (i *+ P.suc m)
<0→*+suc<0 i zero =
  Negative i          ↝⟨ subst Negative (sym $ ℤG.right-identity i) ⟩
  Negative (i + + 0)  ↔⟨⟩
  Negative (i *+ 1)   □
<0→*+suc<0 i (P.suc m) =
  Negative i                            ↝⟨ (λ p → p , <0→*+suc<0 i m p) ⟩
  Negative i × Negative (i *+ P.suc m)  ↝⟨ uncurry (<0→<0→+<0 i (i *+ P.suc m)) ⟩
  Negative (i + i *+ P.suc m)           ↔⟨⟩
  Negative (i *+ P.suc (P.suc m))       □

------------------------------------------------------------------------
-- Integer division by two

-- Division by two, rounded downwards.

⌊_/2⌋ : ℤ → ℤ
⌊ + n      /2⌋ = + Nat.⌊ n /2⌋
⌊ -[1+ n ] /2⌋ = -[ Nat.⌈ P.suc n /2⌉ ]

-- A kind of distributivity property for ⌊_/2⌋ and _+_.

⌊+*+2/2⌋≡ : ∀ i {j} → ⌊ i + j *+ 2 /2⌋ ≡ ⌊ i /2⌋ + j
⌊+*+2/2⌋≡ = λ where
    (+ m) {j = + n} → cong +_
      (Nat.⌊ m ⊕ 2 ⊛ n /2⌋  ≡⟨ cong Nat.⌊_/2⌋ $ Nat.+-comm m ⟩
       Nat.⌊ 2 ⊛ n ⊕ m /2⌋  ≡⟨ Nat.⌊2*+/2⌋≡ n ⟩
       n ⊕ Nat.⌊ m /2⌋      ≡⟨ Nat.+-comm n ⟩∎
       Nat.⌊ m /2⌋ ⊕ n      ∎)

    -[1+ zero ] {j = -[1+ n ]} → cong -[1+_]
      (Nat.⌈ P.suc (n ⊕ n) /2⌉            ≡⟨ cong (Nat.⌈_/2⌉ ∘ P.suc) $ ⊕-lemma n ⟩
       Nat.⌈ 1 ⊕ 2 ⊛ n /2⌉                ≡⟨ cong Nat.⌈_/2⌉ $ Nat.+-comm 1 ⟩
       Nat.⌈ 2 ⊛ n ⊕ 1 /2⌉                ≡⟨ Nat.⌈2*+/2⌉≡ n ⟩
       n ⊕ Nat.⌈ 1 /2⌉                    ≡⟨ Nat.+-comm n ⟩∎
       P.suc n                            ∎)

    -[1+ P.suc m ] {j = -[1+ n ]} → cong -[1+_]
      (Nat.⌈ P.suc m ⊕ P.suc (n ⊕ n) /2⌉  ≡⟨ cong (Nat.⌈_/2⌉ ∘ P.suc) $ sym $ Nat.suc+≡+suc m ⟩
       P.suc Nat.⌈ m ⊕ (n ⊕ n) /2⌉        ≡⟨ cong (P.suc ∘ Nat.⌈_/2⌉ ∘ (m ⊕_)) $ ⊕-lemma n ⟩
       P.suc Nat.⌈ m ⊕ 2 ⊛ n /2⌉          ≡⟨ cong (P.suc ∘ Nat.⌈_/2⌉) $ Nat.+-comm m ⟩
       P.suc Nat.⌈ 2 ⊛ n ⊕ m /2⌉          ≡⟨ cong P.suc $ Nat.⌈2*+/2⌉≡ n ⟩
       P.suc (n ⊕ Nat.⌈ m /2⌉)            ≡⟨ cong P.suc $ Nat.+-comm n ⟩∎
       P.suc (Nat.⌈ m /2⌉ ⊕ n)            ∎)

    (+ m) {j = -[1+ n ]} →
      ⌊ + m +-[1+ P.suc (n ⊕ n) ] /2⌋  ≡⟨ cong (λ n → ⌊ + m +-[1+ P.suc n ] /2⌋) $ ⊕-lemma n ⟩
      ⌊ + m +-[1+ P.suc (2 ⊛ n) ] /2⌋  ≡⟨ lemma₁ m n ⟩∎
      + Nat.⌊ m /2⌋ +-[1+ n ]          ∎

    -[1+ 0 ] {j = + 0} →
      -[ 1 ]  ≡⟨⟩
      -[ 1 ]  ∎

    -[1+ 0 ] {j = + P.suc n} → cong +_
      (Nat.⌊ n ⊕ P.suc (n ⊕ 0) /2⌋  ≡⟨ cong Nat.⌊_/2⌋ $ sym $ Nat.suc+≡+suc n ⟩
       Nat.⌊ 1 ⊕ 2 ⊛ n /2⌋          ≡⟨ Nat.⌊1+2*/2⌋≡ n ⟩∎
       n                            ∎)

    -[1+ P.suc m ] {j = + n} →
      ⌊ + 2 ⊛ n +-[1+ P.suc m ] /2⌋  ≡⟨ lemma₂ m n ⟩∎
      + n +-[1+ Nat.⌈ m /2⌉ ]        ∎
  where
  ⊕-lemma : ∀ n → n ⊕ n ≡ 2 ⊛ n
  ⊕-lemma n = cong (n ⊕_) $ sym Nat.+-right-identity

  lemma₁ :
    ∀ m n →
    ⌊ + m +-[1+ P.suc (2 ⊛ n) ] /2⌋ ≡
    + Nat.⌊ m /2⌋ +-[1+ n ]
  lemma₁ zero n = cong -[1+_]
    (Nat.⌈ 2 ⊛ n /2⌉  ≡⟨ Nat.⌈2*/2⌉≡ n ⟩∎
     n                ∎)
  lemma₁ (P.suc zero) n =
    -[ Nat.⌈ 1 ⊕ 2 ⊛ n /2⌉ ]  ≡⟨ cong -[_] $ Nat.⌈1+2*/2⌉≡ n ⟩∎
    -[1+ n ]                  ∎
  lemma₁ (P.suc (P.suc m)) zero =
    ⌊ + m /2⌋      ≡⟨⟩
    + Nat.⌊ m /2⌋  ∎
  lemma₁ (P.suc (P.suc m)) (P.suc n) =
    ⌊ + m +-[1+ n ⊕ P.suc (n ⊕ 0) ] /2⌋  ≡⟨ cong (⌊_/2⌋ ∘ + m +-[1+_]) $ sym $ Nat.suc+≡+suc n ⟩
    ⌊ + m +-[1+ P.suc (2 ⊛ n) ] /2⌋      ≡⟨ lemma₁ m n ⟩∎
    + Nat.⌊ m /2⌋ +-[1+ n ]              ∎

  mutual

    lemma₂ :
      ∀ m n →
      ⌊ + 2 ⊛ n +-[1+ P.suc m ] /2⌋ ≡
      + n +-[1+ Nat.⌈ m /2⌉ ]
    lemma₂ m zero =
      ⌊ -[1+ P.suc m ] /2⌋  ≡⟨⟩
      -[1+ Nat.⌈ m /2⌉ ]    ∎
    lemma₂ m (P.suc n) =
      ⌊ + n ⊕ P.suc (n ⊕ 0) +-[1+ m ] /2⌋  ≡⟨ cong (⌊_/2⌋ ∘ +_+-[1+ m ]) $ sym $ Nat.suc+≡+suc n ⟩
      ⌊ + P.suc (2 ⊛ n) +-[1+ m ] /2⌋      ≡⟨ lemma₃ m n ⟩∎
      + P.suc n +-[1+ Nat.⌈ m /2⌉ ]        ∎

    lemma₃ :
      ∀ m n →
      ⌊ + P.suc (2 ⊛ n) +-[1+ m ] /2⌋ ≡
      + P.suc n +-[1+ Nat.⌈ m /2⌉ ]
    lemma₃ zero n = cong +_
      (Nat.⌊ 2 ⊛ n /2⌋  ≡⟨ Nat.⌊2*/2⌋≡ n ⟩∎
       n                ∎)
    lemma₃ (P.suc zero) zero =
      -[ 1 ]  ≡⟨⟩
      -[ 1 ]  ∎
    lemma₃ (P.suc zero) (P.suc n) = cong +_
      (Nat.⌊ n ⊕ P.suc (n ⊕ zero) /2⌋  ≡⟨ cong Nat.⌊_/2⌋ $ sym $ Nat.suc+≡+suc n ⟩
       Nat.⌊ 1 ⊕ 2 ⊛ n /2⌋             ≡⟨ Nat.⌊1+2*/2⌋≡ n ⟩∎
       n                               ∎)
    lemma₃ (P.suc (P.suc m)) n =
      ⌊ + 2 ⊛ n +-[1+ P.suc m ] /2⌋  ≡⟨ lemma₂ m n ⟩∎
      + n +-[1+ Nat.⌈ m /2⌉ ]        ∎

-- If you double and then halve an integer, then you get back what you
-- started with.

⌊*+2/2⌋≡ : ∀ i → ⌊ i *+ 2 /2⌋ ≡ i
⌊*+2/2⌋≡ i =
  ⌊ i *+ 2 /2⌋        ≡⟨ cong ⌊_/2⌋ $ sym $ +-left-identity {i = i *+ 2} ⟩
  ⌊ + 0 + i *+ 2 /2⌋  ≡⟨ ⌊+*+2/2⌋≡ (+ 0) {j = i} ⟩
  ⌊ + 0 /2⌋ + i       ≡⟨⟩
  + 0 + i             ≡⟨ +-left-identity ⟩∎
  i                   ∎
