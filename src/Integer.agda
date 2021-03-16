------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Integer
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq hiding (elim)

import Agda.Builtin.Int

open import Prelude hiding (_^_) renaming (_+_ to _⊕_)

open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq hiding (id; _∘_)
open import Group eq as G
  using (Group; Generated-by; Cyclic; Abelian; _≃ᴳ_)
open import H-level eq
open import H-level.Closure eq
import Nat eq as Nat
open import Univalence-axiom eq

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

------------------------------------------------------------------------
-- The group of integers

-- The definition of ℤ-group is parametrised by a proof of
-- associativity of addition. Such a proof can be found in
-- Integer.Quotient.

module ℤ-group (+-assoc : ∀ i j k → i + (j + k) ≡ (i + j) + k) where

  -- The group of integers.

  ℤ-group : Group lzero
  ℤ-group .Group.Carrier        = ℤ
  ℤ-group .Group.Carrier-is-set = ℤ-set
  ℤ-group .Group._∘_            = _+_
  ℤ-group .Group.id             = + 0
  ℤ-group .Group._⁻¹            = -_
  ℤ-group .Group.left-identity  = λ where
    (+ _)    → refl _
    -[1+ _ ] → refl _
  ℤ-group .Group.right-identity = λ where
    (+ _)    → cong (+_) Nat.+-right-identity
    -[1+ _ ] → refl _
  ℤ-group .Group.assoc          = +-assoc
  ℤ-group .Group.right-inverse  = +-
  ℤ-group .Group.left-inverse i =
    - i + i  ≡⟨ +-comm (- i) ⟩
    i + - i  ≡⟨ +- i ⟩∎
    + 0      ∎

  private
    module G¹ = Group ℤ-group
  open G¹ using () renaming (_^+_ to infixl 7 _*+_)

  private

    -- If a positive number is multiplied by a positive number, then
    -- the result is positive.

    >0→>0→>0 : ∀ i m → Positive i → Positive (i *+ suc m)
    >0→>0→>0 i zero =
      Positive i          ↝⟨ subst Positive (sym $ G¹.right-identity i) ⟩
      Positive (i + + 0)  ↔⟨⟩
      Positive (i *+ 1)   □
    >0→>0→>0 i (suc m) =
      Positive i                          ↝⟨ (λ p → p , >0→>0→>0 i m p) ⟩
      Positive i × Positive (i *+ suc m)  ↝⟨ uncurry (>0→>0→+>0 i (i *+ suc m)) ⟩
      Positive (i + i *+ suc m)           ↔⟨⟩
      Positive (i *+ suc (suc m))         □

    -- If a negative number is multiplied by a positive number, then
    -- the result is negative.

    <0→>0→<0 : ∀ i m → Negative i → Negative (i *+ suc m)
    <0→>0→<0 i zero =
      Negative i          ↝⟨ subst Negative (sym $ G¹.right-identity i) ⟩
      Negative (i + + 0)  ↔⟨⟩
      Negative (i *+ 1)   □
    <0→>0→<0 i (suc m) =
      Negative i                          ↝⟨ (λ p → p , <0→>0→<0 i m p) ⟩
      Negative i × Negative (i *+ suc m)  ↝⟨ uncurry (<0→<0→+<0 i (i *+ suc m)) ⟩
      Negative (i + i *+ suc m)           ↔⟨⟩
      Negative (i *+ suc (suc m))         □

  -- The group of integers is generated by + 1.

  ℤ-generated-by-1 : Generated-by ℤ-group (+ 1)
  ℤ-generated-by-1 i = i , lemma i
    where
    open G¹

    +lemma : ∀ n → + n ≡ (+ 1) ^+ n
    +lemma zero    = refl _
    +lemma (suc n) =
      + suc n           ≡⟨⟩
      + 1 + + n         ≡⟨ cong (λ i → + 1 + i) $ +lemma n ⟩∎
      + 1 + (+ 1) ^+ n  ∎

    -lemma : ∀ n → -[ n ] ≡ -[ 1 ] ^+ n
    -lemma zero          = refl _
    -lemma (suc zero)    = refl _
    -lemma (suc (suc n)) =
      -[ suc (suc n) ]          ≡⟨⟩
      -[ 1 ] + -[ suc n ]       ≡⟨ cong (λ i → -[ 1 ] + i) $ -lemma (suc n) ⟩∎
      -[ 1 ] + -[ 1 ] ^+ suc n  ∎

    lemma : ∀ i → i ≡ (+ 1) ^ i
    lemma (+ n)    = +lemma n
    lemma -[1+ n ] = -lemma (suc n)

  -- The group of integers is cyclic.

  ℤ-cyclic : Cyclic ℤ-group
  ℤ-cyclic = _ , ℤ-generated-by-1

  -- The group of integers is abelian.

  ℤ-abelian : Abelian ℤ-group
  ℤ-abelian = G.Cyclic→Abelian ℤ-group ℤ-cyclic

  -- The direct product of the group of integers and the group of
  -- integers is not cyclic.

  ℤ×ℤ-not-cyclic : ¬ Cyclic (ℤ-group G.× ℤ-group)
  ℤ×ℤ-not-cyclic (g , gen-by) =
    let i , 0,1≡ = gen-by (+ 0 , + 1)
        j , 1,0≡ = gen-by (+ 1 , + 0)
    in lemma₂ g i j (0,1≡ , 1,0≡)
    where
    module G² = Group (ℤ-group G.× ℤ-group)

    0≡^+→≡0 : ∀ n i → + 0 ≡ i *+ suc n → i ≡ + 0
    0≡^+→≡0 n i 0≡ = case -⊎0⊎+ i of λ where
      (inj₁ neg)        → ⊥-elim $ ¬-0 (<0→>0→<0 i n neg) (sym 0≡)
      (inj₂ (inj₁ ≡0))  → ≡0
      (inj₂ (inj₂ pos)) → ⊥-elim $ ¬+0 (>0→>0→>0 i n pos) (sym 0≡)

    1≢0^ : ∀ i → + 1 ≢ (+ 0) G¹.^ i
    1≢0^ i =
      + 1 ≡ (+ 0) G¹.^ i  ↝⟨ flip trans (G¹.id^ i) ⟩
      + 1 ≡ + 0           ↝⟨ +[1+]≢- ⟩□
      ⊥                   □

    -≡0→≡0 : - i ≡ + 0 → i ≡ + 0
    -≡0→≡0 {i = i} hyp =
      i      ≡⟨ sym $ G¹.involutive _ ⟩
      - - i  ≡⟨ cong -_ hyp ⟩
      - + 0  ≡⟨ G¹.identity ⟩∎
      + 0    ∎

    lemma₁ :
      ∀ g₁ g₂ i j →
      ¬ ((+ 0 ≡ g₁ G¹.^ i × + 1 ≡ g₂ G¹.^ i) ×
         (+ 1 ≡ g₁ G¹.^ j × + 0 ≡ g₂ G¹.^ j))
    lemma₁ _ _ (+ zero) _ =
      (_ × + 1 ≡ + 0) × _  ↝⟨ proj₂ ∘ proj₁ ⟩
      + 1 ≡ + 0            ↝⟨ +[1+]≢- ⟩□
      ⊥                    □

    lemma₁ g₁ g₂ (+ suc m) j =
      (+ 0 ≡ g₁ *+ suc m × _) × (+ 1 ≡ g₁ G¹.^ j × _)  ↝⟨ Σ-map (0≡^+→≡0 m _ ∘ proj₁) proj₁ ⟩
      g₁ ≡ + 0 × + 1 ≡ g₁ G¹.^ j                       ↝⟨ (λ (p , q) → trans q (cong (G¹._^ j) p)) ⟩
      + 1 ≡ (+ 0) G¹.^ j                               ↝⟨ 1≢0^ j ⟩□
      ⊥                                                □

    lemma₁ g₁ g₂ -[1+ m ] j =
      (+ 0 ≡ (- g₁) *+ suc m × _) × (+ 1 ≡ g₁ G¹.^ j × _)  ↝⟨ Σ-map (0≡^+→≡0 m _ ∘ proj₁) proj₁ ⟩
      - g₁ ≡ + 0 × + 1 ≡ g₁ G¹.^ j                         ↝⟨ Σ-map -≡0→≡0 id ⟩
      g₁ ≡ + 0 × + 1 ≡ g₁ G¹.^ j                           ↝⟨ (λ (p , q) → trans q (cong (G¹._^ j) p)) ⟩
      + 1 ≡ (+ 0) G¹.^ j                                   ↝⟨ 1≢0^ j ⟩□
      ⊥                                                    □

    lemma₂ : ∀ g i j → ¬ ((+ 0 , + 1) ≡ g G².^ i × (+ 1 , + 0) ≡ g G².^ j)
    lemma₂ g@(g₁ , g₂) i j =
      (+ 0 , + 1) ≡ g G².^ i × (+ 1 , + 0) ≡ g G².^ j  ↝⟨ Σ-map (flip trans (G.^-× ℤ-group ℤ-group i))
                                                                (flip trans (G.^-× ℤ-group ℤ-group j)) ⟩
      (+ 0 , + 1) ≡ (g₁ G¹.^ i , g₂ G¹.^ i) ×
      (+ 1 , + 0) ≡ (g₁ G¹.^ j , g₂ G¹.^ j)            ↔⟨ inverse $ ≡×≡↔≡ ×-cong ≡×≡↔≡ ⟩

      (+ 0 ≡ g₁ G¹.^ i × + 1 ≡ g₂ G¹.^ i) ×
      (+ 1 ≡ g₁ G¹.^ j × + 0 ≡ g₂ G¹.^ j)              ↝⟨ lemma₁ g₁ g₂ i j ⟩□

      ⊥                                                □

  -- The group of integers is not isomorphic to the direct product of
  -- the group of integers and the group of integers.

  ℤ≄ᴳℤ×ℤ : ¬ ℤ-group ≃ᴳ (ℤ-group G.× ℤ-group)
  ℤ≄ᴳℤ×ℤ =
    ℤ-group ≃ᴳ (ℤ-group G.× ℤ-group)  ↝⟨ flip G.≃ᴳ→Cyclic→Cyclic ℤ-cyclic ⟩
    Cyclic (ℤ-group G.× ℤ-group)      ↝⟨ ℤ×ℤ-not-cyclic ⟩□
    ⊥                                 □

  -- The group of integers is not equal to the direct product of the
  -- group of integers and the group of integers.

  ℤ≢ℤ×ℤ : ℤ-group ≢ (ℤ-group G.× ℤ-group)
  ℤ≢ℤ×ℤ =
    ℤ-group ≡ (ℤ-group G.× ℤ-group)   ↝⟨ flip (subst (ℤ-group ≃ᴳ_)) G.↝ᴳ-refl ⟩
    ℤ-group ≃ᴳ (ℤ-group G.× ℤ-group)  ↝⟨ ℤ≄ᴳℤ×ℤ ⟩□
    ⊥                                 □
