------------------------------------------------------------------------
-- Some decision procedures for equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Equality.Decision-procedures
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Prelude hiding (module Bool; module ℕ)

------------------------------------------------------------------------
-- Booleans

module Bool where

  -- The values true and false are distinct.

  abstract

    true≢false : true ≢ false
    true≢false true≡false = subst T true≡false _

  -- Equality of booleans is decidable.

  _≟_ : Decidable-equality Bool
  true  ≟ true  = inj₁ (refl _)
  false ≟ false = inj₁ (refl _)
  true  ≟ false = inj₂ true≢false
  false ≟ true  = inj₂ (true≢false ∘ sym)

------------------------------------------------------------------------
-- Natural numbers

module ℕ where

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
  zero  ≟ zero  = inj₁ (refl _)
  suc m ≟ suc n = ⊎-map (cong suc) (λ m≢n → m≢n ∘ cancel-suc) (m ≟ n)
  zero  ≟ suc n = inj₂ 0≢+
  suc m ≟ zero  = inj₂ (0≢+ ∘ sym)

------------------------------------------------------------------------
-- Binary sums

module ⊎ {a b} {A : Set a} {B : Set b} where

  abstract

    -- The values inj₁ x and inj₂ y are never equal.

    inj₁≢inj₂ : {x : A} {y : B} → inj₁ x ≢ inj₂ y
    inj₁≢inj₂ = Bool.true≢false ∘
                cong {A = A ⊎ B} {B = Bool} [ const true , const false ]

  -- The inj₁ and inj₂ constructors are cancellative.

  cancel-inj₁ : {x y : A} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
  cancel-inj₁ {x = x} = cong {A = A ⊎ B} {B = A} [ id , const x ]

  cancel-inj₂ : {x y : B} → _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y) → x ≡ y
  cancel-inj₂ {x = x} = cong {A = A ⊎ B} {B = B} [ const x , id ]

  -- _⊎_ preserves decidability of equality.

  module Dec (_≟A_ : Decidable-equality A)
             (_≟B_ : Decidable-equality B) where

    _≟_ : Decidable-equality (A ⊎ B)
    inj₁ x ≟ inj₁ y = ⊎-map (cong (inj₁ {B = B})) (λ x≢y → x≢y ∘ cancel-inj₁) (x ≟A y)
    inj₂ x ≟ inj₂ y = ⊎-map (cong (inj₂ {A = A})) (λ x≢y → x≢y ∘ cancel-inj₂) (x ≟B y)
    inj₁ x ≟ inj₂ y = inj₂ inj₁≢inj₂
    inj₂ x ≟ inj₁ y = inj₂ (inj₁≢inj₂ ∘ sym)

------------------------------------------------------------------------
-- Finite sets

module Fin where

  -- Equality of finite numbers is decidable.

  _≟_ : ∀ {n} → Decidable-equality (Fin n)
  _≟_ {zero}  = λ ()
  _≟_ {suc n} = ⊎.Dec._≟_ (λ _ _ → inj₁ (refl tt)) (_≟_ {n})
