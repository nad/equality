------------------------------------------------------------------------
-- A forded variant of Fin.Data.Fin
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Fin.Data.Forded
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq hiding (elim)

open import Prelude hiding (Fin)

open import Equivalence eq as Eq using (_≃_)
open import Erased.Level-1 eq as Erased
import Fin.Data eq as F

private variable
  p      : Level
  @0 m n : ℕ

------------------------------------------------------------------------
-- The type

-- Fin n is a type that contains n values.

data Fin (@0 n : ℕ) : Type where
  zero : @0 suc m ≡ n → Fin n
  suc  : Fin m → @0 suc m ≡ n → Fin n

private variable
  i : Fin _

opaque

  -- Zero.

  zeroᶠ : Fin (suc n)
  zeroᶠ = zero (refl _)

opaque

  -- Successor.

  sucᶠ : Fin n → Fin (suc n)
  sucᶠ i = suc i (refl _)

opaque
  unfolding zeroᶠ sucᶠ

  -- An eliminator for Fin.

  elim :
    []-cong-axiomatisation lzero →
    (P : ∀ {@0 n} → Fin n → Type p) →
    (∀ {@0 n} → P (zeroᶠ {n = n})) →
    (∀ {@0 n} (i : Fin n) → P i → P (sucᶠ i)) →
    (i : Fin n) → P i
  elim ax P z s (zero eq) = elim¹ᴱ (λ eq → P (zero eq)) z eq
    where
    open Erased.[]-cong₁ ax
  elim ax P z s (suc i eq) =
    elim¹ᴱ (λ eq → P (suc i eq)) (s i (elim ax P z s i)) eq
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding elim

  -- A "computation" rule.

  elim-zeroᶠ :
    {ax : []-cong-axiomatisation lzero} {P : ∀ {@0 n} → Fin n → Type p}
    {z : ∀ {@0 n} → P (zeroᶠ {n = n})}
    {s : ∀ {@0 n} (i : Fin n) → P i → P (sucᶠ i)} →
    elim ax P z s (zeroᶠ {n = n}) ≡ z
  elim-zeroᶠ {ax} {P} = elim¹ᴱ-refl (λ eq → P (zero eq))
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding elim

  -- A "computation" rule.

  elim-sucᶠ :
    {ax : []-cong-axiomatisation lzero} {P : ∀ {@0 n} → Fin n → Type p}
    {z : ∀ {@0 n} → P (zeroᶠ {n = n})}
    {s : ∀ {@0 n} (i : Fin n) → P i → P (sucᶠ i)} {i : Fin n} →
    elim ax P z s (sucᶠ i) ≡ s i (elim ax P z s i)
  elim-sucᶠ {ax} {P} = elim¹ᴱ-refl (λ eq → P (suc _ eq))
    where
    open Erased.[]-cong₁ ax

------------------------------------------------------------------------
-- A conversion function

opaque

  -- Fin and F.Fin are pointwise equivalent.

  Fin≃Fin :
    []-cong-axiomatisation lzero →
    Fin n ≃ F.Fin n
  Fin≃Fin ax = Eq.↔→≃ to from to-from from-to
    where
    to : Fin n → F.Fin n
    to = elim ax (λ {n} _ → F.Fin n) F.zero (λ _ → F.suc)

    from : F.Fin n → Fin n
    from F.zero    = zeroᶠ
    from (F.suc i) = sucᶠ (from i)

    to-from : (i : F.Fin n) → to (from i) ≡ i
    to-from F.zero =
      to zeroᶠ  ≡⟨ elim-zeroᶠ ⟩∎
      F.zero    ∎
    to-from (F.suc i) =
      to (sucᶠ (from i))   ≡⟨ elim-sucᶠ ⟩
      F.suc (to (from i))  ≡⟨ cong F.suc (to-from i) ⟩∎
      F.suc i              ∎

    from-to : (i : Fin n) → from (to i) ≡ i
    from-to = elim ax (λ i → from (to i) ≡ i)
      (from (to zeroᶠ)  ≡⟨ cong from elim-zeroᶠ ⟩
       from F.zero      ≡⟨⟩
       zeroᶠ            ∎)
      (λ i ih →
         from (to (sucᶠ i))   ≡⟨ cong from elim-sucᶠ ⟩
         from (F.suc (to i))  ≡⟨⟩
         sucᶠ (from (to i))   ≡⟨ cong sucᶠ ih ⟩∎
         sucᶠ i               ∎)

------------------------------------------------------------------------
-- A cast function

opaque

  -- A cast function.

  cast : @0 m ≡ n → Fin m → Fin n
  cast eq₁ (zero eq₂)  = zero (trans eq₂ eq₁)
  cast eq₁ (suc i eq₂) = suc i (trans eq₂ eq₁)

------------------------------------------------------------------------
-- An observation

opaque
  unfolding zeroᶠ sucᶠ

  -- If a function with the type of elim (but without the first
  -- explicit argument) can be implemented, then a family of special
  -- cases of []-cong (without computation rules) can be implemented.

  elim→[]-cong₊ :
    (∀ {p} {@0 n}
     (P : ∀ {@0 n} → Fin n → Type p) →
     (∀ {@0 n} → P (zeroᶠ {n = n})) →
     (∀ {@0 n} (i : Fin n) → P i → P (sucᶠ i)) →
     (i : Fin n) → P i) →
    {m : ℕ} → @0 suc m ≡ n → [ suc m ] ≡ [ n ]
  elim→[]-cong₊ elim {m} eq =
    elim
      (λ where
         {n} (zero {m} _)  → [ suc m ] ≡ [ n ]
         {n} (suc {m} _ _) → [ suc m ] ≡ [ n ])
      (refl _) (λ _ _ → refl _) (zero eq)
