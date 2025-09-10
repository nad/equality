------------------------------------------------------------------------
-- Fin, defined using an inductive family
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Fin.Data {e⁺} (eq-J : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq-J

open import Prelude as P hiding (Fin)

open import Equivalence eq-J as Eq using (_≃_)

private variable
  n : ℕ

-- The type Fin n is a type that contains n values.

data Fin : @0 ℕ → Type where
  zero : Fin (suc n)
  suc  : ∀ {@0 n} → Fin n → Fin (suc n)

-- Fin and P.Fin are pointwise equivalent.

Fin≃Fin : Fin n ≃ P.Fin n
Fin≃Fin = Eq.↔→≃ to from to-from from-to
  where
  to : Fin n → P.Fin n
  to {n = suc _} zero    = fzero
  to {n = suc _} (suc i) = fsuc (to i)

  from : P.Fin n → Fin n
  from {n = suc _} fzero    = zero
  from {n = suc _} (fsuc i) = suc (from i)

  to-from : (i : P.Fin n) → to (from i) ≡ i
  to-from {n = suc _} fzero    = refl _
  to-from {n = suc _} (fsuc i) = cong fsuc (to-from i)

  from-to : (i : Fin n) → from (to i) ≡ i
  from-to {n = suc _} zero    = refl _
  from-to {n = suc _} (suc i) = cong suc (from-to i)
