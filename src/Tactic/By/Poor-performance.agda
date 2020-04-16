------------------------------------------------------------------------
-- Code related to Agda issue #4594
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --show-implicit -vby:20 #-}

module Tactic.By.Poor-performance where

open import Equality.Propositional
open import Prelude
open import Tactic.By.Propositional

open import Maybe equality-with-J
open import Monad equality-with-J
open import TC-monad equality-with-J

test : (h : ℕ → Maybe ℕ) →
       ((xs : ℕ) → h xs ≡ just xs) →
       (xs : ℕ) → suc ⟨$⟩ h xs ≡ suc ⟨$⟩ return xs
test h hyp xs =
  suc ⟨$⟩ ⟨ h xs ⟩   ≡⟨ ⟨by⟩ (hyp xs) ⟩∎
  suc ⟨$⟩ return xs  ∎
