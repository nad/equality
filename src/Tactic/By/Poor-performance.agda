------------------------------------------------------------------------
-- Code related to Agda issue #4593
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --show-implicit -vby:20 #-}

module Tactic.By.Poor-performance where

open import Equality.Propositional
open import Prelude
open import Tactic.By.Propositional

open import List equality-with-J
open import Maybe equality-with-J
open import Monad equality-with-J
open import TC-monad equality-with-J

test : (h : List ℕ → Maybe (List ℕ)) →
       ((xs : List ℕ) → h xs ≡ just xs) →
       (x : ℕ) (xs : List ℕ) → _
test h hyp x xs =
  _∷_ ⟨$⟩ ⟨ h xs ⟩   ≡⟨ ⟨by⟩ (hyp xs) ⟩∎
  _∷_ ⟨$⟩ return xs  ∎
