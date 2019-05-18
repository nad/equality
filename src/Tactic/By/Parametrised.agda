------------------------------------------------------------------------
-- A tactic aimed at making equational reasoning proofs more readable
-- in modules that are parametrised by an implementation of equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
open import Prelude

module Tactic.By.Parametrised
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import List eq
open import Monad eq
open import Tactic.By eq as TB
open import TC-monad eq

open TB public using (⟨_⟩)

------------------------------------------------------------------------
-- The ⟨by⟩ tactic

module _
  (distance-to-eq : ℕ)
  -- The de Bruijn index of the "eq" argument at the tactics' use
  -- sites.
  where

  private

    -- A term that stands for the eq argument at the tactics' use
    -- sites.

    eq-term : Term
    eq-term = var distance-to-eq []

  open ⟨By⟩
    (λ where
       (def (quote Reflexive-relation._≡_)
            (arg _ a ∷ _ ∷ arg _ A ∷ arg _ x ∷ arg _ y ∷ [])) →
         return $ just (a , A , x , y)
       _ → return nothing)
    (λ p → def (quote sym) (varg eq-term ∷ varg p ∷ []))
    (λ lhs rhs f p → def (quote cong)
                         (varg eq-term ∷
                          replicate 4 (harg unknown) ++
                          harg lhs ∷ harg rhs ∷ varg f ∷ varg p ∷ []))
    public
