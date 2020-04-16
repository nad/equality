------------------------------------------------------------------------
-- A tactic aimed at making equational reasoning proofs more readable
-- in modules that are parametrised by an implementation of equality
------------------------------------------------------------------------

-- The tactic uses the first instance of Equality-with-J that it finds
-- in the context.

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

private

  -- Finds the first instance of "∀ Δ → Equality-with-J something" in
  -- the context (if any; Δ must not contain "visible" arguments),
  -- starting from the "outside", and returns a term standing for this
  -- instance.

  find-Equality-with-J : TC Term
  find-Equality-with-J = do
    c ← getContext
    n ← search (reverse c)
    return (var (length c ∸ suc n) [])
    where
    search : List (Arg Type) → TC ℕ
    search [] = typeError (strErr err ∷ [])
      where
      err = "⟨by⟩: No instance of Equality-with-J found in the context."
    search (a@(arg _ t) ∷ args) = do
      if ok t then return 0
              else suc ⟨$⟩ search args
      where
      ok : Term → Bool
      ok (def f _) =
        if eq-Name f (quote Equality-with-J)
        then true
        else false

      ok (pi (arg (arg-info visible _) _) _) = false
      ok (pi _ (abs _ b))                    = ok b
      ok _                                   = false

open ⟨By⟩
  (λ where
     (def (quote Reflexive-relation._≡_)
          (arg _ a ∷ _ ∷ arg _ A ∷ arg _ x ∷ arg _ y ∷ [])) →
       return $ just (a , A , x , y)
     _ → return nothing)
  find-Equality-with-J
  (λ eq p → def (quote sym) (varg eq ∷ varg p ∷ []))
  (λ eq lhs rhs f p → def (quote cong)
                          (varg eq ∷
                           replicate 4 (harg unknown) ++
                           harg lhs ∷ harg rhs ∷ varg f ∷ varg p ∷ []))
  false
  public
