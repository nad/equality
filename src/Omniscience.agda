------------------------------------------------------------------------
-- Some omniscience principles
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Omniscience where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equality.Decision-procedures equality-with-J
open import H-level equality-with-J
open import H-level.Closure equality-with-J

-- I don't know who first came up with these principles. Perhaps
-- Bishop came up with one or both of them.

-- The limited principle of omniscience.
--
-- I think that Escardo has proved that the principle as stated below
-- is logically equivalent to the principle stated with a
-- propositionally truncated binary sum (presumably assuming
-- extensionality).

LPO : Set
LPO = (f : ℕ → Bool) → (∀ n → f n ≡ false) ⊎ (∃ λ n → f n ≡ true)

-- The weak limited principle of omniscience.

WLPO : Set
WLPO = (f : ℕ → Bool) → Dec (∀ n → f n ≡ false)

-- WLPO is propositional (assuming extensionality).

WLPO-propositional :
  Extensionality lzero lzero →
  Is-proposition WLPO
WLPO-propositional ext =
  Π-closure ext 1 λ f →
  Dec-closure-propositional ext
    (Π-closure ext 1 λ _ →
     Bool-set _ _)

-- LPO implies WLPO.

LPO→WLPO : LPO → WLPO
LPO→WLPO LPO f =
  ⊎-map id
        (uncurry λ n fn≡true ∀n→fn≡false → Bool.true≢false (
           true   ≡⟨ sym fn≡true ⟩
           f n    ≡⟨ ∀n→fn≡false n ⟩∎
           false  ∎))
        (LPO f)
