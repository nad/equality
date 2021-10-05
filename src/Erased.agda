------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Erased.Basics
import Erased.Level-1

module Erased
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (ax : ∀ {a} → Erased.Level-1.[]-cong-axiomatisation eq a)
  where

-- Re-exported definitions.

private
  module E₁ = Erased.Level-1 eq
open E₁ public hiding (module []-cong)
open E₁.[]-cong ax public
open import Erased.Level-2 eq ax public
open import Erased.Stability eq as ES public
  hiding (module []-cong)
open ES.[]-cong ax public
