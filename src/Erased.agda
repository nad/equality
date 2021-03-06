------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Erased.Basics

module Erased
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (ax : ∀ {a} → Erased.Basics.[]-cong-axiomatisation eq a)
  where

-- Re-exported definitions.

open import Erased.Level-1 eq as E₁ public
  hiding (module []-cong₁; module []-cong₂; module []-cong₃)
open E₁.[]-cong₃ ax public
open import Erased.Level-2 eq ax public
open import Erased.Stability eq as ES public
  hiding (module []-cong)
open ES.[]-cong ax public
