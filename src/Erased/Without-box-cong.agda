------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

-- This module reexports definitions that do not depend on an
-- implementation of []-cong.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Erased.Without-box-cong
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

-- Re-exported definitions.

open import Erased.Level-1 eq public
  hiding (module []-cong₁; module []-cong₂; module []-cong₃)
open import Erased.Stability eq public
  hiding (module []-cong)
