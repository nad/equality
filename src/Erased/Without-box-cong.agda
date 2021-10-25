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
  hiding (module Erased-cong;
          module []-cong; module []-cong₁; module []-cong₂;
          module Extensionality)
open import Erased.Stability eq public
  hiding (module []-cong;
          module []-cong₁; module []-cong₁-lsuc; module []-cong₁₃;
          module []-cong₂₁; module []-cong₂₂;
          module Extensionality)
