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
  (ax : ∀ {ℓ} → Erased.Level-1.[]-cong-axiomatisation eq ℓ)
  where

-- Re-exported definitions.

private
  module E₁ = Erased.Level-1 eq
open E₁ public
  hiding (module Erased-cong;
          module []-cong; module []-cong₁; module []-cong₂)
open E₁.[]-cong ax public
import Erased.Level-2 eq as E₂
private
  open module E₂′ {ℓ₁ ℓ₂} =
    E₂ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) ax
    public
open import Erased.Stability eq as ES public
  hiding (module []-cong;
          module []-cong₁; module []-cong₁-lsuc; module []-cong₁₃;
          module []-cong₂; module []-cong₂₁; module []-cong₂₂)
open ES.[]-cong ax public
