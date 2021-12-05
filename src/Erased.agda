------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Erased.Basics
import Erased.Box-cong-axiomatisation

module Erased
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (ax : ∀ {ℓ} →
        Erased.Box-cong-axiomatisation.[]-cong-axiomatisation eq ℓ)
  where

-- Re-exported definitions.

open import Erased.Level-1 eq as E₁ public
  hiding (module Erased-cong;
          module []-cong;
          module []-cong₁;
          module []-cong₂; module []-cong₂-⊔;
          module Extensionality)
open E₁.[]-cong ax public
import Erased.Level-2 eq as E₂
open E₂.[]-cong ax public
open import Erased.Stability eq as ES public
  hiding (module []-cong;
          module []-cong₁; module []-cong₁-lsuc;
          module []-cong₂; module []-cong₂-⊔₁; module []-cong₂-⊔₂;
          module Extensionality)
open ES.[]-cong ax public
