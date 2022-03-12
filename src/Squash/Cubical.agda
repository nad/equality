------------------------------------------------------------------------
-- Code related to Squash that uses --erased-cubical
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --prop --safe #-}

import Equality.Path as P

module Squash.Cubical
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import H-level.Truncation.Propositional eq as Trunc using (∥_∥)
open import Squash equality-with-J

private
  variable
    a : Level
    A : Type a

-- ∥ A ∥ implies Squash A.

∥∥→Squash : ∥ A ∥ → Squash A
∥∥→Squash = Trunc.rec Squash-propositional [_]
