------------------------------------------------------------------------
-- Some theory of equivalences with erased "proofs", developed using
-- Cubical Agda
------------------------------------------------------------------------

-- This module instantiates and reexports code from
-- Equivalence.Erased.

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Equivalence.Erased.Cubical
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Erased.Cubical eq

import Equivalence.Erased
open Equivalence.Erased equality-with-J public
  hiding (module []-cong)
open Equivalence.Erased.[]-cong
  equality-with-J instance-of-[]-cong-axiomatisation
  public
