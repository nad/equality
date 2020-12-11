------------------------------------------------------------------------
-- Some theory of equivalences with erased "proofs", defined in terms
-- of partly erased contractible fibres, developed using Cubical Agda
------------------------------------------------------------------------

-- This module instantiates and reexports code from
-- Equivalence.Erased.Contractible-preimages.

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Equivalence.Erased.Contractible-preimages.Cubical
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Erased.Cubical eq

import Equivalence.Erased.Contractible-preimages
open Equivalence.Erased.Contractible-preimages equality-with-J public
  hiding (module []-cong)
open Equivalence.Erased.Contractible-preimages.[]-cong
  equality-with-J instance-of-[]-cong-axiomatisation
  public
