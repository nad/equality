------------------------------------------------------------------------
-- Propositional equality, with some extra bells and whistles
-- definable in Cubical Agda
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Equality.Propositional.Cubical where

import Equality.Path as P

open import Equality.Propositional

open Equality.Propositional public using (refl; equivalence-relation⁺)

-- A family of implementations of P.Equality-with-paths.

equality-with-paths :
  ∀ {a p} → P.Equality-with-paths a p equivalence-relation⁺
equality-with-paths =
  P.Equality-with-J⇒Equality-with-paths equality-with-J

open P.Derived-definitions-and-properties equality-with-paths public
  hiding (refl)

open import Equality.Path.Isomorphisms equality-with-paths public
