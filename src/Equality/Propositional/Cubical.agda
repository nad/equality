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

private

  equality-with-paths′ :
    ∀ {a p} → P.Equality-with-paths a p equivalence-relation⁺
  equality-with-paths′ =
    P.Equality-with-J⇒Equality-with-paths equality-with-J

-- A family of implementations of P.Equality-with-paths.
--
-- The definition has been expanded in order to ensure that it does
-- not reduce (unless a projection is applied to it).

equality-with-paths :
  ∀ {a p} → P.Equality-with-paths a p equivalence-relation⁺
equality-with-paths         .P.Equality-with-paths.equality-with-J   = equality-with-paths′         .P.Equality-with-paths.equality-with-J
equality-with-paths {p = p} .P.Equality-with-paths.to-path           = equality-with-paths′ {p = p} .P.Equality-with-paths.to-path
equality-with-paths {p = p} .P.Equality-with-paths.from-path         = equality-with-paths′ {p = p} .P.Equality-with-paths.from-path
equality-with-paths {p = p} .P.Equality-with-paths.to-path∘from-path = equality-with-paths′ {p = p} .P.Equality-with-paths.to-path∘from-path
equality-with-paths {p = p} .P.Equality-with-paths.from-path∘to-path = equality-with-paths′ {p = p} .P.Equality-with-paths.from-path∘to-path
equality-with-paths {p = p} .P.Equality-with-paths.to-path-refl      = equality-with-paths′ {p = p} .P.Equality-with-paths.to-path-refl
equality-with-paths {p = p} .P.Equality-with-paths.from-path-refl    = equality-with-paths′ {p = p} .P.Equality-with-paths.from-path-refl

open P.Derived-definitions-and-properties equality-with-paths public
  hiding (refl)

open import Equality.Path.Isomorphisms equality-with-paths public
