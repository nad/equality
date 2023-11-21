------------------------------------------------------------------------
-- A proof of univalence for an arbitrary "equality with J"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Equality.Path.Isomorphisms.Univalence
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

import Equality.Path.Univalence as PU
open import Prelude

open import Equivalence equality-with-J
open import Univalence-axiom equality-with-J
open import Equality.Path.Isomorphisms eq

private
  variable
    ℓ : Level

opaque

  -- Univalence.

  univ : Univalence ℓ
  univ = _≃_.from Univalence≃Univalence PU.univ

-- Propositional extensionality.

prop-ext : Propositional-extensionality ℓ
prop-ext =
  _≃_.from
    (Propositional-extensionality-is-univalence-for-propositions ext)
    (λ _ _ → univ)
