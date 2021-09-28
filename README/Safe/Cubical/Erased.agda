------------------------------------------------------------------------
-- Safe modules that use --erased-cubical
------------------------------------------------------------------------

{-# OPTIONS --safe --erased-cubical #-}

module README.Safe.Cubical.Erased where

-- Paths, extensionality and univalence.

import Equality.Path

-- Isomorphisms and equalities relating an arbitrary "equality with J"
-- to path equality, along with proofs of extensionality and
-- univalence for the "equality with J".

import Equality.Path.Isomorphisms

-- The cubical identity type.

import Equality.Id

-- Propositional equality, with some extra bells and whistles
-- definable in Cubical Agda.

import Equality.Propositional.Cubical

-- Some tactics aimed at making equational reasoning proofs more
-- readable for path equality.

import Tactic.By.Path

-- Some tactics aimed at making equational reasoning proofs more
-- readable for the cubical identity type.

import Tactic.By.Id

-- Some theory of Erased, developed using Cubical Agda.

import Erased.Cubical

-- Some theory of equivalences with erased "proofs", defined in terms
-- of partly erased contractible fibres, developed using Cubical Agda.

import Equivalence.Erased.Contractible-preimages.Cubical

-- Some theory of equivalences with erased "proofs", developed using
-- Cubical Agda.

import Equivalence.Erased.Cubical

-- A sequential colimit for which everything except for the "base
-- case" is erased.

import Colimit.Sequential.Very-erased

-- The sequential colimit HIT with an erased higher constructor.

import Colimit.Sequential.Erased

-- The one-step truncation HIT with an erased higher constructor.

import H-level.Truncation.Propositional.One-step.Erased

-- A non-recursive variant of H-level.Truncation.Propositional.Erased.

import H-level.Truncation.Propositional.Non-recursive.Erased

-- A variant of the propositional truncation operator with an erased
-- truncation constructor.

import H-level.Truncation.Propositional.Erased

-- Completely erased propositional truncation.

import H-level.Truncation.Propositional.Completely-erased

-- A variant of set quotients with erased higher constructors.

import Quotient.Erased.Basics

-- The circle with an erased higher constructor.

import Circle.Erased

-- A variant of set quotients with erased higher constructors.

import Quotient.Erased

-- A variant of Nat.Wrapper.Cubical, defined using --erased-cubical.

import Nat.Wrapper.Cubical.Erased

-- A variant of the development in "Internalizing Representation
-- Independence with Univalence" (by Angiuli, Cavallo, Mörtberg and
-- Zeuner) with support for erasure.

import Structure-identity-principle.Erased
