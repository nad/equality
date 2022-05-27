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

-- Sequential colimits.

import Colimit.Sequential

-- The one-step truncation HIT with an erased higher constructor.

import H-level.Truncation.Propositional.One-step.Erased

-- The one-step truncation.

import H-level.Truncation.Propositional.One-step

-- A non-recursive variant of H-level.Truncation.Propositional.Erased.

import H-level.Truncation.Propositional.Non-recursive.Erased

-- A variant of the propositional truncation operator with an erased
-- truncation constructor.

import H-level.Truncation.Propositional.Erased

-- Propositional truncation.

import H-level.Truncation.Propositional

-- A definition of the propositional truncation operator that does not
-- use recursive higher inductive types.

import H-level.Truncation.Propositional.Non-recursive

-- The "interval".

import Interval

-- Suspensions.

import Suspension

-- Spheres.

import Sphere

-- Pushouts, defined using a HIT.

import Pushout

-- Joins.

import Join

-- Localisation.

import Localisation

-- Nullification.

import Nullification

-- The nullification modality.

import Nullification.Modality

-- Truncation, defined as a HIT.

import H-level.Truncation

-- Homotopy groups of pointed types.

import Pointed-type.Homotopy-group

-- Connectedness for pointed types.

import Pointed-type.Connected

-- A variant of set quotients with erased higher constructors.

import Quotient.Erased.Basics

-- Quotients (set-quotients), defined using a higher inductive type.

import Quotient

-- Two variants of the set quotients from Quotient.

import Quotient.Set-truncated-if-propositional
import Quotient.Higher-constructors-if-propositional

-- A variant of set quotients with erased higher constructors.

import Quotient.Erased

-- Listed finite subsets.

import Finite-subset.Listed

-- Kuratowski finite subsets.

import Finite-subset.Kuratowski

-- Listed finite subsets, defined using a HIT with erased higher
-- constructors.

import Finite-subset.Listed.Erased

-- Cyclic groups.

import Group.Cyclic

-- Integers, defined using a quotient type.

import Integer.Quotient

-- The Eilenberg-MacLane space K(G, 1).

import Eilenberg-MacLane-space

-- Coherently constant functions.

import Coherently-constant

-- The "circle".

import Circle

-- The circle with an erased higher constructor.

import Circle.Erased

-- The torus, defined as a HIT.

import Torus

-- The figure of eight.

import Figure-of-eight

-- A variant of Nat.Wrapper.Cubical, defined using --erased-cubical.

import Nat.Wrapper.Cubical.Erased

-- A variant of the development in "Internalizing Representation
-- Independence with Univalence" (by Angiuli, Cavallo, Mörtberg and
-- Zeuner) with support for erasure.

import Structure-identity-principle.Erased

-- Truncated queues: any two queues representing the same sequence are
-- equal, and things are set up so that at compile-time (but not at
-- run-time) some queue operations compute in roughly the same way as
-- the corresponding list operations.

import Queue.Truncated

-- Queue instances for the queues in Queue.Truncated.

import Queue.Truncated.Instances

-- Quotiented queues: any two queues representing the same sequence
-- are equal.

import Queue.Quotiented

-- Queue instances for the queues in Queue.Quotiented.

import Queue.Quotiented.Instances
