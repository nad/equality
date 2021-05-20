------------------------------------------------------------------------
-- Safe modules that use --cubical
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical #-}

module README.Safe.Cubical where

-- Paths and extensionality.

import Equality.Path

-- A proof of univalence.

import Equality.Path.Univalence

-- Isomorphisms and equalities relating an arbitrary "equality with J"
-- to path equality, along with a proof of extensionality for the
-- "equality with J".

import Equality.Path.Isomorphisms

-- A proof of univalence for an arbitrary "equality with J".

import Equality.Path.Isomorphisms.Univalence

-- The cubical identity type.

import Equality.Id

-- Propositional equality, with some extra bells and whistles
-- definable in Cubical Agda.

import Equality.Propositional.Cubical

-- The "interval".

import Interval

-- Propositional truncation.

import H-level.Truncation.Propositional

-- Sequential colimits.

import Colimit.Sequential

-- Suspensions.

import Suspension

-- Spheres.

import Sphere

-- Pullbacks.

import Pullback

-- Pushouts, defined using a HIT.

import Pushout

-- Truncation, defined as a HIT.

import H-level.Truncation

-- Homotopy groups of pointed types.

import Pointed-type.Homotopy-group

-- Connectedness for pointed types.

import Pointed-type.Connected

-- Some tactics aimed at making equational reasoning proofs more
-- readable for path equality.

import Tactic.By.Path

-- Some tactics aimed at making equational reasoning proofs more
-- readable for the cubical identity type.

import Tactic.By.Id

-- Quotients (set-quotients), defined using a higher inductive type.

import Quotient

-- Two variants of the set quotients from Quotient.

import Quotient.Set-truncated-if-propositional
import Quotient.Higher-constructors-if-propositional

-- Some theory of Erased, developed using Cubical Agda.

import Erased.Cubical

-- Some theory of equivalences with erased "proofs", developed using
-- Cubical Agda.

import Equivalence.Erased.Cubical

-- Some theory of equivalences with erased "proofs", defined in terms
-- of partly erased contractible fibres, developed using Cubical Agda.

import Equivalence.Erased.Contractible-preimages.Cubical

-- Very stable booleans.

import Bool.Very-stable

-- A sequential colimit for which everything except for the "base
-- case" is erased.

import Colimit.Sequential.Very-erased

-- The sequential colimit HIT with an erased higher constructor.

import Colimit.Sequential.Erased

-- Listed finite subsets.

import Finite-subset.Listed

-- An alternative definition of listed finite subsets.

import Finite-subset.Listed.Alternative

-- Kuratowski finite subsets.

import Finite-subset.Kuratowski

-- Integers, defined using a quotient type.

import Integer.Quotient

-- Cyclic groups.

import Group.Cyclic

-- The "circle".

import Circle

-- The torus, defined as a HIT.

import Torus

-- The figure of eight.

import Figure-of-eight

-- The Eilenberg-MacLane space K(G, 1).

import Eilenberg-MacLane-space

-- Coherently constant functions.

import Coherently-constant

-- The one-step truncation.

import H-level.Truncation.Propositional.One-step

-- The one-step truncation HIT with an erased higher constructor.

import H-level.Truncation.Propositional.One-step.Erased

-- A definition of the propositional truncation operator that does not
-- use recursive higher inductive types.

import H-level.Truncation.Propositional.Non-recursive

-- A non-recursive variant of H-level.Truncation.Propositional.Erased.

import H-level.Truncation.Propositional.Non-recursive.Erased

-- A variant of the propositional truncation operator with an erased
-- truncation constructor.

import H-level.Truncation.Propositional.Erased

-- The circle with an erased higher constructor.

import Circle.Erased

-- A variant of set quotients with erased higher constructors.

import Quotient.Erased

-- An example related to Nat.Wrapper, defined in Cubical Agda.

import Nat.Wrapper.Cubical

-- Quotiented queues: any two queues representing the same sequence
-- are equal.

import Queue.Quotiented

-- Queue instances for the queues in Queue.Quotiented.

import Queue.Quotiented.Instances

-- Truncated queues: any two queues representing the same sequence are
-- equal, and things are set up so that at compile-time (but not at
-- run-time) some queue operations compute in roughly the same way as
-- the corresponding list operations.

import Queue.Truncated

-- Queue instances for the queues in Queue.Truncated.

import Queue.Truncated.Instances

-- Abstract binding trees, based on Harper's "Practical Foundations
-- for Programming Languages".

import Abstract-binding-tree
import README.Abstract-binding-tree

-- Overview of code related to a paper.

import README.HITs-without-paths
