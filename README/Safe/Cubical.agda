------------------------------------------------------------------------
-- Safe modules that use --cubical
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical #-}

module README.Safe.Cubical where

-- A proof of univalence.

import Equality.Path.Univalence

-- A proof of univalence for an arbitrary "equality with J".

import Equality.Path.Isomorphisms.Univalence

-- Sequential colimits.

import Colimit.Sequential

-- The one-step truncation.

import H-level.Truncation.Propositional.One-step

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

-- Pullbacks.

import Pullback

-- Pushouts, defined using a HIT.

import Pushout

-- Localisation.

import Localisation

-- Truncation, defined as a HIT.

import H-level.Truncation

-- Homotopy groups of pointed types.

import Pointed-type.Homotopy-group

-- Connectedness for pointed types.

import Pointed-type.Connected

-- Quotients (set-quotients), defined using a higher inductive type.

import Quotient

-- Two variants of the set quotients from Quotient.

import Quotient.Set-truncated-if-propositional
import Quotient.Higher-constructors-if-propositional

-- Very stable booleans.

import Bool.Very-stable

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

-- The Eilenberg-MacLane space K(G, 1).

import Eilenberg-MacLane-space

-- Coherently constant functions.

import Coherently-constant

-- The "circle".

import Circle

-- The torus, defined as a HIT.

import Torus

-- The figure of eight.

import Figure-of-eight

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
