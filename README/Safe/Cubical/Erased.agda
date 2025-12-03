------------------------------------------------------------------------
-- Safe modules that use --cubical=erased
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical=erased #-}

module README.Safe.Cubical.Erased where

-- Quotients (set-quotients), defined using a higher inductive type.

import Quotient

-- Two variants of the set quotients from Quotient.

import Quotient.Set-truncated-if-propositional
import Quotient.Higher-constructors-if-propositional

-- A variant of set quotients with erased higher constructors.

import Quotient.Erased

-- A membership relation for listed finite subsets (defined using
-- erased univalence).

import Finite-subset.Listed.Membership.Erased

-- Listed finite subsets, defined using a HIT with erased higher
-- constructors.

import Finite-subset.Listed.Erased

-- Cyclic groups.

import Group.Cyclic

-- Integers, defined using a quotient type.

import Integer.Quotient

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

-- A variant of Nat.Wrapper.Cubical, defined using --cubical=erased.

import Nat.Wrapper.Cubical.Erased

-- A variant of the development in "Internalizing Representation
-- Independence with Univalence" (by Angiuli, Cavallo, Mörtberg and
-- Zeuner) with support for erasure.

import Structure-identity-principle.Erased

-- Quotiented queues: any two queues representing the same sequence
-- are equal.

import Queue.Quotiented

-- Queue instances for the queues in Queue.Quotiented.

import Queue.Quotiented.Instances

-- Abstract binding trees, based on Harper's "Practical Foundations
-- for Programming Languages".

import Abstract-binding-tree
import README.Abstract-binding-tree
