------------------------------------------------------------------------
-- Safe modules that use --cubical
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical #-}

module README.Safe.Cubical where

-- A proof of univalence.

import Equality.Path.Univalence

-- A proof of univalence for an arbitrary "equality with J".

import Equality.Path.Isomorphisms.Univalence

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

-- Abstract binding trees, based on Harper's "Practical Foundations
-- for Programming Languages".

import Abstract-binding-tree
import README.Abstract-binding-tree

-- Overview of code related to a paper.

import README.HITs-without-paths
