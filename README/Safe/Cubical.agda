------------------------------------------------------------------------
-- Safe modules that use --cubical
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical #-}

module README.Safe.Cubical where

-- A proof of univalence.

import Equality.Path.Univalence

-- A proof of univalence for an arbitrary "equality with J".

import Equality.Path.Isomorphisms.Univalence

-- Very stable booleans.

import Bool.Very-stable

-- A membership relation for listed finite subsets (defined using
-- non-erased univalence).

import Finite-subset.Listed.Membership

-- An alternative definition of listed finite subsets.

import Finite-subset.Listed.Alternative

-- A membership relation for Kuratowski finite subsets (defined using
-- non-erased univalence).

import Finite-subset.Kuratowski.Membership

-- An example related to Nat.Wrapper, defined in Cubical Agda.

import Nat.Wrapper.Cubical

-- Abstract binding trees, based on Harper's "Practical Foundations
-- for Programming Languages".

import Abstract-binding-tree
import README.Abstract-binding-tree

-- Overview of code related to a paper.

import README.HITs-without-paths
