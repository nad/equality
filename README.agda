------------------------------------------------------------------------
-- Experiments related to equality
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

-- Definitions of some basic types and some related functions.

import Prelude

-- Equivalences.

import Equivalence

-- Two equivalent axiomatisations of equality. Most of the modules
-- below are parametrised by a definition of equality which satisfies
-- these axioms. The reason for this parametrisation is that I might
-- later want to use a definition of equality where the application
-- elim P r (refl x) does not compute to r x, unlike the equality in
-- Equality.Propositional. (Equality.Tactic also contains a definition
-- of equality which, roughly speaking, computes in this way.)

import Equality

-- One model of the axioms: propositional equality.

import Equality.Propositional

-- Some decision procedures for equality.

import Equality.Decision-procedures

-- A simple tactic for proving equality of equality proofs.

import Equality.Tactic

-- Equalities can be turned into groupoids which are sometimes
-- commutative.

import Equality.Groupoid

-- A proof which shows that sets with decidable equality have unique
-- identity proofs.

import Equality.Decidable-UIP

-- Injections.

import Injection

-- Surjections.

import Surjection

-- Bijections.

import Bijection

-- All instances of the equality axioms are isomorphic.

import Equality.Instances-isomorphic

-- H-levels, along with some general properties.

import H-level

-- Closure properties for h-levels.

import H-level.Closure

-- Preimages.

import Preimage

-- Weak equivalences.

import Weak-equivalence

-- The univalence axiom.

import Univalence-axiom

-- A universe which includes several kinds of functions (ordinary
-- functions, equivalences, injections, surjections, bijections and
-- weak equivalences).

import Function-universe

-- Some definitions related to and properties of finite sets.

import Fin

-- Bag equivalence for lists.

import Bag-equivalence

-- An implementation of tree sort, formally proved to return a sorted
-- permutation of the input.

import Tree-sort
import Tree-sort.Example

-- Containers, including a definition of bag equivalence.

import Container

-- An implementation of tree sort which uses containers to represent
-- trees and lists.
--
-- In Tree-sort.Correct indexed types are used to enforce sortedness,
-- but Containers contains a definition of non-indexed containers, so
-- sortedness is not enforced in this development.
--
-- The implementation using containers has the advantage of uniform
-- definitions of Any/membership/bag equivalence, but the other
-- implementation uses more direct definitions and is perhaps a bit
-- "leaner".

import Container.List
import Container.Tree
import Container.Tree-sort
import Container.Tree-sort.Example

-- The stream container.

import Container.Stream
