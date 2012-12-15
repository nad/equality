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

-- Two equivalent axiomatisations of equality. Many of the modules
-- below are parametrised by a definition of equality that satisfies
-- these axioms. The reason for this parametrisation is that I might
-- later want to use a definition of equality where the application
-- elim P r (refl x) does not compute to r x, unlike the equality in
-- Equality.Propositional. (Equality.Tactic also contains a definition
-- of equality which, roughly speaking, computes in this way.)

import Equality

-- One model of the axioms: propositional equality.

import Equality.Propositional

-- A simple tactic for proving equality of equality proofs (at the
-- time of writing only used in Equality.Groupoid).

import Equality.Tactic

-- Some decision procedures for equality.

import Equality.Decision-procedures

-- A proof which shows that sets with decidable equality have unique
-- identity proofs.

import Equality.Decidable-UIP

-- Groupoids.

import Groupoid

-- Equalities can be turned into groupoids which are sometimes
-- commutative.

import Equality.Groupoid

-- Injections.

import Injection

-- Split surjections.

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

-- Isomorphic instances of certain algebraic structures are equal
-- (assuming univalence).

import Univalence-axiom.Isomorphism-implies-equality.Examples

-- In fact, several large classes of algebraic structures satisfy
-- the property that isomorphic instances of a structure are equal
-- (assuming univalence).

import Univalence-axiom.Isomorphism-implies-equality
import Univalence-axiom.Isomorphism-implies-equality.Simple
import Univalence-axiom.Isomorphism-implies-equality.More

-- A universe which includes several kinds of functions (ordinary
-- functions, equivalences, injections, surjections, bijections and
-- weak equivalences).

import Function-universe

-- Some definitions related to and properties of finite sets.

import Fin

-- Bag equivalence for lists.

import Bag-equivalence

-- Implementations of tree sort. One only establishes that the
-- algorithm permutes its input, the other one also establishes
-- sortedness.

import Tree-sort.Partial
import Tree-sort.Full
import Tree-sort.Examples

-- Containers, including a definition of bag equivalence.

import Container

-- An implementation of tree sort which uses containers to represent
-- trees and lists.
--
-- In the module Tree-sort.Full indexed types are used to enforce
-- sortedness, but Containers contains a definition of non-indexed
-- containers, so sortedness is not enforced in this development.
--
-- The implementation using containers has the advantage of uniform
-- definitions of Any/membership/bag equivalence, but the other
-- implementations use more direct definitions and are perhaps a bit
-- "leaner".

import Container.List
import Container.Tree
import Container.Tree-sort
import Container.Tree-sort.Example

-- The stream container.

import Container.Stream
