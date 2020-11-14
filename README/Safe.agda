------------------------------------------------------------------------
-- Safe modules
------------------------------------------------------------------------

{-# OPTIONS --cubical --prop --safe --sized-types #-}

module README.Safe where

-- Definitions of some basic types and some related functions.

import Prelude

-- Support for sized types.

import Prelude.Size

-- Logical equivalences.

import Logical-equivalence

-- Some definitions related to Dec.

import Dec

-- Two logically equivalent axiomatisations of equality. Many of the
-- modules below are parametrised by a definition of equality that
-- satisfies these axioms.
--
-- The reason for this parametrisation was that I thought that I might
-- later want to use a definition of equality where the application
-- elim P r (refl x) did not compute to r x, unlike the equality in
-- Equality.Propositional. Now, with the advent of cubical type theory
-- and paths, there is such an equality (see Equality.Path).
--
-- (Note that Equality.Tactic contains a definition of equality which,
-- roughly speaking, computes like the one in Equality.Propositional.)

import Equality

-- One model of the axioms: propositional equality.

import Equality.Propositional

-- A simple tactic for proving equality of equality proofs.

import Equality.Tactic

-- Injections.

import Injection

-- Split surjections.

import Surjection

-- Some definitions related to and properties of natural numbers.

import Nat

-- H-levels, along with some general properties.

import H-level

-- Types with decidable equality have unique identity proofs, and
-- related results.

import Equality.Decidable-UIP

-- Some decision procedures for equality.

import Equality.Decision-procedures

-- Bijections.

import Bijection

-- Groupoids.

import Groupoid

-- Closure properties for h-levels.

import H-level.Closure

-- Excluded middle.

import Excluded-middle

-- Equivalence relations

import Equivalence-relation

-- Preimages.

import Preimage

-- Equivalences.

import Equivalence

-- A type for values that should be erased at run-time.

import Erased.Basics

-- Equivalences with erased "proofs".

import Equivalence.Erased.Basics

-- Embeddings.

import Embedding

-- A universe which includes several kinds of functions (ordinary
-- functions, logical equivalences, injections, embeddings,
-- surjections, bijections and equivalences).

import Function-universe

-- Some alternative definitions of the concept of being an
-- equivalence: n-path-split and ∞-path-split.

import Equivalence.Path-split

-- Pointed types and loop spaces.

import Pointed-type

-- Equalities can be turned into groupoids which are sometimes
-- commutative.

import Equality.Groupoid

-- Results relating different instances of certain axioms related to
-- equality.

import Equality.Instances-related

-- A parametrised specification of "natrec", along with a proof that
-- the specification is propositional (assuming extensionality).

import Nat.Eliminator

-- A solver for certain natural number equalities.

import Nat.Solver

-- Some definitions related to the binary sum type former.

import Sum

-- Some definitions related to and properties of booleans.

import Bool

-- Monads.

import Monad

-- The reader monad transformer.

import Monad.Reader

-- The state monad transformer.

import Monad.State

-- The double-negation monad.

import Double-negation

-- The univalence axiom.

import Univalence-axiom

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

-- The "interval".

import Interval

-- Truncation, defined using a kind of Church encoding.

import H-level.Truncation.Church

-- Propositional truncation.

import H-level.Truncation.Propositional

-- Sequential colimits.

import Colimit.Sequential

-- The one-step truncation.

import H-level.Truncation.Propositional.One-step

-- A definition of the propositional truncation operator that does not
-- use recursive higher inductive types.

import H-level.Truncation.Propositional.Non-recursive

-- The "circle".

import Circle

-- The torus, defined as a HIT.

import Torus

-- Suspensions.

import Suspension

-- Spheres.

import Sphere

-- Pullbacks.

import Pullback

-- Pushouts, defined using a HIT.

import Pushout

-- The figure of eight.

import Figure-of-eight

-- Truncation, defined as a HIT.

import H-level.Truncation

-- Some omniscience principles.

import Omniscience

-- Lists.

import List

-- Conatural numbers.

import Conat

-- Colists.

import Colist

-- Some definitions related to and properties of finite sets.

import Fin

-- M-types.

import M

-- Some definitions related to and properties of the Maybe type.

import Maybe

-- Vectors, defined using a recursive function.

import Vec

-- Vectors, defined using an inductive family.

import Vec.Data

-- Vectors, defined as functions from finite sets.

import Vec.Function

-- Some properties related to the const function.

import Const

-- Some results related to the For-iterated-equality predicate
-- transformer.

import For-iterated-equality

-- Squashing.

import Squash

-- Support for reflection.

import TC-monad

-- Code used to construct tactics aimed at making equational reasoning
-- proofs more readable.

import Tactic.By

-- A tactic aimed at making equational reasoning proofs more readable
-- in modules that are parametrised by an implementation of equality.

import Tactic.By.Parametrised
import Tactic.By.Parametrised.Tests

-- Some tactics aimed at making equational reasoning proofs more
-- readable for propositional equality.

import Tactic.By.Propositional

-- Some tactics aimed at making equational reasoning proofs more
-- readable for path equality.

import Tactic.By.Path

-- Some tactics aimed at making equational reasoning proofs more
-- readable for the cubical identity type.

import Tactic.By.Id

-- Bag equivalence for lists.

import Bag-equivalence

-- The All predicate, defined using _∈_.

import List.All

-- The All predicate, defined recursively.

import List.All.Recursive

-- Quotients, defined as families of equivalence classes.

import Quotient.Families-of-equivalence-classes

-- Quotients (set-quotients), defined using a higher inductive type.

import Quotient

-- Two variants of the set quotients from Quotient.

import Quotient.Set-truncated-if-propositional
import Quotient.Higher-constructors-if-propositional

-- A type for values that should be erased at run-time.

import Erased.Level-1

-- Equivalences with erased "proofs".

import Equivalence.Erased

-- Embeddings with erased "proofs".

import Embedding.Erased

-- A type for values that should be erased at run-time.

import Erased.Level-2

-- Stability for Erased.

import Erased.Stability

-- A type for values that should be erased at run-time.

import Erased
import Erased.Without-box-cong

-- Some theory of Erased, developed using Cubical Agda.

import Erased.Cubical

-- Some theory of equivalences with erased "proofs", developed using
-- Cubical Agda.

import Equivalence.Erased.Cubical

-- Very stable booleans.

import Bool.Very-stable

-- Listed finite subsets.

import Finite-subset.Listed

-- An alternative definition of listed finite subsets.

import Finite-subset.Listed.Alternative

-- Kuratowski finite subsets.

import Finite-subset.Kuratowski

-- Integers.

import Integer

-- Integers, defined using a quotient type.

import Integer.Quotient

-- A wrapper that turns a representation of natural numbers (with a
-- unique representative for every number) into a representation that
-- computes roughly like the unary natural numbers (at least for some
-- operations).

import Nat.Wrapper

-- An example related to Nat.Wrapper, defined in Cubical Agda.

import Nat.Wrapper.Cubical

-- A binary representation of natural numbers.

import Nat.Binary

-- Specifications of output-restricted deques (single-ended queues
-- with cons).

import Queue

-- Simple queues, implemented in the usual way using two lists
-- (following Hood and Melville).

import Queue.Simple

-- Queue instances for the queues in Queue.Simple.

import Queue.Simple.Instances

-- Banker's queues (following Okasaki).

import Queue.Bankers

-- Queue instances for the queues in Queue.Bankers.

import Queue.Bankers.Instances

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

-- Isomorphism of monoids on sets coincides with equality (assuming
-- univalence).

import Univalence-axiom.Isomorphism-is-equality.Monoid

-- In fact, several large classes of algebraic structures satisfy the
-- property that isomorphism coincides with equality (assuming
-- univalence).

import Univalence-axiom.Isomorphism-is-equality.Simple
import Univalence-axiom.Isomorphism-is-equality.Simple.Variant
import Univalence-axiom.Isomorphism-is-equality.More
import Univalence-axiom.Isomorphism-is-equality.More.Examples

-- A class of structures that satisfies the property that isomorphic
-- instances of a structure are equal (assuming univalence). This code
-- is superseded by the code above, but preserved because it is
-- mentioned in a blog post.

import Univalence-axiom.Isomorphism-implies-equality

-- 1-categories.

import Category
import Functor
import Adjunction

-- Aczel's structure identity principle (for 1-categories).

import Structure-identity-principle

-- The structure identity principle can be used to establish that
-- isomorphism coincides with equality (assuming univalence).

import
  Univalence-axiom.Isomorphism-is-equality.Structure-identity-principle

-- Bi-invertibility.

import Bi-invertibility
import Bi-invertibility.Erased

-- Binary trees.

import Tree

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

-- Record types with manifest fields and "with".

import Records-with-with

-- Overview of code related to some papers.

import README.Bag-equivalence
import README.Isomorphism-is-equality
import README.Weak-J
import README.HITs-without-paths
