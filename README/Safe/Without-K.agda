------------------------------------------------------------------------
-- Safe modules that use --without-K
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module README.Safe.Without-K where

-- Definitions of some basic types and some related functions.

import Prelude

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

-- Integers.

import Integer.Basics

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

-- Is-equivalence, defined in terms of contractible fibres.

import Equivalence.Contractible-preimages

-- Half adjoint equivalences.

import Equivalence.Half-adjoint

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
-- equivalence.

import Equivalence.Path-split

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

-- Raw monads.

import Monad.Raw

-- Monads.

import Monad

-- The reader monad transformer.

import Monad.Reader

-- The state monad transformer.

import Monad.State

-- The double-negation monad.

import Double-negation

-- Lists.

import List

-- Pullbacks.

import Pullback

-- The univalence axiom.

import Univalence-axiom

-- Pointed types and loop spaces.

import Pointed-type

-- Equalities can be turned into groupoids which are sometimes
-- commutative.

import Equality.Groupoid

-- Groups.

import Group

-- Integers.

import Integer

-- Some definitions related to and properties of finite sets.

import Fin

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

-- Support for reflection.

import TC-monad

-- Tactics for proving instances of Σ-cong (and Surjection.Σ-cong)
-- with "better" computational behaviour.

import Tactic.Sigma-cong

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

-- A type for values that should be erased at run-time.

import Erased.Level-1

-- Equivalences with erased "proofs", defined in terms of partly
-- erased contractible fibres.

import Equivalence.Erased.Contractible-preimages

-- Equivalences with erased "proofs".

import Equivalence.Erased

-- Embeddings with erased "proofs".

import Embedding.Erased

-- A type for values that should be erased at run-time.

import Erased.Level-2

-- Some results related to the For-iterated-equality predicate
-- transformer.

import For-iterated-equality

-- Properties related to stability for Erased.

import Erased.Stability

-- Some properties that hold for Erased do not hold for every
-- topological modality.

import Erased.Counterexamples

-- Truncation, defined using a kind of Church encoding.

import H-level.Truncation.Church

-- Some omniscience principles.

import Omniscience

-- Bag equivalence for lists.

import Bag-equivalence

-- The All predicate, defined using _∈_.

import List.All

-- The All predicate, defined recursively.

import List.All.Recursive

-- Quotients, defined as families of equivalence classes.

import Quotient.Families-of-equivalence-classes

-- A type for values that should be erased at run-time.

import Erased
import Erased.Without-box-cong

-- A wrapper that turns a representation of natural numbers (with a
-- unique representative for every number) into a representation that
-- computes roughly like the unary natural numbers (at least for some
-- operations).

import Nat.Wrapper

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

-- Indexed containers.

import Container.Indexed

-- Another definition of indexed containers.

import Container.Indexed.Variant

-- M-types for indexed containers, defined using functions.

import Container.Indexed.M.Function

-- Record types with manifest fields and "with".

import Records-with-with

-- Overview of code related to some papers.

import README.Bag-equivalence
import README.Isomorphism-is-equality
import README.Weak-J
