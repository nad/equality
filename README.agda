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

-- The univalence axiom. (Currently this module uses --type-in-type,
-- and one example is based on a postulate which could probably be
-- proved if the development was more universe-polymorphic.)

import Univalence-axiom

-- Some definitions related to and properties of finite sets.

import Fin

-- Bag equality.

import Bag-equality
