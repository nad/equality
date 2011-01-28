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

-- Two equivalent axiomatisations of equality.

import Equality.Axiomatisations

-- Propositional equality, defined with an abstract (non-computing)
-- eliminator.

import Equality

-- A simple tactic for proving equality of equality proofs.

import Equality.Tactic

-- The equality can be turned into a groupoid.

import Equality.Groupoid

-- A proof which shows that sets with decidable equality have unique
-- identity proofs.

import Equality.Decidable-UIP

-- Surjections.

import Surjection

-- Bijections.

import Bijection

-- H-levels, along with some general properties.

import H-level

-- Closure properties for h-levels.

import H-level.Closure

-- Preimages.

import Preimage

-- Weak equivalences.

import Weak-equivalence
