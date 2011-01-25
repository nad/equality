------------------------------------------------------------------------
-- Experiments related to equality
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module README where

-- Two equivalent axiomatisations of equality.

import Equality-without-K.Axiomatisations

-- An equality which I pretend does not come with the K rule.

import Equality-without-K

-- A simple tactic for proving equality of equality proofs.

import Equality-without-K.Tactic

-- The equality can be turned into a groupoid.

import Equality-without-K.Groupoid

-- A proof which shows that sets with decidable equality have unique
-- identity proofs.

import Equality-without-K.Decidable-UIP

-- H-levels, along with some general properties.

import H-level

-- Closure properties for h-levels.

import H-level.Closure
