------------------------------------------------------------------------
-- Experiments related to equality
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module README where

-- An equality without the K rule.

import Equality-without-K

-- A simple tactic for proving equality of equality proofs.

import Equality-without-K.Tactic

-- The equality can be turned into a groupoid.

import Equality-without-K.Groupoid

-- A proof which shows that sets with decidable equality have unique
-- identity proofs.

import Equality-without-K.Decidable-UIP

-- W-types.

import W-type

-- H-levels, along with some general properties.

import H-level

-- Closure properties for h-levels.

import H-level.Closure
