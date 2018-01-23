------------------------------------------------------------------------
-- Experiments related to equality involving code that can (perhaps)
-- not be type-checked in --safe mode
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

-- Support for using propositional equality with the rewriting
-- machinery.

import Equality.Propositional.Rewriting

-- IO.

import IO

-- The following modules use postulates and rewrite rules to encode
-- higher inductive types.

-- The "interval".

import Interval

-- Propositional truncation.

import H-level.Truncation.Propositional

-- Quotients, defined using a higher inductive type.

import Quotient.HIT
