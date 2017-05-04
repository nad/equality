------------------------------------------------------------------------
-- Code related to the abstract "Type Theory with Weak J" by Thorsten
-- Altenkirch, Paolo Capriotti, Thierry Coquand, Nils Anders
-- Danielsson, Simon Huber and Nicolai Kraus
--
-- The code is written by Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Weak-J where

-- For the equality between the two equalities, see proof₁≡proof₂.
--
-- For the main result about contractibility of the type of pairs
-- containing J functions and the corresponding β-rule, see
-- Equality-with-J-contractible.
--
-- Note that there are minor differences between the code and the
-- presentation in the abstract.

import Equality.Instances-related
