------------------------------------------------------------------------
-- Code related to the paper "Bag Equality via a Proof-Relevant
-- Membership Relation"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Note that the code does not follow the paper exactly. For instance,
-- in some cases where the paper contains a specialised and a more
-- general definition the code only contains the more general one.

{-# OPTIONS --without-K #-}

module README.Bag-equality where

-- Definitions of some basic types and some related functions.

import Prelude

-- Equivalences.

import Equivalence

-- Bijections.

import Bijection

-- Equality.

import Equality.Propositional

-- Bag equality for lists.

import Bag-equality

-- A universe which includes several kinds of functions (including
-- ordinary functions, equivalences, injections and bijections), along
-- with a number of properties.

import Function-universe

-- Some definitions related to and properties of finite sets.

import Fin

-- Containers, including a definition of bag equality.

import Container

-- Injections.

import Injection

-- For an overview over the other modules in this development, see the
-- README:

import README
