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

-- An implementation of tree sort, formally proved to return a sorted
-- permutation of the input.

import Tree-sort
import Tree-sort.Example

-- Some definitions related to and properties of finite sets.

import Fin

-- Containers, including a definition of bag equality.

import Container

-- An implementation of tree sort which uses containers to represent
-- trees and lists.
--
-- In Tree-sort.Correct indexed types are used to enforce sortedness,
-- but Containers contains a definition of non-indexed containers, so
-- sortedness is not enforced in this development.
--
-- The implementation using containers has the advantage of uniform
-- definitions of Any/membership/bag equality, but the other
-- implementation uses more direct definitions and is perhaps a bit
-- "leaner".

import Container.List
import Container.Tree
import Container.Tree-sort
import Container.Tree-sort.Example

-- The stream container.

import Container.Stream

-- Injections.

import Injection

-- For an overview over the other modules in this development, see the
-- README:

import README
