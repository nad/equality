------------------------------------------------------------------------
-- Code related to the paper "Bag Equivalence via a Proof-Relevant
-- Membership Relation"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Note that the code does not follow the paper exactly. For instance,
-- many definitions are universe-polymorphic, and in some cases where
-- the paper contains both a specialised and a more general definition
-- the code only contains the more general one.

{-# OPTIONS --without-K #-}

module README.Bag-equivalence where

------------------------------------------------------------------------
-- 1: Introduction

-- The introduction mentions tree sort as an example. Two
-- implementations of tree sort are provided. (You may want to read
-- about the more basic definitions first.)

-- 1) An implementation of tree sort, formally proved to return a
--    sorted permutation of the input.

import Tree-sort
import Tree-sort.Example

-- 2) An implementation of tree sort which uses containers to
--    represent trees and lists.
--
--    In the module Tree-sort indexed types are used to enforce
--    sortedness, but Containers contains a definition of non-indexed
--    containers, so sortedness is not enforced in this development.
--
--    The implementation using containers has the advantage of uniform
--    definitions of Any/membership/bag equivalence, but the other
--    implementation uses more direct definitions and is perhaps a bit
--    "leaner".

import Container.Tree
import Container.Tree-sort
import Container.Tree-sort.Example

------------------------------------------------------------------------
-- 2: Brief introduction to Agda

-- The prelude, containing List, ℕ, length, Fin, ⊥, ⊤, _⊎_ (written as
-- _+_ in the paper), lookup, ∃, and _×_.

import Prelude

-- Equivalences: _⇔_.

import Equivalence

-- Bijections: _↔_.

import Bijection

-- Equality: _≡_.

import Equality.Propositional

-- Bijectional reasoning combinators (more general than those in the
-- paper): inverse (written as sym in the paper), _□, and _↔⟨_⟩_.

import Function-universe

------------------------------------------------------------------------
-- 3: Bag equivalence for lists

-- Any, _∈_, and the two definitions of bag equivalence.

import Bag-equivalence

------------------------------------------------------------------------
-- 4: Bijectional reasoning

-- Definitions of map, concat and _>>=_.

import Prelude

-- Algebraic properties of type constructors (like ⊥ ⊎ A ↔ A).

import Function-universe
import Fin

-- All the main lemmas from this section, including
-- >>=-left-distributive.

import Bag-equivalence

------------------------------------------------------------------------
-- 5: The definitions are equivalent

-- The equivalence proof.

import Bag-equivalence

-- There are infinitely many proofs of ℕ ≡ ℕ in homotopy type theory.

import Univalence-axiom

------------------------------------------------------------------------
-- 6: Bag equivalence for arbitrary containers

-- Containers, including Any, _∈_, the two definitions of bag
-- equivalence, and a proof showing that the two definitions are
-- equivalent.

import Container

-- The List, Stream and Tree containers. It is shown that the general
-- definition of bag equivalence for containers, instantiated with the
-- List container, is equivalent (in a certain sense) to the list-only
-- definition given above.

import Container.List
import Container.Stream
import Container.Tree

------------------------------------------------------------------------
-- 7: Set equivalence, subsets and subbags

-- Injections: _↣_.

import Injection

-- The general definition of set and bag equivalence and the subset
-- and subbag preorders, as well as preservation lemmas such as
-- >>=-cong.

import Bag-equivalence

------------------------------------------------------------------------
-- 8: Related work

-- One of the definitions of bag equivalence from Coq's standard
-- library has been replicated, and shown to be sound with respect to
-- the other ones.

import Bag-equivalence

------------------------------------------------------------------------
-- 9: Conclusions

-- The K rule, and a proof showing that it implies proof-irrelevance.

import Equality

------------------------------------------------------------------------

-- For an overview over the other modules in this development, see the
-- README.

import README
