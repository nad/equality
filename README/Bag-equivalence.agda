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
-- 2: Brief Introduction to Agda

-- The prelude, containing List, ℕ, Fin, ⊥, ⊤, _⊎_ (written as _+_ in
-- the paper), ∃, and _×_.

import Prelude

-- Some list functions: length and lookup.

import List

-- Logical equivalences: _⇔_.

import Logical-equivalence

-- Bijections: _↔_.

import Bijection

-- Equality: _≡_.

import Equality.Propositional

-- The K rule, and a proof showing that it implies proof-irrelevance.

import Equality

-- Bijectional reasoning combinators (more general than those in the
-- paper): inverse (written as sym in the paper), _□, and _↔⟨_⟩_.

import Function-universe

------------------------------------------------------------------------
-- 3: Bag Equivalence for Lists

-- Any, _∈_, and the two definitions of bag equivalence.

import Bag-equivalence

------------------------------------------------------------------------
-- 4: Bijectional Reasoning

-- Definitions of map, concat and _>>=_ (the latter as part of a monad
-- instance).

import List

-- Algebraic properties of type constructors (like ⊥ ⊎ A ↔ A).

import Function-universe
import Fin

-- All the main lemmas from this section, including
-- >>=-left-distributive.

import Bag-equivalence

------------------------------------------------------------------------
-- 5: The Definitions Are Equivalent

-- The equivalence proof.

import Bag-equivalence

-- There are infinitely many proofs of ℕ ≡ ℕ in homotopy type theory.

import Univalence-axiom

------------------------------------------------------------------------
-- 6: Bag Equivalence for Arbitrary Containers

-- Containers, including Any, _∈_, the two definitions of bag
-- equivalence, and a proof showing that the two definitions are
-- logically equivalent.
--
-- There is also a proof which shows that the definitions are
-- isomorphic (assuming extensionality), if "bijection" is replaced by
-- the logically equivalent concept of "(weak) equivalence" in the
-- definitions of bag equivalence.

import Container
import Equivalence

-- The List, Stream and Tree containers. It is shown that the general
-- definition of bag equivalence for containers, instantiated with the
-- List container, is equivalent (in a certain sense) to the list-only
-- definition given above.

import Container.List
import Container.Stream
import Container.Tree

------------------------------------------------------------------------
-- 7: More Bijectional Reasoning

-- Three implementations of tree sort are provided.

-- 1) An implementation of tree sort, formally proved to return a
--    permutation of the input.

import Tree-sort.Partial
import Tree-sort.Examples

-- 2) An implementation of tree sort, formally proved to return a
--    /sorted/ permutation of the input.

import Tree-sort.Full
import Tree-sort.Examples

-- 3) An implementation of tree sort which uses containers to
--    represent trees and lists.
--
--    In the module Tree-sort.Full indexed types are used to enforce
--    sortedness, but this development uses non-indexed containers, so
--    sortedness is not enforced.
--
--    The implementation using containers has the advantage of uniform
--    definitions of Any/membership/bag equivalence, but the other
--    implementations use more direct definitions and are perhaps a
--    bit "leaner".

import Container.Tree
import Container.Tree-sort
import Container.Tree-sort.Example

------------------------------------------------------------------------
-- 8: Set Equivalence, Subsets and Subbags

-- Injections: _↣_.

import Injection

-- The general definition of set and bag equivalence and the subset
-- and subbag preorders, as well as preservation lemmas such as
-- >>=-cong.

import Bag-equivalence

------------------------------------------------------------------------
-- 9: Related Work

-- One of the definitions of bag equivalence from Coq's standard
-- library has been replicated, and shown to be sound with respect to
-- the other ones.

import Bag-equivalence

------------------------------------------------------------------------
-- 10: Conclusions

-- Two proofs showing that cons is left cancellative, using different
-- definitions of bag equivalence.

import Bag-equivalence
