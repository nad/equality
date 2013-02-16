------------------------------------------------------------------------
-- Code related to the paper "Isomorphism Is Equality" by Thierry
-- Coquand and Nils Anders Danielsson
--
-- The code is written by Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Isomorphism-is-equality where

---=====================================================================
-- 2: Preliminaries

------------------------------------------------------------------------
-- 2.1: Hierarchy of Types

-- The lifting operator ↑. (Note that Agda is universe-polymorphic.)

import Prelude

------------------------------------------------------------------------
-- 2.2: Quantifiers

-- Σ, ∃ and _×_. (The code sometimes uses ∃ instead of Σ.)

import Prelude

------------------------------------------------------------------------
-- 2.3: Equality

-- Axiomatisations of equality, used in order to ensure that the
-- elimination rule (J) does not compute. J is called elim in the
-- code.

import Equality

-- Bijections (_↔_), the key property of equality of Σ-types
-- (Σ-≡,≡↔≡).

import Bijection

-- Extensionality.

import Equality

-- "∀ x. f x ≡ g x is in bijective correspondence with f ≡ g"
-- (extensionality-isomorphism).

import Equivalence

------------------------------------------------------------------------
-- 2.4: More Types

-- ⊤, ⊥, _+_ (called _⊎_ in the code), ℕ.

import Prelude

-- Logical equivalences (_⇔_).

import Logical-equivalence

------------------------------------------------------------------------
-- 2.5: Univalent Foundations

-- Contractible.

import Equality

-- H-level, Is-proposition, Is-set.

import H-level

-- Results that can be used to establish that a type has a certain
-- h-level.

import H-level
import H-level.Closure
import Equality.Decidable-UIP

-- Propositional second components of pairs can be dropped
-- (ignore-propositional-component).

import Function-universe

-- Is-equivalence, subst P eq is an equivalence
-- (subst-is-equivalence), _≃_, _≃_ is logically equivalent to _↔_ and
-- related properties (_≃_.bijection, ↔⇒≃, ↔↔≃, ⇔↔≃), congruence
-- properties for Σ and Π (Σ-preserves, Π-preserves),

import Equivalence

-- More congruence properties (including _⊎-cong_ and →-cong).

import Function-universe

-- ≡⇒≃, Univalence, ≃⇒≡, the univalence axiom implies extensionality
-- (dependent-extensionality), the transport theorem (subst-unique),
-- resp eq is an equivalence (resp-is-equivalence), resp eq preserves
-- compositions (resp-preserves-compositions).

import Univalence-axiom

---=====================================================================
-- 3: Isomorphism Is Equality

------------------------------------------------------------------------
-- 3.1: Parameters

-- The parameters are represented using a record type called Universe.

import Univalence-axiom.Isomorphism-implies-equality.Simple

------------------------------------------------------------------------
-- 3.2: Codes for Structures

-- Code, Instance, Is-isomorphism, Isomorphic, Carrier, element,
-- equality-pair-lemma.

import Univalence-axiom.Isomorphism-implies-equality.Simple

------------------------------------------------------------------------
-- 3.3: Main Theorem

-- The main result (isomorphism-is-equality) as well as a corollary
-- (isomorphic≡≡).

import Univalence-axiom.Isomorphism-implies-equality.Simple

------------------------------------------------------------------------
-- 3.4: A Universe

-- U, El, cast, resp, resp-id, Is-isomorphism′,
-- isomorphism-definitions-isomorphic.

import Univalence-axiom.Isomorphism-implies-equality.Simple

-- The operators _→-eq_ (→-cong-⇔), _×-eq_ (_×-cong_) and _+-eq_
-- (_⊎-cong_).

import Function-universe

-- The operators _→-rel_, _×-rel_ and _+-rel_ (_⊎-rel_).

import Prelude

------------------------------------------------------------------------
-- 3.5: Examples

-- Monoids, posets, discrete fields, fixpoint operators.

import Univalence-axiom.Isomorphism-implies-equality.Simple

---=====================================================================
-- 4: Related Work

-- A slightly restricted variant of our main theorem can be proved
-- using one (preliminary?) version of the "Abstract SIP Theorem"
-- (isomorphism-is-equality-is-corollary).

import Univalence-axiom.Isomorphism-implies-equality.Simple

---=====================================================================
-- 5: Conclusions

-- A development with support for multiple carrier types as well as
-- polynomial types (using a computing J rule).

import Univalence-axiom.Isomorphism-implies-equality.More
import Univalence-axiom.Isomorphism-implies-equality.More.Examples
