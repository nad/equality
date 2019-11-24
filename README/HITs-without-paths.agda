------------------------------------------------------------------------
-- Code related to the paper "Higher Inductive Types Without Paths"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Note that the code does not follow the paper exactly. For instance,
-- some definitions use bijections (functions with quasi-inverses)
-- instead of equivalences.

{-# OPTIONS  --cubical --safe #-}

module README.HITs-without-paths where

import Equality
import Equality.Id
import Equality.Instances-related
import Equality.Path
import Equality.Path.Isomorphisms
import Equality.Propositional
import Function-universe
import H-level
import H-level.Truncation.Propositional
import Quotient

------------------------------------------------------------------------
-- 1: Introduction

-- The propositional truncation.

∥_∥ = H-level.Truncation.Propositional.∥_∥

-- Equality defined as an inductive family with a single constructor
-- refl.

_≡_ = Equality.Propositional._≡_

------------------------------------------------------------------------
-- 2: An Axiomatisation of Equality With J

-- The code uses an axiomatisation of "equality with J", as discussed
-- in the text. The axiomatisation is a little convoluted in order to
-- support using equality at all universe levels. Furthermore, also as
-- discussed in the text, the axiomatisation supports choosing
-- specific definitions for other functions, like cong, to make the
-- code more usable when it is instantiated with Cubical Agda paths
-- (for which the canonical definition of cong computes in a different
-- way than typical definitions obtained using J).

-- Equality and reflexivity.

≡-refl = Equality.Reflexive-relation

-- The J rule and its computation rule.

J-J-refl = Equality.Equality-with-J₀

-- Extended variants of the two definitions above.

Equivalence-relation⁺ = Equality.Equivalence-relation⁺
Equality-with-J       = Equality.Equality-with-J

-- The extended variants are inhabited for all universe levels if the
-- basic ones are inhabited for all universe levels.

J₀⇒Equivalence-relation⁺ = Equality.J₀⇒Equivalence-relation⁺
J₀⇒J                     = Equality.J₀⇒J

-- To see how the code is axiomatised, see the module header of, say,
-- Circle.

import Circle

-- Any two notions of equality satisfying the axioms are pointwise
-- isomorphic, and the isomorphisms map canonical proofs of
-- reflexivity to canonical proofs of reflexivity.

instances-isomorphic =
  Equality.Instances-related.all-equality-types-isomorphic

-- Cubical Agda paths, the Cubical Agda identity type family, and a
-- definition of equality as an inductive family with a single
-- constructor refl are instances of the axioms.

paths-instance            = Equality.Path.equality-with-J
id-instance               = Equality.Id.equality-with-J
inductive-family-instance = Equality.Propositional.equality-with-J

------------------------------------------------------------------------
-- 3: Heterogeneous Paths

-- Pathᴴ and Path.

Pathᴴ = Equality.Path.[_]_≡_
Path  = Equality.Path._≡_

-- The eliminator elimᴾ for the propositional truncation.

module ∥_∥ where

  elimᴾ = H-level.Truncation.Propositional.elimᴾ′

------------------------------------------------------------------------
-- 3.1: An Equivalence

-- The equivalence.

Pathᴴ≃Path = Equality.Path.heterogeneous↔homogeneous

-- A variant of transitivity.

transᴴᵣ = Equality.Path.htransʳ

------------------------------------------------------------------------
-- 3.2: Consequences of the Equivalence

-- The lemmas subst and subst-refl from the axiomatisation.

subst      = Equality.Equality-with-J.subst
subst-refl = Equality.Equality-with-J.subst-refl

-- The lemmas substᴴ and substᴾ.

substᴴ = Equality.Path.hsubst
substᴾ = Equality.Path.subst

-- A pointwise isomorphism between the arbitrary notion of equality
-- and paths (used instead of from-path and to-path).

≡↔≡ = Equality.Path.Isomorphisms.≡↔≡

-- The lemmas subst≡substᴾ, subst≡≃Pathᴴ and subst≡→Pathᴴ.

subst≡substᴾ = Equality.Path.Isomorphisms.subst≡subst
subst≡≃Pathᴴ = Equality.Path.Isomorphisms.subst≡↔[]≡
subst≡→Pathᴴ = Equality.Path.Isomorphisms.subst≡→[]≡

-- The lemmas congᴰ and congᴰ-refl from the axiomatisation.

congᴰ      = Equality.Equality-with-J.dcong
congᴰ-refl = Equality.Equality-with-J.dcong-refl

-- The lemma congᴴ.

congᴴ = Equality.Path.hcong

-- The proofs congᴰ≡congᴴ and dependent‐computation‐rule‐lemma.

congᴰ≡congᴴ = Equality.Path.Isomorphisms.dcong≡hcong
dependent‐computation‐rule‐lemma =
  Equality.Path.Isomorphisms.dcong-subst≡→[]≡

------------------------------------------------------------------------
-- 4: The Circle Without Paths

-- The circle and loop.

𝕊¹   = Circle.𝕊¹
loop = Circle.loop

-- The lemmas cong and cong-refl from the axiomatisation.

cong      = Equality.Equality-with-J.cong
cong-refl = Equality.Equality-with-J.cong-refl

-- The lemma non-dependent-computation-rule-lemma.

non-dependent-computation-rule-lemma =
  Equality.Path.Isomorphisms.cong-≡↔≡

-- The lemma trans, which is actually a part of the axiomatisation
-- that I use (but which can be proved using J).

trans = Equality.Equivalence-relation⁺.trans

-- The lemma subst-const.

subst-const = Equality.Derived-definitions-and-properties.subst-const

-- The lemma congᴰ≡→cong≡.

congᴰ≡→cong≡ = Equality.Derived-definitions-and-properties.dcong≡→cong≡

-- Eliminators and computation rules.

module 𝕊¹ where

  elimᴾ     = Circle.elimᴾ
  recᴾ      = Circle.recᴾ
  elim      = Circle.elim
  elim-loop = Circle.elim-loop
  rec       = Circle.rec
  rec-loop  = Circle.rec-loop
  rec′      = Circle.rec′
  rec′-loop = Circle.rec′-loop

------------------------------------------------------------------------
-- 5: Set Quotients Without Paths

-- The definition of h-levels.

Contractible   = Equality.Derived-definitions-and-properties.Contractible
H-level        = H-level.H-level
Is-proposition = Equality.Derived-definitions-and-properties.Is-proposition
Is-set         = Equality.Derived-definitions-and-properties.Is-set

-- Set quotients.

_/_ = Quotient._/_

-- Some lemmas.

H-levelᴾ-suc≃H-levelᴾ-Pathᴴ = Equality.Path.H-level-suc↔H-level[]≡
index-irrelevant            = Equality.Path.index-irrelevant
transport-refl              = Equality.Path.transport-refl
transport-transport         = Equality.Path.transport∘transport
heterogeneous-irrelevance   = Equality.Path.heterogeneous-irrelevance
heterogeneous-UIP           = Equality.Path.heterogeneous-UIP
H-level≃H-levelᴾ            = Equality.Path.Isomorphisms.H-level↔H-level

-- A generalisation of Π-cong. Note that equality is provably
-- extensionality in Cubical Agda.

Π-cong         = Function-universe.Π-cong
extensionality = Equality.Path.ext

-- Variants of the constructors.

[]-respects-relation = Quotient.[]-respects-relation
/-is-set             = Quotient./-is-set

-- Eliminators.

module _/_ where

  elimᴾ′ = Quotient.elimᴾ′
  elimᴾ  = Quotient.elimᴾ
  recᴾ   = Quotient.recᴾ
  elim   = Quotient.elim
  rec    = Quotient.rec

------------------------------------------------------------------------
-- 6: Discussion

-- The interval.

import Interval

-- Suspensions.

import Suspension

-- Pushouts.

import Pushout

-- A general truncation operator.

import H-level.Truncation

-- The propositional truncation.

import H-level.Truncation.Propositional

-- The torus.

import Torus
