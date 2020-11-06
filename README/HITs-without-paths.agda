------------------------------------------------------------------------
-- Code related to the paper "Higher Inductive Type Eliminators
-- Without Paths"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Note that the code does not follow the paper exactly. For instance,
-- some definitions use bijections (functions with quasi-inverses)
-- instead of equivalences. Furthermore type universes are called
-- "Set a" instead of "Type a".

{-# OPTIONS --cubical --safe #-}

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
import Suspension

------------------------------------------------------------------------
-- 1: Introduction

-- The propositional truncation operator.

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
Equality-with-paths   = Equality.Path.Equality-with-paths

-- The extended variants are inhabited for all universe levels if the
-- basic ones are inhabited for all universe levels.

J₀⇒Equivalence-relation⁺             = Equality.J₀⇒Equivalence-relation⁺
J₀⇒J                                 = Equality.J₀⇒J
Equality-with-J₀⇒Equality-with-paths =
  Equality.Path.Equality-with-J₀⇒Equality-with-paths

-- To see how the code is axiomatised, see the module header of, say,
-- Circle.

import Circle

-- Any two notions of equality satisfying the axioms are pointwise
-- isomorphic, and the isomorphisms map canonical proofs of
-- reflexivity to canonical proofs of reflexivity.
--
-- Note that in some cases the code uses bijections (_↔_) instead of
-- equivalences (_≃_).

instances-isomorphic =
  Equality.Instances-related.all-equality-types-isomorphic

-- Cubical Agda paths, the Cubical Agda identity type family, and a
-- definition of equality as an inductive family with a single
-- constructor refl are instances of the axioms. (The last instance is
-- for Equality-with-J rather than Equality-with-paths, because the
-- latter definition is defined in Cubical Agda, and the instance is
-- not.)

paths-instance            = Equality.Path.equality-with-paths
id-instance               = Equality.Id.equality-with-paths
inductive-family-instance = Equality.Propositional.equality-with-J

------------------------------------------------------------------------
-- 3: Homogeneous Paths

-- The path type constructor.

Path = Equality.Path._≡_

-- Zero and one.

0̲ = Equality.Path.0̲
1̲ = Equality.Path.1̲

-- Reflexivity.

reflᴾ = Equality.Path.refl

-- Minimum, maximum and negation.

min = Equality.Path.min
max = Equality.Path.max
-_  = Equality.Path.-_

-- The primitive transport operation.

open Equality.Path using (transport)

-- The J rule and transport-refl.

Jᴾ             = Equality.Path.elim
transport-refl = Equality.Path.transport-refl

-- Transitivity (more general than in the paper).

transᴾ = Equality.Path.htransʳ

------------------------------------------------------------------------
-- 4: Heterogeneous Paths

-- Pathᴴ.

Pathᴴ = Equality.Path.[_]_≡_

-- The eliminator elimᴾ for the propositional truncation operator.

module ∥_∥ where

  elimᴾ = H-level.Truncation.Propositional.elimᴾ′

-- Pathᴴ≡Path and Pathᴴ≃Path.

Pathᴴ≡Path = Equality.Path.heterogeneous≡homogeneous
Pathᴴ≃Path = Equality.Path.heterogeneous↔homogeneous

-- The lemma substᴾ.

substᴾ = Equality.Path.subst

-- The lemmas subst and subst-refl from the axiomatisation.

subst      = Equality.Equality-with-J.subst
subst-refl = Equality.Equality-with-J.subst-refl

-- The axiomatisation makes it possible to choose the implementations
-- of to-path and from-path.

to-path   = Equality.Path.Equality-with-paths.to-path
from-path = Equality.Path.Equality-with-paths.from-path

-- The code mostly uses a pointwise isomorphism between the arbitrary
-- notion of equality and paths instead of from-path and to-path.

≡↔≡ = Equality.Path.Derived-definitions-and-properties.≡↔≡

-- The lemmas subst≡substᴾ, subst≡≃Pathᴴ, subst≡→Pathᴴ and
-- subst≡→substᴾ≡ (which is formulated as a bijection).

subst≡substᴾ   = Equality.Path.Isomorphisms.subst≡subst
subst≡≃Pathᴴ   = Equality.Path.Isomorphisms.subst≡↔[]≡
subst≡→Pathᴴ   = Equality.Path.Isomorphisms.subst≡→[]≡
subst≡→substᴾ≡ = Equality.Path.Isomorphisms.subst≡↔subst≡

-- The lemmas congᴰ and congᴰ-refl from the axiomatisation.

congᴰ      = Equality.Equality-with-J.dcong
congᴰ-refl = Equality.Equality-with-J.dcong-refl

-- The lemmas congᴴ and congᴰᴾ.

congᴴ  = Equality.Path.hcong
congᴰᴾ = Equality.Path.dcong

-- The proofs congᴰ≡congᴰᴾ, congᴰᴾ≡congᴴ, congᴰ≡congᴴ and
-- dependent‐computation‐rule‐lemma.

congᴰ≡congᴰᴾ = Equality.Path.Isomorphisms.dcong≡dcong
congᴰᴾ≡congᴴ = Equality.Path.dcong≡hcong
congᴰ≡congᴴ = Equality.Path.Isomorphisms.dcong≡hcong
dependent‐computation‐rule‐lemma =
  Equality.Path.Isomorphisms.dcong-subst≡→[]≡

------------------------------------------------------------------------
-- 5: The Circle Without Paths

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
-- that I use, but which can be proved using the J rule.

trans    = Equality.Equivalence-relation⁺.trans
J₀⇒trans = Equality.J₀⇒Equivalence-relation⁺

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
-- 6: Set Quotients Without Paths

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
transport-transport         = Equality.Path.transport∘transport
heterogeneous-irrelevance   = Equality.Path.heterogeneous-irrelevance
heterogeneous-UIP           = Equality.Path.heterogeneous-UIP
H-level≃H-levelᴾ            = Equality.Path.Isomorphisms.H-level↔H-level

-- A generalisation of Π-cong. Note that equality is provably
-- extensional in Cubical Agda.

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
-- 7: More Examples

-- Suspensions.

module Susp where

  Susp          = Suspension.Susp
  elimᴾ         = Suspension.elimᴾ
  recᴾ          = Suspension.recᴾ
  meridian      = Suspension.meridian
  elim          = Suspension.elim
  elim-meridian = Suspension.elim-meridian
  rec           = Suspension.rec
  rec-meridian  = Suspension.rec-meridian

-- The propositional truncation operator.

module Propositional-truncation where

  elimᴾ′  = H-level.Truncation.Propositional.elimᴾ′
  elimᴾ   = H-level.Truncation.Propositional.elimᴾ
  recᴾ    = H-level.Truncation.Propositional.recᴾ
  trivial = H-level.Truncation.Propositional.truncation-is-proposition
  elim    = H-level.Truncation.Propositional.elim
  rec     = H-level.Truncation.Propositional.rec

------------------------------------------------------------------------
-- 8: An Alternative Approach

-- Circle and Circleᴾ, combined into a single definition.

Circle = Circle.Circle

-- Circleᴾ≃Circle, circleᴾ and circle.

Circleᴾ≃Circle = Circle.Circle≃Circle
circleᴾ        = Circle.circleᴾ
circle         = Circle.circle

-- The computation rule for the higher constructor.

elim-loop-circle = Circle.elim-loop-circle

-- Alternative definitions of Circleᴾ≃Circle and circle that (at the
-- time of writing) do not give the "correct" computational behaviour
-- for the point constructor.

Circleᴾ≃Circle′ = Circle.Circle≃Circle′
circle′         = Circle.circle′

------------------------------------------------------------------------
-- 9: Discussion

-- The interval.

import Interval

-- Pushouts.

import Pushout

-- A general truncation operator.

import H-level.Truncation

-- The torus.

import Torus
