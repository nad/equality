------------------------------------------------------------------------
-- Code related to the paper "Logical properties of a modality for
-- erasure"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Note that the code does not follow the paper exactly. For instance,
-- some definitions use bijections (functions with quasi-inverses)
-- instead of equivalences. Some other differences are mentioned
-- below.

-- This file is not checked using --safe, because some parts use
-- --cubical, and some parts use --with-K. However, all files
-- imported below use --safe.

{-# OPTIONS --cubical --with-K #-}

module README.Erased where

import Agda.Builtin.Equality
import Agda.Builtin.Cubical.Id
import Agda.Builtin.Cubical.Path

import Embedding
import Equality
import Equality.Id
import Equality.Instances-related
import Equality.Path
import Equality.Propositional
import Equivalence
import Erased
import Erased.Cubical
import Erased.With-K
import Function-universe
import H-level
import Nat.Wrapper
import Nat.Wrapper.Cubical
import Prelude
import Queue.Truncated
import Quotient

------------------------------------------------------------------------
-- 3: Erased

-- Erased.

Erased = Erased.Erased

------------------------------------------------------------------------
-- 3.1: Erased is a monad

-- Bind.

bind = Erased._>>=′_

-- Erased is a monad.

erased-monad = Erased.monad

-- Lemma 3.

Lemma-3 = Erased.Erased-Erased↔Erased

------------------------------------------------------------------------
-- 3.2: The relationship between @0 and Erased

-- Lemma 4 and Lemma 5.

Lemmas-4-and-5 = Erased.Π-Erased↔Π0[]

-- The equality type family, defined as an inductive family.

Equality-defined-as-an-inductive-family = Agda.Builtin.Equality._≡_

-- Cubical Agda paths.

Path = Agda.Builtin.Cubical.Path._≡_

-- The Cubical Agda identity type family.

Id = Agda.Builtin.Cubical.Id.Id

-- The code uses an axiomatisation of "equality with J". The
-- axiomatisation is a little convoluted in order to support using
-- equality at all universe levels. Furthermore the axiomatisation
-- supports choosing specific definitions for other functions, like
-- cong, to make the code more usable when it is instantiated with
-- Cubical Agda paths (for which the canonical definition of cong
-- computes in a different way than typical definitions obtained
-- using J).

-- Equality and reflexivity.

≡-refl = Equality.Reflexive-relation

-- The J rule and its computation rule.

J-J-refl = Equality.Equality-with-J₀

-- Extended variants of the two definitions above.

Equivalence-relation⁺ = Equality.Equivalence-relation⁺
Equality-with-J       = Equality.Equality-with-J

-- To see how the code is axiomatised, see the module header of, say,
-- Erased.

module See-the-module-header-of = Erased

-- The equality type family defined as an inductive family, Cubical
-- Agda paths and the Cubical Agda identity type family can all be
-- used to instantiate the axioms.

Equality-with-J-for-equality-defined-as-an-inductive-family =
  Equality.Propositional.equality-with-J
Equality-with-J-for-Path = Equality.Path.equality-with-J
Equality-with-J-for-Id   = Equality.Id.equality-with-J

-- Lemma 7 in Cubical Agda.

Lemma-7-cubical = Erased.Cubical.Π-Erased≃Π0[]

-- Lemma 7 in traditional Agda.

Lemma-7-traditional = Erased.With-K.Π-Erased≃Π0[]

------------------------------------------------------------------------
-- 3.3: Erased commutes

-- Some lemmas.

Lemma-8  = Erased.Erased-⊤↔⊤
Lemma-9  = Erased.Erased-⊥↔⊥
Lemma-10 = Erased.Erased-Π↔Π
Lemma-11 = Erased.Erased-Π↔Π-Erased
Lemma-12 = Erased.Erased-Σ↔Σ

-- W-types.

W = Prelude.W

-- Lemma 14 (Erased commutes with W-types up to logical equivalence).

Lemma-14 = Erased.Erased-W⇔W

-- Erased commutes with W-types, assuming extensionality for functions
-- and []-cong.
--
-- The code uses a universe of "function formers" which makes it
-- possible to prove a single statement that can be instantiated both
-- as a logical equivalence that does not rely on extensionality, as
-- well as an equivalence that does rely on extensionality (and in
-- other ways). This lemma, and several others, are stated in that
-- way.

Lemma-14′ = Erased.Erased-W↔W

------------------------------------------------------------------------
-- 3.4: The []-cong property

-- []-cong, proved in traditional Agda.

[]-cong-traditional = Erased.With-K.[]-cong

-- []-cong, proved in Cubical Agda for paths.

[]-cong-cubical-paths = Erased.Cubical.[]-cong-Path

-- Every family of equality types satisfying the axiomatisation
-- discussed above is in pointwise bijective correspondence with every
-- other, with the bijections mapping reflexivity to reflexivity.

Families-equivalent =
  Equality.Instances-related.all-equality-types-isomorphic

-- []-cong, proved in Cubical Agda for an arbitrary equality type
-- family satisfying the axiomatisation discussed above.

[]-cong-cubical = Erased.Cubical.[]-cong

-- Lemmas 17 and 18 in traditional Agda.

Lemma-17-traditional = Erased.With-K.[]-cong-equivalence
Lemma-18-traditional = Erased.With-K.[]-cong-[refl]

-- Lemmas 17 and 18 in Cubical Agda, with paths.

Lemma-17-cubical-paths = Erased.Cubical.[]-cong-Path-equivalence
Lemma-18-cubical-paths = Erased.Cubical.[]-cong-Path-[refl]

-- Lemmas 17 and 18 in Cubical Agda, with an arbitrary family of
-- equality types satisfying the axiomatisation discussed above.

Lemma-17-cubical = Erased.Cubical.[]-cong-equivalence
Lemma-18-cubical = Erased.Cubical.[]-cong-[refl]

------------------------------------------------------------------------
-- 3.5: H-levels

-- H-level, For-iterated-equality and Contractible.

H-level               = H-level.H-level′
For-iterated-equality = H-level.For-iterated-equality
Contractible          = Equality.Reflexive-relation′.Contractible

-- Sometimes the code uses the following definition of h-levels
-- instead of the one used in the paper.

Other-definition-of-h-levels = H-level.H-level

-- The two definitions are pointwise logically equivalent, and
-- pointwise equivalent if equality is extensional for functions.

H-level≃H-level′ = Function-universe.H-level↔H-level′

-- There is a single statement for Lemmas 22 and 23.

Lemmas-22-and-23 = Erased.Erased-H-level′↔H-level′

------------------------------------------------------------------------
-- 3.6: Erased is a modality

-- Some lemmas.

Lemma-24 = Erased.uniquely-eliminating-modality
Lemma-25 = Erased.lex-modality

-- The map function.

map = Erased.map

-- Erased is a Σ-closed reflective subuniverse.

Σ-closed-reflective-subuniverse =
  Erased.Erased-Σ-closed-reflective-subuniverse

-- Another lemma.

Lemma-27 = Erased.Erased-connected↔Erased-Is-equivalence

------------------------------------------------------------------------
-- 3.7: Is [_] an embedding?

-- The function cong is unique up to pointwise equality if it is
-- required to map the canonical proof of reflexivity to the canonical
-- proof of reflexivity.

cong-canonical =
  Equality.Derived-definitions-and-properties.cong-canonical

-- Is-embedding.

Is-embedding = Embedding.Is-embedding

-- Embeddings are injective.

embeddings-are-injective = Embedding.injective

-- Some lemmas.

Lemma-29 = Erased.Is-proposition→Is-embedding-[]
Lemma-30 = Erased.With-K.Injective-[]
Lemma-31 = Erased.With-K.Is-embedding-[]
Lemma-32 = Erased.With-K.Is-proposition-Erased→Is-proposition

------------------------------------------------------------------------
-- 3.8: More commutation properties

-- There is a single statement for Lemmas 33–38 (and more).

Lemmas-33-to-38 = Erased.Erased-↝↔↝

-- There is also a single statement for the variants of Lemmas 33–38,
-- stated as logical equivalences instead of equivalences, that can be
-- proved without using extensionality.

Lemmas-33-to-38-with-⇔ = Erased.Erased-↝↝↝

-- Some lemmas.

Lemma-39 = Erased.Erased-cong-≃
Lemma-40 = Erased.Erased-Is-equivalence↔Is-equivalence

-- A generalisation of Lemma 41.

Lemma-41 = Function-universe.Σ-cong

-- More lemmas.

Lemma-42 = Erased.Erased-Split-surjective↔Split-surjective
Lemma-43 = Erased.Erased-Has-quasi-inverse↔Has-quasi-inverse
Lemma-44 = Erased.Erased-Injective↔Injective
Lemma-45 = Erased.Erased-Is-embedding↔Is-embedding
Lemma-46 = Erased.map-cong≡cong-map

-- There is a single statement for Lemmas 47–52 (and more).

Lemmas-47-to-52 = Erased.Erased-cong

-- The map function is functorial.

map-id = Erased.map-id
map-∘  = Erased.map-∘

-- All preservation lemmas (47–52) map identity to identity (assuming
-- extensionality, except for logical equivalences).

Erased-cong-id = Erased.Erased-cong-id

-- All preservation lemmas (47–52) commute with composition (assuming
-- extensionality, except for logical equivalences).

Erased-cong-∘ = Erased.Erased-cong-∘

------------------------------------------------------------------------
-- 4.1: Stable types

-- Stable.

Stable = Erased.Stable

-- Some lemmas.

Lemma-54 = Erased.¬¬-Stable→Stable
Lemma-55 = Erased.Erased→¬¬
Lemma-56 = Erased.Dec→Stable

------------------------------------------------------------------------
-- 4.2: Very stable types

-- Very-stable.

Very-stable = Erased.Very-stable

-- A generalisation of Very-stable′.

Very-stable′ = Erased.Stable-[_]

-- Very stable types are stable (and Very-stable A implies
-- Very-stable′ A, and more).

Very-stable→Stable = Erased.Very-stable→Stable

-- [_] is an embedding for very stable types.

Very-stable→Is-embedding-[] = Erased.Very-stable→Is-embedding-[]

-- Some lemmas.

Lemma-59 = Erased.Stable→Left-inverse→Very-stable
Lemma-60 = Erased.Stable-proposition→Very-stable
Lemma-61 = Erased.Very-stable-Erased

-- It is not the case that every very stable type is a proposition.

¬-Very-stable→Is-proposition = Erased.¬-Very-stable→Is-proposition

-- More lemmas.

Lemma-62 = Erased.Very-stable-∃-Very-stable
Lemma-63 = Erased.Stable-∃-Very-stable

------------------------------------------------------------------------
-- 4.3: Stability for equality types

-- Stable-≡ and Very-stable-≡.

Stable-≡      = Erased.Stable-≡
Very-stable-≡ = Erased.Very-stable-≡

-- Some lemmas.

Lemma-66 = Erased.Stable→H-level-suc→Very-stable
Lemma-67 = Erased.Decidable-equality→Very-stable-≡
Lemma-68 = Erased.H-level→Very-stable

-- Lemmas 69 and 70, stated both as logical equivalences, and as
-- equivalences depending on extensionality.

Lemma-69 = Erased.Stable-≡↔Injective-[]
Lemma-70 = Erased.Very-stable-≡↔Is-embedding-[]

-- Equality is always very stable in traditional Agda.

Very-stable-≡-trivial = Erased.With-K.Very-stable-≡-trivial

------------------------------------------------------------------------
-- 4.4: Map-like functions

-- Lemma 71.

Lemma-71 = Erased.Stable-map-⇔

-- There is a single statement for Lemmas 72 and 73.

Lemmas-72-and-73 = Erased.Very-stable-cong

-- Lemma 74.

Lemma-74 = Erased.Very-stable-Erased↝Erased

-- Lemma 74, with Stable instead of Very-stable, and no assumption of
-- extensionality.

Lemma-74-Stable = Erased.Stable-Erased↝Erased

------------------------------------------------------------------------
-- 4.5: Closure properties

-- Lots of lemmas.

Lemmas-75-and-76 = Erased.Very-stable→Very-stable-≡
Lemma-77         = Erased.Very-stable-⊤
Lemma-78         = Erased.Very-stable-⊥
Lemma-79         = Erased.Stable-Π
Lemma-80         = Erased.Very-stable-Π
Lemma-81         = Erased.Very-stable-Stable-Σ
Lemma-82         = Erased.Very-stable-Σ
Lemma-83         = Erased.Stable-×
Lemma-84         = Erased.Very-stable-×
Lemma-85         = Erased.Very-stable-W
Lemmas-86-and-87 = Erased.Stable-H-level′
Lemmas-88-and-89 = Erased.Very-stable-H-level′
Lemma-90         = Erased.Stable-≡-⊎
Lemma-91         = Erased.Very-stable-≡-⊎
Lemma-92         = Erased.Stable-≡-List
Lemma-93         = Erased.Very-stable-≡-List
Lemma-94         = Quotient.Very-stable-≡-/

------------------------------------------------------------------------
-- 4.6: []‐cong can be proved using extensionality

-- The proof has been changed. Lemmas 95 and 97 have been removed.

-- A lemma.

Lemma-96 = Equivalence.≃-≡

-- []-cong, proved using extensionality, along with proofs showing
-- that it is an equivalence and that it satisfies the computation
-- rule of []-cong.

Extensionality→[]-cong = Erased.Extensionality→[]-cong

------------------------------------------------------------------------
-- 5.1: Singleton types with erased equality proofs

-- Some lemmas.

Lemma-99  = Erased.erased-singleton-contractible
Lemma-100 = Erased.erased-singleton-with-erased-center-propositional

-- The generalisation of Lemma 82 used in the proof of Lemma 100.

Lemma-82-generalised = Erased.Very-stable-Σⁿ

-- Another lemma.

Lemma-101 = Erased.Σ-Erased-Erased-singleton↔

------------------------------------------------------------------------
-- 5.2: Efficient natural numbers

-- An implementation of natural numbers as lists of bits with the
-- least significant bit first and an erased invariant that ensures
-- that there are no trailing zeros.

import Nat.Binary

-- Nat-[_].

Nat-[_] = Nat.Wrapper.Nat-[_]

-- A lemma.

Lemma-103 = Nat.Wrapper.Nat-[]-propositional

-- Nat.

Nat = Nat.Wrapper.Nat

-- ⌊_⌋.

@0 ⌊_⌋ : _
⌊_⌋ = Nat.Wrapper.⌊_⌋

-- Another lemma.

Lemma-106 = Nat.Wrapper.≡-for-indices↔≡

------------------------------------------------------------------------
-- 5.2.1: Arithmetic

-- The functions unary-[] and unary.

unary-[] = Nat.Wrapper.unary-[]
unary    = Nat.Wrapper.unary

-- Similar functions for arbitrary arities.

n-ary-[] = Nat.Wrapper.n-ary-[]
n-ary    = Nat.Wrapper.n-ary

------------------------------------------------------------------------
-- 5.2.2: Converting Nat to ℕ

-- Some lemmas.

Lemma-109 = Nat.Wrapper.Nat-[]↔Σℕ
Lemma-110 = Nat.Wrapper.Nat↔ℕ
@0 Lemma-111 : _
Lemma-111 = Nat.Wrapper.≡⌊⌋
Lemma-112 = Nat.Wrapper.unary-correct

-- A variant of Lemma 112 for n-ary.

Lemma-112-for-n-ary = Nat.Wrapper.n-ary-correct

------------------------------------------------------------------------
-- 5.2.3: Decidable equality

-- Some lemmas.

Lemma-113 = Nat.Wrapper.Operations-for-Nat._≟_
Lemma-114 = Nat.Wrapper.Operations-for-Nat-[]._≟_

------------------------------------------------------------------------
-- 5.3: Queues

-- The implementation of queues (parametrised by an underlying queue
-- implementation).

module Queue = Queue.Truncated

-- The functions enqueue and dequeue.

enqueue = Queue.Truncated.Non-indexed.enqueue
dequeue = Queue.Truncated.Non-indexed.dequeue

------------------------------------------------------------------------
-- 6: Discussion and related work

-- Nat-[_]′.

Nat-[_]′ = Nat.Wrapper.Cubical.Nat-[_]′

-- An alternative implementation of Nat.

Alternative-Nat = Nat.Wrapper.Cubical.Nat-with-∥∥

-- The alternative implementation of Nat is isomorphic to the unit
-- type.

Alternative-Nat-isomorphic-to-⊤ = Nat.Wrapper.Cubical.Nat-with-∥∥↔⊤

-- The alternative implementation of Nat is not isomorphic to the
-- natural numbers.

Alternative-Nat-not-isomorphic-to-ℕ =
  Nat.Wrapper.Cubical.¬-Nat-with-∥∥↔ℕ
