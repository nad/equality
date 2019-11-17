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

{-# OPTIONS  --cubical --with-K #-}

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
import Erased
import Erased.Cubical
import Erased.Stability
import Erased.With-K
import Function-universe
import H-level
import Nat.Wrapper
import Prelude
import Queue.Truncated

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

Congruence⁺     = Equality.Congruence⁺
Equality-with-J = Equality.Equality-with-J

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

Lemma-14′ = Erased.[]-cong₁.Erased-W↔W

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

Lemmas-22-and-23 = Erased.[]-cong₂.Erased-H-level′↔H-level′

------------------------------------------------------------------------
-- 3.6: Is [_] an embedding?

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

Lemma-25 = Erased.[]-cong₂.Is-proposition→Is-embedding-[]
Lemma-26 = Erased.With-K.Injective-[]
Lemma-27 = Erased.With-K.Is-embedding-[]
Lemma-28 = Erased.With-K.Is-proposition-Erased→Is-proposition

------------------------------------------------------------------------
-- 3.7: More commutation properties

-- There is a single statement for Lemmas 29–34 (and more).

Lemmas-29-to-34 = Erased.[]-cong₃.Erased-↝↔↝

-- There is also a single statement for the variants of Lemmas 29–34,
-- stated as logical equivalences instead of equivalences, that can be
-- proved without using extensionality.

Lemmas-29-to-34-with-⇔ = Erased.[]-cong₃.Erased-↝↝↝

-- Some lemmas.

Lemma-35 = Erased.[]-cong₁.Erased-cong-≃
Lemma-36 = Erased.[]-cong₂.Erased-Is-equivalence↔Is-equivalence

-- The map function.

map = Erased.map

-- A generalisation of Lemma 38.

Lemma-38 = Function-universe.Σ-cong

-- More lemmas.

Lemma-39 = Erased.[]-cong₂.Erased-Split-surjective↔Split-surjective
Lemma-40 = Erased.[]-cong₂.Erased-Has-quasi-inverse↔Has-quasi-inverse
Lemma-41 = Erased.[]-cong₂.Erased-Injective↔Injective
Lemma-42 = Erased.[]-cong₃.Erased-Is-embedding↔Is-embedding
Lemma-43 = Erased.[]-cong₃.map-cong≡cong-map

-- There is a single statement for Lemmas 44–49 (and more).

Lemmas-44-to-49 = Erased.[]-cong₃.Erased-cong

-- The map function is functorial.

map-id = Erased.map-id
map-∘  = Erased.map-∘

-- All preservation lemmas (44–49) map identity to identity (assuming
-- extensionality, except for logical equivalences).

Erased-cong-id = Erased.Stability.[]-cong.Erased-cong-id

-- All preservation lemmas (44–49) commute with composition (assuming
-- extensionality, except for logical equivalences).

Erased-cong-∘ = Erased.Stability.[]-cong.Erased-cong-∘

------------------------------------------------------------------------
-- 3.8: Erased is a modality

-- Some lemmas.

Lemma-50 = Erased.uniquely-eliminating-modality
Lemma-51 = Erased.[]-cong₂.lex-modality

------------------------------------------------------------------------
-- 4.1: Stable types

-- Stable.

Stable = Erased.Stability.Stable

-- Some lemmas.

Lemma-53 = Erased.Stability.¬¬-Stable→Stable
Lemma-54 = Erased.Stability.Erased→¬¬
Lemma-55 = Erased.Stability.Dec→Stable

------------------------------------------------------------------------
-- 4.2: Very stable types

-- Very-stable.

Very-stable = Erased.Stability.Very-stable

-- A generalisation of Very-stable′.

Very-stable′ = Erased.Stability.Stable-[_]

-- Very stable types are stable (and Very-stable A implies
-- Very-stable′ A, and more).

Very-stable→Stable = Erased.Stability.Very-stable→Stable

-- [_] is an embedding for very stable types.

Very-stable→Is-embedding-[] =
  Erased.Stability.Very-stable→Is-embedding-[]

-- Some lemmas.

Lemma-58 = Erased.Stability.[]-cong.Stable→Left-inverse→Very-stable
Lemma-59 = Erased.Stability.[]-cong.Stable-proposition→Very-stable
Lemma-60 = Erased.Stability.Very-stable-Erased

-- It is not the case that every very stable type is a proposition.

¬-Very-stable→Is-proposition =
  Erased.Stability.¬-Very-stable→Is-proposition

------------------------------------------------------------------------
-- 4.3: Stability for equality types

-- Stable-≡ and Very-stable-≡.

Stable-≡      = Erased.Stability.Stable-≡
Very-stable-≡ = Erased.Stability.Very-stable-≡

-- Some lemmas.

Lemma-63 = Erased.Stability.[]-cong.Stable→H-level-suc→Very-stable
Lemma-64 = Erased.Stability.[]-cong.Decidable-equality→Very-stable-≡
Lemma-65 = Erased.Stability.[]-cong.H-level→Very-stable

-- Lemmas 66 and 67, stated both as logical equivalences, and as
-- equivalences depending on extensionality.

Lemma-66 = Erased.Stability.[]-cong.Stable-≡↔Injective-[]
Lemma-67 = Erased.Stability.[]-cong.Very-stable-≡↔Is-embedding-[]

-- Equality is always very stable in traditional Agda.

Very-stable-≡-trivial = Erased.With-K.Very-stable-≡-trivial

------------------------------------------------------------------------
-- 4.4: Map-like functions

-- Lemma 68.

Lemma-68 = Erased.Stability.Stable-map-⇔

-- There is a single statement for Lemmas 69 and 70.

Lemmas-69-and-70 = Erased.Stability.[]-cong.Very-stable-cong

-- Lemma 71.

Lemma-71 = Erased.Stability.[]-cong.Very-stable-Erased↝Erased

-- Lemma 71, with Stable instead of Very-stable, and no assumption of
-- extensionality.

Lemma-71-Stable = Erased.Stability.[]-cong.Stable-Erased↝Erased

------------------------------------------------------------------------
-- 4.5: Closure properties

-- Lots of lemmas.

Lemmas-72-and-73 = Erased.Stability.[]-cong.Very-stable→Very-stable-≡
Lemma-74         = Erased.Stability.Very-stable-⊥
Lemma-75         = Erased.Stability.Very-stable-⊤
Lemma-76         = Erased.Stability.Stable-Π
Lemma-77         = Erased.Stability.Very-stable-Π
Lemma-78         = Erased.Stability.Very-stable-Stable-Σ
Lemma-79         = Erased.Stability.Very-stable-Σ
Lemma-80         = Erased.Stability.Stable-×
Lemma-81         = Erased.Stability.Very-stable-×
Lemma-82         = Erased.Stability.[]-cong.Very-stable-W
Lemmas-83-and-84 = Erased.Stability.Stable-H-level′
Lemmas-85-and-86 = Erased.Stability.[]-cong.Very-stable-H-level′
Lemma-87         = Erased.Stability.Stable-≡-⊎
Lemma-88         = Erased.Stability.[]-cong.Very-stable-≡-⊎
Lemma-89         = Erased.Stability.Stable-≡-List
Lemma-90         = Erased.Stability.[]-cong.Very-stable-≡-List
Lemma-91         = Erased.Cubical.Very-stable-≡-/

------------------------------------------------------------------------
-- 5.1: Efficient natural numbers

-- Nat-[_] and Nat.

Nat-[_] = Nat.Wrapper.Nat-[_]
Nat     = Nat.Wrapper.Nat

-- ⌊_⌋.

@0 ⌊_⌋ : _
⌊_⌋ = Nat.Wrapper.⌊_⌋

-- Lemma 95.

Lemma-95 = Nat.Wrapper.≡-for-indices↔≡

-- The functions unary-[] and unary.

unary-[] = Nat.Wrapper.unary-[]
unary    = Nat.Wrapper.unary

-- Similar functions for arbitrary arities.

n-ary-[] = Nat.Wrapper.n-ary-[]
n-ary    = Nat.Wrapper.n-ary

------------------------------------------------------------------------
-- 5.2: Singleton types with erased equality proofs

-- Some lemmas.

Lemma-98 = Erased.Stability.[]-cong.erased-singleton-contractible
Lemma-99 =
  Erased.Stability.[]-cong.erased-singleton-with-erased-center-propositional

-- The generalisation of Lemma 79 used in the proof of Lemma 99.

Lemma-79-generalised = Erased.Stability.[]-cong.Very-stable-Σⁿ

-- More lemmas.

Lemma-100 = Erased.Cubical.↠→↔Erased-singleton
Lemma-101 = Erased.Stability.[]-cong.Σ-Erased-Erased-singleton↔

------------------------------------------------------------------------
-- 5.3: Converting Nat to ℕ

-- Some lemmas.

Lemma-102 = Nat.Wrapper.Nat-[]↔Σℕ
Lemma-103 = Nat.Wrapper.Nat↔ℕ
@0 Lemma-104 : _
Lemma-104 = Nat.Wrapper.≡⌊⌋
Lemma-105 = Nat.Wrapper.unary-correct

-- A variant of Lemma 105 for n-ary.

Lemma-105-for-n-ary = Nat.Wrapper.n-ary-correct

------------------------------------------------------------------------
-- 5.4: Decidable equality

-- Lemma 106.

Lemma-106 = Nat.Wrapper.Operations-for-Nat._≟_

-- The assumption with number 107.

Assumption-107 = Nat.Wrapper.Operations._≟_

-- Lemma 108.

Lemma-108 = Nat.Wrapper.Operations-for-Nat-[]._≟_

------------------------------------------------------------------------
-- 5.5: Queues

-- The implementation of queues (parametrised by an underlying queue
-- implementation).

module Queue = Queue.Truncated

-- The functions enqueue and dequeue.

enqueue = Queue.Truncated.Non-indexed.enqueue
dequeue = Queue.Truncated.Non-indexed.dequeue

------------------------------------------------------------------------
-- 6: Discussion and related work

-- Nat-[_]′.

Nat-[_]′ = Nat.Wrapper.Nat-with-∥∥.Nat-[_]′

-- An alternative implementation of Nat.

Alternative-Nat = Nat.Wrapper.Nat-with-∥∥.Nat-with-∥∥

-- The alternative implementation of Nat is isomorphic to the unit
-- type.

Alternative-Nat-isomorphic-to-⊤ = Nat.Wrapper.Nat-with-∥∥.Nat-with-∥∥↔⊤

-- The alternative implementation of Nat is not isomorphic to the
-- natural numbers.

Alternative-Nat-not-isomorphic-to-ℕ =
  Nat.Wrapper.Nat-with-∥∥.¬-Nat-with-∥∥↔ℕ
