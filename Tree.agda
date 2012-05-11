------------------------------------------------------------------------
-- Binary trees
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Tree where

open import Bag-equivalence
open import Equality.Propositional
open import Prelude hiding (id)

import Bijection
open Bijection equality-with-J using (_↔_)
import Function-universe
open Function-universe equality-with-J

------------------------------------------------------------------------
-- Binary trees

data Tree (A : Set) : Set where
  leaf : Tree A
  node : (l : Tree A) (x : A) (r : Tree A) → Tree A

-- Any.

AnyT : ∀ {A} → (A → Set) → (Tree A → Set)
AnyT P leaf         = ⊥
AnyT P (node l x r) = AnyT P l ⊎ P x ⊎ AnyT P r

-- Membership.

_∈T_ : ∀ {A} → A → Tree A → Set
x ∈T t = AnyT (_≡_ x) t

------------------------------------------------------------------------
-- Singleton

-- Singleton trees.

singleton : {A : Set} → A → Tree A
singleton x = node leaf x leaf

-- Any lemma for singleton.

Any-singleton : ∀ {A : Set} (P : A → Set) {x} →
                AnyT P (singleton x) ↔ P x
Any-singleton P {x} =
  AnyT P (singleton x)  ↔⟨ id ⟩
  ⊥ ⊎ P x ⊎ ⊥           ↔⟨ ⊎-left-identity ⟩
  P x ⊎ ⊥               ↔⟨ ⊎-right-identity ⟩
  P x                   □

------------------------------------------------------------------------
-- Flatten

-- Inorder flattening of a tree.

flatten : {A : Set} → Tree A → List A
flatten leaf         = []
flatten (node l x r) = flatten l ++ x ∷ flatten r

-- Flatten does not add or remove any elements.

flatten-lemma : {A : Set} (t : Tree A) → ∀ z → z ∈ flatten t ↔ z ∈T t
flatten-lemma leaf         = λ z → ⊥ □
flatten-lemma (node l x r) = λ z →
  z ∈ flatten l ++ x ∷ flatten r         ↔⟨ Any-++ (_≡_ z) _ _ ⟩
  z ∈ flatten l ⊎ z ≡ x ⊎ z ∈ flatten r  ↔⟨ flatten-lemma l z ⊎-cong (z ≡ x □) ⊎-cong flatten-lemma r z ⟩
  z ∈T l        ⊎ z ≡ x ⊎ z ∈T r         □
