------------------------------------------------------------------------
-- Finite binary trees with information in internal nodes
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Tree where

open import Bag-equality using (Any-++) renaming (_∈_ to _∈L_)
open import Equality.Propositional
open import Prelude hiding (id)

import Bijection
open Bijection equality-with-J using (_↔_)
import Function-universe
open Function-universe equality-with-J

------------------------------------------------------------------------
-- Types

-- Trees.

data Tree (A : Set) : Set where
  leaf : Tree A
  node : (l : Tree A) (x : A) (r : Tree A) → Tree A

-- Any.

Any : {A : Set} → (A → Set) → Tree A → Set
Any P leaf         = ⊥
Any P (node l x r) = Any P l ⊎ P x ⊎ Any P r

-- Tree membership.

infix 4 _∈_

_∈_ : {A : Set} → A → Tree A → Set
x ∈ t = Any (λ y → x ≡ y) t

-- Bag equality.

infix 4 _≈-bag_

_≈-bag_ : {A : Set} → Tree A → Tree A → Set
t₁ ≈-bag t₂ = ∀ z → z ∈ t₁ ↔ z ∈ t₂

------------------------------------------------------------------------
-- More functions

-- Singleton trees.

singleton : {A : Set} → A → Tree A
singleton x = node leaf x leaf

-- Any lemma for singleton.

Any-singleton : ∀ {A : Set} (P : A → Set) {x} →
                Any P (singleton x) ↔ P x
Any-singleton P {x} =
  Any P (singleton x)  ↔⟨ id ⟩
  ⊥ ⊎ P x ⊎ ⊥          ↔⟨ ⊎-left-identity ⟩
  P x ⊎ ⊥              ↔⟨ ⊎-right-identity ⟩
  P x                  □

-- Inorder flattening of a tree.

flatten : {A : Set} → Tree A → List A
flatten leaf         = []
flatten (node l x r) = flatten l ++ x ∷ flatten r

-- Flatten does not add or remove any elements.

flatten≈ : {A : Set} (t : Tree A) → ∀ z → z ∈L flatten t ↔ z ∈ t
flatten≈ leaf = λ z →
  z ∈L []   ↔⟨ id ⟩
  z ∈ leaf  □
flatten≈ (node l x r) = λ z →
  z ∈L flatten l ++ x ∷ flatten r          ↔⟨ Any-++ (λ x → z ≡ x) _ _ ⟩
  z ∈L flatten l ⊎ z ∈L x ∷ flatten r      ↔⟨ id ⟩
  z ∈L flatten l ⊎ z ≡ x ⊎ z ∈L flatten r  ↔⟨ flatten≈ l z ⊎-cong id ⊎-cong flatten≈ r z ⟩
  z ∈ l ⊎ z ≡ x ⊎ z ∈ r                    ↔⟨ id ⟩
  z ∈ node l x r                           □
