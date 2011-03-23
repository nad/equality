------------------------------------------------------------------------
-- Containers, including a definition of bag equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container where

open import Bag-equality hiding (Any; _∈_; _∼[_]_; _≈-bag_)
open import Equality.Propositional
open import Prelude hiding (List)

import Bijection; open Bijection equality-with-J
import Function-universe
open Function-universe equality-with-J using (_↝[_]_)

-- Containers.

record Container : Set₁ where
  constructor _▷_
  field
    Shape    : Set
    Position : Shape → Set

-- Interpretation of containers.

⟦_⟧ : Container → Set → Set
⟦ S ▷ P ⟧ A = ∃ λ (s : S) → (P s → A)

-- Some examples.

module Examples where

  -- Lists.

  List : Container
  List = ℕ ▷ Fin

  -- Streams.

  Stream : Container
  Stream = ⊤ ▷ const ℕ

  -- Finite binary trees with information in the internal nodes.

  data S : Set where
    leaf  : S
    node  : S → S → S

  P : S → Set
  P leaf       = ⊥
  P (node l r) = P l ⊎ ⊤ ⊎ P r

  Tree : Container
  Tree = S ▷ P

-- Definition of Any for containers.

Any :  {C : Container} {A : Set} →
       (A → Set) → (⟦ C ⟧ A → Set)
Any {S ▷ P} Q (s , f) = ∃ λ (p : P s) → Q (f p)

-- Membership predicate.

infix 4 _∈_

_∈_ : {C : Container} {A : Set} → A → ⟦ C ⟧ A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

-- Bag equality etc. Note that the containers can be different as long
-- as the elements they contain have equal types.

infix 4 _∼[_]_

_∼[_]_ : ∀ {C₁ C₂ A} → ⟦ C₁ ⟧ A → Kind → ⟦ C₂ ⟧ A → Set
xs ∼[ k ] ys = ∀ z → z ∈ xs ↝[ k ] z ∈ ys

-- Bag equality.

infix 4 _≈-bag_

_≈-bag_ : {C₁ C₂ : Container} {A : Set} → ⟦ C₁ ⟧ A → ⟦ C₂ ⟧ A → Set
xs ≈-bag ys = xs ∼[ bag ] ys
