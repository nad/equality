------------------------------------------------------------------------
-- An implementation of tree sort, formally proved to return a
-- permutation of the input
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Prelude hiding (id; _∘_)

module Tree-sort
  {A : Set}
  (_≤_ : A → A → Bool) -- A comparison function.
  where

open import Bag-equality renaming (_∈_ to _∈L_)
open import Equality.Propositional
open import Tree hiding (_≈-bag_) renaming (_∈_ to _∈T_)

import Bijection
open Bijection equality-with-J using (_↔_)
import Function-universe
open Function-universe equality-with-J

------------------------------------------------------------------------
-- Boring lemmas

private

  -- The following lemma is easy to prove automatically (for
  -- instance by using a ring solver).

  lemma₁ : (A B C D : Set) → A ⊎ B ⊎ C ⊎ D ↔ C ⊎ A ⊎ B ⊎ D
  lemma₁ A B C D =
    A ⊎ B ⊎ C ⊎ D      ↔⟨ id ⊎-cong ⊎-assoc ⟩
    A ⊎ (B ⊎ C) ⊎ D    ↔⟨ id ⊎-cong ⊎-comm ⊎-cong id ⟩
    A ⊎ (C ⊎ B) ⊎ D    ↔⟨ ⊎-assoc ⟩
    (A ⊎ C ⊎ B) ⊎ D    ↔⟨ ⊎-assoc ⊎-cong id ⟩
    ((A ⊎ C) ⊎ B) ⊎ D  ↔⟨ (⊎-comm ⊎-cong id) ⊎-cong id ⟩
    ((C ⊎ A) ⊎ B) ⊎ D  ↔⟨ inverse ⊎-assoc ⊎-cong id ⟩
    (C ⊎ A ⊎ B) ⊎ D    ↔⟨ inverse ⊎-assoc ⟩
    C ⊎ (A ⊎ B) ⊎ D    ↔⟨ id ⊎-cong inverse ⊎-assoc ⟩
    C ⊎ A ⊎ B ⊎ D      □

  lemma₂ : {A B C D : Set} (b : Bool) →
           T b × ((A ⊎ B) ⊎ C ⊎ D) ⊎ T (not b) × (B ⊎ C ⊎ A ⊎ D) ↔
           A ⊎ B ⊎ C ⊎ D
  lemma₂ = if-lemma (λ _ → _) (inverse ⊎-assoc) (lemma₁ _ _ _ _)

------------------------------------------------------------------------
-- Insertion into trees

-- Inserts an element into the tree.

insert : A → Tree A → Tree A
insert x leaf         = singleton x
insert x (node l y r) =
  if x ≤ y then node (insert x l) y r
           else node l y (insert x r)

-- The insert function inserts.

Any-insert : ∀ (P : A → Set) x t →
             Tree.Any P (insert x t) ↔ P x ⊎ Tree.Any P t
Any-insert P x leaf =
  Tree.Any P (singleton x)  ↔⟨ Any-singleton P ⟩
  P x                       ↔⟨ inverse ⊎-right-identity ⟩
  P x ⊎ ⊥                   ↔⟨ id ⟩
  P x ⊎ Tree.Any P leaf     □
Any-insert P x (node l y r) =
  ◇ P (if x ≤ y then node l′ y r else node l y r′)  ↔⟨ inverse $ if-lemma (λ b → ◇ P (if b then node l′ y r else node l y r′))
                                                                          id id (x ≤ y) ⟩
  T (x ≤ y) × (◇ P l′ ⊎ P y ⊎ ◇ P r) ⊎
    T (not (x ≤ y)) × (◇ P l ⊎ P y ⊎ ◇ P r′)        ↔⟨ id ×-cong (Any-insert P x l ⊎-cong id) ⊎-cong
                                                       id ×-cong (id ⊎-cong id ⊎-cong Any-insert P x r) ⟩
  T (x ≤ y) × ((P x ⊎ ◇ P l) ⊎ P y ⊎ ◇ P r) ⊎
    T (not (x ≤ y)) × (◇ P l ⊎ P y ⊎ P x ⊎ ◇ P r)   ↔⟨ lemma₂ (x ≤ y) ⟩

  P x ⊎ ◇ P (node l y r)                            □
  where
  ◇  = Tree.Any
  l′ = insert x l
  r′ = insert x r

------------------------------------------------------------------------
-- Turning a list into a search tree

-- Converts the list to a search tree.

to-search-tree : List A → Tree A
to-search-tree []       = leaf
to-search-tree (x ∷ xs) = insert x (to-search-tree xs)

-- No elements are added or removed.

to-search-tree≈ : ∀ xs z → z ∈T to-search-tree xs ↔ z ∈L xs
to-search-tree≈ [] = λ z →
  z ∈T leaf  ↔⟨ id ⟩
  z ∈L []    □
to-search-tree≈ (x ∷ xs) = λ z →
  z ∈T insert x (to-search-tree xs)  ↔⟨ Any-insert (λ x → z ≡ x) _ _ ⟩
  z ≡ x ⊎ z ∈T to-search-tree xs     ↔⟨ id ⊎-cong to-search-tree≈ xs z ⟩
  z ∈L x ∷ xs                        □

------------------------------------------------------------------------
-- Sorting

-- Sorts a list.

sort : List A → List A
sort = flatten ∘ to-search-tree

-- The result is a permutation of the input.

sort≈ : ∀ xs → sort xs ≈-bag xs
sort≈ xs = λ z →
  z ∈L sort xs                      ↔⟨ id ⟩
  z ∈L flatten (to-search-tree xs)  ↔⟨ flatten≈ (to-search-tree xs) _ ⟩
  z ∈T to-search-tree xs            ↔⟨ to-search-tree≈ xs _ ⟩
  z ∈L xs                           □
