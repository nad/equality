------------------------------------------------------------------------
-- An implementation of tree sort, formally proved to return a
-- permutation of the input
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Prelude hiding (id)

module Tree-sort.Partial
  {A : Set}
  (_≤_ : A → A → Bool) -- A comparison function.
  where

open import Bag-equivalence
open import Equality.Propositional
open import Tree

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (_∘_)

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
             AnyT P (insert x t) ↔ P x ⊎ AnyT P t
Any-insert P x leaf =
  AnyT P (singleton x)  ↔⟨ Any-singleton P ⟩
  P x                   ↔⟨ inverse ⊎-right-identity ⟩
  P x ⊎ ⊥               ↔⟨⟩
  P x ⊎ AnyT P leaf     □
Any-insert P x (node l y r) with x ≤ y
... | true  =
  AnyT P (insert x l) ⊎ P y ⊎ AnyT P r  ↔⟨ Any-insert P x l ⊎-cong id ⟩
  (P x ⊎ AnyT P l)    ⊎ P y ⊎ AnyT P r  ↔⟨ inverse ⊎-assoc ⟩
  P x ⊎ AnyT P l      ⊎ P y ⊎ AnyT P r  □
... | false =
  AnyT P l ⊎ P y ⊎ AnyT P (insert x r)  ↔⟨ id ⊎-cong id ⊎-cong Any-insert P x r ⟩
  AnyT P l ⊎ P y ⊎ P x ⊎ AnyT P r       ↔⟨ lemma (AnyT P l) (P y) (P x) (AnyT P r) ⟩
  P x ⊎ AnyT P l ⊎ P y ⊎ AnyT P r       □
  where
  -- The following lemma is easy to prove automatically (for instance
  -- by using a ring solver).

  lemma : (A B C D : Set) → A ⊎ B ⊎ C ⊎ D ↔ C ⊎ A ⊎ B ⊎ D
  lemma A B C D =
    A ⊎ B ⊎ C ⊎ D      ↔⟨ id ⊎-cong ⊎-assoc ⟩
    A ⊎ (B ⊎ C) ⊎ D    ↔⟨ id ⊎-cong ⊎-comm ⊎-cong id ⟩
    A ⊎ (C ⊎ B) ⊎ D    ↔⟨ ⊎-assoc ⟩
    (A ⊎ C ⊎ B) ⊎ D    ↔⟨ ⊎-assoc ⊎-cong id ⟩
    ((A ⊎ C) ⊎ B) ⊎ D  ↔⟨ (⊎-comm ⊎-cong id) ⊎-cong id ⟩
    ((C ⊎ A) ⊎ B) ⊎ D  ↔⟨ inverse ⊎-assoc ⊎-cong id ⟩
    (C ⊎ A ⊎ B) ⊎ D    ↔⟨ inverse ⊎-assoc ⟩
    C ⊎ (A ⊎ B) ⊎ D    ↔⟨ id ⊎-cong inverse ⊎-assoc ⟩
    C ⊎ A ⊎ B ⊎ D      □

------------------------------------------------------------------------
-- Turning a list into a search tree

-- Converts the list to a search tree.

to-search-tree : List A → Tree A
to-search-tree = foldr insert leaf

-- No elements are added or removed.

to-search-tree-lemma : ∀ xs z → z ∈T to-search-tree xs ↔ z ∈ xs
to-search-tree-lemma [] = λ z →
  z ∈T leaf  ↔⟨⟩
  z ∈  []    □
to-search-tree-lemma (x ∷ xs) = λ z →
  z ∈T insert x (to-search-tree xs)  ↔⟨ Any-insert (λ x → z ≡ x) _ _ ⟩
  z ≡ x ⊎ z ∈T to-search-tree xs     ↔⟨ id ⊎-cong to-search-tree-lemma xs z ⟩
  z ∈ x ∷ xs                         □

------------------------------------------------------------------------
-- Sorting

-- Sorts a list.

tree-sort : List A → List A
tree-sort = flatten ∘ to-search-tree

-- The result is a permutation of the input.

tree-sort-permutes : ∀ xs → tree-sort xs ≈-bag xs
tree-sort-permutes xs = λ z →
  z ∈  flatten (to-search-tree xs)  ↔⟨ flatten-lemma (to-search-tree xs) z ⟩
  z ∈T to-search-tree xs            ↔⟨ to-search-tree-lemma xs z ⟩
  z ∈  xs                           □
