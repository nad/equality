------------------------------------------------------------------------
-- An implementation of tree sort, formally proved to return a
-- permutation of the input
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Prelude hiding (id; _∘_; List; module List; []; _∷_)

module Container.Tree-sort
  {A : Set}
  (_≤_ : A → A → Bool) -- A comparison function.
  where

open import Container
open import Container.List as List
open import Container.Tree as Tree
open import Equality.Propositional

import Bijection
open Bijection equality-with-J using (_↔_; module _↔_)
import Function-universe
open Function-universe equality-with-J

------------------------------------------------------------------------
-- Insertion into trees

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

-- Inserts an element into the tree.

abstract

  insert′ : ∀ (x : A) (t : ⟦ Tree ⟧ A) →
            ∃ λ (t′ : ⟦ Tree ⟧ A) →
                (P : A → Set) → Any P t′ ↔ P x ⊎ Any P t
  insert′ x = Tree.fold
    (λ t → ∃ λ t′ → ∀ P → Any P t′ ↔ P x ⊎ Any P t)
    (λ t₁ t₂ t₁≈t₂ → ∃-cong (λ xs hyp P →
       Any P xs        ↔⟨ hyp P ⟩
       P x ⊎ Any P t₁  ↔⟨ id ⊎-cong Any-cong P P t₁ t₂ (λ _ → id) t₁≈t₂ ⟩
       P x ⊎ Any P t₂  □))
    (singleton x , (λ P →
     Any P (singleton x)  ↔⟨ Any-singleton P ⟩
     P x                  ↔⟨ inverse ⊎-right-identity ⟩
     P x ⊎ ⊥              ↔⟨ id ⊎-cong inverse (Any-leaf P) ⟩
     P x ⊎ Any P leaf     □))
    (λ { l y r (l′ , ih-l) (r′ , ih-r) →
         ( if x ≤ y then node l′ y r else node l y r′ , λ P →
           Any P (if x ≤ y then node l′ y r else node l y r′)   ↔⟨ Any-if P (node l′ y r) (node l y r′) (x ≤ y) ⟩
           T (x ≤ y) × Any P (node l′ y r) ⊎
             T (not (x ≤ y)) × Any P (node l y r′)              ↔⟨ id ×-cong Any-node P ⊎-cong id ×-cong Any-node P ⟩
           T (x ≤ y) × (Any P l′ ⊎ P y ⊎ Any P r) ⊎
             T (not (x ≤ y)) × (Any P l ⊎ P y ⊎ Any P r′)       ↔⟨ id ×-cong (ih-l P ⊎-cong id) ⊎-cong
                                                                   id ×-cong (id ⊎-cong id ⊎-cong ih-r P) ⟩
           T (x ≤ y) × ((P x ⊎ Any P l) ⊎ P y ⊎ Any P r) ⊎
             T (not (x ≤ y)) × (Any P l ⊎ P y ⊎ P x ⊎ Any P r)  ↔⟨ lemma₂ (x ≤ y) ⟩
           P x ⊎ Any P l ⊎ P y ⊎ Any P r                        ↔⟨ id ⊎-cong inverse (Any-node P) ⟩
           P x ⊎ Any P (node l y r)                             □
         ) })

insert : A → ⟦ Tree ⟧ A → ⟦ Tree ⟧ A
insert x t = proj₁ (insert′ x t)

-- The insert function inserts.

Any-insert : ∀ (P : A → Set) x t →
             Any P (insert x t) ↔ P x ⊎ Any P t
Any-insert P x t = proj₂ (insert′ x t) P

------------------------------------------------------------------------
-- Turning a list into a search tree

-- Converts the list to a search tree.

abstract

  to-search-tree′ :
    (xs : ⟦ List ⟧ A) → ∃ λ (t : ⟦ Tree ⟧ A) → t ≈-bag xs
  to-search-tree′ = List.fold
    (λ xs → ∃ λ t → t ≈-bag xs)
    (λ xs ys xs≈ys → ∃-cong (λ t t≈xs z →
       z ∈ t   ↔⟨ t≈xs z ⟩
       z ∈ xs  ↔⟨ xs≈ys z ⟩
       z ∈ ys  □))
    (leaf , λ z →
     z ∈ leaf  ↔⟨ Any-leaf (λ x → z ≡ x) ⟩
     ⊥         ↔⟨ inverse $ Any-[] (λ x → z ≡ x) ⟩
     z ∈ []    □)
    (λ { x xs (t , t≈xs) → (insert x t , λ z →
     z ∈ insert x t  ↔⟨ Any-insert (λ x → z ≡ x) _ _ ⟩
     z ≡ x ⊎ z ∈ t   ↔⟨ id ⊎-cong t≈xs z ⟩
     z ≡ x ⊎ z ∈ xs  ↔⟨ inverse $ Any-∷ (λ x → z ≡ x) ⟩
     z ∈ x ∷ xs      □) })

to-search-tree : ⟦ List ⟧ A → ⟦ Tree ⟧ A
to-search-tree xs = proj₁ (to-search-tree′ xs)

-- No elements are added or removed.

to-search-tree≈ : ∀ xs → to-search-tree xs ≈-bag xs
to-search-tree≈ xs = proj₂ (to-search-tree′ xs)

------------------------------------------------------------------------
-- Sorting

-- Sorts a list.

sort : ⟦ List ⟧ A → ⟦ List ⟧ A
sort = flatten ∘ to-search-tree

-- The result is a permutation of the input.

sort≈ : ∀ xs → sort xs ≈-bag xs
sort≈ xs = λ z →
  z ∈ sort xs                      ↔⟨ id ⟩
  z ∈ flatten (to-search-tree xs)  ↔⟨ flatten≈ (to-search-tree xs) _ ⟩
  z ∈ to-search-tree xs            ↔⟨ to-search-tree≈ xs _ ⟩
  z ∈ xs                           □
