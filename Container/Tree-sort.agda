------------------------------------------------------------------------
-- An implementation of tree sort, formally proved to return a
-- permutation of the input
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Prelude hiding (id; _∘_; List; []; _∷_; foldr)

module Container.Tree-sort
  {A : Set}
  (_≤_ : A → A → Bool) -- A comparison function.
  where

open import Container
open import Container.List
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

-- Inserts an element into the tree.

insert : A → ⟦ Tree ⟧ A → ⟦ Tree ⟧ A
insert x (lf     , lkup) = singleton x
insert x (nd l r , lkup) =
  if x ≤ lkup root then
    node (insert x (l , lkup ∘ left)) (lkup root) (r , lkup ∘ right)
  else
    node (l , lkup ∘ left) (lkup root) (insert x (r , lkup ∘ right))

-- The insert function inserts.

Any-insert : ∀ (P : A → Set) x t →
             Any P (insert x t) ↔ P x ⊎ Any P t
Any-insert P x (lf , lkup) =
  Any P (insert x (lf , lkup))        ↔⟨ id ⟩
  Any P (singleton x)                 ↔⟨ Any-singleton P ⟩
  P x                                 ↔⟨ inverse ⊎-right-identity ⟩
  P x ⊎ ⊥                             ↔⟨ id ⊎-cong inverse (Any-leaf P) ⟩
  P x ⊎ Any P leaf                    ↔⟨ id ⊎-cong Any-cong {D = Tree} P P leaf (lf , lkup) (λ _ → id) leaf≈ ⟩
  P x ⊎ Any {C = Tree} P (lf , lkup)  □
Any-insert P x (nd l r , lkup) =
  Any P (if x ≤ lkup root then
           node (insert x l′) (lkup root) r′
         else
           node l′ (lkup root) (insert x r′))  ↔⟨ helper (x ≤ lkup root) (l , lkup ∘ left) (r , lkup ∘ right) ⟩
  P x ⊎ Any P l′ ⊎ P (lkup root) ⊎ Any P r′    ↔⟨ id ⊎-cong inverse (Any-node P) ⟩
  P x ⊎ Any P (node l′ (lkup root) r′)         ↔⟨ id ⊎-cong
                                                  Any-cong {D = Tree} P P (node l′ (lkup root) r′) (nd l r , lkup) (λ _ → id) node≈ ⟩
  P x ⊎ Any {C = Tree} P (nd l r , lkup)       □
  where
  l′ : ⟦ Tree ⟧ A
  l′ = (l , lkup ∘ left)

  r′ : ⟦ Tree ⟧ A
  r′ = (r , lkup ∘ right)

  helper : ∀ (b : Bool) l′ r′ →
           Any P (if b then node (insert x l′) (lkup root) r′
                       else node l′ (lkup root) (insert x r′)) ↔
           P x ⊎ Any P l′ ⊎ P (lkup root) ⊎ Any P r′
  helper true l′ r′ =
    Any P (node (insert x l′) (lkup root) r′)       ↔⟨ Any-node P ⟩
    Any P (insert x l′) ⊎ P (lkup root) ⊎ Any P r′  ↔⟨ Any-insert P x l′ ⊎-cong id ⊎-cong id ⟩
    (P x ⊎ Any P l′) ⊎ P (lkup root) ⊎ Any P r′     ↔⟨ inverse ⊎-assoc ⟩
    P x ⊎ Any P l′ ⊎ P (lkup root) ⊎ Any P r′       □
  helper false l′ r′ =
    Any P (node l′ (lkup root) (insert x r′))       ↔⟨ Any-node P ⟩
    Any P l′ ⊎ P (lkup root) ⊎ Any P (insert x r′)  ↔⟨ id ⊎-cong id ⊎-cong Any-insert P x r′ ⟩
    Any P l′ ⊎ P (lkup root) ⊎ P x ⊎ Any P r′       ↔⟨ lemma _ _ _ _ ⟩
    P x ⊎ Any P l′ ⊎ P (lkup root) ⊎ Any P r′       □

------------------------------------------------------------------------
-- Turning a list into a search tree

-- Converts the list to a search tree.

to-search-tree : ⟦ List ⟧ A → ⟦ Tree ⟧ A
to-search-tree = foldr insert leaf

-- No elements are added or removed.

to-search-tree≈ : ∀ xs → to-search-tree xs ≈-bag xs
to-search-tree≈ (zero , lkup) = λ z →
  z ∈ leaf                        ↔⟨ Any-leaf (λ x → z ≡ x) ⟩
  ⊥                               ↔⟨ inverse $ Any-[] (λ x → z ≡ x) ⟩
  z ∈ []                          ↔⟨ []≈ _ ⟩
  _∈_ {C = List} z (zero , lkup)  □
to-search-tree≈ (suc n , lkup) = λ z →
  z ∈ to-search-tree (suc n , lkup)  ↔⟨ id ⟩
  z ∈ insert x (to-search-tree xs)   ↔⟨ Any-insert (λ x → z ≡ x) _ _ ⟩
  z ≡ x ⊎ z ∈ to-search-tree xs      ↔⟨ id ⊎-cong to-search-tree≈ (n , lkup ∘ inj₂) _ ⟩
  z ≡ x ⊎ z ∈ xs                     ↔⟨ inverse $ Any-∷ (λ x → z ≡ x) ⟩
  z ∈ x ∷ xs                         ↔⟨ ∷≈ _ ⟩
  _∈_ {C = List} z (suc n , lkup)    □
  where
  x  = lkup (inj₁ tt)
  xs = (n , lkup ∘ inj₂)

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
