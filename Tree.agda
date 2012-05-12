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

-- Bag equivalence.

_≈-bagT_ : ∀ {A} → Tree A → Tree A → Set
t₁ ≈-bagT t₂ = ∀ x → x ∈T t₁ ↔ x ∈T t₂

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

------------------------------------------------------------------------
-- Bags can (perhaps) be defined as binary trees quotiented by bag
-- equivalence

-- Agda doesn't support quotients, so the following type is used to
-- state that two quotients are isomorphic.
--
-- Note that this definition may not actually make sense if the
-- relations _≈A_ and _≈B_ are not /proof-irrelevant/ equivalence
-- relations.

record _/_↔_/_ (A : Set) (_≈A_ : A → A → Set)
               (B : Set) (_≈B_ : B → B → Set) : Set where
  field
    to        : A → B
    to-resp   : ∀ x y → x ≈A y → to x ≈B to y
    from      : B → A
    from-resp : ∀ x y → x ≈B y → from x ≈A from y
    to∘from   : ∀ x → to (from x) ≈B x
    from∘to   : ∀ x → from (to x) ≈A x

-- Lists quotiented by bag equivalence are isomorphic to binary trees
-- quotiented by bag equivalence (assuming that one can actually
-- quotient by bag equivalence, and that the definition of _/_↔_/_
-- makes sense in this case).

list-bags↔tree-bags : {A : Set} → List A / _≈-bag_ ↔ Tree A / _≈-bagT_
list-bags↔tree-bags {A} = record
  { to        = to-tree
  ; to-resp   = λ xs ys xs≈ys z →
                  z ∈T to-tree xs  ↔⟨ to-tree-lemma xs z ⟩
                  z ∈ xs           ↔⟨ xs≈ys z ⟩
                  z ∈ ys           ↔⟨ inverse $ to-tree-lemma ys z ⟩
                  z ∈T to-tree ys  □
  ; from      = flatten
  ; from-resp = λ t₁ t₂ t₁≈t₂ z →
                  z ∈ flatten t₁  ↔⟨ flatten-lemma t₁ z ⟩
                  z ∈T t₁         ↔⟨ t₁≈t₂ z ⟩
                  z ∈T t₂         ↔⟨ inverse $ flatten-lemma t₂ z ⟩
                  z ∈ flatten t₂  □
  ; to∘from   = to∘from
  ; from∘to   = from∘to
  }
  where
  to-tree : List A → Tree A
  to-tree = foldr (node leaf) leaf

  to-tree-lemma : ∀ xs z → z ∈T to-tree xs ↔ z ∈ xs
  to-tree-lemma []       = λ z → ⊥ □
  to-tree-lemma (x ∷ xs) = λ z →
    ⊥ ⊎ z ≡ x   ⊎ z ∈T to-tree xs  ↔⟨ id ⊎-cong id ⊎-cong to-tree-lemma xs z ⟩
    ⊥ ⊎ z ≡ x   ⊎ z ∈ xs           ↔⟨ ⊎-assoc ⟩
    (⊥ ⊎ z ≡ x) ⊎ z ∈ xs           ↔⟨ ⊎-left-identity ⊎-cong id ⟩
    z ≡ x       ⊎ z ∈ xs           □

  to-tree-++ : ∀ {P : A → Set} xs {ys} →
               AnyT P (to-tree (xs ++ ys)) ↔
               AnyT P (to-tree xs) ⊎ AnyT P (to-tree ys)
  to-tree-++ {P} [] {ys} =
    AnyT P (to-tree ys)      ↔⟨ inverse ⊎-left-identity ⟩
    ⊥ ⊎ AnyT P (to-tree ys)  □
  to-tree-++ {P} (x ∷ xs) {ys} =
    ⊥ ⊎ P x ⊎ AnyT P (to-tree (xs ++ ys))                  ↔⟨ id ⊎-cong id ⊎-cong to-tree-++ xs ⟩
    ⊥ ⊎ P x ⊎ AnyT P (to-tree xs) ⊎ AnyT P (to-tree ys)    ↔⟨ lemma _ _ _ _ ⟩
    (⊥ ⊎ P x ⊎ AnyT P (to-tree xs)) ⊎ AnyT P (to-tree ys)  □
    where
    lemma : (A B C D : Set) → A ⊎ B ⊎ C ⊎ D ↔ (A ⊎ B ⊎ C) ⊎ D
    lemma A B C D =
      A ⊎ B ⊎ C ⊎ D      ↔⟨ ⊎-assoc ⟩
      (A ⊎ B) ⊎ C ⊎ D    ↔⟨ ⊎-assoc ⟩
      ((A ⊎ B) ⊎ C) ⊎ D  ↔⟨ inverse ⊎-assoc ⊎-cong id ⟩
      (A ⊎ B ⊎ C) ⊎ D    □

  to∘from : ∀ t → to-tree (flatten t) ≈-bagT t
  to∘from leaf         = λ z → ⊥ □
  to∘from (node l x r) = λ z →
    z ∈T to-tree (flatten l ++ x ∷ flatten r)                        ↔⟨ to-tree-++ (flatten l) ⟩
    z ∈T to-tree (flatten l) ⊎ ⊥ ⊎ z ≡ x ⊎ z ∈T to-tree (flatten r)  ↔⟨ to∘from l z ⊎-cong id ⊎-cong id ⊎-cong to∘from r z ⟩
    z ∈T l                   ⊎ ⊥ ⊎ z ≡ x ⊎ z ∈T r                    ↔⟨ id ⊎-cong ⊎-left-identity ⟩
    z ∈T l                   ⊎     z ≡ x ⊎ z ∈T r                    □

  from∘to : ∀ xs → flatten (to-tree xs) ≈-bag xs
  from∘to []       = λ z → ⊥ □
  from∘to (x ∷ xs) = λ z →
    z ≡ x ⊎ z ∈ flatten (to-tree xs)  ↔⟨ id ⊎-cong from∘to xs z ⟩
    z ≡ x ⊎ z ∈ xs                    □
