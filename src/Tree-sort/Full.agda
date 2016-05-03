------------------------------------------------------------------------
-- A correct implementation of tree sort
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- The algorithm and the treatment of ordering information is taken
-- from Conor McBride's talk "Pivotal pragmatism".

-- The module is parametrised by a total relation.

open import Prelude hiding (id; _∘_; _≤_; lower)

module Tree-sort.Full
  {A : Set}
  (le : A → A → Set)
  (total : ∀ x y → le x y ⊎ le y x)
  where

open import Bag-equivalence using () renaming (Any to AnyL)
open import Equality.Propositional

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (Kind; module Kind)
open import List equality-with-J

------------------------------------------------------------------------
-- Extending the order with new minimum and maximum elements

-- A extended with a new minimum and maximum.

data Extended : Set where
  min max : Extended
  [_]     : (x : A) → Extended

infix 4 _≤_

_≤_ : Extended → Extended → Set
min   ≤ y     = ⊤
[ x ] ≤ [ y ] = le x y
x     ≤ max   = ⊤
_     ≤ _     = ⊥

-- A pair of ordering constraints (written as a record type to aid
-- type inference).

infix 4 _,_

record _≤[_]≤_ (l : Extended) (x : A) (u : Extended) : Set where
  constructor _,_
  field
    lower : l ≤ [ x ]
    upper : [ x ] ≤ u

------------------------------------------------------------------------
-- Ordered lists

data Ordered-list (l u : Extended) : Set where
  nil  : (l≤u : l ≤ u) → Ordered-list l u
  cons : (x : A) (xs : Ordered-list [ x ] u) (l≤x : l ≤ [ x ]) →
         Ordered-list l u

-- Conversion to ordinary lists.

to-list : ∀ {l u} → Ordered-list l u → List A
to-list (nil l≤u)       = []
to-list (cons x xs l≤x) = x ∷ to-list xs

------------------------------------------------------------------------
-- Unbalanced binary search trees

infix 5 node

syntax node x lx xu = lx -[ x ]- xu

data Search-tree (l u : Extended) : Set where
  leaf : (l≤u : l ≤ u) → Search-tree l u
  node : (x : A) (lx : Search-tree l [ x ]) (xu : Search-tree [ x ] u) →
         Search-tree l u

-- Any.

AnyT : ∀ {l u} → (A → Set) → Search-tree l u → Set
AnyT P (leaf _)     = ⊥
AnyT P (node x l r) = AnyT P l ⊎ P x ⊎ AnyT P r

------------------------------------------------------------------------
-- An ad-hoc universe consisting of lists, ordered lists and search
-- trees

-- The purpose of this universe is to allow overloading of Any, _∈_
-- and _≈-bag_.

-- Codes.

data Kind : Set where
  list ordered-list search-tree : Kind

-- Index type.
--
-- Note that Agda infers values of type ⊤ automatically.

Index : Kind → Set
Index list = ⊤
Index _    = Extended

-- Interpretation.

⟦_⟧ : (k : Kind) → (Index k → Index k → Set)
⟦ list         ⟧ _ _ = List A
⟦ ordered-list ⟧ l u = Ordered-list l u
⟦ search-tree  ⟧ l u = Search-tree l u

-- Any.

Any : ∀ {k l u} → (A → Set) → (⟦ k ⟧ l u → Set)
Any {list}         = AnyL
Any {ordered-list} = λ P → AnyL P ∘ to-list
Any {search-tree}  = AnyT

-- Membership.

infix 4 _∈_

_∈_ : ∀ {k l u} → A → ⟦ k ⟧ l u → Set
x ∈ xs = Any (λ y → x ≡ y) xs

-- Bag equivalence.

infix 4 _≈-bag_

_≈-bag_ : ∀ {k₁ k₂ l₁ u₁ l₂ u₂} → ⟦ k₁ ⟧ l₁ u₁ → ⟦ k₂ ⟧ l₂ u₂ → Set
xs ≈-bag ys = ∀ z → z ∈ xs ↔ z ∈ ys

------------------------------------------------------------------------
-- Singleton trees

singleton : ∀ {l u} (x : A) → l ≤[ x ]≤ u → Search-tree l u
singleton x (l≤x , x≤u) = leaf l≤x -[ x ]- leaf x≤u

-- Any lemma for singleton.

Any-singleton : ∀ (P : A → Set) {l u x} (l≤x≤u : l ≤[ x ]≤ u) →
                Any P (singleton x l≤x≤u) ↔ P x
Any-singleton P {x = x} l≤x≤u =
  Any P (singleton x l≤x≤u)  ↔⟨⟩
  ⊥ ⊎ P x ⊎ ⊥                ↔⟨ ⊎-left-identity ⟩
  P x ⊎ ⊥                    ↔⟨ ⊎-right-identity ⟩
  P x                        □

------------------------------------------------------------------------
-- Insertion into a search tree

insert : ∀ {l u} (x : A) → Search-tree l u → l ≤[ x ]≤ u →
         Search-tree l u
insert x (leaf _)        l≤x≤u       = singleton x l≤x≤u
insert x (ly -[ y ]- yu) (l≤x , x≤u) with total x y
... | inj₁ x≤y = insert x ly (l≤x , x≤y) -[ y ]- yu
... | inj₂ y≤x = ly -[ y ]- insert x yu (y≤x , x≤u)

-- Any lemma for insert.

Any-insert : ∀ (P : A → Set) {l u} x t (l≤x≤u : l ≤[ x ]≤ u) →
             Any P (insert x t l≤x≤u) ↔ P x ⊎ Any P t
Any-insert P {l} {u} x (leaf l≤u) l≤x≤u =
  Any P (singleton x l≤x≤u)               ↔⟨ Any-singleton P l≤x≤u ⟩
  P x                                     ↔⟨ inverse ⊎-right-identity ⟩
  P x ⊎ ⊥                                 ↔⟨⟩
  P x ⊎ Any P (leaf {l = l} {u = u} l≤u)  □
Any-insert P x (ly -[ y ]- yu) (l≤x , x≤u) with total x y
... | inj₁ x≤y =
  Any P (insert x ly (l≤x , x≤y)) ⊎ P y ⊎ Any P yu  ↔⟨ Any-insert P x ly (l≤x , x≤y) ⊎-cong id ⟩
  (P x ⊎ Any P ly) ⊎ P y ⊎ Any P yu                 ↔⟨ inverse ⊎-assoc ⟩
  P x ⊎ Any P ly ⊎ P y ⊎ Any P yu                   □
... | inj₂ y≤x =
  Any P ly ⊎ P y ⊎ Any P (insert x yu (y≤x , x≤u))  ↔⟨ id ⊎-cong id ⊎-cong Any-insert P x yu (y≤x , x≤u) ⟩
  Any P ly ⊎ P y ⊎ P x ⊎ Any P yu                   ↔⟨ lemma _ _ _ _ ⟩
  P x ⊎ Any P ly ⊎ P y ⊎ Any P yu                   □
  where

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

------------------------------------------------------------------------
-- Turning an unordered list into a search tree

to-search-tree : List A → Search-tree min max
to-search-tree = foldr (λ x t → insert x t _) (leaf _)

-- No elements are added or removed.

to-search-tree-lemma : ∀ xs → to-search-tree xs ≈-bag xs
to-search-tree-lemma [] = λ z →
  z ∈ leaf {l = min} {u = max} _  ↔⟨⟩
  z ∈ []                          □
to-search-tree-lemma (x ∷ xs) = λ z →
  z ∈ insert x (to-search-tree xs) _  ↔⟨ Any-insert (λ x → z ≡ x) _ _ _ ⟩
  z ≡ x ⊎ z ∈ to-search-tree xs       ↔⟨ id ⊎-cong to-search-tree-lemma xs z ⟩
  z ∈ x ∷ xs                          □

------------------------------------------------------------------------
-- Appending two ordered lists with an extra element in between

infixr 5 append

syntax append x lx xu = lx -⁅ x ⁆- xu

append : ∀ {l u} (x : A) →
         Ordered-list l [ x ] → Ordered-list [ x ] u → Ordered-list l u
nil l≤x       -⁅ x ⁆- xu = cons x xu l≤x
cons y yx l≤y -⁅ x ⁆- xu = cons y (yx -⁅ x ⁆- xu) l≤y

-- Any lemma for append.

Any-append : ∀ (P : A → Set) {l u} x
             (lx : Ordered-list l [ x ]) (xu : Ordered-list [ x ] u) →
             Any P (lx -⁅ x ⁆- xu) ↔ Any P lx ⊎ P x ⊎ Any P xu
Any-append P x (nil l≤x) xu =
  P x ⊎ Any P xu      ↔⟨ inverse ⊎-left-identity ⟩
  ⊥ ⊎ P x ⊎ Any P xu  □
Any-append P x (cons y yx l≤y) xu =
  P y ⊎ Any P (append x yx xu)       ↔⟨ id ⊎-cong Any-append P x yx xu ⟩
  P y ⊎ Any P yx ⊎ P x ⊎ Any P xu    ↔⟨ ⊎-assoc ⟩
  (P y ⊎ Any P yx) ⊎ P x ⊎ Any P xu  □

------------------------------------------------------------------------
-- Inorder flattening of a tree

flatten : ∀ {l u} → Search-tree l u → Ordered-list l u
flatten (leaf l≤u)    = nil l≤u
flatten (l -[ x ]- r) = flatten l -⁅ x ⁆- flatten r

-- Flatten does not add or remove any elements.

flatten-lemma : ∀ {l u} (t : Search-tree l u) → flatten t ≈-bag t
flatten-lemma {l} {u} (leaf l≤u) = λ z →
  z ∈ nil  {l = l} {u = u} l≤u  ↔⟨⟩
  z ∈ leaf {l = l} {u = u} l≤u  □
flatten-lemma (l -[ x ]- r) = λ z →
  z ∈ flatten l -⁅ x ⁆- flatten r        ↔⟨ Any-append (λ x → z ≡ x) _ _ _ ⟩
  z ∈ flatten l ⊎ z ≡ x ⊎ z ∈ flatten r  ↔⟨ flatten-lemma l z ⊎-cong id ⊎-cong flatten-lemma r z ⟩
  z ∈ l ⊎ z ≡ x ⊎ z ∈ r                  ↔⟨⟩
  z ∈ l -[ x ]- r                        □

------------------------------------------------------------------------
-- Sorting

-- Sorts a list.

tree-sort : List A → Ordered-list min max
tree-sort = flatten ∘ to-search-tree

-- The result is a permutation of the input.

tree-sort-permutes : ∀ xs → tree-sort xs ≈-bag xs
tree-sort-permutes xs = λ z →
  z ∈ tree-sort xs                 ↔⟨⟩
  z ∈ flatten (to-search-tree xs)  ↔⟨ flatten-lemma (to-search-tree xs) _ ⟩
  z ∈ to-search-tree xs            ↔⟨ to-search-tree-lemma xs _ ⟩
  z ∈ xs                           □
