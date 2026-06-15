------------------------------------------------------------------------
-- Red-black trees
------------------------------------------------------------------------

-- The implementation is based on Okasaki's presentation in "Red-black
-- trees in a functional setting". The ordering invariant is handled
-- using more or less the approach described by McBride in "How to
-- Keep Your Neighbours in Order".

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Tree.Red-black {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude as P

open import Equality.Decision-procedures eq
open import Erased.Level-1 eq
open import Function-universe eq as F hiding (id; _∘_)
open import Total-order.Erased eq

private variable
  a o      : Level
  @0 m n   : ℕ
  A        : Type _
  x y      : A
  O        : Total-order _ _
  @0 lb ub : Extended _

------------------------------------------------------------------------
-- Red-black trees

-- Colours.

Colour : Type
Colour = Bool

pattern red   = false
pattern black = true

private variable
  c     : Colour
  @0 pc : Colour

opaque

  -- The red invariant: red nodes do not have red parents.

  @0 Red-invariant : Colour → Colour → Type
  Red-invariant pc c =
    c ≡ red → pc ≡ red → ⊥

private variable
  @0 rinv : Red-invariant _ _

opaque

  -- The black invariant implies that the number of black nodes is
  -- equal on every path from the root to a leaf.

  @0 Black-invariant : Colour → ℕ → ℕ → Type
  Black-invariant red   m n = n ≡ m
  Black-invariant black m n = n ≡ suc m

private variable
  @0 binv : Black-invariant _ _ _

-- Red-black trees.
--
-- The colour parameter is the *parent's* colour (if any). The natural
-- number parameter is the number of black nodes on every path from
-- the root to a leaf. The parameter lb is a lower bound for the nodes
-- in the tree, and ub is an upper bound.

data Tree {A : Type a} (O : Total-order A o) (@0 pc : Colour)
       (@0 n : ℕ) (@0 lb ub : Extended A) : Type (a ⊔ o) where
  leaf :
    let open Total-order (extended O) in
    (@0 lb<ub : lb < ub) (@0 n≡0 : n ≡ 0) → Tree O pc n lb ub
  node :
    (c : Colour) (x : A) (l : Tree O c m lb [ x ])
    (r : Tree O c m [ x ] ub) (@0 rinv : Red-invariant pc c)
    (@0 binv : Black-invariant c m n) →
    Tree O pc n lb ub

private variable
  l r t : Tree _ pc n lb ub

------------------------------------------------------------------------
-- Some lemmas related to Red-invariant

opaque
  unfolding Red-invariant

  -- The red invariant holds for black children.

  @0 black-child : Red-invariant pc black
  black-child black≡red _ = Bool.true≢false black≡red

opaque
  unfolding Red-invariant

  -- The red invariant holds for black parents.

  @0 black-parent : Red-invariant black c
  black-parent _ black≡red = Bool.true≢false black≡red

opaque
  unfolding Red-invariant

  -- The red invariant does not hold for two red nodes.

  @0 not-red-red : ¬ Red-invariant red red
  not-red-red inv = inv (refl _) (refl _)

opaque
  unfolding Red-invariant

  -- If the red invariant holds for pc and red, then it holds for pc
  -- and c.

  @0 red-child : ∀ {pc} → Red-invariant pc red → Red-invariant pc c
  red-child {pc = red}   inv = ⊥-elim (not-red-red inv)
  red-child {pc = black} _   = black-parent

opaque
  unfolding Red-invariant

  -- If the red invariant holds for rec and c, then it holds for pc
  -- and c.

  @0 red-parent : Red-invariant red c → Red-invariant pc c
  red-parent {c = red}   inv = ⊥-elim (not-red-red inv)
  red-parent {c = black} _   = black-child

------------------------------------------------------------------------
-- A lemma related to Black-invariant

opaque
  unfolding Black-invariant

  -- The black invariant is preserved (possibly for a different second
  -- number) if the root is coloured black.

  @0 black-black :
    Black-invariant c m n →
    ∃ (Black-invariant black m)
  black-black {c = red}   eq = _ , cong suc eq
  black-black {c = black} eq = _ , eq

------------------------------------------------------------------------
-- A lemma related to the bounds

opaque

  -- The lower bound is strictly below the upper bound.

  @0 lower-bound-<-upper-bound :
    let open Total-order (extended O) in
    Tree O pc n lb ub →
    lb < ub
  lower-bound-<-upper-bound     (leaf lb<ub _)     = lb<ub
  lower-bound-<-upper-bound {O} (node _ _ l r _ _) =
    <-trans (lower-bound-<-upper-bound l) (lower-bound-<-upper-bound r)
    where
    open Total-order (extended O)

------------------------------------------------------------------------
-- Membership

-- Tree membership.

infix 4 _∈_

_∈_ :
  ∀ {A : Type a} {O : Total-order A o} {@0 lb ub} →
  A → Tree O pc n lb ub → Type (a ⊔ o)
_ ∈ leaf _ _         = ⊥
x ∈ node _ y l r _ _ = x ∈ l ⊎ x ≡ y ⊎ x ∈ r

opaque

  -- If x is in the tree, then x is strictly between the lower and
  -- upper bounds.

  @0 ∈→<< :
    let open Total-order (extended O) in
    {t : Tree O pc n lb ub} →
    x ∈ t → lb < [ x ] × [ x ] < ub
  ∈→<< {O} {t = node _ _ _ r _ _} (inj₁ x∈l) =
    let <x , x< = ∈→<< x∈l in
    <x , <-trans x< (lower-bound-<-upper-bound r)
    where
    open Total-order (extended O)
  ∈→<< {O} {t = node _ _ l r _ _} (inj₂ (inj₁ x≡y)) =
    let eq = cong [_] (sym x≡y) in
    subst (_<_ _) eq (lower-bound-<-upper-bound l) ,
    subst (flip _<_ _) eq (lower-bound-<-upper-bound r)
    where
    open Total-order (extended O)
  ∈→<< {O} {t = node _ _ l _ _ _} (inj₂ (inj₂ x∈r)) =
    let <x , x< = ∈→<< x∈r in
    <-trans (lower-bound-<-upper-bound l) <x , x<
    where
    open Total-order (extended O)

opaque

  -- If x is below the lower bound, then x is not in the tree.

  @0 <→∉ :
    let open Total-order (extended O) in
    {t : Tree O pc n lb ub} → [ x ] < lb → ¬ x ∈ t
  <→∉ {O} <lb ∈t =
    let lb< , _ = ∈→<< ∈t in
    <-asymmetric <lb lb<
    where
    open Total-order (extended O)

opaque

  -- If x is above the upper bound, then x is not in the tree.

  @0 >→∉ :
    let open Total-order (extended O) in
    {t : Tree O pc n lb ub} → ub < [ x ] → ¬ x ∈ t
  >→∉ {O} ub< ∈t =
    let _ , <ub = ∈→<< ∈t in
    <-asymmetric <ub ub<
    where
    open Total-order (extended O)

opaque

  -- If x < y, then x is in a tree with y in the root if and only if x
  -- is in the left sub-tree.

  @0 <→∈⇔∈ :
    let open Total-order O in
    x < y →
    x ∈ l ⇔ x ∈ node {O = O} c y l r rinv binv
  <→∈⇔∈ {O} x<y = record
    { to   = inj₁
    ; from =
        P.[ id
          , P.[ (λ eq → ⊥-elim₀ (<-irreflexive (subst (_< _) eq x<y)))
              , (λ ∈r → ⊥-elim₀ (<→∉ ([]-[] x<y) ∈r))
              ]
          ]
    }
    where
    open Total-order O

opaque

  -- If x > y, then x is in a tree with y in the root if and only if x
  -- is in the right sub-tree.

  @0 >→∈⇔∈ :
    let open Total-order O in
    x > y →
    x ∈ r ⇔ x ∈ node {O = O} c y l r rinv binv
  >→∈⇔∈ {O} x>y = record
    { to   = inj₂ ∘ inj₂
    ; from =
        P.[ (λ ∈l → ⊥-elim₀ (>→∉ ([]-[] x>y) ∈l))
          , P.[ (λ eq → ⊥-elim₀ (<-irreflexive (subst (_ <_) eq x>y)))
              , id
              ]
          ]
    }
    where
    open Total-order O

------------------------------------------------------------------------
-- A membership test

opaque

  -- Does the element exist in the tree?

  member? : (x : A) (t : Tree O pc n lb ub) → Dec-Erased (x ∈ t)
  member? _ (leaf _ _) =
    no [ ⊥-elim ]
  member? {O} x (node _ y l r rinv binv)
    with O .Total-order.compare x y
  … | ltᵀ x<y =
    Dec-Erased-map (<→∈⇔∈ {rinv = rinv} {binv = binv} x<y) (member? x l)
  … | eqᵀ x≡y = yes [ inj₂ (inj₁ x≡y) ]
  … | gtᵀ x>y =
    Dec-Erased-map (>→∈⇔∈ {rinv = rinv} {binv = binv} x>y) (member? x r)

------------------------------------------------------------------------
-- An empty tree

opaque

  -- An empty tree.

  empty :
    {@0 A : Type a} {@0 O : Total-order A o} →
    Tree O pc 0 min max
  empty = leaf min-max (refl _)

opaque
  unfolding empty

  -- The empty tree is empty.

  @0 ∉empty : ¬ x ∈ empty {pc = pc} {O = O}
  ∉empty ()

------------------------------------------------------------------------
-- A cast lemma

opaque

  -- A cast lemma.
  --
  -- TODO: It would be nice if this could be compiled into something
  -- that just returned the input tree.

  cast : @0 m ≡ n → Tree O pc m lb ub → Tree O pc n lb ub
  cast eq (leaf lb<ub n≡0) =
    leaf lb<ub (trans (sym eq) n≡0)
  cast eq (node c x l r rinv binv) =
    node c x l r rinv (subst (Black-invariant _ _) eq binv)

opaque
  unfolding cast

  -- A membership lemma for cast.

  @0 ∈-cast : {@0 m≡n : m ≡ n} → x ∈ cast m≡n t ⇔ x ∈ t
  ∈-cast {t = leaf _ _}         = F.id
  ∈-cast {t = node _ _ _ _ _ _} = F.id

------------------------------------------------------------------------
-- Insertion

-- A "fake" parent colour, used in the implementation of
-- Insertion-tree.

@0 fake-parent-colour : Colour → Colour → Colour
fake-parent-colour pc red   = pc
fake-parent-colour pc black = black

-- Insertion-trees are trees for which the red invariant might be
-- broken for the top-most layer.

data Insertion-tree {A : Type a} (O : Total-order A o) (@0 pc : Colour)
       (@0 n : ℕ) (@0 lb ub : Extended A) : Type (a ⊔ o) where
  leaf :
    let open Total-order (extended O) in
    (@0 lb<ub : lb < ub) (@0 n≡0 : n ≡ 0) →
    Insertion-tree O pc n lb ub
  node :
    (c : Colour) (x : A)
    (l : Tree O (fake-parent-colour pc c) m lb [ x ])
    (r : Tree O (fake-parent-colour pc c) m [ x ] ub)
    (@0 binv : Black-invariant c m n) →
    Insertion-tree O pc n lb ub

private variable
  lᴵ rᴵ tᴵ : Insertion-tree _ pc n lb ub

-- Insertion tree membership.

infix 4 _∈ᴵ_

_∈ᴵ_ :
  ∀ {A : Type a} {O : Total-order A o} {@0 lb ub} →
  A → Insertion-tree O pc n lb ub → Type (a ⊔ o)
_ ∈ᴵ leaf _ _       = ⊥
x ∈ᴵ node _ y l r _ = x ∈ l ⊎ x ≡ y ⊎ x ∈ r

-- TODO: It would be nice if the following tree conversion lemmas
-- could be compiled into pieces of code that just returned the input
-- trees.

opaque

  -- Well-formed trees are still well-formed if the parent node is
  -- coloured black.

  with-black-parent :
    Tree O pc n lb ub →
    Tree O black n lb ub
  with-black-parent (leaf lb<ub n≡0)         = leaf lb<ub n≡0
  with-black-parent (node c x l r rinv binv) =
    node c x l r black-parent binv

opaque

  -- A tree that is well-formed for a red parent is well-formed with a
  -- parent of any colour.

  Tree-red→Tree :
    Tree O red n lb ub →
    Tree O pc n lb ub
  Tree-red→Tree (leaf lb<ub n≡0) =
    leaf lb<ub n≡0
  Tree-red→Tree (node c x l r rinv binv) =
    node c x l r (red-parent rinv) binv

opaque

  -- A tree that is well-formed for the colour c is well-formed for
  -- the colour fake-parent-colour pc c.

  with-fake-parent-colour :
    Tree O c n lb ub →
    Tree O (fake-parent-colour pc c) n lb ub
  with-fake-parent-colour {c = black} t = t
  with-fake-parent-colour {c = red}   t = Tree-red→Tree t

opaque

  -- Trees can be converted to insertion trees.

  Tree→Insertion-tree :
    Tree O pc n lb ub → Insertion-tree O pc n lb ub
  Tree→Insertion-tree (leaf lb<ub n≡0) =
    leaf lb<ub n≡0
  Tree→Insertion-tree (node c x l r rinv binv) =
    node c x (with-fake-parent-colour l) (with-fake-parent-colour r)
      binv

opaque

  -- An insertion tree with a red parent can be turned into a tree
  -- with a black parent.

  Insertion-tree-red→Tree-black :
    Insertion-tree O red n lb ub → Tree O black n lb ub
  Insertion-tree-red→Tree-black (leaf lb<ub n≡0) =
    leaf lb<ub n≡0
  Insertion-tree-red→Tree-black (node black x l r binv) =
    node black x l r black-parent binv
  Insertion-tree-red→Tree-black (node red x l r binv) =
    node red x l r black-parent binv

opaque

  -- If the red invariant holds for pc and red, then a tree that is
  -- well-formed with a black parent is well-formed for pc.

  Tree-black→Tree :
    @0 Red-invariant pc red →
    Tree O black n lb ub →
    Tree O pc n lb ub
  Tree-black→Tree rinv (leaf lb<ub n≡0) =
    leaf lb<ub n≡0
  Tree-black→Tree rinv (node c x l r _ binv) =
    node c x l r (red-child rinv) binv

opaque

  -- An insertion tree can be turned into a tree by colouring the
  -- top-most node black.

  Insertion-tree→Tree :
    Insertion-tree O pc n lb ub →
    ∃ λ (n : Erased ℕ) → Tree O pc (n .erased) lb ub
  Insertion-tree→Tree (leaf lb<ub n≡0) =
    [ _ ] , leaf lb<ub n≡0
  Insertion-tree→Tree (node c x l r binv) =
    [ _ ] ,
    node black x (with-black-parent l) (with-black-parent r)
      black-child (black-black binv .proj₂)

opaque
  unfolding Black-invariant

  -- A balancing lemma.

  balanceˡ :
    (x : A) →
    Insertion-tree O c m lb [ x ] →
    Tree O c m [ x ] ub →
    @0 Red-invariant pc c →
    @0 Black-invariant c m n →
    Insertion-tree O pc n lb ub
  balanceˡ {c = red} x l r rinv binv =
    node red x (Tree-black→Tree rinv (Insertion-tree-red→Tree-black l))
      (Tree-red→Tree r) binv
  balanceˡ
    {c = black} x₆ (node red x₄ (node red x₂ t₁ t₃ _ binv₁) t₅ binv₂) t₇
    rinv₃ binv₃ =
    node red x₄
      (node black x₂ (with-black-parent t₁) (with-black-parent t₃)
         rinv₃ (cong suc (trans binv₂ binv₁)))
      (node black x₆ t₅ (cast binv₂ t₇) rinv₃ (cong suc binv₂))
      binv₃
  balanceˡ
    {c = black} x₆ (node red x₂ t₁ (node red x₄ t₃ t₅ _ binv₁) binv₂) t₇
    rinv₃ binv₃ =
    node red x₄
      (node black x₂ t₁ (with-black-parent (cast (sym binv₁) t₃)) rinv₃
         (cong suc binv₂))
      (node black x₆ (with-black-parent (cast (sym binv₁) t₅))
         (cast binv₂ t₇) rinv₃ (cong suc binv₂))
      binv₃
  balanceˡ {c = black} x (leaf lb< n≡0) t _ binv =
    node black x (leaf lb< n≡0) t binv
  balanceˡ
    {c = black} x₂ (node red x₁ (leaf lb< n≡0) (leaf x₁<x₂ _) binv₁) t₃
    _ binv₂ =
    node black x₂
      (node red x₁ (leaf lb< n≡0) (leaf x₁<x₂ n≡0) black-parent binv₁)
      t₃ binv₂
  balanceˡ
    {c = black} x₅
    (node red x₁ (leaf lb< n≡0) (node black x₃ t₂ t₄ _ binv₁) binv₂) t₆
    _ binv₃ =
    node black x₅
      (node red x₁ (leaf lb< n≡0)
         (node black x₃ t₂ t₄ black-child binv₁) black-parent binv₂)
      t₆ binv₃
  balanceˡ
    {c = black} x₅
    (node red x₄ (node black x₂ t₁ t₃ _ binv₁) (leaf x₄<x₅ n≡0) binv₂)
    t₆ _ binv₃ =
    node black x₅
      (node red x₄ (node black x₂ t₁ t₃ black-child binv₁)
         (leaf x₄<x₅ n≡0) black-parent binv₂)
      t₆ binv₃
  balanceˡ
    {c = black} x₈
    (node red x₄ (node black x₂ t₁ t₃ _ binv₁)
       (node black x₆ t₅ t₇ _ binv₂) binv₃)
    t₉ _ binv₄ =
    node black x₈
      (node red x₄ (node black x₂ t₁ t₃ black-child binv₁)
         (node black x₆ t₅ t₇ black-child binv₂) black-parent binv₃)
      t₉ binv₄
  balanceˡ
    {c = black} x₄ (node black x₂ t₁ t₃ binv₁) t₅ _ binv₂ =
    node black x₄ (node black x₂ t₁ t₃ black-parent binv₁) t₅ binv₂

opaque
  unfolding Black-invariant

  -- A balancing lemma.

  balanceʳ :
    (x : A) →
    Tree O c m lb [ x ] →
    Insertion-tree O c m [ x ] ub →
    @0 Red-invariant pc c →
    @0 Black-invariant c m n →
    Insertion-tree O pc n lb ub
  balanceʳ {c = red} x l r rinv binv =
    node red x (Tree-red→Tree l)
      (Tree-black→Tree rinv (Insertion-tree-red→Tree-black r)) binv
  balanceʳ
    {c = black} x₂ t₁ (node red x₆ (node red x₄ t₃ t₅ _ binv₁) t₇ binv₂)
    rinv₃ binv₃ =
    node red x₄
      (node black x₂ (with-black-parent t₁)
         (with-black-parent (cast (sym (trans binv₂ binv₁)) t₃)) rinv₃
         (refl _))
      (node black x₆ (with-black-parent (cast (sym binv₁) t₅)) t₇ rinv₃
         (cong suc binv₂))
      binv₃
  balanceʳ
    {c = black} x₂ t₁ (node red x₄ t₃ (node red x₆ t₅ t₇ _ binv₁) binv₂)
    rinv₃ binv₃ =
    node red x₄
      (node black x₂ t₁ (cast (sym binv₂) t₃) rinv₃ (refl _))
      (node black x₆ (with-black-parent (cast (sym binv₁) t₅))
         (with-black-parent (cast (sym binv₁) t₇)) rinv₃
         (cong suc binv₂))
      binv₃
  balanceʳ {c = black} x t (leaf lb< n≡0) _ binv =
    node black x t (leaf lb< n≡0) binv
  balanceʳ
    {c = black} x₂ t₁ (node red x₃ (leaf x₂<x₃ n≡0) (leaf <ub _) binv₁)
    _ binv₂ =
    node black x₂ t₁
      (node red x₃ (leaf x₂<x₃ n≡0) (leaf <ub n≡0) black-parent binv₁)
      binv₂
  balanceʳ
    {c = black} x₂ t₁
    (node red x₃ (leaf x₂<x₃ n≡0) (node black x₅ t₄ t₆ _ binv₁) binv₂)
    _ binv₃ =
    node black x₂ t₁
      (node red x₃ (leaf x₂<x₃ n≡0)
         (node black x₅ t₄ t₆ black-child binv₁) black-parent binv₂)
      binv₃
  balanceʳ
    {c = black} x₂ t₁
    (node red x₆ (node black x₄ t₃ t₅ _ binv₁) (leaf <ub n≡0) binv₂)
    _ binv₃ =
    node black x₂ t₁
      (node red x₆ (node black x₄ t₃ t₅ black-child binv₁)
         (leaf <ub n≡0) black-parent binv₂)
      binv₃
  balanceʳ
    {c = black} x₂ t₁
    (node red x₆ (node black x₄ t₃ t₅ _ binv₁)
       (node black x₈ t₇ t₉ _ binv₂) binv₃)
    _ binv₄ =
    node black x₂ t₁
      (node red x₆ (node black x₄ t₃ t₅ black-child binv₁)
         (node black x₈ t₇ t₉ black-child binv₂) black-parent binv₃)
      binv₄
  balanceʳ
    {c = black} x₂ t₁ (node black x₄ t₃ t₅ binv₁) _ binv₂ =
    node black x₂ t₁ (node black x₄ t₃ t₅ black-parent binv₁) binv₂

opaque
  unfolding Black-invariant

  -- Inserts an element into the tree.

  insert′ :
    let open Total-order (extended O) in
    (x : A) → Tree O pc n lb ub →
    @0 lb < [ x ] → @0 [ x ] < ub →
    Insertion-tree O pc n lb ub
  insert′ x (leaf lb<ub n≡0) lb< <ub =
    node red x (leaf lb< (refl _)) (leaf <ub (refl _)) n≡0
  insert′ {O} x t@(node c y l r rinv binv) lb< <ub
    with O .Total-order.compare x y
  … | eqᵀ _   = Tree→Insertion-tree t
  … | ltᵀ x<y =
    balanceˡ y (insert′ x l lb< ([]-[] x<y)) r rinv binv
  … | gtᵀ x>y =
    balanceʳ y l (insert′ x r ([]-[] x>y) <ub) rinv binv

opaque

  -- Inserts an element into the tree.

  insert :
    let open Total-order (extended O) in
    (x : A) → Tree O pc n lb ub →
    @0 lb < [ x ] → @0 [ x ] < ub →
    ∃ λ (n : Erased ℕ) → Tree O pc (n .erased) lb ub
  insert x t lb< <ub =
    Insertion-tree→Tree (insert′ x t lb< <ub)

------------------------------------------------------------------------
-- Membership lemmas for insertion

opaque
  unfolding with-black-parent

  -- A membership lemma for with-black-parent.

  @0 ∈-with-black-parent :
    x ∈ with-black-parent t ⇔ x ∈ t
  ∈-with-black-parent {t = leaf _ _}         = F.id
  ∈-with-black-parent {t = node _ _ _ _ _ _} = F.id

opaque
  unfolding Tree-red→Tree

  -- A membership lemma for Tree-red→Tree.

  @0 ∈-Tree-red→Tree : x ∈ Tree-red→Tree {pc = pc} t ⇔ x ∈ t
  ∈-Tree-red→Tree {t = leaf _ _}         = F.id
  ∈-Tree-red→Tree {t = node _ _ _ _ _ _} = F.id

opaque
  unfolding with-fake-parent-colour

  -- A membership lemma for with-fake-parent-colour.

  @0 ∈-with-fake-parent-colour :
    x ∈ with-fake-parent-colour {c = c} {pc = pc} t ⇔ x ∈ t
  ∈-with-fake-parent-colour {c = black} = F.id
  ∈-with-fake-parent-colour {c = red}   = ∈-Tree-red→Tree

opaque
  unfolding Tree→Insertion-tree

  -- Trees can be converted to insertion trees.

  @0 ∈-Tree→Insertion-tree : x ∈ᴵ Tree→Insertion-tree t ⇔ x ∈ t
  ∈-Tree→Insertion-tree {t = leaf _ _} =
    F.id
  ∈-Tree→Insertion-tree {t = node _ _ _ _ _ _} =
    ∈-with-fake-parent-colour ⊎-cong F.id ⊎-cong
    ∈-with-fake-parent-colour

opaque
  unfolding Insertion-tree-red→Tree-black

  -- Trees can be converted to insertion trees.

  @0 ∈-Insertion-tree-red→Tree-black :
    x ∈ Insertion-tree-red→Tree-black tᴵ ⇔ x ∈ᴵ tᴵ
  ∈-Insertion-tree-red→Tree-black {tᴵ = leaf _ _}           = F.id
  ∈-Insertion-tree-red→Tree-black {tᴵ = node black _ _ _ _} = F.id
  ∈-Insertion-tree-red→Tree-black {tᴵ = node red _ _ _ _}   = F.id

opaque
  unfolding Tree-black→Tree

  -- A membership lemma for Tree-black→Tree.

  @0 ∈-Tree-black→Tree :
    x ∈ Tree-black→Tree rinv t ⇔ x ∈ t
  ∈-Tree-black→Tree {t = leaf _ _}         = F.id
  ∈-Tree-black→Tree {t = node _ _ _ _ _ _} = F.id

opaque
  unfolding Insertion-tree→Tree

  -- A membership lemma for Insertion-tree→Tree.

  @0 ∈-Insertion-tree→Tree :
    x ∈ Insertion-tree→Tree tᴵ .proj₂ ⇔ x ∈ᴵ tᴵ
  ∈-Insertion-tree→Tree {tᴵ = leaf _ _}       = F.id
  ∈-Insertion-tree→Tree {tᴵ = node _ _ _ _ _} =
    ∈-with-black-parent ⊎-cong F.id ⊎-cong ∈-with-black-parent

opaque
  unfolding balanceˡ

  -- A membership lemma for balanceˡ.

  @0 ∈-balanceˡ :
    x ∈ᴵ balanceˡ {c = c} y lᴵ r rinv binv ⇔
    x ∈ᴵ lᴵ ⊎ x ≡ y ⊎ x ∈ r
  ∈-balanceˡ {c = red} =
    (∈-Insertion-tree-red→Tree-black F.∘ ∈-Tree-black→Tree) ⊎-cong
    F.id ⊎-cong
    ∈-Tree-red→Tree
  ∈-balanceˡ
    {x} {c = black} {y = x₆}
    {lᴵ = node red x₄ (node red x₂ t₁ t₃ _ _) t₅ _} {r = t₇} =
    (x ∈ with-black-parent t₁ ⊎ x ≡ x₂ ⊎ x ∈ with-black-parent t₃) ⊎
    x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ cast _ t₇                          ↝⟨ (∈-with-black-parent ⊎-cong F.id ⊎-cong ∈-with-black-parent) ⊎-cong
                                                                         F.id ⊎-cong F.id ⊎-cong F.id ⊎-cong ∈-cast ⟩

    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃) ⊎ x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ t₇    ↝⟨ record
                                                                           { to   = P.[ inj₁ ∘ inj₁
                                                                                      , P.[ inj₁ ∘ inj₂ ∘ inj₁ , P.[ inj₁ ∘ inj₂ ∘ inj₂ , inj₂ ] ]
                                                                                      ]
                                                                           ; from = P.[ P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ] ]
                                                                                      , inj₂ ∘ inj₂ ∘ inj₂
                                                                                      ]
                                                                           } ⟩□
    ((x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃) ⊎ x ≡ x₄ ⊎ x ∈ t₅) ⊎ x ≡ x₆ ⊎ x ∈ t₇  □
  ∈-balanceˡ
    {x} {c = black} {y = x₆}
    {lᴵ =
       node red x₂ t₁@(node black _ _ _ _ _) (node red x₄ t₃ t₅ _ _) _}
    {r = t₇} =
    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ with-black-parent (cast _ t₃)) ⊎ x ≡ x₄ ⊎
    x ∈ with-black-parent (cast _ t₅) ⊎ x ≡ x₆ ⊎ x ∈ cast _ t₇        ↝⟨ (F.id ⊎-cong F.id ⊎-cong (∈-cast F.∘ ∈-with-black-parent)) ⊎-cong
                                                                         F.id ⊎-cong (∈-cast F.∘ ∈-with-black-parent) ⊎-cong F.id ⊎-cong ∈-cast ⟩

    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃) ⊎ x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ t₇    ↝⟨ record
                                                                           { to   = P.[ P.[ inj₁ ∘ inj₁
                                                                                          , P.[ inj₁ ∘ inj₂ ∘ inj₁ , inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                          ]
                                                                                      , P.[ inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
                                                                                          , P.[ inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ , inj₂ ]
                                                                                          ]
                                                                                      ]
                                                                           ; from = P.[ P.[ inj₁ ∘ inj₁
                                                                                          , P.[ inj₁ ∘ inj₂ ∘ inj₁
                                                                                              , P.[ inj₁ ∘ inj₂ ∘ inj₂
                                                                                                  , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                                  ]
                                                                                              ]
                                                                                          ]
                                                                                      , inj₂ ∘ inj₂ ∘ inj₂
                                                                                      ]
                                                                           } ⟩□

    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃ ⊎ x ≡ x₄ ⊎ x ∈ t₅) ⊎ x ≡ x₆ ⊎ x ∈ t₇    □
  ∈-balanceˡ
    {x} {c = black} {y = x₆}
    {lᴵ = node red x₂ t₁@(leaf _ _) (node red x₄ t₃ t₅ _ _) _}
    {r = t₇} =
    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ with-black-parent (cast _ t₃)) ⊎ x ≡ x₄ ⊎
    x ∈ with-black-parent (cast _ t₅) ⊎ x ≡ x₆ ⊎ x ∈ cast _ t₇        ↝⟨ (F.id ⊎-cong F.id ⊎-cong (∈-cast F.∘ ∈-with-black-parent)) ⊎-cong
                                                                         F.id ⊎-cong (∈-cast F.∘ ∈-with-black-parent) ⊎-cong F.id ⊎-cong ∈-cast ⟩

    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃) ⊎ x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ t₇    ↝⟨ record
                                                                           { to   = P.[ P.[ inj₁ ∘ inj₁
                                                                                          , P.[ inj₁ ∘ inj₂ ∘ inj₁ , inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                          ]
                                                                                      , P.[ inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
                                                                                          , P.[ inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ , inj₂ ]
                                                                                          ]
                                                                                      ]
                                                                           ; from = P.[ P.[ inj₁ ∘ inj₁
                                                                                          , P.[ inj₁ ∘ inj₂ ∘ inj₁
                                                                                              , P.[ inj₁ ∘ inj₂ ∘ inj₂
                                                                                                  , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                                  ]
                                                                                              ]
                                                                                          ]
                                                                                      , inj₂ ∘ inj₂ ∘ inj₂
                                                                                      ]
                                                                           } ⟩□

    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃ ⊎ x ≡ x₄ ⊎ x ∈ t₅) ⊎ x ≡ x₆ ⊎ x ∈ t₇    □
  ∈-balanceˡ {c = black} {lᴵ = leaf _ _} =
    F.id
  ∈-balanceˡ {c = black} {lᴵ = node red _ (leaf _ _) (leaf _ _) _} =
    F.id
  ∈-balanceˡ
    {c = black} {lᴵ = node red _ (leaf _ _) (node black _ _ _ _ _) _} =
    F.id
  ∈-balanceˡ
    {c = black} {lᴵ = node red _ (node black _ _ _ _ _) (leaf _ _) _} =
    F.id
  ∈-balanceˡ
    {c = black}
    {lᴵ = node red _ (node black _ _ _ _ _) (node black _ _ _ _ _) _} =
    F.id
  ∈-balanceˡ {c = black} {lᴵ = node black _ _ _ _} =
    F.id

opaque
  unfolding balanceʳ

  -- A membership lemma for balanceʳ.

  @0 ∈-balanceʳ :
    x ∈ᴵ balanceʳ {c = c} y l rᴵ rinv binv ⇔
    x ∈ l ⊎ x ≡ y ⊎ x ∈ᴵ rᴵ
  ∈-balanceʳ {c = red} =
    ∈-Tree-red→Tree ⊎-cong F.id ⊎-cong
    (∈-Insertion-tree-red→Tree-black F.∘ ∈-Tree-black→Tree)
  ∈-balanceʳ
    {x} {c = black} {y = x₂} {l = t₁}
    {rᴵ = node red x₆ (node red x₄ t₃ t₅ _ _) t₇ _} =
    (x ∈ with-black-parent t₁ ⊎ x ≡ x₂ ⊎
     x ∈ with-black-parent (cast _ t₃)) ⊎
    x ≡ x₄ ⊎ x ∈ with-black-parent (cast _ t₅) ⊎ x ≡ x₆ ⊎ x ∈ t₇    ↝⟨ (∈-with-black-parent ⊎-cong F.id ⊎-cong
                                                                        (∈-cast F.∘ ∈-with-black-parent)) ⊎-cong
                                                                       F.id ⊎-cong ∈-cast F.∘ ∈-with-black-parent ⊎-cong F.id ⟩

    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃) ⊎ x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ t₇  ↝⟨ record
                                                                         { to   = P.[ P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ∘ inj₁ ] ]
                                                                                    , P.[ inj₂ ∘ inj₂ ∘ inj₁ ∘ inj₂ ∘ inj₁
                                                                                        , P.[ inj₂ ∘ inj₂ ∘ inj₁ ∘ inj₂ ∘ inj₂
                                                                                            , inj₂ ∘ inj₂ ∘ inj₂
                                                                                            ]
                                                                                        ]
                                                                                    ]
                                                                         ; from = P.[ inj₁ ∘ inj₁
                                                                                    , P.[ inj₁ ∘ inj₂ ∘ inj₁
                                                                                        , P.[ P.[ inj₁ ∘ inj₂ ∘ inj₂
                                                                                                , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                                ]
                                                                                            , inj₂ ∘ inj₂ ∘ inj₂
                                                                                            ]
                                                                                        ]
                                                                                    ]
                                                                         } ⟩□
    x ∈ t₁ ⊎ x ≡ x₂ ⊎ (x ∈ t₃ ⊎ x ≡ x₄ ⊎ x ∈ t₅) ⊎ x ≡ x₆ ⊎ x ∈ t₇  □
  ∈-balanceʳ
    {x} {c = black} {y = x₂} {l = t₁}
    {rᴵ =
       node red x₄ t₃@(node black _ _ _ _ _) (node red x₆ t₅ t₇ _ _)
         _} =
    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ cast _ t₃) ⊎ x ≡ x₄ ⊎
     x ∈ with-black-parent (cast _ t₅) ⊎ x ≡ x₆ ⊎
     x ∈ with-black-parent (cast _ t₇)                              ↝⟨ (F.id ⊎-cong F.id ⊎-cong ∈-cast) ⊎-cong F.id ⊎-cong
                                                                       (∈-cast F.∘ ∈-with-black-parent) ⊎-cong F.id ⊎-cong
                                                                       (∈-cast F.∘ ∈-with-black-parent) ⟩

    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃) ⊎ x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ t₇  ↝⟨ record
                                                                         { to   = P.[ P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ] ]
                                                                                    , inj₂ ∘ inj₂ ∘ inj₂
                                                                                    ]
                                                                         ; from = P.[ inj₁ ∘ inj₁
                                                                                    , P.[ inj₁ ∘ inj₂ ∘ inj₁ , P.[ inj₁ ∘ inj₂ ∘ inj₂ , inj₂ ] ]
                                                                                    ]
                                                                         } ⟩□
    x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃ ⊎ x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ t₇    □
  ∈-balanceʳ
    {x} {c = black} {y = x₂} {l = t₁}
    {rᴵ = node red x₄ t₃@(leaf _ _) (node red x₆ t₅ t₇ _ _) _} =
    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ cast _ t₃) ⊎ x ≡ x₄ ⊎
     x ∈ with-black-parent (cast _ t₅) ⊎ x ≡ x₆ ⊎
     x ∈ with-black-parent (cast _ t₇)                              ↝⟨ (F.id ⊎-cong F.id ⊎-cong ∈-cast) ⊎-cong F.id ⊎-cong
                                                                       (∈-cast F.∘ ∈-with-black-parent) ⊎-cong F.id ⊎-cong
                                                                       (∈-cast F.∘ ∈-with-black-parent) ⟩

    (x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃) ⊎ x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ t₇  ↝⟨ record
                                                                         { to   = P.[ P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ] ]
                                                                                    , inj₂ ∘ inj₂ ∘ inj₂
                                                                                    ]
                                                                         ; from = P.[ inj₁ ∘ inj₁
                                                                                    , P.[ inj₁ ∘ inj₂ ∘ inj₁ , P.[ inj₁ ∘ inj₂ ∘ inj₂ , inj₂ ] ]
                                                                                    ]
                                                                         } ⟩□
    x ∈ t₁ ⊎ x ≡ x₂ ⊎ x ∈ t₃ ⊎ x ≡ x₄ ⊎ x ∈ t₅ ⊎ x ≡ x₆ ⊎ x ∈ t₇    □
  ∈-balanceʳ {c = black} {rᴵ = leaf _ _} =
    F.id
  ∈-balanceʳ
    {c = black} {rᴵ = node red _ (leaf _ _) (leaf _ _) _} =
    F.id
  ∈-balanceʳ
    {c = black} {rᴵ = node red _ (leaf _ _) (node black _ _ _ _ _) _} =
    F.id
  ∈-balanceʳ
    {c = black} {rᴵ = node red _ (node black _ _ _ _ _) (leaf _ _) _} =
    F.id
  ∈-balanceʳ
    {c = black}
    {rᴵ = node red _ (node black _ _ _ _ _) (node black _ _ _ _ _) _} =
    F.id
  ∈-balanceʳ {c = black} {rᴵ = node black _ _ _ _} =
    F.id

opaque
  unfolding insert′

  -- The value y is in insert′ x t if and only if y is x or y is in t.

  @0 ∈-insert′ :
    ∀ {t : Tree O pc n lb ub} {@0 lb< <ub} →
    y ∈ᴵ insert′ x t lb< <ub ⇔ y ≡ x ⊎ y ∈ t
  ∈-insert′ {y} {x} {t = leaf _ _} =
    ⊥ ⊎ y ≡ x ⊎ ⊥  ↔⟨ ⊎-left-identity ⟩□
    y ≡ x ⊎ ⊥      □
  ∈-insert′ {O} {y} {x} {t = t@(node _ z l r _ _)}
    with O .Total-order.compare x z
  … | eqᵀ x≡z =
    y ∈ᴵ Tree→Insertion-tree t     ↝⟨ ∈-Tree→Insertion-tree ⟩
    y ∈ t                          ↔⟨⟩
    y ∈ l ⊎ y ≡ z ⊎ y ∈ r          ↝⟨ record { to   = inj₂
                                             ; from = P.[ inj₂ ∘ inj₁ ∘ flip trans x≡z , id ]
                                             } ⟩□
    y ≡ x ⊎ y ∈ l ⊎ y ≡ z ⊎ y ∈ r  □
  … | ltᵀ _ =
    y ∈ᴵ balanceˡ z (insert′ x l _ _) r _ _  ↝⟨ ∈-balanceˡ ⟩
    y ∈ᴵ insert′ x l _ _ ⊎ y ≡ z ⊎ y ∈ r     ↝⟨ ∈-insert′ ⊎-cong F.id ⟩
    (y ≡ x ⊎ y ∈ l) ⊎ y ≡ z ⊎ y ∈ r          ↔⟨ inverse ⊎-assoc ⟩□
    y ≡ x ⊎ y ∈ l ⊎ y ≡ z ⊎ y ∈ r            □
  … | gtᵀ _ =
    y ∈ᴵ balanceʳ z l (insert′ x r _ _) _ _  ↝⟨ ∈-balanceʳ ⟩
    y ∈ l ⊎ y ≡ z ⊎ y ∈ᴵ insert′ x r _ _     ↝⟨ F.id ⊎-cong F.id ⊎-cong ∈-insert′ ⟩
    y ∈ l ⊎ y ≡ z ⊎ y ≡ x ⊎ y ∈ r            ↝⟨ record
                                                  { to   = P.[ inj₂ ∘ inj₁ , P.[ inj₂ ∘ inj₂ ∘ inj₁ , P.[ inj₁ , inj₂ ∘ inj₂ ∘ inj₂ ] ] ]
                                                  ; from = P.[ inj₂ ∘ inj₂ ∘ inj₁ , P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₂ ] ] ]
                                                  } ⟩□
    y ≡ x ⊎ y ∈ l ⊎ y ≡ z ⊎ y ∈ r            □

opaque
  unfolding insert

  -- The value y is in insert x t if and only if y is x or y is in t.

  @0 ∈-insert :
    ∀ {@0 lb< <ub} →
    y ∈ insert x t lb< <ub .proj₂ ⇔ y ≡ x ⊎ y ∈ t
  ∈-insert {y} {x} {t} {lb<} {<ub}=
    y ∈ Insertion-tree→Tree (insert′ x t lb< <ub) .proj₂  ↝⟨ ∈-Insertion-tree→Tree ⟩
    y ∈ᴵ insert′ x t lb< <ub                              ↝⟨ ∈-insert′ ⟩□
    y ≡ x ⊎ y ∈ t                                         □

------------------------------------------------------------------------
-- An interface with fewer parameters

opaque

  -- Trees with fewer parameters.

  Tree⁻ : {A : Type a} → Total-order A o → Type (a ⊔ o)
  Tree⁻ O = ∃ λ (n : Erased ℕ) → Tree O black (n .erased) min max

opaque
  unfolding Tree⁻

  infix 4 _∈⁻_

  -- A membership relation.

  _∈⁻_ :
    {A : Type a} {O : Total-order A o} →
    A → Tree⁻ O → Type (a ⊔ o)
  x ∈⁻ (_ , t) = x ∈ t

opaque
  unfolding Tree⁻ _∈⁻_

  -- Does the element exist in the tree?

  member?⁻ : (x : A) (t : Tree⁻ O) → Dec-Erased (x ∈⁻ t)
  member?⁻ x (_ , t) = member? x t

opaque
  unfolding Tree⁻

  -- An empty tree.

  empty⁻ :
    {@0 A : Type a} {@0 O : Total-order A o} →
    Tree⁻ O
  empty⁻ = [ _ ] , empty

opaque
  unfolding _∈⁻_ empty⁻

  -- The empty tree is empty.

  @0 ∉empty⁻ : ¬ x ∈⁻ empty⁻ {O = O}
  ∉empty⁻ = ∉empty

opaque
  unfolding Tree⁻

  -- Inserts an element into the tree.

  insert⁻ : {O : Total-order A o} → A → Tree⁻ O → Tree⁻ O
  insert⁻ x (_ , t) = insert x t min-[] []-max

opaque
  unfolding _∈⁻_ insert⁻

  -- The value y is in insert⁻ x t if and only if y is x or y is in t.

  @0 ∈⁻-insert⁻ :
    {t : Tree⁻ O} →
    y ∈⁻ insert⁻ x t ⇔ y ≡ x ⊎ y ∈⁻ t
  ∈⁻-insert⁻ = ∈-insert
