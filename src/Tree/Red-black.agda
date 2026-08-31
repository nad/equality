------------------------------------------------------------------------
-- Red-black trees with integrated invariants
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
open import Prelude
import Total-order.Erased

module Tree.Red-black
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺)
  (open Total-order.Erased eq)
  {a o}
  -- The carrier type.
  {A : Type a}
  -- The carrier type is assumed to be totally ordered.
  (O : Total-order A o)
  where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)

import Bag-equivalence eq as L
open import Bijection eq using (_↔_)
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_)
open import Equivalence-relation eq
open import Erased.Level-1 eq
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level.Closure eq
open import List eq
open import Maybe eq
import Nat eq as N
import Total-order.Erased eq as TE
open import Tree.Red-black.External-invariants eq O

private
  open module O = TE.Total-order O using (_<_; _≤_)
open Sorted-list O

private variable
  @0 m n   : ℕ
  @0 x y   : A
  @0 lb ub : Extended _
  @0 c     : Colour

------------------------------------------------------------------------
-- Red-black trees with integrated invariants

-- Red-black trees.

record Tree : Type (a ⊔ o) where
  no-eta-equality
  pattern
  field
    tree              : Tree⁻
    @0 {black-height} : ℕ
    @0 red-black      : Red-black black black-height min max tree

private variable
  @0 t t′ t″ t₁ t₂ : Tree

opaque

  -- There is an equivalence between equality of two trees and
  -- equality of the corresponding underlying trees.

  @0 tree-cong : (Tree.tree t₁ ≡ Tree.tree t₂) ≃ (t₁ ≡ t₂)
  tree-cong {t₁} {t₂} =
    Tree.tree t₁ ≡ Tree.tree t₂               ↔⟨ ignore-propositional-component
                                                   (proj₁-unique→Σ-propositional
                                                      (λ (_ , rb₁) (_ , rb₂) → black-height-unique rb₁ rb₂)
                                                      (λ _ → Red-black-propositional)) ⟩
    (Tree.tree t₁ , _ , Tree.red-black t₁) ≡
    (Tree.tree t₂ , _ , Tree.red-black t₂)    ↔⟨ Eq.≃-≡ equiv ⟩□

    t₁ ≡ t₂                                   □
    where
    equiv :
      Tree ≃ (∃ λ (t : Tree⁻) → ∃ λ n → Red-black black n min max t)
    equiv = Eq.↔→≃
      (λ t → Tree.tree t , _ , Tree.red-black t)
      (λ (t , _ , tʳᵇ) → record { tree = t; red-black = tʳᵇ })
      refl
      (λ { record{} → refl _ })

------------------------------------------------------------------------
-- Membership

opaque

  infix 4 _∈_

  -- A membership relation.

  _∈_ : A → Tree → Type a
  x ∈ t = x ∈⁻ Tree.tree t

opaque
  unfolding _∈_

  -- Tree membership is propositional.

  @0 ∈-propositional : Is-proposition (x ∈ t)
  ∈-propositional {t} = ∈⁻-propositional (Tree.red-black t)

------------------------------------------------------------------------
-- Set equivalence

opaque

  -- Set equivalence.

  infix 4 _≈_

  _≈_ : (_ _ : Tree) → Type a
  t₁ ≈ t₂ = ∀ {x} → x ∈ t₁ ⇔ x ∈ t₂

opaque
  unfolding _≈_

  -- The relation _≈_ is propositional (assuming function
  -- extensionality).

  @0 ≈-propositional :
    Extensionality a a →
    Is-proposition (t₁ ≈ t₂)
  ≈-propositional ext =
    implicit-Π-closure ext 1 λ _ →
    ⇔-closure ext 1 ∈-propositional ∈-propositional

opaque
  unfolding _≈_

  -- The relation _≈_ is an equivalence relation.

  ≈-equivalence : Is-equivalence-relation _≈_
  ≈-equivalence = λ where
      .reflexive  → F.id
      .symmetric  → λ x≈y → inverse x≈y
      .transitive → λ x≈y y≈z → y≈z F.∘ x≈y
    where
    open Is-equivalence-relation

opaque

  -- A variant of set equivalence for the results returned by
  -- delete-min₀ (which is defined below).

  @0 Delete-min₀-≈ : (_ _ : Maybe (A × Tree)) → Type a
  Delete-min₀-≈ = Maybeᴾ (_≡_ ×ᴾ _≈_)

------------------------------------------------------------------------
-- Heights

-- The height of a red-black tree.

@0 height : Tree → ℕ
height t = height⁻ (Tree.tree t)

opaque

  -- The height is at least the black height.

  @0 black-height≤height : ∀ t → Tree.black-height t N.≤ height t
  black-height≤height = lemma _ ∘ Tree.red-black
    where
    lemma : ∀ t → Red-black c n lb ub t → n N.≤ height⁻ t
    lemma {n} leaf (leafʳᵇ _ n≡0) =
      n  N.≡⟨ n≡0 ⟩≤
      0  N.∎≤
    lemma {n} (node _ l _ r) (m , l-ok , r-ok , _ , binv) =
      n                                    N.≤⟨ Black-invariant→≤ binv ⟩
      suc m                                N.≡⟨ cong suc (sym (N.max-idempotent _)) ⟩≤
      suc (N.max m m)                      N.≤⟨ N.suc≤suc (N.max-mono (lemma l l-ok) (lemma r r-ok)) ⟩∎
      suc (N.max (height⁻ l) (height⁻ r))  ∎≤

opaque
  unfolding Red-invariant Black-invariant

  -- The height is at most one plus twice the black height.

  @0 height≤1+2*black-height :
    ∀ t → height t N.≤ 1 + 2 * Tree.black-height t
  height≤1+2*black-height = lemmaᵇ _ ∘ Tree.red-black
    where
    mutual
      lemmaᵇ :
        ∀ t → Red-black black n lb ub t → height⁻ t N.≤ 1 + 2 * n
      lemmaᵇ {n} leaf (leafʳᵇ _ n≡0) =
        N.zero≤ _
      lemmaᵇ {n} (node black l _ r) (nodeʳᵇ l-ok r-ok _ n≡1+m) =
        1 + N.max (height⁻ l) (height⁻ r)  N.≤⟨ black-case l r l-ok r-ok n≡1+m ⟩
        2 * n                              N.≤⟨ N.pred≤ _ ⟩∎
        1 + 2 * n                          ∎≤
      lemmaᵇ {n} (node red l _ r) (m , l-ok , r-ok , _ , n≡m) =
        1 + N.max (height⁻ l) (height⁻ r)  N.≤⟨ N.≤-refl N.+-mono N.max-mono (lemmaʳ l l-ok) (lemmaʳ r r-ok) ⟩
        1 + N.max (2 * m) (2 * m)          N.≡⟨ cong (1 +_) (N.max-idempotent _) ⟩≤
        1 + 2 * m                          N.≡⟨ cong ((1 +_) ∘ (2 *_)) (sym n≡m) ⟩≤
        1 + 2 * n                          N.∎≤

      lemmaʳ : ∀ t → Red-black red n lb ub t → height⁻ t N.≤ 2 * n
      lemmaʳ leaf (leafʳᵇ _ n≡0) =
        N.zero≤ _
      lemmaʳ (node black l _ r) (nodeʳᵇ l-ok r-ok _ n≡1+m) =
        black-case l r l-ok r-ok n≡1+m
      lemmaʳ (node red _ _ _) (nodeʳᵇ _ _ rinv _) =
        ⊥-elim (not-red-red rinv)

      black-case :
        ∀ l r →
        Red-black black m lb [ x ] l →
        Red-black black m [ x ] ub r →
        n ≡ 1 + m →
        1 + N.max (height⁻ l) (height⁻ r) N.≤ 2 * n
      black-case {m} {n} l r l-ok r-ok n≡1+m =
        1 + N.max (height⁻ l) (height⁻ r)  N.≤⟨ N.≤-refl N.+-mono N.max-mono (lemmaᵇ l l-ok) (lemmaᵇ r r-ok) ⟩
        1 + N.max (1 + 2 * m) (1 + 2 * m)  N.≡⟨ cong suc (N.max-idempotent _) ⟩≤
        2 + 2 * m                          N.≡⟨ sym (N.*-+-distribˡ 2 {n = 1}) ⟩≤
        2 * suc m                          N.≡⟨ cong (2 *_) (sym n≡1+m) ⟩≤
        2 * n                              N.∎≤

opaque

  -- A variant of height≤1+2*black-height.

  @0 ⌈height∸1/2⌉≤black-height :
    ∀ t → N.⌈ height t ∸ 1 /2⌉ N.≤ Tree.black-height t
  ⌈height∸1/2⌉≤black-height t =
    N.⌈ height t ∸ 1 /2⌉                       N.≤⟨ N.⌈/2⌉-mono (height≤1+2*black-height t N.∸-mono N.≤-refl) ⟩
    N.⌈ (1 + 2 * Tree.black-height t) ∸ 1 /2⌉  N.≡⟨⟩≤
    N.⌈ 2 * Tree.black-height t /2⌉            N.≡⟨ N.⌈2*/2⌉≡ _ ⟩≤
    Tree.black-height t                        N.∎≤

------------------------------------------------------------------------
-- Conversion to lists

opaque

  -- Converts the tree to a sorted list.

  to-List : Tree → List A
  to-List t = to-List⁻ (Tree.tree t)

opaque
  unfolding _∈_ to-List

  -- A membership lemma for to-List.

  @0 ∈-to-List : (x L.∈ to-List t) ≃ (x ∈ t)
  ∈-to-List = ∈⁻-to-List⁻

opaque
  unfolding to-List

  -- The list returned by to-List is sorted.

  @0 Sorted-to-List : Sorted min max (to-List t)
  Sorted-to-List {t} = Sorted-to-List⁻ (Tree.red-black t)

opaque
  unfolding _≈_

  -- The trees t₁ and t₂ are set equivalent if and only if to-List t₁
  -- is equal to to-List t₂.

  @0 ≈⇔to-List≡to-List : t₁ ≈ t₂ ⇔ to-List t₁ ≡ to-List t₂
  ≈⇔to-List≡to-List {t₁} {t₂} = record
    { to = λ t₁≈t₂ →
        Sorted→≈→≡ Sorted-to-List Sorted-to-List λ x →
          x L.∈ to-List t₁  ↔⟨ ∈-to-List ⟩
          x ∈ t₁            ↝⟨ t₁≈t₂ ⟩
          x ∈ t₂            ↔⟨ inverse ∈-to-List ⟩□
          x L.∈ to-List t₂  □
    ; from = λ eq {x} →
        x ∈ t₁            ↔⟨ inverse ∈-to-List ⟩
        x L.∈ to-List t₁  ↝⟨ ≡⇒↝ _ (cong (L._∈_ _) eq) ⟩
        x L.∈ to-List t₂  ↔⟨ ∈-to-List ⟩□
        x ∈ t₂            □
    }

------------------------------------------------------------------------
-- Size

-- The size of a red-black tree.
--
-- The function is erased because it is (at least) linear in the size
-- of the tree, so it is not recommended to be used at run-time.

@0 size : Tree → ℕ
size t = size⁻ (Tree.tree t)

opaque
  unfolding to-List

  -- The function size can be expressed using length and to-List.

  @0 size≡length∘to-List : size t ≡ length (to-List t)
  size≡length∘to-List = size⁻≡length∘to-List⁻

opaque
  unfolding _≈_

  -- The function size respects set equivalence.

  @0 size-respects-set-equivalence :
    t₁ ≈ t₂ → size t₁ ≡ size t₂
  size-respects-set-equivalence {t₁} {t₂} t₁≈t₂ =
    size t₁              ≡⟨ size≡length∘to-List ⟩
    length (to-List t₁)  ≡⟨ cong length (_⇔_.to ≈⇔to-List≡to-List t₁≈t₂) ⟩
    length (to-List t₂)  ≡⟨ sym size≡length∘to-List ⟩∎
    size t₂              ∎

------------------------------------------------------------------------
-- Lemmas relating sizes and heights

opaque

  -- A lemma relating the size of a red-black tree to its height.
  --
  -- See also 2^⌈height∸1/2⌉∸1≤size below.

  @0 size≤2^height∸1 : ∀ t → size t N.≤ 2 ^ height t ∸ 1
  size≤2^height∸1 _ = size⁻≤2^height⁻∸1

opaque

  -- A lemma relating the size of a red-black tree to its black
  -- height.

  @0 size≤2^1+2*black-height∸1 :
    ∀ t → size t N.≤ 2 ^ (1 + 2 * Tree.black-height t) ∸ 1
  size≤2^1+2*black-height∸1 t =
    size t                                 N.≤⟨ size≤2^height∸1 t ⟩
    2 ^ height t ∸ 1                       N.≤⟨ N.≤-refl N.⁺^-mono height≤1+2*black-height t N.∸-mono N.≤-refl {n = 1} ⟩∎
    2 ^ (1 + 2 * Tree.black-height t) ∸ 1  ∎≤

opaque
  unfolding Black-invariant

  -- Another lemma relating the size of a red-black tree to its black
  -- height.

  @0 2^black-height∸1≤size :
    ∀ t → 2 ^ Tree.black-height t ∸ 1 N.≤ size t
  2^black-height∸1≤size t =
    lemma _ (Tree.red-black t) N.∸-mono N.≤-refl
    where
    lemma : ∀ t → Red-black c n lb ub t → 2 ^ n N.≤ 1 + size⁻ t
    lemma {n} leaf (leafʳᵇ _ n≡0) =
      2 ^ n  N.≡⟨ cong (2 ^_) n≡0 ⟩≤
      1      N.∎≤
    lemma {n} (node black l _ r) (m , l-ok , r-ok , _ , n≡1+m) =
      2 ^ n                          N.≡⟨ cong (2 ^_) n≡1+m ⟩≤
      2 ^ (1 + m)                    N.≡⟨ N.2*≡+ (2 ^ m) ⟩≤
      2 ^ m + 2 ^ m                  N.≤⟨ lemma l l-ok N.+-mono lemma r r-ok ⟩
      (1 + size⁻ l) + (1 + size⁻ r)  N.≡⟨ sym (N.suc+≡+suc (1 + _)) ⟩≤
      2 + size⁻ l + size⁻ r          N.∎≤
    lemma {n} (node red l _ r) (m , l-ok , r-ok , _ , n≡m) =
      2 ^ n                          N.≡⟨ cong (2 ^_) n≡m ⟩≤
      2 ^ m                          N.≤⟨ N.m≤m+n _ _ ⟩
      2 ^ m + 2 ^ m                  N.≤⟨ lemma l l-ok N.+-mono lemma r r-ok ⟩
      (1 + size⁻ l) + (1 + size⁻ r)  N.≡⟨ sym (N.suc+≡+suc (1 + _)) ⟩≤
      2 + size⁻ l + size⁻ r          N.∎≤

opaque

  -- Another lemma relating the size of a red-black tree to its
  -- height.
  --
  -- Note that this lemma and size≤2^height∸1 imply that the height is
  -- Θ(log n), where n is the size.

  @0 2^⌈height∸1/2⌉∸1≤size :
    ∀ t → 2 ^ N.⌈ height t ∸ 1 /2⌉ ∸ 1 N.≤ size t
  2^⌈height∸1/2⌉∸1≤size t =
    2 ^ N.⌈ height t ∸ 1 /2⌉ ∸ 1  N.≤⟨ N.≤-refl N.⁺^-mono ⌈height∸1/2⌉≤black-height t N.∸-mono N.≤-refl {n = 1} ⟩
    2 ^ Tree.black-height t ∸ 1   N.≤⟨ 2^black-height∸1≤size t ⟩∎
    size t                        ∎≤

------------------------------------------------------------------------
-- A membership test

opaque
  unfolding _∈_

  -- Does the element exist in the tree?

  member? : (x : A) (t : Tree) → Dec-Erased (x ∈ t)
  member? x t = member?⁻ x (Tree.tree t) (Tree.red-black t)

------------------------------------------------------------------------
-- An empty tree

opaque

  -- An empty tree.

  empty : Tree
  empty = record
    { tree      = empty⁻
    ; red-black = empty⁻ʳᵇ
    }

opaque
  unfolding _∈_ empty

  -- The empty tree is empty.

  @0 ∉empty : ¬ x ∈ empty
  ∉empty = ∉⁻empty⁻

------------------------------------------------------------------------
-- Insertion

opaque

  -- Inserts an element into the tree.

  insert : A → Tree → Tree
  insert x t = record
    { tree      = insert⁻ x (Tree.tree t)
    ; red-black = insert⁻ʳᵇ (Tree.red-black t) min-[] []-max .proj₂
    }

opaque
  unfolding _∈_ insert

  -- The value y is in insert x t if and only if y is x or y is in t.

  @0 ∈-insert :
    y ∈ insert x t ⇔ y ≡ x ⊎ y ∈ t
  ∈-insert = ∈⁻-insert⁻

opaque
  unfolding _≈_

  -- The function insert respects set equivalence.

  @0 insert-respects-set-equivalence :
    t₁ ≈ t₂ → insert x t₁ ≈ insert x t₂
  insert-respects-set-equivalence {t₁} {t₂} {x} =
    (∀ {y} → y ∈ t₁ ⇔ y ∈ t₂)                    →⟨ (λ hyp {y} →

      y ∈ insert x t₁                                  ↝⟨ ∈-insert ⟩
      y ≡ x ⊎ y ∈ t₁                                   ↝⟨ F.id ⊎-cong hyp ⟩
      y ≡ x ⊎ y ∈ t₂                                   ↝⟨ inverse ∈-insert ⟩□
      y ∈ insert x t₂                                  □) ⟩□

    (∀ {y} → y ∈ insert x t₁ ⇔ y ∈ insert x t₂)  □

------------------------------------------------------------------------
-- Deletion

opaque

  -- Deletes the given element, if it exists in the tree.

  delete : A → Tree → Tree
  delete x t = record
    { tree      = delete⁻ x (Tree.tree t)
    ; red-black = delete⁻ʳᵇ (Tree.red-black t) .proj₂
    }

opaque
  unfolding _∈_ delete

  -- A membership lemma for delete.

  @0 ∈-delete : y ∈ delete x t ⇔ y ≢ x × y ∈ t
  ∈-delete {t} = ∈⁻-delete⁻ (Tree.red-black t)

opaque
  unfolding _≈_

  -- The function delete respects set equivalence.

  @0 delete-respects-set-equivalence :
    t₁ ≈ t₂ → delete x t₁ ≈ delete x t₂
  delete-respects-set-equivalence {t₁} {t₂} {x} =
    (∀ {y} → y ∈ t₁ ⇔ y ∈ t₂)                    →⟨ (λ hyp {y} →

      y ∈ delete x t₁                                  ↝⟨ ∈-delete ⟩
      y ≢ x × y ∈ t₁                                   ↝⟨ F.id ×-cong hyp ⟩
      y ≢ x × y ∈ t₂                                   ↝⟨ inverse ∈-delete ⟩□
      y ∈ delete x t₂                                  □) ⟩□

    (∀ {y} → y ∈ delete x t₁ ⇔ y ∈ delete x t₂)  □

------------------------------------------------------------------------
-- Finding the minimum element

opaque
  unfolding empty empty⁻

  -- Finds the minimum element. The tree must be non-empty.

  find-min : (t : Tree) → @0 t ≢ empty → A
  find-min t ≢empty =
    find-min⁻ (Tree.tree t)
      (Tree.tree t ≡ leaf  →⟨ _≃_.to tree-cong ⟩
       t ≡ empty           →⟨ ≢empty ⟩□
       ⊥                   □)

opaque
  unfolding _∈_ find-min

  -- A membership lemma for find-min.

  @0 find-min-∈ :
    {≢empty : t ≢ empty} →
    find-min t ≢empty ∈ t
  find-min-∈ = find-min⁻-∈⁻

opaque
  unfolding _∈_ find-min

  -- An ordering lemma for find-min.

  @0 find-min-≤ :
    {≢empty : t ≢ empty} →
    x ∈ t → find-min t ≢empty ≤ x
  find-min-≤ {t} = find-min⁻-≤ _ (Tree.red-black t)

opaque
  unfolding _≈_

  -- The function find-min respects set equivalence.

  @0 find-min-respects-set-equivalence :
    {t₁≢empty : t₁ ≢ empty}
    {t₂≢empty : t₂ ≢ empty} →
    t₁ ≈ t₂ → find-min t₁ t₁≢empty ≡ find-min t₂ t₂≢empty
  find-min-respects-set-equivalence t₁≈t₂ =
    O.≤-antisym (find-min-≤ (_⇔_.from t₁≈t₂ find-min-∈))
      (find-min-≤ (_⇔_.to t₁≈t₂ find-min-∈))

------------------------------------------------------------------------
-- Deleting the minimum element

private opaque

  -- A function used in the implementation of delete-min₀.

  delete-min₀-helper-just :
    (t : Tree) (result : A × Tree⁻) →
    @0 delete-min⁻₀ (Tree.tree t) ≡ just result →
    A × Tree
  delete-min₀-helper-just t (x , t′) eq =
    ( x
    , record
        { tree      = t′
        ; red-black =
            let _ , t′ʳᵇ = delete-min⁻₀ʳᵇ _ eq (Tree.red-black t) in
            Red-black-<ˡ min-[] t′ʳᵇ
        }
    )

  -- A function used in the implementation of delete-min₀.

  delete-min₀-helper :
    (t : Tree)
    (result : Maybe (A × Tree⁻)) →
    @0 delete-min⁻₀ (Tree.tree t) ≡ result →
    Maybe (A × Tree)
  delete-min₀-helper _ nothing  _  = nothing
  delete-min₀-helper t (just r) eq =
    just (delete-min₀-helper-just t r eq)

  -- A lemma related to delete-min₀-helper.

  @0 Is-nothing-delete-min₀-helper :
    (result : Maybe (A × Tree⁻))
    {eq : delete-min⁻₀ (Tree.tree t) ≡ result} →
    Is-nothing (delete-min₀-helper t result eq) ⇔ Is-nothing result
  Is-nothing-delete-min₀-helper nothing  = F.id
  Is-nothing-delete-min₀-helper (just _) = F.id

  -- A lemma related to delete-min₀-helper.

  @0 Is-just-delete-min₀-helper :
    (result : Maybe (A × Tree⁻))
    {eq : delete-min⁻₀ (Tree.tree t) ≡ result} →
    Is-just (delete-min₀-helper t result eq) ⇔ Is-just result
  Is-just-delete-min₀-helper nothing  = F.id
  Is-just-delete-min₀-helper (just _) = F.id

opaque

  -- Returns and deletes the minimum element, if any. If the tree is
  -- empty, then nothing is returned.

  delete-min₀ : Tree → Maybe (A × Tree)
  delete-min₀ t =
    delete-min₀-helper t (delete-min⁻₀ (Tree.tree t)) (refl _)

opaque
  unfolding _∈_ delete-min₀

  -- The function delete-min₀ returns nothing if and only if the tree
  -- is empty.

  @0 Is-nothing-delete-min₀ :
    Is-nothing (delete-min₀ t) ⇔ (∀ {x} → ¬ x ∈ t)
  Is-nothing-delete-min₀ {t} =
    Is-nothing (delete-min₀ t)                                      ↔⟨⟩

    Is-nothing
      (delete-min₀-helper t (delete-min⁻₀ (Tree.tree t)) (refl _))  ↝⟨ Is-nothing-delete-min₀-helper _ ⟩

    Is-nothing (delete-min⁻₀ (Tree.tree t))                         ↝⟨ Is-nothing-delete-min⁻₀ ⟩

    (∀ {x} → ¬ x ∈⁻ Tree.tree t)                                    ↔⟨⟩

    (∀ {x} → ¬ x ∈ t)                                               □

opaque
  unfolding _∈_ delete-min₀

  -- The value of delete-min₀ t is just something if and only if t is
  -- non-empty.

  @0 Is-just-delete-min₀ :
    Is-just (delete-min₀ t) ⇔ (∃ λ x → x ∈ t)
  Is-just-delete-min₀ {t} =
    Is-just (delete-min₀ t)                                               ↔⟨⟩
    Is-just (delete-min₀-helper t (delete-min⁻₀ (Tree.tree t)) (refl _))  ↝⟨ Is-just-delete-min₀-helper _ ⟩
    Is-just (delete-min⁻₀ (Tree.tree t))                                  ↝⟨ Is-just-delete-min⁻₀ ⟩
    (∃ λ x → x ∈⁻ Tree.tree t)                                            ↔⟨⟩
    (∃ λ x → x ∈ t)                                                       □

opaque
  unfolding _∈_ _≈_ delete-min₀ delete-min⁻₀ delete-min₀-helper

  -- The value of delete-min₀ t is just (x , t″) for some tree t″ that
  -- is set equivalent to t′ if and only if
  --
  -- * x is strictly smaller than all elements in t′ and
  --
  -- * every value is in t if and only it is either equal to x or in
  --   t′.

  @0 delete-min₀-just-⇔ :
    (∃ λ t″ →
         delete-min₀ t ≡ just (x , t″) × t′ ≈ t″) ⇔
    (∀ {y} → y ∈ t′ → x < y) × (∀ {y} → y ∈ t ⇔ y ≡ x ⊎ y ∈ t′)
  delete-min₀-just-⇔ {t@record{}} {x} {t′} =
    (∃ λ t″ → delete-min₀ t ≡ just (x , t″) × t′ ≈ t″)           ↝⟨ record
                                                                      { to   = λ (_ , eq , equiv) → _ , lemma₁ _ eq , equiv
                                                                      ; from = λ (_ , eq , equiv) → lemma₂ _ _ eq equiv
                                                                      } ⟩
    (∃ λ t″ →
       delete-min⁻₀ (Tree.tree t) ≡ just (x , t″) ×
       (∀ {y} → y ∈ t′ ⇔ y ∈⁻ t″))                               ↝⟨ delete-min⁻₀-just-⇔ (Tree.red-black t) ⟩□

    (∀ {y} → y ∈ t′ → x < y) × (∀ {y} → y ∈ t ⇔ y ≡ x ⊎ y ∈ t′)  □
    where
    lemma₁ :
      (t : Tree⁻) {tʳᵇ : Red-black black n min max t} →
      delete-min₀ (record { tree = t; red-black = tʳᵇ }) ≡
        just (x , t″) →
      delete-min⁻₀ t ≡ just (x , Tree.tree t″)
    lemma₁ leaf  = ⊥-elim ∘ ⊎.inj₁≢inj₂
    lemma₁ node⁰ = cong (just ∘ Σ-map id Tree.tree) ∘ ⊎.cancel-inj₂

    lemma₂ :
      ∀ {t″}
      (result : Maybe (A × Tree⁻))
      (eq : delete-min⁻₀ (Tree.tree t) ≡ result) →
      result ≡ just (x , t″) →
      (∀ {y} → y ∈ t′ ⇔ y ∈⁻ t″) →
      ∃ λ t‴ →
          delete-min₀-helper t result eq ≡ just (x , t‴) ×
          (∀ {y} → y ∈ t′ ⇔ y ∈ t‴)
    lemma₂ nothing _ eq′ _ =
      ⊥-elim (⊎.inj₁≢inj₂ eq′)
    lemma₂ (just _) eq eq′ equiv =
      let ≡x , ≡t″ = _↔_.from ≡×≡↔≡ (⊎.cancel-inj₂ eq′) in
      delete-min₀-helper-just t _ eq .proj₂ ,
      cong (λ x → just (x , _)) ≡x ,
      subst ((_ ⇔_) ∘ (_ ∈⁻_)) (sym ≡t″) equiv

opaque
  unfolding _≈_

  -- An ordering lemma for delete-min₀.

  @0 <-delete-min₀ :
    delete-min₀ t ≡ just (x , t′) →
    y ∈ t′ → x < y
  <-delete-min₀ eq =
    _⇔_.to delete-min₀-just-⇔ (_ , eq , F.id) .proj₁

opaque
  unfolding _≈_

  -- A membership lemma for delete-min₀.

  @0 ∈-delete-min₀ :
    delete-min₀ t ≡ just (x , t′) →
    y ∈ t ⇔ y ≡ x ⊎ y ∈ t′
  ∈-delete-min₀ eq =
    _⇔_.to delete-min₀-just-⇔ (_ , eq , F.id) .proj₂

opaque
  unfolding _≈_ Delete-min₀-≈

  -- The function delete-min₀ respects set equivalence.

  @0 delete-min₀-respects-set-equivalence :
    t₁ ≈ t₂ → Delete-min₀-≈ (delete-min₀ t₁) (delete-min₀ t₂)
  delete-min₀-respects-set-equivalence =
    lemma _ _ (refl _) (refl _)
    where
    lemma :
      (r₁ r₂ : Maybe (A × Tree)) →
      r₁ ≡ delete-min₀ t₁ →
      r₂ ≡ delete-min₀ t₂ →
      t₁ ≈ t₂ → Delete-min₀-≈ r₁ r₂
    lemma nothing nothing _ _ _ =
      _
    lemma nothing (just _) eq₁ eq₂ t₁≈t₂ =
      ⊥-elim $
      not-both-just-and-nothing (delete-min₀ _)
        (_⇔_.from Is-just-delete-min₀
           (_ ,
            _⇔_.from t₁≈t₂
              (_⇔_.to Is-just-delete-min₀ (subst Is-just eq₂ _)
                 .proj₂)))
        (subst Is-nothing eq₁ _)
    lemma (just _) nothing eq₁ eq₂ t₁≈t₂ =
      ⊥-elim $
      not-both-just-and-nothing (delete-min₀ _)
        (_⇔_.from Is-just-delete-min₀
           (_ ,
            _⇔_.to t₁≈t₂
              (_⇔_.to Is-just-delete-min₀ (subst Is-just eq₁ _)
                 .proj₂)))
        (subst Is-nothing eq₂ _)
    lemma {t₁} {t₂} (just (x₁ , t₁′)) (just (x₂ , t₂′)) eq₁ eq₂ t₁≈t₂ =
      let t₂″ , eq , t₂′≈t₂″ =
            _⇔_.from delete-min₀-just-⇔
              ( <-delete-min₀ (sym eq₂)
              , λ {y} →
                   y ∈ t₁            ↝⟨ t₁≈t₂ ⟩
                   y ∈ t₂            ↝⟨ ∈-delete-min₀ (sym eq₂) ⟩□
                   y ≡ x₂ ⊎ y ∈ t₂′  □
              )

          eq = ⊎.cancel-inj₂
            (just (x₁ , t₁′)  ≡⟨ eq₁ ⟩
             delete-min₀ t₁   ≡⟨ eq ⟩∎
             just (x₂ , t₂″)  ∎)
      in
      cong proj₁ eq ,
      (λ {x} →
         x ∈ t₁′  ↝⟨ ≡⇒↝ _ (cong ((_ ∈_) ∘ proj₂) eq) ⟩
         x ∈ t₂″  ↝⟨ inverse t₂′≈t₂″ ⟩□
         x ∈ t₂′  □)
