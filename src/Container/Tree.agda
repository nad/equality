------------------------------------------------------------------------
-- A container for finite binary trees with information in internal
-- nodes
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Container.Tree
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude hiding (id; _∘_; List; []; _∷_)

open import Bijection eq using (_↔_; module _↔_)
open import Container eq hiding (Shape; Position)
open import Container.List eq hiding (fold; fold-lemma)
import Equivalence eq as Eq
open import Function-universe eq
import Tree eq as Tree

------------------------------------------------------------------------
-- The type

-- Shapes.

data Shape : Type where
  lf : Shape
  nd : Shape → Shape → Shape

-- Positions.

data Position : Shape → Type where
  root  : ∀ {l r} → Position (nd l r)
  left  : ∀ {l r} → Position l → Position (nd l r)
  right : ∀ {l r} → Position r → Position (nd l r)

-- Trees.

Tree : Container lzero
Tree = Shape ▷ Position

------------------------------------------------------------------------
-- An isomorphism

-- The type of shapes is isomorphic to Tree.Tree ⊤.
--
-- This lemma is included because it was mentioned in the paper "Bag
-- Equivalence via a Proof-Relevant Membership Relation".

Shape↔Tree-⊤ : Shape ↔ Tree.Tree ⊤
Shape↔Tree-⊤ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : Shape → Tree.Tree ⊤
  to lf       = Tree.leaf
  to (nd l r) = Tree.node (to l) tt (to r)

  from : Tree.Tree ⊤ → Shape
  from Tree.leaf          = lf
  from (Tree.node l tt r) = nd (from l) (from r)

  to∘from : ∀ t → to (from t) ≡ t
  to∘from Tree.leaf          = refl _
  to∘from (Tree.node l tt r) =
    cong₂ (λ l r → Tree.node l tt r) (to∘from l) (to∘from r)

  from∘to : ∀ s → from (to s) ≡ s
  from∘to lf       = refl _
  from∘to (nd l r) = cong₂ nd (from∘to l) (from∘to r)

------------------------------------------------------------------------
-- Constructors

-- Leaves.

leaf : {A : Type} → ⟦ Tree ⟧ A
leaf = (lf , λ ())

-- Internal nodes.

node : {A : Type} → ⟦ Tree ⟧ A → A → ⟦ Tree ⟧ A → ⟦ Tree ⟧ A
node (l , lkup-l) x (r , lkup-r) =
  ( nd l r
  , λ { root      → x
      ; (left  p) → lkup-l p
      ; (right p) → lkup-r p
      }
  )

-- Even if we don't assume extensionality we can prove that
-- intensionally distinct implementations of the constructors are bag
-- equivalent.

leaf≈ : {A : Type} {lkup : _ → A} →
        _≈-bag_ {C₂ = Tree} leaf (lf , lkup)
leaf≈ _ = Eq.↔→≃
  (λ { (() , _) })
  (λ { (() , _) })
  (λ { (() , _) })
  (λ { (() , _) })

node≈ : ∀ {A : Type} {l r} {lkup : _ → A} →
        _≈-bag_ {C₂ = Tree}
                (node (l , lkup ∘ left) (lkup root) (r , lkup ∘ right))
                (nd l r , lkup)
node≈ _ = Eq.↔→≃
  (λ { (root    , eq) → (root    , eq)
     ; (left p  , eq) → (left p  , eq)
     ; (right p , eq) → (right p , eq)
     })
  (λ { (root    , eq) → (root    , eq)
     ; (left p  , eq) → (left p  , eq)
     ; (right p , eq) → (right p , eq)
     })
  (λ { (root    , eq) → refl _
     ; (left p  , eq) → refl _
     ; (right p , eq) → refl _
     })
  (λ { (root    , eq) → refl _
     ; (left p  , eq) → refl _
     ; (right p , eq) → refl _
     })

-- Any lemmas for the constructors.

Any-leaf : ∀ {A : Type} (P : A → Type) →
           Any P leaf ↔ ⊥₀
Any-leaf _ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (() , _) }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { (() , _) }
  }

Any-node : ∀ {A : Type} (P : A → Type) {l x r} →
           Any P (node l x r) ↔ Any P l ⊎ P x ⊎ Any P r
Any-node _ {l = _ , _} {r = _ , _} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (root    , eq) → inj₂ (inj₁ eq)
                 ; (left p  , eq) → inj₁ (p , eq)
                 ; (right p , eq) → inj₂ (inj₂ (p , eq))
                 }
      ; from = λ { (inj₁ (p , eq))        → (left p  , eq)
                 ; (inj₂ (inj₁ eq))       → (root    , eq)
                 ; (inj₂ (inj₂ (p , eq))) → (right p , eq)
                 }
      }
    ; right-inverse-of = λ { (inj₁ (p , eq))        → refl _
                           ; (inj₂ (inj₁ eq))       → refl _
                           ; (inj₂ (inj₂ (p , eq))) → refl _
                           }
    }
  ; left-inverse-of = λ { (root    , eq) → refl _
                        ; (left p  , eq) → refl _
                        ; (right p , eq) → refl _
                        }
  }

------------------------------------------------------------------------
-- More functions

-- Singleton trees.

singleton : {A : Type} → A → ⟦ Tree ⟧ A
singleton x = node leaf x leaf

-- Any lemma for singleton.

Any-singleton : ∀ {A : Type} (P : A → Type) {x} →
                Any P (singleton x) ↔ P x
Any-singleton P {x} =
  Any P (singleton x)            ↔⟨⟩
  Any P (node leaf x leaf)       ↔⟨ Any-node P ⟩
  Any P leaf ⊎ P x ⊎ Any P leaf  ↔⟨ Any-leaf P ⊎-cong id ⊎-cong Any-leaf P ⟩
  ⊥ ⊎ P x ⊎ ⊥                    ↔⟨ ⊎-left-identity ⟩
  P x ⊎ ⊥                        ↔⟨ ⊎-right-identity ⟩
  P x                            □

-- For the design considerations underlying the inclusion of fold and
-- fold-lemma, see Container.List.fold/fold-lemma.

-- A fold for trees. (Well, this is not a catamorphism, it is a
-- paramorphism.)

fold : {A B : Type} →
       B → (⟦ Tree ⟧ A → A → ⟦ Tree ⟧ A → B → B → B) → ⟦ Tree ⟧ A → B
fold {A} {B} fl fn = uncurry fold′
  where
  fold′ : (s : Shape) → (Position s → A) → B
  fold′ lf       lkup = fl
  fold′ (nd l r) lkup =
    fn (l , lkup ∘ left )
       (lkup root)
       (r , lkup ∘ right)
       (fold′ l (lkup ∘ left ))
       (fold′ r (lkup ∘ right))

-- A lemma which can be used to prove properties about fold.
--
-- The "respects bag equivalence" argument could be omitted if
-- equality of functions were extensional.

fold-lemma : ∀ {A B : Type}
               {fl : B} {fn : ⟦ Tree ⟧ A → A → ⟦ Tree ⟧ A → B → B → B}
             (P : ⟦ Tree ⟧ A → B → Type) →
             (∀ t₁ t₂ → t₁ ≈-bag t₂ → ∀ b → P t₁ b → P t₂ b) →
             P leaf fl →
             (∀ l x r b₁ b₂ →
                P l b₁ → P r b₂ → P (node l x r) (fn l x r b₁ b₂)) →
             ∀ t → P t (fold fl fn t)
fold-lemma {A} {fl = fl} {fn} P resp P-le P-no = uncurry fold-lemma′
  where
  fold-lemma′ : (s : Shape) (lkup : Position s → A) →
                P (s , lkup) (fold fl fn (s , lkup))
  fold-lemma′ lf       lkup = resp _ _ leaf≈ _ P-le
  fold-lemma′ (nd l r) lkup = resp _ _ node≈ _ $
    P-no _ _ _ _ _
       (fold-lemma′ l (lkup ∘ left ))
       (fold-lemma′ r (lkup ∘ right))

-- Inorder flattening of a tree.

flatten : {A : Type} → ⟦ Tree ⟧ A → ⟦ List ⟧ A
flatten = fold [] (λ _ x _ xs ys → xs ++ x ∷ ys)

-- Flatten does not add or remove any elements.

flatten≈ : {A : Type} (t : ⟦ Tree ⟧ A) → flatten t ≈-bag t
flatten≈ = fold-lemma
  (λ t xs → xs ≈-bag t)

  (λ t₁ t₂ t₁≈t₂ xs xs≈t₁ z →
     z ∈ xs  ↔⟨ xs≈t₁ z ⟩
     z ∈ t₁  ↔⟨ t₁≈t₂ z ⟩
     z ∈ t₂  □)

  (λ z →
   z ∈ []    ↔⟨ Any-[] (λ x → z ≡ x) ⟩
   ⊥         ↔⟨ inverse $ Any-leaf (λ x → z ≡ x) ⟩
   z ∈ leaf  □)

  (λ l x r xs ys xs≈l ys≈r z →
     z ∈ xs ++ x ∷ ys         ↔⟨ Any-++ (λ x → z ≡ x) _ _ ⟩
     z ∈ xs ⊎ z ∈ x ∷ ys      ↔⟨ id ⊎-cong Any-∷ (λ x → z ≡ x) ⟩
     z ∈ xs ⊎ z ≡ x ⊎ z ∈ ys  ↔⟨ xs≈l z ⊎-cong id ⊎-cong ys≈r z ⟩
     z ∈ l ⊎ z ≡ x ⊎ z ∈ r    ↔⟨ inverse $ Any-node (λ x → z ≡ x) ⟩
     z ∈ node l x r           □)
