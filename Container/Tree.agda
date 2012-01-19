------------------------------------------------------------------------
-- A container for finite binary trees with information in internal
-- nodes
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container.Tree where

open import Container hiding (Shape; Position)
open import Container.List hiding (fold)
open import Equality.Propositional
open import Prelude hiding (id; _∘_; List; []; _∷_; _++_; lookup)

import Bijection
open Bijection equality-with-J using (_↔_; module _↔_)
import Function-universe
open Function-universe equality-with-J

------------------------------------------------------------------------
-- The type

-- Shapes.

data Shape : Set where
  lf : Shape
  nd : Shape → Shape → Shape

-- Positions.

data Position : Shape → Set where
  root  : ∀ {l r} → Position (nd l r)
  left  : ∀ {l r} → Position l → Position (nd l r)
  right : ∀ {l r} → Position r → Position (nd l r)

-- Trees.

Tree : Container lzero
Tree = Shape ▷ Position

------------------------------------------------------------------------
-- Constructors

-- Leaves.

leaf : {A : Set} → ⟦ Tree ⟧ A
leaf = (lf , λ ())

-- Internal nodes.

node : {A : Set} → ⟦ Tree ⟧ A → A → ⟦ Tree ⟧ A → ⟦ Tree ⟧ A
node (l , lkup-l) x (r , lkup-r) =
  ( nd l r
  , λ { root      → x
      ; (left  p) → lkup-l p
      ; (right p) → lkup-r p
      }
  )

-- Even if we don't assume extensionality we can prove that
-- intensionally distinct implementations of the constructors are bag
-- equal.

leaf≈ : {A : Set} {lkup : _ → A} →
        _≈-bag_ {C₂ = Tree} leaf (lf , lkup)
leaf≈ _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (() , _) }
      ; from = λ { (() , _) }
      }
    ; right-inverse-of = λ { (() , _) }
    }
  ; left-inverse-of = λ { (() , _) }
  }

node≈ : ∀ {A : Set} {l r} {lkup : _ → A} →
        _≈-bag_ {C₂ = Tree}
                (node (l , lkup ∘ left) (lkup root) (r , lkup ∘ right))
                (nd l r , lkup)
node≈ _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (root    , eq) → (root    , eq)
                 ; (left p  , eq) → (left p  , eq)
                 ; (right p , eq) → (right p , eq)
                 }
      ; from = λ { (root    , eq) → (root    , eq)
                 ; (left p  , eq) → (left p  , eq)
                 ; (right p , eq) → (right p , eq)
                 }
      }
    ; right-inverse-of = λ { (root    , eq) → refl
                           ; (left p  , eq) → refl
                           ; (right p , eq) → refl
                           }
    }
  ; left-inverse-of = λ { (root    , eq) → refl
                        ; (left p  , eq) → refl
                        ; (right p , eq) → refl
                        }
  }

-- Any lemmas for the constructors.

Any-leaf : ∀ {A : Set} (P : A → Set) →
           Any P leaf ↔ ⊥ {ℓ = lzero}
Any-leaf _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (() , _) }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { (() , _) }
  }

Any-node : ∀ {A : Set} (P : A → Set) {l x r} →
           Any P (node l x r) ↔ Any P l ⊎ P x ⊎ Any P r
Any-node _ {l = _ , _} {r = _ , _} = record
  { surjection = record
    { equivalence = record
      { to   = λ { (root    , eq) → inj₂ (inj₁ eq)
                 ; (left p  , eq) → inj₁ (p , eq)
                 ; (right p , eq) → inj₂ (inj₂ (p , eq))
                 }
      ; from = λ { (inj₁ (p , eq))        → (left p  , eq)
                 ; (inj₂ (inj₁ eq))       → (root    , eq)
                 ; (inj₂ (inj₂ (p , eq))) → (right p , eq)
                 }
      }
    ; right-inverse-of = λ { (inj₁ (p , eq))        → refl
                           ; (inj₂ (inj₁ eq))       → refl
                           ; (inj₂ (inj₂ (p , eq))) → refl
                           }
    }
  ; left-inverse-of = λ { (root    , eq) → refl
                        ; (left p  , eq) → refl
                        ; (right p , eq) → refl
                        }
  }

------------------------------------------------------------------------
-- More functions

-- A variant of the dependent eliminator for trees.
--
-- The "respect bag equality" argument could be omitted if equality of
-- functions were extensional.

fold : ∀ {A : Set} {p}
       (P : ⟦ Tree ⟧ A → Set p) →
       (∀ t₁ t₂ → t₁ ≈-bag t₂ → P t₁ → P t₂) →
       P leaf →
       (∀ l x r → P l → P r → P (node l x r)) →
       ∀ t → P t
fold P resp le no (lf     , lkup) = resp _ _ leaf≈ le
fold P resp le no (nd l r , lkup) = resp _ _ node≈ $
  no _ _ _ (fold P resp le no (l , lkup ∘ left ))
           (fold P resp le no (r , lkup ∘ right))

-- Singleton trees.

singleton : {A : Set} → A → ⟦ Tree ⟧ A
singleton x = node leaf x leaf

-- Any lemma for singleton.

Any-singleton : ∀ {A : Set} (P : A → Set) {x} →
                Any P (singleton x) ↔ P x
Any-singleton P {x} =
  Any P (singleton x)            ↔⟨ id ⟩
  Any P (node leaf x leaf)       ↔⟨ Any-node P ⟩
  Any P leaf ⊎ P x ⊎ Any P leaf  ↔⟨ Any-leaf P ⊎-cong id ⊎-cong Any-leaf P ⟩
  ⊥ ⊎ P x ⊎ ⊥                    ↔⟨ ⊎-left-identity ⟩
  P x ⊎ ⊥                        ↔⟨ ⊎-right-identity ⟩
  P x                            □

-- Inorder flattening of a tree.

abstract

  flatten′ : {A : Set} (t : ⟦ Tree ⟧ A) →
             ∃ λ (xs : ⟦ List ⟧ A) → xs ≈-bag t
  flatten′ = fold
    (λ t → ∃ λ xs → xs ≈-bag t)
    (λ t₁ t₂ t₁≈t₂ → ∃-cong (λ xs xs≈t₁ z →
       z ∈ xs  ↔⟨ xs≈t₁ z ⟩
       z ∈ t₁  ↔⟨ t₁≈t₂ z ⟩
       z ∈ t₂  □))
    ([] , λ z →
     z ∈ []    ↔⟨ Any-[] (λ x → z ≡ x) ⟩
     ⊥         ↔⟨ inverse $ Any-leaf (λ x → z ≡ x) ⟩
     z ∈ leaf  □)
    (λ { l x r (xs , xs≈l) (ys , ys≈r) → (xs ++ x ∷ ys , λ z →
         z ∈ xs ++ x ∷ ys         ↔⟨ Any-++ (λ x → z ≡ x) _ _ ⟩
         z ∈ xs ⊎ z ∈ x ∷ ys      ↔⟨ id ⊎-cong Any-∷ (λ x → z ≡ x) ⟩
         z ∈ xs ⊎ z ≡ x ⊎ z ∈ ys  ↔⟨ xs≈l z ⊎-cong id ⊎-cong ys≈r z ⟩
         z ∈ l ⊎ z ≡ x ⊎ z ∈ r    ↔⟨ inverse $ Any-node (λ x → z ≡ x) ⟩
         z ∈ node l x r           □) })

flatten : {A : Set} → ⟦ Tree ⟧ A → ⟦ List ⟧ A
flatten t = proj₁ (flatten′ t)

-- Flatten does not add or remove any elements.

flatten≈ : ∀ {A : Set} (t : ⟦ Tree ⟧ A) →
           flatten t ≈-bag t
flatten≈ t = proj₂ (flatten′ t)
