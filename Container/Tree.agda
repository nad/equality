------------------------------------------------------------------------
-- A container for finite binary trees with information in internal
-- nodes
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container.Tree where

open import Container hiding (Shape; Position)
open import Container.List
open import Equality.Propositional
open import Prelude hiding (id; _∘_; List; []; _∷_; _++_; lookup)

import Bijection
open Bijection equality-with-J using (_↔_; module _↔_)
import Function-universe
open Function-universe equality-with-J

------------------------------------------------------------------------
-- The type and some functions

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

-- Constructors.

leaf : {A : Set} → ⟦ Tree ⟧ A
leaf = (lf , λ ())

node : {A : Set} → ⟦ Tree ⟧ A → A → ⟦ Tree ⟧ A → ⟦ Tree ⟧ A
node (l , lkup-l) x (r , lkup-r) =
  ( nd l r
  , λ { root      → x
      ; (left  p) → lkup-l p
      ; (right p) → lkup-r p
      }
  )

-- Singleton trees.

singleton : {A : Set} → A → ⟦ Tree ⟧ A
singleton x = node leaf x leaf

-- Inorder flattening of a tree.

flatten : {A : Set} → ⟦ Tree ⟧ A → ⟦ List ⟧ A
flatten (lf     , lkup) = []
flatten (nd l r , lkup) =
  flatten (l , lkup ∘ left) ++
  lkup root ∷
  flatten (r , lkup ∘ right)

------------------------------------------------------------------------
-- Even if we don't assume extensionality we can prove that
-- intensionally distinct implementations of the constructors are bag
-- equal

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

------------------------------------------------------------------------
-- Lemmas relating Any to some of the functions above

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

Any-singleton : ∀ {A : Set} (P : A → Set) {x} →
                Any P (singleton x) ↔ P x
Any-singleton P {x} =
  Any P (singleton x)            ↔⟨ id ⟩
  Any P (node leaf x leaf)       ↔⟨ Any-node P ⟩
  Any P leaf ⊎ P x ⊎ Any P leaf  ↔⟨ Any-leaf P ⊎-cong id ⊎-cong Any-leaf P ⟩
  ⊥ ⊎ P x ⊎ ⊥                    ↔⟨ ⊎-left-identity ⟩
  P x ⊎ ⊥                        ↔⟨ ⊎-right-identity ⟩
  P x                            □

------------------------------------------------------------------------
-- Flatten does not add or remove any elements

flatten≈ : ∀ {A : Set} (t : ⟦ Tree ⟧ A) →
           flatten t ≈-bag t
flatten≈ (lf , lkup) = λ z →
  z ∈ []                        ↔⟨ Any-[] (λ x → z ≡ x) ⟩
  ⊥                             ↔⟨ inverse $ Any-leaf (λ x → z ≡ x) ⟩
  z ∈ leaf                      ↔⟨ leaf≈ _ ⟩
  _∈_ {C = Tree} z (lf , lkup)  □
flatten≈ (nd l r , lkup) = λ z →
  z ∈ flatten l′ ++ lkup root ∷ flatten r′         ↔⟨ Any-++ (λ x → z ≡ x) _ _ ⟩
  z ∈ flatten l′ ⊎ z ∈ lkup root ∷ flatten r′      ↔⟨ id ⊎-cong Any-∷ (λ x → z ≡ x) ⟩
  z ∈ flatten l′ ⊎ z ≡ lkup root ⊎ z ∈ flatten r′  ↔⟨ flatten≈ (l , lkup ∘ left) z ⊎-cong id ⊎-cong flatten≈ (r , lkup ∘ right) z ⟩
  z ∈ l′ ⊎ z ≡ lkup root ⊎ z ∈ r′                  ↔⟨ inverse $ Any-node (λ x → z ≡ x) ⟩
  z ∈ node l′ (lkup root) r′                       ↔⟨ node≈ _ ⟩
  _∈_ {C = Tree} z (nd l r , lkup)                 □
  where
  l′ : ⟦ Tree ⟧ _
  l′ = (l , lkup ∘ left)

  r′ : ⟦ Tree ⟧ _
  r′ = (r , lkup ∘ right)
