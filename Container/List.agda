------------------------------------------------------------------------
-- The list container
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container.List where

open import Container
open import Equality.Propositional
open import Prelude hiding (List; []; _∷_; foldr; _++_; id; _∘_)

import Bijection
open Bijection equality-with-J using (_↔_; module _↔_)
import Function-universe
open Function-universe equality-with-J

------------------------------------------------------------------------
-- The type and some functions

-- Lists.

List : Container lzero
List = ℕ ▷ Fin

-- Constructors.

[] : {A : Set} → ⟦ List ⟧ A
[] = (zero , λ ())

infixr 5 _∷_

_∷_ : {A : Set} → A → ⟦ List ⟧ A → ⟦ List ⟧ A
x ∷ (n , lkup) = (suc n , [ (λ _ → x) , lkup ])

-- Fold.

foldr : {A B : Set} → (A → B → B) → B → ⟦ List ⟧ A → B
foldr f x (zero  , lkup) = x
foldr f x (suc n , lkup) =
  f (lkup (inj₁ _)) (foldr f x (n , lkup ∘ inj₂))

-- Append.

infixr 5 _++_

_++_ : {A : Set} → ⟦ List ⟧ A → ⟦ List ⟧ A → ⟦ List ⟧ A
xs ++ ys = foldr _∷_ ys xs

------------------------------------------------------------------------
-- Even if we don't assume extensionality we can prove that
-- intensionally distinct implementations of the constructors are bag
-- equal

[]≈ : {A : Set} {lkup : _ → A} →
      _≈-bag_ {C₂ = List} [] (zero , lkup)
[]≈ _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (() , _) }
      ; from = λ { (() , _) }
      }
    ; right-inverse-of = λ { (() , _) }
    }
  ; left-inverse-of = λ { (() , _) }
  }

∷≈ : ∀ {A : Set} {n} {lkup : _ → A} →
     _≈-bag_ {C₂ = List}
             (lkup (inj₁ tt) ∷ (n , lkup ∘ inj₂))
             (suc n , lkup)
∷≈ _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (inj₁ tt , eq) → (inj₁ tt , eq)
                 ; (inj₂ s  , eq) → (inj₂ s  , eq)
                 }
      ; from = λ { (inj₁ tt , eq) → (inj₁ tt , eq)
                 ; (inj₂ s  , eq) → (inj₂ s  , eq)
                 }
      }
    ; right-inverse-of = λ { (inj₁ tt , eq) → refl
                           ; (inj₂ s  , eq) → refl
                           }
    }
  ; left-inverse-of = λ { (inj₁ tt , eq) → refl
                        ; (inj₂ s  , eq) → refl
                        }
  }

------------------------------------------------------------------------
-- Lemmas relating Any to some of the functions above

Any-[] : {A : Set} (P : A → Set) →
         Any P [] ↔ ⊥ {ℓ = lzero}
Any-[] _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (() , _) }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { (() , _) }
  }

Any-∷ : ∀ {A : Set} (P : A → Set) {x xs} →
        Any P (x ∷ xs) ↔ P x ⊎ Any P xs
Any-∷ _ = record
  { surjection = record
    { equivalence = record
      { to   = λ { (inj₁ tt , eq) → inj₁ eq
                 ; (inj₂ s  , eq) → inj₂ (s , eq)
                 }
      ; from = λ { (inj₁ eq)       → (inj₁ tt , eq)
                 ; (inj₂ (s , eq)) → (inj₂ s  , eq)
                 }
      }
    ; right-inverse-of = λ { (inj₁ eq)       → refl
                           ; (inj₂ (s , eq)) → refl
                           }
    }
  ; left-inverse-of = λ { (inj₁ tt , eq) → refl
                        ; (inj₂ s  , eq) → refl
                        }
  }

Any-++ : ∀ {A : Set} (P : A → Set) xs ys →
         Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P (zero , lkup) ys =
  Any P ((zero , lkup) ++ ys)                ↔⟨ id ⟩
  Any P ys                                   ↔⟨ inverse ⊎-left-identity ⟩
  ⊥ ⊎ Any P ys                               ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩
  Any P [] ⊎ Any P ys                        ↔⟨ Any-cong {D = List} P P [] (zero , lkup) (λ _ → id) []≈ ⊎-cong id ⟩
  Any {C = List} P (zero , lkup) ⊎ Any P ys  □
Any-++ P (suc n , lkup) ys =
  Any P ((suc n , lkup) ++ ys)                ↔⟨ id ⟩
  Any P (x ∷ xs ++ ys)                        ↔⟨ Any-∷ P ⟩
  P (x) ⊎ Any P (xs ++ ys)                    ↔⟨ id ⊎-cong Any-++ P (n , lkup ∘ inj₂) ys ⟩
  P (x) ⊎ Any P xs ⊎ Any P ys                 ↔⟨ ⊎-assoc ⟩
  (P (x) ⊎ Any P xs) ⊎ Any P ys               ↔⟨ inverse (Any-∷ P) ⊎-cong id ⟩
  (Any P (x ∷ xs)) ⊎ Any P ys                 ↔⟨ Any-cong {D = List} P P (x ∷ xs) (suc n , lkup) (λ _ → id) ∷≈ ⊎-cong id ⟩
  Any {C = List} P (suc n , lkup) ⊎ Any P ys  □
  where
  x = lkup (inj₁ tt)

  xs : ⟦ List ⟧ _
  xs = (n , lkup ∘ inj₂)
