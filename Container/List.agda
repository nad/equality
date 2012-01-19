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
-- The type

-- Lists.

List : Container lzero
List = ℕ ▷ Fin

------------------------------------------------------------------------
-- Constructors

[] : {A : Set} → ⟦ List ⟧ A
[] = (zero , λ ())

infixr 5 _∷_

_∷_ : {A : Set} → A → ⟦ List ⟧ A → ⟦ List ⟧ A
x ∷ (n , lkup) = (suc n , [ (λ _ → x) , lkup ])

-- Even if we don't assume extensionality we can prove that
-- intensionally distinct implementations of the constructors are bag
-- equal.

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

-- Any lemmas for the constructors.

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

------------------------------------------------------------------------
-- More functions

-- A variant of the dependent eliminator for lists.
--
-- The "respect bag equality" argument could be omitted if equality of
-- functions were extensional.

fold : ∀ {A : Set} {p}
       (P : ⟦ List ⟧ A → Set p) →
       (∀ xs ys → xs ≈-bag ys → P xs → P ys) →
       P [] →
       (∀ x xs → P xs → P (x ∷ xs)) →
       ∀ xs → P xs
fold P resp nl cns (zero  , lkup) = resp _ _ []≈ nl
fold P resp nl cns (suc n , lkup) = resp _ _ ∷≈ $
  cns (lkup (inj₁ tt)) _ (fold P resp nl cns (n , lkup ∘ inj₂))

-- Append.

infixr 5 _++_ _++′_

abstract

  _++′_ : ∀ {A : Set} (xs ys : ⟦ List ⟧ A) →
          ∃ λ (zs : ⟦ List ⟧ A) →
              (P : A → Set) → Any P zs ↔ Any P xs ⊎ Any P ys
  xs ++′ ys = fold
    (λ xs → ∃ λ zs → ∀ P → Any P zs ↔ Any P xs ⊎ Any P ys)
    (λ us vs us≈vs → ∃-cong (λ zs hyp P →
       Any P zs             ↔⟨ hyp P ⟩
       Any P us ⊎ Any P ys  ↔⟨ Any-cong P P us vs (λ _ → id) us≈vs ⊎-cong id ⟩
       Any P vs ⊎ Any P ys  □))
    (ys , λ P → Any P ys             ↔⟨ inverse ⊎-left-identity ⟩
                ⊥ ⊎ Any P ys         ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩
                Any P [] ⊎ Any P ys  □)
    (λ { x xs (zs , ih) → (x ∷ zs , λ P →
         Any P (x ∷ zs)               ↔⟨ Any-∷ P ⟩
         P x ⊎ Any P zs               ↔⟨ id ⊎-cong ih P ⟩
         P x ⊎ Any P xs ⊎ Any P ys    ↔⟨ ⊎-assoc ⟩
         (P x ⊎ Any P xs) ⊎ Any P ys  ↔⟨ inverse (Any-∷ P) ⊎-cong id ⟩
         (Any P (x ∷ xs)) ⊎ Any P ys  □) })
    xs

_++_ : {A : Set} → ⟦ List ⟧ A → ⟦ List ⟧ A → ⟦ List ⟧ A
xs ++ ys = proj₁ (xs ++′ ys)

-- An Any lemma for append.

Any-++ : ∀ {A : Set} (P : A → Set) xs ys →
         Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P xs ys = proj₂ (xs ++′ ys) P
