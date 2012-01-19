------------------------------------------------------------------------
-- The list container
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container.List where

open import Container
open import Equality.Propositional
open import Equivalence using (module _⇔_)
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

-- A fold for lists. (Well, this is not a catamorphism, it is a
-- paramorphism.)

fold : {A B : Set} → B → (A → ⟦ List ⟧ A → B → B) → ⟦ List ⟧ A → B
fold nl cns (zero  , lkup) = nl
fold nl cns (suc n , lkup) =
  cns (lkup (inj₁ tt)) (n , lkup ∘ inj₂)
      (fold nl cns (n , lkup ∘ inj₂))

-- A lemma which can be used to prove properties about fold.
--
-- The "respect bag equality" argument could be omitted if equality of
-- functions were extensional.

fold-lemma : ∀ {A B : Set} {nl : B} {cns : A → ⟦ List ⟧ A → B → B}
             (P : ⟦ List ⟧ A → B → Set) →
             (∀ xs ys → xs ≈-bag ys → ∀ b → P xs b → P ys b) →
             P [] nl →
             (∀ x xs b → P xs b → P (x ∷ xs) (cns x xs b)) →
             ∀ xs → P xs (fold nl cns xs)
fold-lemma Q resp nl cns (zero  , lkup) = resp _ _ []≈ _ nl
fold-lemma Q resp nl cns (suc n , lkup) = resp _ _ ∷≈ _ $
  cns _ _ _ $ fold-lemma Q resp nl cns (n , lkup ∘ inj₂)

-- Why have I included both fold and fold-lemma rather than simply a
-- dependent eliminator? I tried this, and could easily define the
-- functions I wanted to define. However, the functions were defined
-- together with (partial) correctness proofs, and were unnecessarily
-- hard to read. I wanted to be able to define functions which were
-- easy to read, like the _++_ function below, and then have the
-- option to prove properties about them, like Any-++.
--
-- Unfortunately this turned out to be harder than expected. When
-- proving the Any-++ lemma it seemed as if I had to prove that _++_
-- preserves bag equality in its first argument in order to
-- instantiate the "respect bag equality" argument. However, my
-- preferred proof of this property uses Any-++…
--
-- An alternative could be to assume that equality of functions is
-- extensional, in which case the "respect bag equality" argument
-- could be removed. Another option would be to listen to Conor
-- McBride and avoid higher-order representations of first-order data.

-- Append.

infixr 5 _++_

_++_ : {A : Set} → ⟦ List ⟧ A → ⟦ List ⟧ A → ⟦ List ⟧ A
xs ++ ys = fold ys (λ z _ zs → z ∷ zs) xs

-- An Any lemma for append.

Any-++ : ∀ {A : Set} (P : A → Set) xs ys →
         Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P xs ys = fold-lemma
  (λ xs xs++ys → Any P xs++ys ↔ Any P xs ⊎ Any P ys)

  (λ us vs us≈vs us++ys hyp →
    Any P us++ys         ↔⟨ hyp ⟩
    Any P us ⊎ Any P ys  ↔⟨ _⇔_.to (∼⇔∼″ us vs) us≈vs P ⊎-cong id ⟩
    Any P vs ⊎ Any P ys  □)

  (Any P ys             ↔⟨ inverse ⊎-left-identity ⟩
   ⊥ ⊎ Any P ys         ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩
   Any P [] ⊎ Any P ys  □)

  (λ x xs xs++ys ih →
     Any P (x ∷ xs++ys)           ↔⟨ Any-∷ P ⟩
     P x ⊎ Any P xs++ys           ↔⟨ id ⊎-cong ih ⟩
     P x ⊎ Any P xs ⊎ Any P ys    ↔⟨ ⊎-assoc ⟩
     (P x ⊎ Any P xs) ⊎ Any P ys  ↔⟨ inverse (Any-∷ P) ⊎-cong id ⟩
     Any P (x ∷ xs) ⊎ Any P ys    □)

  xs
