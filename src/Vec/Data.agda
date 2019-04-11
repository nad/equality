------------------------------------------------------------------------
-- Vectors, defined using an inductive family
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Vec.Data
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Function-universe eq hiding (_∘_)
open import List eq using (length)
open import Surjection eq using (_↠_; ↠-≡)

------------------------------------------------------------------------
-- The type

-- Vectors.

infixr 5 _∷_

data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

------------------------------------------------------------------------
-- Some simple functions

-- Finds the element at the given position.

index : ∀ {n} {a} {A : Set a} → Vec A n → Fin n → A
index (x ∷ _)  fzero    = x
index (_ ∷ xs) (fsuc i) = index xs i

-- Updates the element at the given position.

infix 3 _[_≔_]

_[_≔_] : ∀ {n} {a} {A : Set a} → Vec A n → Fin n → A → Vec A n
_[_≔_] []       ()       _
_[_≔_] (x ∷ xs) fzero    y = y ∷ xs
_[_≔_] (x ∷ xs) (fsuc i) y = x ∷ (xs [ i ≔ y ])

-- Applies the function to every element in the vector.

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Constructs a vector containing a certain number of copies of the
-- given element.

replicate : ∀ {n a} {A : Set a} → A → Vec A n
replicate {zero}  _ = []
replicate {suc _} x = x ∷ replicate x

-- The head of the vector.

head : ∀ {n a} {A : Set a} → Vec A (suc n) → A
head (x ∷ _) = x

-- The tail of the vector.

tail : ∀ {n a} {A : Set a} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

------------------------------------------------------------------------
-- Conversions to and from lists

-- Vectors can be converted to lists.

to-list : ∀ {n} {a} {A : Set a} → Vec A n → List A
to-list  []        = []
to-list (x ∷ xs) = x ∷ to-list xs

-- Lists can be converted to vectors.

from-list : ∀ {a} {A : Set a} (xs : List A) → Vec A (length xs)
from-list []       = []
from-list (x ∷ xs) = x ∷ from-list xs

-- ∃ (Vec A) is isomorphic to List A.

∃Vec↔List : ∀ {a} {A : Set a} → ∃ (Vec A) ↔ List A
∃Vec↔List {A = A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = to-list ∘ proj₂
      ; from = λ xs → length xs , from-list xs
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = uncurry from∘to
  }
  where
  to∘from : (xs : List A) → to-list (from-list xs) ≡ xs
  to∘from []       = refl _
  to∘from (x ∷ xs) = cong (x ∷_) (to∘from xs)

  tail′ : A → ∃ (Vec A) ↠ ∃ (Vec A)
  tail′ y = record
    { logical-equivalence = record
      { to   = λ where
                 (suc n , _ ∷ xs) → n , xs
                 xs@(zero , _)    → xs
      ; from = Σ-map suc (y ∷_)
      }
    ; right-inverse-of = refl
    }

  from∘to :
    ∀ n (xs : Vec A n) →
    (length (to-list xs) , from-list (to-list xs)) ≡ (n , xs)
  from∘to zero    []       = refl _
  from∘to (suc n) (x ∷ xs) =                                    $⟨ from∘to n xs ⟩
    (length (to-list xs) , from-list (to-list xs)) ≡ (n , xs)   ↝⟨ _↠_.from $ ↠-≡ (tail′ x) ⟩□

    (length (to-list (x ∷ xs)) , from-list (to-list (x ∷ xs)))
      ≡
    (suc n , x ∷ xs)                                            □
