------------------------------------------------------------------------
-- Vectors, defined using a recursive function
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Vec
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Function-universe eq hiding (id; _∘_)
open import List eq using (length)
open import Surjection eq using (_↠_; ↠-≡)

private

  variable
    a b c : Level
    A B   : Set a
    n     : ℕ

------------------------------------------------------------------------
-- The type

-- Vectors.

Vec : Set a → ℕ → Set a
Vec A zero    = ↑ _ ⊤
Vec A (suc n) = A × Vec A n

------------------------------------------------------------------------
-- Some simple functions

-- Finds the element at the given position.

index : Vec A n → Fin n → A
index {n = suc _} (x , _)  fzero    = x
index {n = suc _} (_ , xs) (fsuc i) = index xs i

-- Updates the element at the given position.

infix 3 _[_≔_]

_[_≔_] : Vec A n → Fin n → A → Vec A n
_[_≔_] {n = zero}  _        ()       _
_[_≔_] {n = suc _} (x , xs) fzero    y = y , xs
_[_≔_] {n = suc _} (x , xs) (fsuc i) y = x , (xs [ i ≔ y ])

-- Applies the function to every element in the vector.

map : (A → B) → Vec A n → Vec B n
map {n = zero}  f _        = _
map {n = suc _} f (x , xs) = f x , map f xs

-- Constructs a vector containing a certain number of copies of the
-- given element.

replicate : A → Vec A n
replicate {n = zero}  _ = _
replicate {n = suc _} x = x , replicate x

-- The head of the vector.

head : Vec A (suc n) → A
head = proj₁

-- The tail of the vector.

tail : Vec A (suc n) → Vec A n
tail = proj₂

------------------------------------------------------------------------
-- Conversions to and from lists

-- Vectors can be converted to lists.

to-list : Vec A n → List A
to-list {n = zero}  _        = []
to-list {n = suc n} (x , xs) = x ∷ to-list xs

-- Lists can be converted to vectors.

from-list : (xs : List A) → Vec A (length xs)
from-list []       = _
from-list (x ∷ xs) = x , from-list xs

-- ∃ (Vec A) is isomorphic to List A.

∃Vec↔List : ∃ (Vec A) ↔ List A
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
                 (suc n , _ , xs) → n , xs
                 xs@(zero , _)    → xs
      ; from = Σ-map suc (y ,_)
      }
    ; right-inverse-of = refl
    }

  from∘to :
    ∀ n (xs : Vec A n) →
    (length (to-list xs) , from-list (to-list xs)) ≡ (n , xs)
  from∘to zero    _        = refl _
  from∘to (suc n) (x , xs) =                                    $⟨ from∘to n xs ⟩
    (length (to-list xs) , from-list (to-list xs)) ≡ (n , xs)   ↝⟨ _↠_.from $ ↠-≡ (tail′ x) ⟩□

    (length (to-list (x , xs)) , from-list (to-list (x , xs)))
      ≡
    (suc n , x , xs)                                            □

------------------------------------------------------------------------
-- Some properties

-- The map function satisfies the functor laws.

map-id :
  {A : Set a} {xs : Vec A n} → map id xs ≡ xs
map-id {n = zero}  = refl _
map-id {n = suc n} = cong (_ ,_) map-id

map-∘ :
  {A : Set a} {B : Set b} {C : Set c} {f : B → C} {g : A → B}
  {xs : Vec A n} →
  map (f ∘ g) xs ≡ map f (map g xs)
map-∘ {n = zero}  = refl _
map-∘ {n = suc n} = cong (_ ,_) map-∘
