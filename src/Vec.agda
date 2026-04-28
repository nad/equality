------------------------------------------------------------------------
-- Vectors, defined using a recursive function
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Function-universe eq hiding (id; _∘_)
open import List eq using (length)
open import Surjection eq using (_↠_; ↠-≡)
import Vec.Dependent.Basics eq as DVec

private

  variable
    a b c : Level
    A B   : Type a
    f g   : A → B
    n     : ℕ

------------------------------------------------------------------------
-- The type

-- Vectors.

Vec : Type a → ℕ → Type a
Vec A n = DVec.Vec n (const A)

------------------------------------------------------------------------
-- Some simple functions

-- Finds the element at the given position.

index : Vec A n → Fin n → A
index = DVec.index

-- Updates the element at the given position.

infix 3 _[_≔_]

_[_≔_] : Vec A n → Fin n → A → Vec A n
_[_≔_] = DVec._[_≔_]

-- Applies the function to every element in the vector.

map : (A → B) → Vec A n → Vec B n
map f = DVec.map f

-- Constructs a vector containing a certain number of copies of the
-- given element.

replicate : A → Vec A n
replicate x = DVec.tabulate (const x)

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
∃Vec↔List {A} = record
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
  {A : Type a} {xs : Vec A n} → map id xs ≡ xs
map-id = DVec.map-id

map-∘ :
  {A : Type a} {B : Type b} {C : Type c} {f : B → C} {g : A → B}
  {xs : Vec A n} →
  map (f ∘ g) xs ≡ map f (map g xs)
map-∘ = DVec.map-∘

-- If f and g are pointwise equal, then map f xs and map g xs are
-- equal.

map-cong :
  ∀ {n} {xs : Vec A n} →
  (∀ x → f x ≡ g x) → map f xs ≡ map g xs
map-cong f≡g = DVec.map-cong f≡g
