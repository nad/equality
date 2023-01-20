------------------------------------------------------------------------
-- Vectors, defined as functions from finite sets
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec.Function
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Extensionality eq
open import Function-universe eq hiding (id; _∘_)
open import List eq using (length)
open import Surjection eq using (_↠_; ↠-≡)

private
  variable
    a   : Level
    A B : Type a
    n   : ℕ
    k   : Kind

------------------------------------------------------------------------
-- The type

-- Vectors.

Vec : ∀ {a} → Type a → ℕ → Type a
Vec A n = Fin n → A

-- Nil.

nil : Vec A zero
nil = λ ()

-- Cons.

cons : A → Vec A n → Vec A (suc n)
cons x xs = [ const x , xs ]

------------------------------------------------------------------------
-- Some simple functions

-- Finds the element at the given position.

index : Vec A n → Fin n → A
index = id

-- Applies the function to every element in the vector.

map : (A → B) → Vec A n → Vec B n
map f xs = f ∘ xs

-- Constructs a vector containing a certain number of copies of the
-- given element.

replicate : A → Vec A n
replicate = const

-- The head of the vector.

head : Vec A (suc n) → A
head = _$ fzero

-- The tail of the vector.

tail : Vec A (suc n) → Vec A n
tail = _∘ fsuc

-- Updates the element at the given position.

infix 3 _[_≔_]

_[_≔_] : Vec A n → Fin n → A → Vec A n
_[_≔_] {n = zero}  _  ()       _
_[_≔_] {n = suc _} xs fzero    x = cons x (tail xs)
_[_≔_] {n = suc _} xs (fsuc i) x = cons (head xs) (tail xs [ i ≔ x ])

------------------------------------------------------------------------
-- Some properties

-- Empty lists are equal to nil (assuming extensionality).

empty≡nil :
  {A : Type a} →
  Extensionality lzero a →
  {xs : Vec A zero} →
  xs ≡ nil
empty≡nil ext = apply-ext ext λ ()

-- A non-empty list is equal to its head consed onto its tail
-- (assuming extensionality).

non-empty≡cons-head-tail :
  {A : Type a} →
  Extensionality lzero a →
  (xs : Vec A (suc n)) →
  xs ≡ cons (head xs) (tail xs)
non-empty≡cons-head-tail ext _ =
  apply-ext ext [ (λ _ → refl _) , (λ _ → refl _) ]

------------------------------------------------------------------------
-- Conversions to and from lists

-- Vectors can be converted to lists.

to-list : Vec A n → List A
to-list {n = zero}  _  = []
to-list {n = suc _} xs = head xs ∷ to-list (tail xs)

-- Lists can be converted to vectors.

from-list : (xs : List A) → Vec A (length xs)
from-list []       = nil
from-list (x ∷ xs) = cons x (from-list xs)

-- There is a split surjection from ∃ (Vec A) to List A.

∃Vec↠List : ∃ (Vec A) ↠ List A
∃Vec↠List {A} = record
  { logical-equivalence = record
    { to   = to-list ∘ proj₂
    ; from = λ xs → length xs , from-list xs
    }
  ; right-inverse-of = to∘from
  }
  where
  to∘from : (xs : List A) → to-list (from-list xs) ≡ xs
  to∘from []       = refl _
  to∘from (x ∷ xs) = cong (x ∷_) (to∘from xs)

-- ∃ (Vec A) is equivalent to List A (assuming extensionality).

∃Vec≃List :
  {A : Type a} →
  ∃ (Vec A) ↝[ lzero ∣ a ] List A
∃Vec≃List {a} {A} =
  generalise-ext?
    (_↠_.logical-equivalence ∃Vec↠List)
    (λ ext →
         _↠_.right-inverse-of ∃Vec↠List
       , uncurry (from∘to ext))
  where
  tail′ : A → ∃ (Vec A) ↠ ∃ (Vec A)
  tail′ y = record
    { logical-equivalence = record
      { to   = λ where
                 (suc n , xs)  → n , tail xs
                 xs@(zero , _) → xs
      ; from = Σ-map suc (cons y)
      }
    ; right-inverse-of = refl
    }

  from∘to :
    Extensionality lzero a →
    ∀ n (xs : Vec A n) →
    (length (to-list xs) , from-list (to-list xs)) ≡ (n , xs)
  from∘to ext zero xs =
    (length {A = A} [] , nil)  ≡⟨ cong (zero ,_) $ sym $ empty≡nil ext ⟩∎
    (zero , xs)                ∎

  from∘to ext (suc n) xs =                                        $⟨ from∘to ext n (tail xs) ⟩
    (length (to-list (tail xs)) , from-list (to-list (tail xs)))
      ≡
    (n , tail xs)                                                 ↝⟨ _↠_.from $ ↠-≡ (tail′ (head xs)) ⟩

    (length (to-list xs) , from-list (to-list xs))
      ≡
    (suc n , cons (head xs) (tail xs))                            ↝⟨ ≡⇒↝ _ $ cong (λ ys → (_ , from-list (to-list xs)) ≡ (_ , ys)) $ sym $
                                                                     non-empty≡cons-head-tail ext xs ⟩□
    (length (to-list xs) , from-list (to-list xs))
      ≡
    (suc n , xs)                                                  □
