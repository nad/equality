------------------------------------------------------------------------
-- Vectors, defined using an inductive family
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec.Data
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (Fin)

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq using (_≃_)
open import Erased.Level-1 eq as Erased hiding (map)
open import Fin.Data eq
open import Function-universe eq as F hiding (_∘_)
open import H-level.Closure eq
open import List eq using (length)
open import Surjection eq using (_↠_; ↠-≡)

private variable
  a    : Level
  A B  : Type _
  @0 n : ℕ

------------------------------------------------------------------------
-- The type

-- Vectors.

infixr 5 _∷_

data Vec (A : Type a) : @0 ℕ → Type a where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

------------------------------------------------------------------------
-- Some simple functions

-- Finds the element at the given position.

index : Vec A n → Fin n → A
index (x ∷ _)  zero    = x
index (_ ∷ xs) (suc i) = index xs i

-- Updates the element at the given position.

infix 3 _[_≔_]

_[_≔_] : Vec A n → Fin n → A → Vec A n
_[_≔_] []       ()      _
_[_≔_] (x ∷ xs) zero    y = y ∷ xs
_[_≔_] (x ∷ xs) (suc i) y = x ∷ (xs [ i ≔ y ])

-- Applies the function to every element in the vector.

map : (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Constructs a vector containing a certain number of copies of the
-- given element.

replicate : ∀ {n} → A → Vec A n
replicate {n = zero}  _ = []
replicate {n = suc _} x = x ∷ replicate x

-- The head of the vector.

head : Vec A (suc n) → A
head (x ∷ _) = x

-- The tail of the vector.

tail : Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

------------------------------------------------------------------------
-- Conversions to and from lists

-- Vectors can be converted to lists.

to-list : Vec A n → List A
to-list  []        = []
to-list (x ∷ xs) = x ∷ to-list xs

-- Lists can be converted to vectors.

from-list : (xs : List A) → Vec A (length xs)
from-list []       = []
from-list (x ∷ xs) = x ∷ from-list xs

-- ∃ (Vec A) is isomorphic to List A.

∃Vec↔List : ∃ (λ n → Vec A n) ↔ List A
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

  tail′ : A → ∃ (λ n → Vec A n) ↠ ∃ (λ n → Vec A n)
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

opaque

  -- The function to-list preserves the length.

  length-to-list : ∀ {n} (xs : Vec A n) → length (to-list xs) ≡ n
  length-to-list xs =
    cong proj₁ (_↔_.left-inverse-of ∃Vec↔List (_ , xs))

-- ∃ (λ (([ n ]) : Erased ℕ) → Vec A n) is equivalent to List A.

∃Erased-Vec≃List : ∃ (λ (([ n ]) : Erased ℕ) → Vec A n) ≃ List A
∃Erased-Vec≃List {A} =
  Eq.↔→≃ (to-list ∘ proj₂) (λ xs → [ _ ] , from-list xs)
    (_↔_.right-inverse-of ∃Vec↔List) from-to
  where
  opaque
    from-to :
      ((n , xs) : ∃ (λ (([ n ]) : Erased ℕ) → Vec A n)) →
      _≡_ {A = ∃ (λ (([ n ]) : Erased ℕ) → Vec A n)}
        ([ length (to-list xs) ] , from-list (to-list xs)) (n , xs)
    from-to ([ _ ] , [])     = refl _
    from-to ([ _ ] , x ∷ xs) =
      cong (Σ-map (Erased.map suc) (x ∷_)) (from-to ([ _ ] , xs))

-- Vec A n is equivalent to ∃ λ (xs : List A) → Erased (length xs ≡ n)
-- (in the presence of []-cong).

Vec≃∃List-Erased :
  {A : Type a} →
  []-cong-axiomatisation lzero →
  Vec A n ≃ ∃ λ (xs : List A) → Erased (length xs ≡ n)
Vec≃∃List-Erased {n} {A} ax =
  Vec A n                                                           ↔⟨ inverse $ drop-⊤-left-Σ $
                                                                       Erased-⊤↔⊤ F.∘
                                                                       Erased-cong.Erased-cong-↔ ax ax
                                                                         (_⇔_.to contractible⇔↔⊤ (singleton-contractible _)) ⟩

  (∃ λ (([ m , _ ]) : Erased (∃ λ (m : ℕ) → m ≡ n)) → Vec A m)      ↝⟨ (Σ-cong Erased-Σ↔Σ λ { [ _ ] → F.id }) ⟩

  (∃ λ (([ m ] , _) : ∃ λ (([ m ]) : Erased ℕ) → Erased (m ≡ n)) →
   Vec A m)                                                         ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (([ m ]) : Erased ℕ) → Erased (m ≡ n) × Vec A m)             ↔⟨ (∃-cong λ _ → ×-comm) ⟩

  (∃ λ (([ m ]) : Erased ℕ) → Vec A m × Erased (m ≡ n))             ↔⟨ Σ-assoc ⟩

  (∃ λ (([ m ] , _) : ∃ (λ (([ m ]) : Erased ℕ) → Vec A m)) →
   Erased (m ≡ n))                                                  ↝⟨ (Σ-cong-contra (inverse ∃Erased-Vec≃List) λ _ → F.id) ⟩

  (∃ λ (xs : List A) → Erased (length xs ≡ n))                      □
