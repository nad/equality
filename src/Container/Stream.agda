------------------------------------------------------------------------
-- The stream container
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Container.Stream
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (id; List; []; _∷_)

open import Bijection eq using (_↔_; module _↔_)
open import Container eq
open import Container.List eq as L hiding (_∷_; _++_; Any-∷; Any-++)
open import Function-universe eq hiding (_∘_)

------------------------------------------------------------------------
-- Streams

Stream : Container lzero
Stream = ⊤ ▷ const ℕ

------------------------------------------------------------------------
-- Operations

-- Cons.

infixr 5 _∷_

_∷_ : {A : Type} → A → ⟦ Stream ⟧ A → ⟦ Stream ⟧ A
x ∷ (tt , lkup) = tt , λ { zero → x; (suc n) → lkup n }

-- The head of a stream.

head : {A : Type} → ⟦ Stream ⟧ A → A
head (tt , lkup) = lkup 0

-- The tail of a stream.

tail : {A : Type} → ⟦ Stream ⟧ A → ⟦ Stream ⟧ A
tail (tt , lkup) = (tt , lkup ∘ suc)

-- Appending a stream to a list.

infixr 5 _++_

_++_ : {A : Type} → ⟦ List ⟧ A → ⟦ Stream ⟧ A → ⟦ Stream ⟧ A
xs ++ ys = fold ys (λ z _ zs → z ∷ zs) xs

-- Taking the first n elements from a stream.

take : {A : Type} → ℕ → ⟦ Stream ⟧ A → ⟦ List ⟧ A
take zero    xs = []
take (suc n) xs = L._∷_ (head xs) (take n (tail xs))

-- Dropping the first n elements from a stream.

drop : {A : Type} → ℕ → ⟦ Stream ⟧ A → ⟦ Stream ⟧ A
drop zero    xs = xs
drop (suc n) xs = drop n (tail xs)

------------------------------------------------------------------------
-- Any lemmas

-- Any lemma for head/tail.

Any-head-tail : ∀ {A : Type} (P : A → Type) {xs} →
                Any P xs ↔ P (head xs) ⊎ Any P (tail xs)
Any-head-tail P = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (zero  , p) → inj₁ p
                 ; (suc n , p) → inj₂ (n , p)
                 }
      ; from = λ { (inj₁ p)       → (zero , p)
                 ; (inj₂ (n , p)) → (suc n , p)
                 }
      }
    ; right-inverse-of = λ { (inj₁ p)       → refl _
                           ; (inj₂ (n , p)) → refl _
                           }
    }
  ; left-inverse-of = λ { (zero  , p) → refl _
                        ; (suc n , p) → refl _
                        }
  }

-- Any lemma for cons.

Any-∷ : ∀ {A : Type} (P : A → Type) {x xs} →
        Any P (x ∷ xs) ↔ P x ⊎ Any P xs
Any-∷ P = Any-head-tail P

-- Any lemma for append.
--
-- (TODO: Generalise. The definitions of _++_ and Any-++ in this
-- module are almost identical to those in Container.List.)

Any-++ : ∀ {A : Type} (P : A → Type) (xs : ⟦ List ⟧ A) ys →
         Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P xs ys = fold-lemma
  (λ xs xs++ys → Any P xs++ys ↔ Any P xs ⊎ Any P ys)

  (λ us vs us≈vs us++ys hyp →
    Any P us++ys         ↔⟨ hyp ⟩
    Any P us ⊎ Any P ys  ↔⟨ _⇔_.to (∼⇔∼″ lzero us vs) us≈vs P ⊎-cong id ⟩
    Any P vs ⊎ Any P ys  □)

  (Any P ys             ↔⟨ inverse ⊎-left-identity ⟩
   ⊥ ⊎ Any P ys         ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩
   Any P [] ⊎ Any P ys  □)

  (λ x xs xs++ys ih →
     Any P (x ∷ xs++ys)             ↔⟨ Any-∷ P ⟩
     P x ⊎ Any P xs++ys             ↔⟨ id ⊎-cong ih ⟩
     P x ⊎ Any P xs ⊎ Any P ys      ↔⟨ ⊎-assoc ⟩
     (P x ⊎ Any P xs) ⊎ Any P ys    ↔⟨ inverse $ L.Any-∷ P ⊎-cong id ⟩
     Any P (L._∷_ x xs) ⊎ Any P ys  □)

  xs

-- Any lemma for take/drop.

Any-take-drop : ∀ {A : Type} (P : A → Type) n {xs} →
                Any P xs ↔ Any P (take n xs) ⊎ Any P (drop n xs)
Any-take-drop P zero {xs} =
  Any P xs             ↔⟨ inverse ⊎-left-identity ⟩
  ⊥        ⊎ Any P xs  ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩
  Any P [] ⊎ Any P xs  □
Any-take-drop P (suc n) {xs} =
  Any P xs                                                 ↔⟨ Any-head-tail P ⟩
  P (head xs) ⊎ Any P (tail xs)                            ↔⟨ id ⊎-cong Any-take-drop P n ⟩
  P (head xs) ⊎
    (Any P (take n (tail xs)) ⊎ Any P (drop n (tail xs)))  ↔⟨ ⊎-assoc ⟩
  (P (head xs) ⊎ Any P (take n (tail xs))) ⊎
    Any P (drop n (tail xs))                               ↔⟨ inverse $ L.Any-∷ P ⊎-cong id ⟩
  Any P (L._∷_ (head xs) (take n (tail xs))) ⊎
    Any P (drop n (tail xs))                               □
