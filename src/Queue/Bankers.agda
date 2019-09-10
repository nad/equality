------------------------------------------------------------------------
-- Banker's queues (following Okasaki)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Queue.Bankers {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Bijection eq using (_↔_)
open import Erased.Without-K eq
open import Function-universe eq hiding (id; _∘_)
open import List eq as L hiding (map)
open import Nat eq
open import Surjection eq using (_↠_)
open import Tactic.By.Parametrised eq

private
  variable
    a     : Level
    A B   : Set a
    p q x : A
    b     : Bool
    f     : A → B

------------------------------------------------------------------------
-- Queues

-- Queues.
--
-- Note that the invariant is erased.

record Queue (@0 A : Set a) : Set a where
  field
    front rear               : List A
    length-front length-rear : ℕ
    @0 length-invariant      : length-rear ≤ length-front
    @0 length-front≡         : length-front ≡ length front
    @0 length-rear≡          : length-rear  ≡ length rear

open Queue public

------------------------------------------------------------------------
-- Conversion functions

-- Converts queues to lists.

to-List : Queue A → List A
to-List q = q .front ++ reverse (q .rear)

-- Converts lists to queues.

from-List : List A → Queue A
from-List xs = record
  { front            = xs
  ; rear             = []
  ; length-front     = length xs
  ; length-rear      = 0
  ; length-invariant = zero≤ _
  ; length-front≡    = refl _
  ; length-rear≡     = refl _
  }

-- There is a split surjection from Queue A to List A.

Queue↠List : Queue A ↠ List A
Queue↠List = record
  { logical-equivalence = record
    { to   = to-List
    ; from = from-List
    }
  ; right-inverse-of = λ xs →
      xs ++ []  ≡⟨ ++-right-identity _ ⟩∎
      xs        ∎
  }

------------------------------------------------------------------------
-- Queues with broken invariants

private

  -- Queues where the invariant may have been broken (slightly).

  record Almost-queue (@0 A : Set a) : Set a where
    field
      front rear               : List A
      length-front length-rear : ℕ
      @0 length-invariant      : length-rear ≤ suc length-front
      @0 length-front≡         : length-front ≡ length front
      @0 length-rear≡          : length-rear  ≡ length rear

  open Almost-queue

  -- Some conversion functions.

  from-Almost-queue : Almost-queue A → List A
  from-Almost-queue q = q .front ++ reverse (q .rear)

  to-Almost-queue : Queue A → Almost-queue A
  to-Almost-queue q = record
    { front            = q .front
    ; rear             = q .rear
    ; length-front     = q .length-front
    ; length-rear      = q .length-rear
    ; length-front≡    = q .length-front≡
    ; length-rear≡     = q .length-rear≡
    ; length-invariant = ≤-step (q .length-invariant)
    }

  -- Restores the invariant by rotating the queue, if necessary.

  rotate′ :
    (q : Almost-queue A) (b : Bool) →
    @0 T b ↔ suc (q .length-front) ≡ q .length-rear →
    Queue A
  rotate′ q true _ = record
    { front            = q .front ++ reverse (q .rear)
    ; rear             = []
    ; length-front     = q .length-front + q .length-rear
    ; length-rear      = 0
    ; length-invariant = zero≤ _
    ; length-rear≡     = refl _
    ; length-front≡    =
        ⟨ q .length-front ⟩ + q .length-rear                ≡⟨ ⟨by⟩ 4 (q .length-front≡) ⟩
        length (q .front) + ⟨ q .length-rear ⟩              ≡⟨ ⟨by⟩ 4 (q .length-rear≡) ⟩
        length (q .front) + ⟨ length (q .rear) ⟩            ≡⟨ ⟨by⟩ 4 (length-reverse (q .rear)) ⟩
        ⟨ length (q .front) + length (reverse (q .rear)) ⟩  ≡⟨ ⟨by⟩ 4 (length-++ (q .front)) ⟩∎
        length (q .front ++ reverse (q .rear))              ∎
    }
  rotate′ q false 1+f≢r = record
    { front            = q .front
    ; rear             = q .rear
    ; length-front     = q .length-front
    ; length-rear      = q .length-rear
    ; length-front≡    = q .length-front≡
    ; length-rear≡     = q .length-rear≡
    ; length-invariant = case ≤→<⊎≡ (q .length-invariant) of λ where
        (inj₁ 1+r≤1+f) → suc≤suc⁻¹ 1+r≤1+f
        (inj₂ r≡1+f)   → ⊥-elim (_↔_.from 1+f≢r (sym r≡1+f))
    }

  rotate : Almost-queue A → Queue A
  rotate q =
    rotate′ q (suc (q .length-front) == q .length-rear) T[==]↔≡

  to-List-rotate′ :
    ∀ b {p} → to-List (rotate′ q b p) ≡ from-Almost-queue q
  to-List-rotate′         false = refl _
  to-List-rotate′ {q = q} true  =
    (q .front ++ reverse (q .rear)) ++ []  ≡⟨ ++-right-identity _ ⟩∎
    q .front ++ reverse (q .rear)          ∎

  to-List-rotate :
    (q : Almost-queue A) → to-List (rotate q) ≡ from-Almost-queue q
  to-List-rotate q =
    to-List-rotate′ (suc (q .length-front) == q .length-rear)

------------------------------------------------------------------------
-- Queue operations

-- An empty queue.

empty : Queue A
empty = from-List []

to-List-empty : to-List empty ≡ ([] ⦂ List A)
to-List-empty = refl _

-- Adds an element to the front of a queue.

cons : A → Queue A → Queue A
cons x q = record q
  { front            = x ∷ q .front
  ; length-front     = suc (q .length-front)
  ; length-invariant = ≤-step (q .length-invariant)
  ; length-front≡    = cong suc (q .length-front≡)
  }

to-List-cons : ∀ q → to-List (cons x q) ≡ x ∷ to-List q
to-List-cons _ = refl _

-- Enqueues an element.

enqueue : A → Queue A → Queue A
enqueue x q =
  rotate (record (to-Almost-queue q)
    { rear             = x ∷ q .rear
    ; length-rear      = 1 + q .length-rear
    ; length-rear≡     = cong suc (q .length-rear≡)
    ; length-invariant = suc≤suc (q .length-invariant)
    })

to-List-enqueue : ∀ q → to-List (enqueue x q) ≡ to-List q ++ x ∷ []
to-List-enqueue {x = x} q =
  to-List (enqueue x q)                      ≡⟨ to-List-rotate (record
                                                  { length-invariant = suc≤suc (q .length-invariant)
                                                  }) ⟩
  q .front ++ ⟨ reverse (x ∷ q .rear) ⟩      ≡⟨ ⟨by⟩ 4 (reverse-∷ (q .rear)) ⟩
  q .front ++ (reverse (q .rear) ++ x ∷ [])  ≡⟨ ++-associative (q .front) _ _ ⟩∎
  (q .front ++ reverse (q .rear)) ++ x ∷ []  ∎

-- Dequeues an element, if possible.

dequeue : Queue A → Maybe (A × Queue A)
dequeue (record { front = [] }) = nothing

dequeue q@(record { front        = x ∷ front
                  ; length-front = suc length-front
                  }) =
  just (x , rotate (record (to-Almost-queue q)
    { front            = front
    ; length-front     = length-front
    ; length-invariant = q .length-invariant
    ; length-front≡    = cancel-suc (q .length-front≡)
    }))

dequeue {A = A}
        q@(record { front        = x ∷ front
                  ; length-front = zero
                  }) =                $⟨ [ q .length-front≡ ] ⟩
  Erased (zero ≡ suc (length front))  ↝⟨ Erased-cong-→ 0≢+ ⟩
  Erased ⊥                            ↔⟨ Erased-⊥↔⊥ ⟩
  ⊥                                   ↝⟨ ⊥-elim ⟩□
  Maybe (A × Queue A)                 □

to-List-dequeue :
  (q : Queue A) →
  ⊎-map id (Σ-map id to-List) (dequeue q) ≡
  _↔_.to List↔Maybe[×List] (to-List q)
to-List-dequeue (record { front = []; rear = [] }) = refl _

to-List-dequeue q@(record { front = []; rear = _ ∷ _ }) =
                                             $⟨ [ q .length-invariant ] ⟩
  Erased (q .length-rear ≤ q .length-front)  ↝⟨ Erased-cong-→ (subst (_ ≤_) (q .length-front≡)) ⟩
  Erased (q .length-rear ≤ 0)                ↝⟨ Erased-cong-→ (subst (_≤ _) (q .length-rear≡)) ⟩
  Erased (suc _ ≤ 0)                         ↝⟨ Erased-cong-→ (≮0 _) ⟩
  Erased ⊥                                   ↔⟨ Erased-⊥↔⊥ ⟩
  ⊥                                          ↝⟨ ⊥-elim ⟩□
  _                                          □

to-List-dequeue q@(record { front        = x ∷ front
                          ; length-front = suc length-front
                          }) =
  cong (just ∘ (x ,_))
    (to-List-rotate (record { length-invariant = q .length-invariant }))

to-List-dequeue q@(record { front        = x ∷ front
                          ; length-front = zero
                  }) =                $⟨ [ q .length-front≡ ] ⟩
  Erased (zero ≡ suc (length front))  ↝⟨ Erased-cong-→ 0≢+ ⟩
  Erased ⊥                            ↔⟨ Erased-⊥↔⊥ ⟩
  ⊥                                   ↝⟨ ⊥-elim ⟩□
  _                                   □

-- A map function.

map : (A → B) → Queue A → Queue B
map f q = record
  { front            = L.map f (q .front)
  ; rear             = L.map f (q .rear)
  ; length-front     = q .length-front
  ; length-rear      = q .length-rear
  ; length-invariant = q .length-invariant
  ; length-front≡    =
      q .length-front              ≡⟨ q .length-front≡ ⟩
      ⟨ length (q .front) ⟩        ≡⟨ ⟨by⟩ 6 (length∘map _ (q .front)) ⟩∎
      length (L.map f (q .front))  ∎
  ; length-rear≡     =
      q .length-rear              ≡⟨ q .length-rear≡ ⟩
      ⟨ length (q .rear) ⟩        ≡⟨ ⟨by⟩ 6 (length∘map _ (q .rear)) ⟩∎
      length (L.map f (q .rear))  ∎
  }

to-List-map : ∀ q → to-List (map f q) ≡ L.map f (to-List q)
to-List-map {f = f} q =
  L.map f (q .front) ++ ⟨ reverse (L.map f (q .rear)) ⟩  ≡⟨ ⟨by⟩ 6 (map-reverse (q .rear)) ⟩
  L.map f (q .front) ++ L.map f (reverse (q .rear))      ≡⟨ sym $ map-++ _ (q .front) _ ⟩∎
  L.map f (q .front ++ reverse (q .rear))                ∎
