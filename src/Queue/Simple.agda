------------------------------------------------------------------------
-- Simple queues, implemented in the usual way using two lists
-- (following Hood and Melville)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Queue.Simple {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Bijection eq using (_↔_)
open import Equality.Decision-procedures eq
open import List eq as L hiding (map)
open import Surjection eq using (_↠_)

private
  variable
    a     : Level
    A B   : Type a
    x     : A
    f     : A → B
    xs ys : List A

------------------------------------------------------------------------
-- Invariant

-- The queue invariant: if the first list is empty, then the second
-- list is empty.

Invariant : {A : Type a} → List A → List A → Type a
Invariant (_ ∷ _) _       = ↑ _ ⊤
Invariant []      []      = ↑ _ ⊤
Invariant []      (_ ∷ _) = ⊥

-- The invariant is propositional.

Invariant-propositional : Is-proposition (Invariant xs ys)
Invariant-propositional {xs = []}    {ys = []} _ _ = refl _
Invariant-propositional {xs = _ ∷ _}           _ _ = refl _

-- Some lemmas related to the invariant.

-[] : Invariant xs []
-[] {xs = []}    = _
-[] {xs = _ ∷ _} = _

map-map : Invariant xs ys → Invariant (L.map f xs) (L.map f ys)
map-map {xs = _ ∷ _}           _ = _
map-map {xs = []}    {ys = []} _ = _

------------------------------------------------------------------------
-- Queues

-- Queues.
--
-- Note that the invariant is erased.

record Queue (A : Type a) : Type a where
  constructor ⟨_,_⟩
  field
    front rear     : List A
    @0 {invariant} : Invariant front rear

open Queue public

-- A variant of ⟨_,_⟩ with three explicit arguments.

pattern ⟨_,_⟩[_] f r i =
  record { front     = f
         ; rear      = r
         ; invariant = i
         }

------------------------------------------------------------------------
-- Conversion functions

-- Converts queues to lists.

to-List : Queue A → List A
to-List q = front q ++ reverse (rear q)

-- Converts lists to queues.

from-List : List A → Queue A
from-List xs = ⟨ xs , [] ⟩[ -[] ]

-- The function from-List is a right inverse of to-List.

to-List-from-List : to-List (from-List xs) ≡ xs
to-List-from-List {xs = xs} =
  xs ++ []  ≡⟨ ++-right-identity _ ⟩∎
  xs        ∎

-- If the carrier type is inhabited, then the function from-List is
-- not, in general, a left inverse of to-List.

¬-from-List-to-List :
  A → ¬ ((q : Queue A) → from-List (to-List q) ≡ q)
¬-from-List-to-List {A = A} x hyp = not-equal equal
  where
  counter-example : Queue A
  counter-example = ⟨ x ∷ [] , x ∷ [] ⟩

  not-equal : from-List (to-List counter-example) ≢ counter-example
  not-equal eq = List.[]≢∷ (cong rear eq)

  equal : from-List (to-List counter-example) ≡ counter-example
  equal = hyp counter-example

------------------------------------------------------------------------
-- The representation is not unique

-- If the carrier type is inhabited, then two queues representing the
-- same list are not necessarily equal.

representation-not-unique :
  A → ¬ ({q₁ q₂ : Queue A} → to-List q₁ ≡ to-List q₂ → q₁ ≡ q₂)
representation-not-unique x hyp =
  ¬-from-List-to-List x λ q → hyp (
    to-List (from-List (to-List q))  ≡⟨ to-List-from-List ⟩∎
    to-List q                        ∎)

-- If the carrier type is inhabited, then the type
-- ∃ λ (q : Queue A) → to-List q ≡ xs is not, in general, a
-- proposition.

¬-Σ-Queue-propositional :
  A →
  ¬ ({xs : List A} →
     Is-proposition (∃ λ (q : Queue A) → to-List q ≡ xs))
¬-Σ-Queue-propositional x hyp =
  representation-not-unique x λ {q₁ q₂} eq →
  cong proj₁ (
    q₁ , eq      ≡⟨ hyp _ _ ⟩∎
    q₂ , refl _  ∎)

------------------------------------------------------------------------
-- Queue operations

-- Enqueues an element.

enqueue : A → Queue A → Queue A
enqueue x ⟨ []            , rear ⟩ = ⟨ x ∷ [] , rear     ⟩
enqueue x ⟨ front@(_ ∷ _) , rear ⟩ = ⟨ front  , x ∷ rear ⟩

to-List-enqueue : ∀ q → to-List (enqueue x q) ≡ to-List q ++ x ∷ []
to-List-enqueue         ⟨ []            , []   ⟩ = refl _
to-List-enqueue {x = x} ⟨ front@(_ ∷ _) , rear ⟩ =
  front ++ reverse (x ∷ rear)        ≡⟨ cong (front ++_) $ reverse-∷ rear ⟩
  front ++ reverse rear ++ x ∷ []    ≡⟨ ++-associative front _ _ ⟩∎
  (front ++ reverse rear) ++ x ∷ []  ∎

-- Dequeues an element, if possible.

dequeue : Queue A → Maybe (A × Queue A)
dequeue ⟨ [] , [] ⟩ = nothing

dequeue ⟨ x ∷ [] , rear ⟩ =
  just (x , ⟨ reverse rear , [] ⟩[ -[] ])

dequeue ⟨ x ∷ front@(_ ∷ _) , rear ⟩ =
  just (x , ⟨ front , rear ⟩)

to-List-dequeue :
  {A : Type a} (q : Queue A) →
  ⊎-map id (Σ-map id to-List) (dequeue q) ≡
  _↔_.to List↔Maybe[×List] (to-List q)
to-List-dequeue ⟨ [] , [] ⟩ = refl _

to-List-dequeue ⟨ x ∷ [] , rear ⟩ = cong (just ∘ (x ,_)) (
  reverse rear ++ []  ≡⟨ ++-right-identity _ ⟩∎
  reverse rear        ∎)

to-List-dequeue ⟨ _ ∷ _ ∷ _ , _ ⟩ = refl _

-- The "inverse" of the dequeue operation.

dequeue⁻¹ : Maybe (A × Queue A) → Queue A
dequeue⁻¹ nothing                       = ⟨ [] , [] ⟩
dequeue⁻¹ (just (x , ⟨ front , rear ⟩)) = ⟨ x ∷ front , rear ⟩

to-List-dequeue⁻¹ :
  (x : Maybe (A × Queue A)) →
  to-List (dequeue⁻¹ x) ≡
  _↔_.from List↔Maybe[×List] (⊎-map id (Σ-map id to-List) x)
to-List-dequeue⁻¹ nothing  = refl _
to-List-dequeue⁻¹ (just _) = refl _

-- A map function.

map : (A → B) → Queue A → Queue B
map f ⟨ front , rear ⟩[ inv ] =
  ⟨ L.map f front , L.map f rear ⟩[ map-map inv ]

to-List-map : ∀ q → to-List (map f q) ≡ L.map f (to-List q)
to-List-map {f = f} ⟨ front , rear ⟩ =
  L.map f front ++ reverse (L.map f rear)  ≡⟨ cong (L.map f front ++_) $ sym $ map-reverse rear ⟩
  L.map f front ++ L.map f (reverse rear)  ≡⟨ sym $ map-++ _ front _ ⟩∎
  L.map f (front ++ reverse rear)          ∎
