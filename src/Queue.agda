------------------------------------------------------------------------
-- Specifications of output-restricted deques (single-ended queues
-- with cons)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Queue {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Bijection eq as Bijection using (_↔_)
import Equivalence eq as Eq
open import Function-universe eq as F hiding (id; _∘_)
open import List eq as L hiding (map)
open import Maybe eq
open import Surjection eq using (_↠_)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B       : Type a
    P Q       : ∀ {ℓ} → Type ℓ → Type ℓ
    p q x     : A
    f         : A → B
    xs        : List A

-- A specification of when (and how) a type constructor implements
-- output-restricted deques.

record Is-queue
         -- A family of queue types.
         (Q : ∀ {ℓ} → Type ℓ → Type ℓ)
         -- Some operations are only available for carrier types
         -- satisfying this predicate.
         (P : ∀ {ℓ} → Type ℓ → Type ℓ)
         ℓ :
         Type (lsuc ℓ) where
  field

    -- Conversion functions.

    to-List           : {A : Type ℓ} → P A → Q A → List A
    from-List         : {A : Type ℓ} → List A → Q A
    to-List-from-List : to-List p (from-List xs) ≡ xs

    -- Enqueues an element.

    enqueue         : {A : Type ℓ} → A → Q A → Q A
    to-List-enqueue : to-List p (enqueue x q) ≡ to-List p q ++ x ∷ []

    -- Dequeues an element, if possible.

    dequeue         : {A : Type ℓ} → P A → Q A → Maybe (A × Q A)
    to-List-dequeue : ⊎-map id (Σ-map id (to-List p)) (dequeue p q) ≡
                      _↔_.to List↔Maybe[×List] (to-List p q)

    -- The "inverse" of the dequeue operation.

    dequeue⁻¹         : {A : Type ℓ} → Maybe (A × Q A) → Q A
    to-List-dequeue⁻¹ :
      to-List p (dequeue⁻¹ x) ≡
      _↔_.from List↔Maybe[×List] (⊎-map id (Σ-map id (to-List p)) x)

-- This module exports universe-polymorphic queue
-- operations/properties.

module Is-queue⁺ ⦃ is-queue : ∀ {ℓ} → Is-queue Q P ℓ ⦄ where

  private
    module Q {ℓ} = Is-queue (is-queue {ℓ = ℓ})
  open Q public

  -- A split surjection from queues to lists.

  Queue↠List : P A → Q A ↠ List A
  Queue↠List p = record
    { logical-equivalence = record
      { to   = to-List p
      ; from = from-List
      }
    ; right-inverse-of = λ _ → to-List-from-List
    }

  -- An empty queue.

  empty : Q A
  empty = dequeue⁻¹ nothing

  to-List-empty : to-List p empty ≡ ([] ⦂ List A)
  to-List-empty {p = p} =
    to-List p empty                                                       ≡⟨⟩
    to-List p (dequeue⁻¹ nothing)                                         ≡⟨ to-List-dequeue⁻¹ ⟩
    _↔_.from List↔Maybe[×List] (⊎-map id (Σ-map id (to-List p)) nothing)  ≡⟨⟩
    []                                                                    ∎

  -- Adds an element to the front of a queue.

  cons : A → Q A → Q A
  cons x q = dequeue⁻¹ (just (x , q))

  to-List-cons : to-List p (cons x q) ≡ x ∷ to-List p q
  to-List-cons {p = p} {x = x} {q = q} =
    to-List p (cons x q)                                ≡⟨⟩

    to-List p (dequeue⁻¹ (just (x , q)))                ≡⟨ to-List-dequeue⁻¹ ⟩

    _↔_.from List↔Maybe[×List]
      (⊎-map id (Σ-map id (to-List p)) (just (x , q)))  ≡⟨⟩

    x ∷ to-List p q                                     ∎

open Is-queue⁺ public

-- A specification of when (and how) a type constructor implements
-- output-restricted deques with a map function.

record Is-queue-with-map
         (Q : ∀ {ℓ} → Type ℓ → Type ℓ)
         ⦃ is-queue : ∀ {ℓ} → Is-queue Q P ℓ ⦄
         ℓ₁ ℓ₂ :
         Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field

    -- A map function.

    map         : {A : Type ℓ₁} {B : Type ℓ₂} →
                  (A → B) → Q A → Q B
    to-List-map : {p₁ : P B} {p₂ : P A} →
                  to-List p₁ (map f q) ≡ L.map f (to-List p₂ q)

-- This module exports universe-polymorphic queue
-- operations/properties.

module Is-queue-with-map⁺
  ⦃ is-queue : ∀ {ℓ} → Is-queue Q P ℓ ⦄
  ⦃ is-queue-with-map : ∀ {ℓ₁ ℓ₂} → Is-queue-with-map Q ℓ₁ ℓ₂ ⦄
  where

  private
    module Q {ℓ₁ ℓ₂} =
      Is-queue-with-map (is-queue-with-map {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂})
  open Q public

open Is-queue-with-map⁺ public

-- A specification of when (and how) a type constructor implements
-- output-restricted deques with unique representations.

record Is-queue-with-unique-representations
         (Q : ∀ {ℓ} → Type ℓ → Type ℓ)
         ⦃ is-queue : ∀ {ℓ} → Is-queue Q P ℓ ⦄
         ℓ :
         Type (lsuc ℓ) where
  field

    -- The from-List function is a left inverse of to-List.

    from-List-to-List :
      {A : Type ℓ} {p : P A} {q : Q A} →
      from-List (to-List p q) ≡ q

-- This module exports universe-polymorphic queue
-- operations/properties.

module Is-queue-with-unique-representations⁺
  ⦃ is-queue : ∀ {ℓ} → Is-queue Q P ℓ ⦄
  ⦃ is-queue-with-unique-representations :
      ∀ {ℓ} → Is-queue-with-unique-representations Q ℓ ⦄
  where

  private
    module Q {ℓ} =
      Is-queue-with-unique-representations
        (is-queue-with-unique-representations {ℓ = ℓ})
  open Q public

  -- A bijection between queues and lists.

  Queue↔List : P A → Q A ↔ List A
  Queue↔List p = record
    { surjection      = Queue↠List p
    ; left-inverse-of = λ _ → from-List-to-List
    }

  -- There is a bijection between equality of two queues and equality
  -- of the corresponding lists.

  ≡-for-lists↔≡ :
    {A : Type a} {p : P A} {q₁ q₂ : Q A} →
    to-List p q₁ ≡ to-List p q₂ ↔ q₁ ≡ q₂
  ≡-for-lists↔≡ {p = p} {q₁ = q₁} {q₂ = q₂} =
    to-List p q₁ ≡ to-List p q₂  ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ $ Queue↔List _ ⟩□
    q₁ ≡ q₂                      □

  -- A variant of Queue↔List.

  Maybe[×Queue]↔List : P A → Maybe (A × Q A) ↔ List A
  Maybe[×Queue]↔List {A = A} p =
    Maybe (A × Q A)     ↝⟨ F.id ⊎-cong F.id ×-cong Queue↔List p ⟩
    Maybe (A × List A)  ↝⟨ inverse List↔Maybe[×List] ⟩□
    List A              □

  -- The function dequeue p is an inverse of dequeue⁻¹.

  Queue↔Maybe[×Queue] : P A → Q A ↔ Maybe (A × Q A)
  Queue↔Maybe[×Queue] {A = A} p =
    Bijection.with-other-function
      (Bijection.with-other-inverse
         (Q A              ↝⟨ Queue↔List p ⟩
          List A           ↝⟨ inverse (Maybe[×Queue]↔List p) ⟩□
          Maybe (A × Q A)  □)
         dequeue⁻¹
         (λ x →
            _↔_.from-to (inverse $ Queue↔List p) (
              to-List p (dequeue⁻¹ x)          ≡⟨ to-List-dequeue⁻¹ ⟩∎
              _↔_.to (Maybe[×Queue]↔List p) x  ∎)))
      (dequeue p)
      (λ q → _↔_.to-from (Maybe[×Queue]↔List p) (
         _↔_.to (Maybe[×Queue]↔List p) (dequeue p q)        ≡⟨⟩

         _↔_.from List↔Maybe[×List]
           (⊎-map id (Σ-map id (to-List p)) (dequeue p q))  ≡⟨ cong (_↔_.from List↔Maybe[×List]) to-List-dequeue ⟩

         _↔_.from List↔Maybe[×List]
           (_↔_.to List↔Maybe[×List] (to-List p q))         ≡⟨ _↔_.left-inverse-of List↔Maybe[×List] _ ⟩∎

         to-List p q                                        ∎))

  _ : {A : Type a} {p : P A} →
      _↔_.to (Queue↔Maybe[×Queue] p) ≡ dequeue p
  _ = refl _

  _ : {A : Type a} {p : P A} →
      _↔_.from (Queue↔Maybe[×Queue] p) ≡ dequeue⁻¹
  _ = refl _

  -- The function from-List can be expressed using enqueue and empty.

  from-List≡foldl-enqueue-empty :
    {A : Type a} {xs : List A} →
    P A → from-List xs ≡ foldl (flip enqueue) empty xs
  from-List≡foldl-enqueue-empty {A = A} {xs = xs} p =
    _↔_.to ≡-for-lists↔≡ (
      to-List p (from-List xs)                   ≡⟨ to-List-from-List ⟩
      xs                                         ≡⟨⟩
      [] ++ xs                                   ≡⟨ cong (_++ _) $ sym to-List-empty ⟩
      to-List p empty ++ xs                      ≡⟨ lemma _ _ ⟩∎
      to-List p (foldl (flip enqueue) empty xs)  ∎)
    where
    lemma :
      ∀ xs (q : Q A) →
      to-List p q ++ xs ≡ to-List p (foldl (flip enqueue) q xs)
    lemma [] q =
      to-List p q ++ []  ≡⟨ ++-right-identity _ ⟩∎
      to-List p q        ∎
    lemma (x ∷ xs) q =
      to-List p q ++ x ∷ xs                              ≡⟨ ++-associative (to-List _ _) _ _ ⟩
      (to-List p q ++ x ∷ []) ++ xs                      ≡⟨ cong (_++ _) $ sym to-List-enqueue ⟩
      to-List p (enqueue x q) ++ xs                      ≡⟨ lemma _ _ ⟩
      to-List p (foldl (flip enqueue) (enqueue x q) xs)  ≡⟨⟩
      to-List p (foldl (flip enqueue) q (x ∷ xs))        ∎

  -- A corollary.

  to-List-foldl-enqueue-empty :
    {A : Type a} {p : P A} (xs : List A) →
    to-List p (foldl (flip enqueue) empty xs) ≡ xs
  to-List-foldl-enqueue-empty {p = p} xs =
    to-List p (foldl (flip enqueue) empty xs)  ≡⟨ cong (to-List p) $ sym $ from-List≡foldl-enqueue-empty p ⟩
    to-List p (from-List xs)                   ≡⟨ to-List-from-List ⟩∎
    xs                                         ∎

open Is-queue-with-unique-representations⁺ public

instance

  -- Lists can be seen as queues.

  List-is-queue : Is-queue List (λ _ → ↑ _ ⊤) ℓ
  List-is-queue .Is-queue.to-List   = λ _ → id
  List-is-queue .Is-queue.from-List = id
  List-is-queue .Is-queue.enqueue   = λ x xs → xs ++ x ∷ []
  List-is-queue .Is-queue.dequeue   = λ _ → _↔_.to List↔Maybe[×List]
  List-is-queue .Is-queue.dequeue⁻¹ = _↔_.from List↔Maybe[×List]

  List-is-queue .Is-queue.to-List-from-List               = refl _
  List-is-queue .Is-queue.to-List-enqueue                 = refl _
  List-is-queue .Is-queue.to-List-dequeue {q = []}        = refl _
  List-is-queue .Is-queue.to-List-dequeue {q = _ ∷ _}     = refl _
  List-is-queue .Is-queue.to-List-dequeue⁻¹ {x = nothing} = refl _
  List-is-queue .Is-queue.to-List-dequeue⁻¹ {x = just _}  = refl _

  List-is-queue-with-map : Is-queue-with-map List ℓ₁ ℓ₂
  List-is-queue-with-map .Is-queue-with-map.map         = L.map
  List-is-queue-with-map .Is-queue-with-map.to-List-map = refl _

  List-is-queue-with-unique-representations :
    Is-queue-with-unique-representations List ℓ
  List-is-queue-with-unique-representations
    .Is-queue-with-unique-representations.from-List-to-List = refl _
