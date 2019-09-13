------------------------------------------------------------------------
-- Specifications of output-restricted deques (single-ended queues
-- with cons)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Queue {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Bijection eq using (_↔_)
import Equivalence eq as Eq
open import Function-universe eq as F hiding (id; _∘_)
open import List eq as L hiding (map)
open import Maybe eq
open import Surjection eq using (_↠_)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B       : Set a
    P Q       : ∀ {ℓ} → Set ℓ → Set ℓ
    p q x     : A
    f         : A → B
    xs        : List A

-- A specification of when (and how) a type constructor implements
-- output-restricted deques.

record Is-queue
         -- A family of queue types.
         (Q : ∀ {ℓ} → Set ℓ → Set ℓ)
         -- Some operations are only available for carrier types
         -- satisfying this predicate.
         (P : ∀ {ℓ} → Set ℓ → Set ℓ)
         ℓ :
         Set (lsuc ℓ) where
  field

    -- Conversion functions.

    to-List           : {A : Set ℓ} → P A → Q A → List A
    from-List         : {A : Set ℓ} → List A → Q A
    to-List-from-List : to-List p (from-List xs) ≡ xs

    -- Enqueues an element.

    enqueue         : {A : Set ℓ} → A → Q A → Q A
    to-List-enqueue : to-List p (enqueue x q) ≡ to-List p q ++ x ∷ []

    -- Dequeues an element, if possible.

    dequeue         : {A : Set ℓ} → P A → Q A → Maybe (A × Q A)
    to-List-dequeue : ⊎-map id (Σ-map id (to-List p)) (dequeue p q) ≡
                      _↔_.to List↔Maybe[×List] (to-List p q)

    -- The "inverse" of the dequeue operation.

    dequeue⁻¹         : {A : Set ℓ} → Maybe (A × Q A) → Q A
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
         (Q : ∀ {ℓ} → Set ℓ → Set ℓ)
         ⦃ is-queue : ∀ {ℓ} → Is-queue Q P ℓ ⦄
         ℓ₁ ℓ₂ :
         Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field

    -- A map function.

    map         : {A : Set ℓ₁} {B : Set ℓ₂} →
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
         (Q : ∀ {ℓ} → Set ℓ → Set ℓ)
         ⦃ is-queue : ∀ {ℓ} → Is-queue Q P ℓ ⦄
         ℓ :
         Set (lsuc ℓ) where
  field

    -- The from-List function is a left inverse of to-List.

    from-List-to-List :
      {A : Set ℓ} {p : P A} {q : Q A} →
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
    {A : Set a} {p : P A} {q₁ q₂ : Q A} →
    to-List p q₁ ≡ to-List p q₂ ↔ q₁ ≡ q₂
  ≡-for-lists↔≡ {p = p} {q₁ = q₁} {q₂ = q₂} =
    to-List p q₁ ≡ to-List p q₂  ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ $ Queue↔List _ ⟩□
    q₁ ≡ q₂                      □

  -- The function dequeue can be expressed using to-List and
  -- from-List.

  dequeue≡from-List-to-List :
    {A : Set a} {p : P A} {q : Q A} →
    dequeue p q ≡
    ⊎-map id (Σ-map id from-List)
      (_↔_.to List↔Maybe[×List] (to-List p q))
  dequeue≡from-List-to-List {p = p} {q = q} =
    dequeue p q                                        ≡⟨ sym $ _↔_.left-inverse-of (F.id ⊎-cong ∃-cong λ _ → Queue↔List _) _ ⟩

    ⊎-map id (Σ-map id from-List)
      (⊎-map id (Σ-map id (to-List p)) (dequeue p q))  ≡⟨ cong (⊎-map id (Σ-map id from-List)) to-List-dequeue ⟩∎

    ⊎-map id (Σ-map id from-List)
      (_↔_.to List↔Maybe[×List] (to-List p q))         ∎

  -- The function dequeue p is an inverse of dequeue⁻¹.

  Queue↔Maybe[×Queue] : P A → Q A ↔ Maybe (A × Q A)
  Queue↔Maybe[×Queue] p = record
    { surjection = record
      { logical-equivalence = record
        { to   = dequeue p
        ; from = dequeue⁻¹
        }
      ; right-inverse-of = λ x →
          dequeue p (dequeue⁻¹ x)                        ≡⟨ dequeue≡from-List-to-List ⟩

          ⊎-map id (Σ-map id from-List)
            (_↔_.to List↔Maybe[×List]
               (to-List p (dequeue⁻¹ x)))                ≡⟨ cong (⊎-map id (Σ-map id from-List) ∘ _↔_.to List↔Maybe[×List])
                                                            to-List-dequeue⁻¹ ⟩
          ⊎-map id (Σ-map id from-List)
            (_↔_.to List↔Maybe[×List]
               (_↔_.from List↔Maybe[×List]
                  (⊎-map id (Σ-map id (to-List p)) x)))  ≡⟨ cong (⊎-map id (Σ-map id from-List)) $
                                                            _↔_.right-inverse-of List↔Maybe[×List] (⊎-map id (Σ-map id (to-List p)) x) ⟩
          ⊎-map id (Σ-map id from-List)
            (⊎-map id (Σ-map id (to-List p)) x)          ≡⟨ _↔_.left-inverse-of (F.id ⊎-cong ∃-cong λ _ → Queue↔List _) _ ⟩∎

          x                                              ∎
      }
    ; left-inverse-of = λ q →
        _↔_.to ≡-for-lists↔≡ (
          to-List p (dequeue⁻¹ (dequeue p q))                ≡⟨ cong (λ x → to-List p (dequeue⁻¹ x)) dequeue≡from-List-to-List ⟩

          to-List p (dequeue⁻¹
            (⊎-map id (Σ-map id from-List)
               (_↔_.to List↔Maybe[×List] (to-List p q))))    ≡⟨ to-List-dequeue⁻¹ ⟩

          _↔_.from List↔Maybe[×List]
            (⊎-map id (Σ-map id (to-List p))
              (⊎-map id (Σ-map id from-List)
                 (_↔_.to List↔Maybe[×List] (to-List p q))))  ≡⟨ cong (_↔_.from List↔Maybe[×List]) $
                                                                _↔_.right-inverse-of (F.id ⊎-cong ∃-cong λ _ → Queue↔List _)
                                                                  (_↔_.to List↔Maybe[×List] (to-List p q)) ⟩
          _↔_.from List↔Maybe[×List]
            (_↔_.to List↔Maybe[×List] (to-List p q))         ≡⟨ _↔_.left-inverse-of List↔Maybe[×List] _ ⟩∎

          to-List p q                                        ∎)
    }

  -- The function from-List can be expressed using enqueue and empty.

  from-List≡foldl-enqueue-empty :
    {A : Set a} {xs : List A} →
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
    {A : Set a} {p : P A} (xs : List A) →
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
