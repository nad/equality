------------------------------------------------------------------------
-- Quotiented simple queues: any two queues representing the same
-- sequence are equal
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Queue.Simple.Quotiented
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Bijection eq using (_↔_)
open import Equality.Path.Isomorphisms eq
import Equivalence eq as Eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level.Closure eq
open import List eq as L hiding (map)
open import Maybe eq
open import Monad eq hiding (map)
import Queue.Simple eq as Q
open import Quotient eq as Quotient
open import Sum eq
open import Surjection eq using (_↠_)
open import Tactic.By.Parametrised eq

private
  variable
    a b             : Level
    A B             : Set a
    s s′ s₁ s₂      : Is-set A
    q q₁ q₂ x x₁ x₂ : A
    f g             : A → B
    xs              : List A

------------------------------------------------------------------------
-- Queues

abstract

  private

    -- The quotienting relation: Two queues are seen as equal if they
    -- represent the same list.

    _∼_ : {A : Set a} (_ _ : Q.Queue A) → Set a
    q₁ ∼ q₂ = Q.to-List q₁ ≡ Q.to-List q₂

  -- Queues.
  --
  -- The type is abstract to ensure that a change to a different
  -- representation (for instance banker's queues) does not break code
  -- that uses this module.

  Queue : Set a → Set a
  Queue A = Q.Queue A / _∼_

  -- Queue A is a set.

  Queue-is-set : Is-set (Queue A)
  Queue-is-set = /-is-set

------------------------------------------------------------------------
-- Conversion functions

abstract

  -- Converts queues to lists. (The carrier type is required to be a
  -- set.)

  to-List : Is-set A → Queue A → List A
  to-List s = Quotient.rec
    Q.to-List
    id
    (H-level-List 0 s)

  -- Converts lists to queues.

  from-List : List A → Queue A
  from-List = [_] ∘ Q.from-List

  private

    to-List∘from-List : ∀ q → to-List s (from-List q) ≡ q
    to-List∘from-List = _↠_.right-inverse-of Q.Queue↠List

    from-List∘to-List :
      (q : Queue A) → _≡_ {A = Queue A} (from-List (to-List s q)) q
    from-List∘to-List = Quotient.elim-Prop
        _
        (λ q → []-respects-relation (
           Q.to-List (Q.from-List (Q.to-List q))  ≡⟨ _↠_.right-inverse-of Q.Queue↠List _ ⟩∎
           Q.to-List q                            ∎))
        (λ _ → Queue-is-set)

-- If A is a set, then there is a bijection between Queue A and
-- List A.

Queue↔List : Is-set A → Queue A ↔ List A
Queue↔List s = record
  { surjection = record
    { logical-equivalence = record
      { to   = to-List s
      ; from = from-List
      }
    ; right-inverse-of = to-List∘from-List
    }
  ; left-inverse-of = from-List∘to-List
  }

abstract

  -- There is a bijection between equality of two queues and equality
  -- of the corresponding lists.

  ≡-for-lists↔≡ : to-List s q₁ ≡ to-List s q₂ ↔ q₁ ≡ q₂
  ≡-for-lists↔≡ {s = s} {q₁ = q₁} {q₂ = q₂} =
    to-List s q₁ ≡ to-List s q₂  ↔⟨ Eq.≃-≡ $ Eq.↔⇒≃ $ Queue↔List s ⟩□
    q₁ ≡ q₂                      □

  -- The type ∃ λ (q : Queue A) → to-List s q ≡ xs is contractible.

  Σ-Queue-contractible :
    Contractible (∃ λ (q : Queue A) → to-List s q ≡ xs)
  Σ-Queue-contractible {A = A} {s = s} {xs = xs} =       $⟨ singleton-contractible _ ⟩
    Contractible (Singleton (from-List xs))              ↝⟨ id ⟩
    Contractible (∃ λ (q : Queue A) → q ≡ from-List xs)  ↝⟨ H-level-cong _ 0 $
                                                            ∃-cong (λ _ → inverse $ from≡↔≡to $ inverse $ Eq.↔⇒≃ $ Queue↔List s) ⟩□
    Contractible (∃ λ (q : Queue A) → to-List s q ≡ xs)  □

------------------------------------------------------------------------
-- Queue operations

abstract

  private

    -- Helper functions that can be used to define unary functions on
    -- queues.

    unary :
      (f : List A → List B)
      (g : Q.Queue A → Q.Queue B) →
      (∀ q → Q.to-List (g q) ≡ f (Q.to-List q)) →
      Queue A → Queue B
    unary f g h =
      g /-map λ q₁ q₂ q₁∼q₂ →
        Q.to-List (g q₁)  ≡⟨ h _ ⟩
        f (Q.to-List q₁)  ≡⟨ cong f q₁∼q₂ ⟩
        f (Q.to-List q₂)  ≡⟨ sym $ h _ ⟩∎
        Q.to-List (g q₂)  ∎

    to-List-unary :
      ∀ {h} q → to-List s₁ (unary f g h q) ≡ f (to-List s₂ q)
    to-List-unary {s₁ = s₁} {f = f} {g = g} {s₂ = s₂} {h = h} =
      elim-Prop
        _
        (λ q →
           to-List s₁ (unary f g h [ q ])  ≡⟨⟩
           Q.to-List (g q)                 ≡⟨ h _ ⟩
           f (Q.to-List q)                 ≡⟨⟩
           f (to-List s₂ [ q ])            ∎)
        (λ _ → H-level-List 0 s₁)

    -- Generalisations of the functions above.

    unary′ :
      {F : Set a → Set b} →
      (∀ {A} → Is-set A → Is-set (F A)) →
      (map : ∀ {A B} → (A → B) → F A → F B) →
      (∀ {A} {x : F A} → map id x ≡ x) →
      (∀ {A B C} {f : B → C} {g : A → B} x →
       map (f ∘ g) x ≡ map f (map g x)) →
      (f : List A → F (List B))
      (g : Q.Queue A → F (Q.Queue B)) →
      (∀ q → map Q.to-List (g q) ≡ f (Q.to-List q)) →
      Is-set B →
      Queue A → F (Queue B)
    unary′ F-set map map-id map-∘ f g h s = Quotient.rec
      (map [_] ∘ g)
      (λ {q₁ q₂} q₁∼q₂ → lemma₂ (
         map (to-List s) (map [_] (g q₁))  ≡⟨ sym $ map-∘ _ ⟩
         map Q.to-List (g q₁)              ≡⟨ h q₁ ⟩
         f (Q.to-List q₁)                  ≡⟨ cong f q₁∼q₂ ⟩
         f (Q.to-List q₂)                  ≡⟨ sym $ h q₂ ⟩
         map Q.to-List (g q₂)              ≡⟨ map-∘ _ ⟩∎
         map (to-List s) (map [_] (g q₂))  ∎))
      (F-set Queue-is-set)
      where
      lemma₁ : map from-List (map (to-List s) x) ≡ x
      lemma₁ {x = x} =
        map from-List (map (to-List s) x)  ≡⟨ sym $ map-∘ _ ⟩
        map (from-List ∘ to-List s) x      ≡⟨ cong (flip map x) $ ⟨ext⟩ $ _↔_.left-inverse-of (Queue↔List s) ⟩
        map id x                           ≡⟨ map-id ⟩∎
        x                                  ∎

      lemma₂ :
        map (to-List s) x₁ ≡ map (to-List s) x₂ →
        x₁ ≡ x₂
      lemma₂ {x₁ = x₁} {x₂ = x₂} eq =
        x₁                                  ≡⟨ sym lemma₁ ⟩
        map from-List (map (to-List s) x₁)  ≡⟨ cong (map from-List) eq ⟩
        map from-List (map (to-List s) x₂)  ≡⟨ lemma₁ ⟩∎
        x₂                                  ∎

    to-List-unary′ :
      {F      : Set a → Set b}
      (F-set  : ∀ {A} → Is-set A → Is-set (F A))
      (map    : ∀ {A B} → (A → B) → F A → F B)
      (map-id : ∀ {A} {x : F A} → map id x ≡ x)
      (map-∘  : ∀ {A B C} {f : B → C} {g : A → B} x →
                map (f ∘ g) x ≡ map f (map g x))
      (f : List A → F (List B))
      (g : Q.Queue A → F (Q.Queue B))
      (h : ∀ q → map Q.to-List (g q) ≡ f (Q.to-List q))
      (s : Is-set B) →
      ∀ q →
      map (to-List s) (unary′ F-set map map-id map-∘ f g h s q) ≡
      f (to-List s′ q)
    to-List-unary′ {s′ = s′} F-set map map-id map-∘ f g h s =
      Quotient.elim-Prop
        _
        (λ q →
           map (to-List s) (unary′ F-set map map-id map-∘ f g h s [ q ])  ≡⟨⟩
           map (to-List s) (map [_] (g q))                                ≡⟨ sym $ map-∘ _ ⟩
           map Q.to-List (g q)                                            ≡⟨ h _ ⟩
           f (Q.to-List q)                                                ≡⟨⟩
           f (to-List s′ [ q ])                                           ∎)
        (λ _ → F-set (H-level-List 0 s))

  -- An empty queue.

  empty : Queue A
  empty = [ Q.empty ]

  to-List-empty : to-List s empty ≡ ([] ⦂ List A)
  to-List-empty = refl _

  -- Adds an element to the front of a queue.

  cons : A → Queue A → Queue A
  cons x = unary (x ∷_) (Q.cons x) Q.to-List-cons

  to-List-cons : to-List s (cons x q) ≡ x ∷ to-List s q
  to-List-cons {q = q} = to-List-unary q

  -- Enqueues an element.

  enqueue : A → Queue A → Queue A
  enqueue x = unary (_++ x ∷ []) (Q.enqueue x) Q.to-List-enqueue

  to-List-enqueue : to-List s (enqueue x q) ≡ to-List s q ++ x ∷ []
  to-List-enqueue {q = q} = to-List-unary q

  -- Dequeues an element, if possible. (The carrier type is required to
  -- be a set.)

  dequeue : Is-set A → Queue A → Maybe (A × Queue A)
  dequeue s = unary′
    (Maybe-closure 0 ∘ ×-closure 2 s)
    (λ f → ⊎-map id (Σ-map id f))
    ⊎-map-id
    ⊎-map-∘
    (_↔_.to List↔Maybe[×List])
    Q.dequeue
    Q.to-List-dequeue
    s

  to-List-dequeue :
    ⊎-map id (Σ-map id (to-List s)) (dequeue s q) ≡
    _↔_.to List↔Maybe[×List] (to-List s q)
  to-List-dequeue {q = q} = to-List-unary′
    (Maybe-closure 0 ∘ ×-closure 2 _)
    (λ f → ⊎-map id (Σ-map id f))
    ⊎-map-id
    ⊎-map-∘
    _
    Q.dequeue
    _
    _
    q

  -- A map function.

  map : (A → B) → Queue A → Queue B
  map f = unary (L.map f) (Q.map f) Q.to-List-map

  to-List-map : to-List s₁ (map f q) ≡ L.map f (to-List s₂ q)
  to-List-map {q = q} = to-List-unary q

------------------------------------------------------------------------
-- Some properties

-- These properties do not depend on implementation details: they are
-- not abstract.

-- If the carrier type is a set, then from-List can be expressed using
-- enqueue and empty.

from-List≡foldl-enqueue-empty :
  {xs : List A} →
  Is-set A →
  from-List xs ≡ foldl (flip enqueue) empty xs
from-List≡foldl-enqueue-empty {xs = xs} s = _↔_.to ≡-for-lists↔≡ (
  to-List s (from-List xs)                   ≡⟨ _↔_.right-inverse-of (Queue↔List _) _ ⟩
  xs                                         ≡⟨⟩
  ⟨ [] ⟩ ++ xs                               ≡⟨ ⟨by⟩ 4 to-List-empty ⟩
  to-List s empty ++ xs                      ≡⟨ lemma _ _ ⟩∎
  to-List s (foldl (flip enqueue) empty xs)  ∎)
  where
  lemma :
    ∀ xs q → to-List s q ++ xs ≡ to-List s (foldl (flip enqueue) q xs)
  lemma [] q =
    to-List s q ++ []  ≡⟨ ++-right-identity _ ⟩∎
    to-List s q        ∎
  lemma (x ∷ xs) q =
    ⟨ to-List s q ++ x ∷ xs ⟩                          ≡⟨ ⟨by⟩ 7 (++-associative (to-List _ _)) ⟩
    ⟨ to-List s q ++ x ∷ [] ⟩ ++ xs                    ≡⟨ ⟨by⟩ 7 to-List-enqueue ⟩
    to-List s (enqueue x q) ++ xs                      ≡⟨ lemma _ _ ⟩
    to-List s (foldl (flip enqueue) (enqueue x q) xs)  ≡⟨⟩
    to-List s (foldl (flip enqueue) q (x ∷ xs))        ∎

-- A corollary.

to-List-foldl-enqueue-empty :
  ∀ xs → to-List s (foldl (flip enqueue) empty xs) ≡ xs
to-List-foldl-enqueue-empty {s = s} xs =
  to-List s ⟨ foldl (flip enqueue) empty xs ⟩  ≡⟨ ⟨by⟩ 4 (from-List≡foldl-enqueue-empty s) ⟩
  to-List s (from-List xs)                     ≡⟨ _↔_.right-inverse-of (Queue↔List _) _ ⟩∎
  xs                                           ∎

-- The function dequeue s is an inverse of a variant of cons.

Queue↔Maybe[×Queue] :
  Is-set A →
  Queue A ↔ Maybe (A × Queue A)
Queue↔Maybe[×Queue] s = record
  { surjection = record
    { logical-equivalence = record
      { to   = dequeue s
      ; from = maybe (uncurry cons) empty
      }
    ; right-inverse-of = λ x →
        dequeue s (maybe (uncurry cons) empty x)            ≡⟨ lemma₀ _ ⟩

        ⊎-map id (Σ-map id from-List)
          (_↔_.to List↔Maybe[×List]
             (to-List s (maybe (uncurry cons) empty x)))    ≡⟨ lemma₁ _ ⟩∎

        x                                                   ∎
    }
  ; left-inverse-of = λ q →
      _↔_.to ≡-for-lists↔≡ (
        to-List s (maybe (uncurry cons) empty ⟨ dequeue s q ⟩)    ≡⟨ ⟨by⟩ 4 lemma₀ ⟩

        to-List s (maybe (uncurry cons) empty
          (⊎-map id (Σ-map id from-List)
             (_↔_.to List↔Maybe[×List] (to-List s q))))           ≡⟨ lemma₂ _ ⟩∎

        to-List s q                                               ∎)
  }
  where
  lemma₀ : ∀ _ → _
  lemma₀ = λ q →
    ⟨ dequeue s q ⟩                                      ≡⟨ ⟨by⟩ 4 (_↔_.left-inverse-of (F.id ⊎-cong ∃-cong λ _ → Queue↔List _)) ⟩

    ⊎-map id (Σ-map id from-List)
      ⟨ ⊎-map id (Σ-map id (to-List s)) (dequeue s q) ⟩  ≡⟨ ⟨by⟩ 4 to-List-dequeue ⟩∎

    ⊎-map id (Σ-map id from-List)
      (_↔_.to List↔Maybe[×List] (to-List s q))           ∎

  lemma₁ :
    ∀ x →
    ⊎-map id (Σ-map id from-List)
      (_↔_.to List↔Maybe[×List]
         (to-List s (maybe (uncurry cons) empty x))) ≡
    x
  lemma₁ nothing =
    ⊎-map id (Σ-map id from-List)
      (_↔_.to List↔Maybe[×List] ⟨ to-List s empty ⟩)             ≡⟨ ⟨by⟩ 3 to-List-empty ⟩

    ⊎-map id (Σ-map id from-List) (_↔_.to List↔Maybe[×List] [])  ≡⟨⟩

    nothing                                                      ∎

  lemma₁ (just (x , q)) =
    ⊎-map id (Σ-map id from-List)
      (_↔_.to List↔Maybe[×List] ⟨ to-List s (cons x q) ⟩)  ≡⟨ ⟨by⟩ 5 to-List-cons ⟩

    ⊎-map id (Σ-map id from-List)
      (_↔_.to List↔Maybe[×List] (x ∷ to-List s q))         ≡⟨⟩

    just (x , ⟨ from-List (to-List s q) ⟩)                 ≡⟨ ⟨by⟩ 5 (_↔_.left-inverse-of (Queue↔List _)) ⟩∎

    just (x , q)                                           ∎

  lemma₂ :
    ∀ xs →
    to-List s (maybe (uncurry cons) empty
      (⊎-map id (Σ-map id from-List)
         (_↔_.to List↔Maybe[×List] xs))) ≡
    xs
  lemma₂ []       = to-List-empty
  lemma₂ (x ∷ xs) =
    to-List s (cons x (from-List xs))  ≡⟨ to-List-cons ⟩
    x ∷ ⟨ to-List s (from-List xs) ⟩   ≡⟨ ⟨by⟩ 5 (_↔_.right-inverse-of (Queue↔List s)) ⟩∎
    x ∷ xs                             ∎

------------------------------------------------------------------------
-- Some examples

private

  module Concrete-examples where

    abstract

      -- When the definitions compute it is easy to prove the
      -- following lemmas.

      example₁ : map suc (enqueue 3 empty) ≡ enqueue 4 empty
      example₁ = refl _

      example₂ :
        dequeue ℕ-set (map (_* 2) (enqueue 3 (enqueue 5 empty))) ≡
        just (10 , enqueue 6 empty)
      example₂ = refl _

      example₃ :
        (do x , q ← dequeue ℕ-set
                      (map (_* 2) (enqueue 3 (enqueue 5 empty)))
            return (enqueue (3 * x) q)) ≡
        just (enqueue 30 (enqueue 6 empty))
      example₃ = refl _

      example₄ :
        (do x , q ← dequeue ℕ-set
                      (map (_* 2) (enqueue 3 (enqueue 5 empty)))
            let q = enqueue (3 * x) q
            return (to-List ℕ-set q)) ≡
        just (6 ∷ 30 ∷ [])
      example₄ = refl _

      example₅ :
        dequeue ℕ-set (from-List (1 ∷ 2 ∷ 3 ∷ xs)) ≡
        just (1 , from-List (2 ∷ 3 ∷ xs))
      example₅ = refl _

      example₆ :
        foldr enqueue empty (3 ∷ 2 ∷ 1 ∷ []) ≡
        from-List (1 ∷ 2 ∷ 3 ∷ [])
      example₆ = []-respects-relation (refl _)

  module Abstract-examples where

    -- When the definitions do not compute the proofs above do not
    -- work.

    private

      ⌊_⌋ = to-List ℕ-set

    example₁ : map suc (enqueue 3 empty) ≡ enqueue 4 empty
    example₁ = _↔_.to ≡-for-lists↔≡ (
      ⟨ ⌊ map suc (enqueue 3 empty) ⌋ ⟩    ≡⟨ ⟨by⟩ 0 to-List-map ⟩
      L.map suc ⟨ ⌊ enqueue 3 empty ⌋ ⟩    ≡⟨ ⟨by⟩ 0 (to-List-foldl-enqueue-empty (_ ∷ [])) ⟩
      L.map suc (3 ∷ [])                   ≡⟨⟩
      ⟨ 4 ∷ [] ⟩                           ≡⟨ ⟨by⟩ 0 to-List-foldl-enqueue-empty ⟩∎
      ⌊ enqueue 4 empty ⌋                  ∎)

    example₂ :
      dequeue ℕ-set (map (_* 2) (enqueue 3 (enqueue 5 empty))) ≡
      just (10 , enqueue 6 empty)
    example₂ =
      dequeue ℕ-set ⟨ map (_* 2) (enqueue 3 (enqueue 5 empty)) ⟩  ≡⟨ ⟨by⟩ 0 lemma ⟩
      ⟨ dequeue ℕ-set (cons 10 (enqueue 6 empty)) ⟩               ≡⟨ ⟨by⟩ 0 (_↔_.right-inverse-of (Queue↔Maybe[×Queue] _)) ⟩∎
      just (10 , enqueue 6 empty)                                 ∎
      where
      lemma = _↔_.to ≡-for-lists↔≡ (
        ⟨ ⌊ map (_* 2) (enqueue 3 (enqueue 5 empty)) ⌋ ⟩  ≡⟨ ⟨by⟩ 0 to-List-map ⟩
        L.map (_* 2) ⟨ ⌊ enqueue 3 (enqueue 5 empty) ⌋ ⟩  ≡⟨ ⟨by⟩ 0 (to-List-foldl-enqueue-empty (_ ∷ _ ∷ [])) ⟩
        L.map (_* 2) (5 ∷ 3 ∷ [])                         ≡⟨⟩
        10 ∷ ⟨ 6 ∷ [] ⟩                                   ≡⟨ ⟨by⟩ 0 to-List-foldl-enqueue-empty ⟩
        ⟨ 10 ∷ ⌊ enqueue 6 empty ⌋ ⟩                      ≡⟨ ⟨by⟩ 0 to-List-cons ⟩∎
        ⌊ cons 10 (enqueue 6 empty) ⌋                     ∎)

    example₃ :
      (do x , q ← dequeue ℕ-set
                    (map (_* 2) (enqueue 3 (enqueue 5 empty)))
          return (enqueue (3 * x) q)) ≡
      just (enqueue 30 (enqueue 6 empty))
    example₃ =
      (do x , q ← ⟨ dequeue ℕ-set
                      (map (_* 2) (enqueue 3 (enqueue 5 empty))) ⟩
          return (enqueue (3 * x) q))                               ≡⟨ ⟨by⟩ 0 example₂ ⟩

      (do x , q ← just (10 , enqueue 6 empty)
          return (enqueue (3 * x) q))                               ≡⟨⟩

      just (enqueue 30 (enqueue 6 empty))                           ∎

    example₄ :
      (do x , q ← dequeue ℕ-set
                    (map (_* 2) (enqueue 3 (enqueue 5 empty)))
          let q = enqueue (3 * x) q
          return ⌊ q ⌋) ≡
      just (6 ∷ 30 ∷ [])
    example₄ =
      (do x , q ← ⟨ dequeue ℕ-set
                      (map (_* 2) (enqueue 3 (enqueue 5 empty))) ⟩
          let q = enqueue (3 * x) q
          return ⌊ q ⌋)                                             ≡⟨ ⟨by⟩ 0 example₂ ⟩

      (do x , q ← just (10 , enqueue 6 empty)
          let q = enqueue (3 * x) q
          return ⌊ q ⌋)                                             ≡⟨⟩

      just ⟨ ⌊ enqueue 30 (enqueue 6 empty) ⌋ ⟩                     ≡⟨ ⟨by⟩ 0 (to-List-foldl-enqueue-empty (_ ∷ _ ∷ [])) ⟩∎

      just (6 ∷ 30 ∷ [])                                            ∎

    example₅ :
      dequeue ℕ-set (from-List (1 ∷ 2 ∷ 3 ∷ xs)) ≡
      just (1 , from-List (2 ∷ 3 ∷ xs))
    example₅ {xs = xs} =
      dequeue ℕ-set ⟨ from-List (1 ∷ 2 ∷ 3 ∷ xs) ⟩         ≡⟨ ⟨by⟩ 1 lemma ⟩
      ⟨ dequeue ℕ-set (cons 1 (from-List (2 ∷ 3 ∷ xs))) ⟩  ≡⟨ ⟨by⟩ 1 (_↔_.right-inverse-of (Queue↔Maybe[×Queue] _)) ⟩∎
      just (1 , from-List (2 ∷ 3 ∷ xs))                    ∎
      where
      lemma = _↔_.to ≡-for-lists↔≡ (
        ⟨ ⌊ from-List (1 ∷ 2 ∷ 3 ∷ xs) ⌋ ⟩   ≡⟨ ⟨by⟩ 1 (_↔_.right-inverse-of (Queue↔List _)) ⟩
        1 ∷ ⟨ 2 ∷ 3 ∷ xs ⟩                   ≡⟨ ⟨by⟩ 1 (_↔_.right-inverse-of (Queue↔List _)) ⟩
        ⟨ 1 ∷ ⌊ from-List (2 ∷ 3 ∷ xs) ⌋ ⟩   ≡⟨ ⟨by⟩ 1 to-List-cons ⟩∎
        ⌊ cons 1 (from-List (2 ∷ 3 ∷ xs)) ⌋  ∎)

    example₆ :
      foldr enqueue empty (3 ∷ 2 ∷ 1 ∷ []) ≡
      from-List (1 ∷ 2 ∷ 3 ∷ [])
    example₆ = sym $ from-List≡foldl-enqueue-empty ℕ-set
