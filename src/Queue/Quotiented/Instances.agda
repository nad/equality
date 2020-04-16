------------------------------------------------------------------------
-- Queue instances for the queues in Queue.Quotiented
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality
open import Prelude
import Queue

module Queue.Quotiented.Instances
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)

  {Q : ∀ {ℓ} → Set ℓ → Set ℓ}
  ⦃ is-queue : ∀ {ℓ} → Queue.Is-queue eq Q (λ _ → ↑ _ ⊤) ℓ ⦄
  ⦃ is-queue-with-map : ∀ {ℓ₁ ℓ₂} → Queue.Is-queue-with-map eq Q ℓ₁ ℓ₂ ⦄
  where

open Derived-definitions-and-properties eq

open Queue eq
open import Queue.Quotiented eq as Q using (Queue)

open import Bijection eq using (_↔_)
open import H-level.Closure eq
open import List eq as L hiding (map)
open import Maybe eq
open import Monad eq hiding (map)
open import Tactic.By.Parametrised eq

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A         : Set a
    xs        : List A

instance

  -- Instances.

  Queue-is-queue : Is-queue (Queue Q) Is-set ℓ
  Queue-is-queue .Is-queue.to-List           = Q.to-List
  Queue-is-queue .Is-queue.from-List         = Q.from-List
  Queue-is-queue .Is-queue.to-List-from-List = Q.to-List-from-List
  Queue-is-queue .Is-queue.enqueue           = Q.enqueue
  Queue-is-queue .Is-queue.to-List-enqueue   = Q.to-List-enqueue
  Queue-is-queue .Is-queue.dequeue           = Q.dequeue
  Queue-is-queue .Is-queue.to-List-dequeue   = Q.to-List-dequeue
  Queue-is-queue .Is-queue.dequeue⁻¹         = Q.dequeue⁻¹
  Queue-is-queue .Is-queue.to-List-dequeue⁻¹ = Q.to-List-dequeue⁻¹

  Queue-is-queue-with-map : Is-queue-with-map (Queue Q) ℓ₁ ℓ₂
  Queue-is-queue-with-map .Is-queue-with-map.map         = Q.map
  Queue-is-queue-with-map .Is-queue-with-map.to-List-map = Q.to-List-map

  Queue-is-queue-with-unique-representations :
    Is-queue-with-unique-representations (Queue Q) ℓ
  Queue-is-queue-with-unique-representations
    .Is-queue-with-unique-representations.from-List-to-List =
    Q.from-List-to-List _

------------------------------------------------------------------------
-- Some examples

private

  ⌊_⌋      = to-List (λ {_ _} → ℕ-set)
  dequeue′ = dequeue (λ {_ _} → ℕ-set)
  empty′   = empty ⦂ Queue Q ℕ

  example₁ : map suc (enqueue 3 empty) ≡ enqueue 4 empty′
  example₁ = _↔_.to ≡-for-lists↔≡ (
    ⟨ ⌊ map suc (enqueue 3 empty) ⌋ ⟩    ≡⟨ ⟨by⟩ to-List-map ⟩
    L.map suc ⟨ ⌊ enqueue 3 empty ⌋ ⟩    ≡⟨ ⟨by⟩ (to-List-foldl-enqueue-empty (_ ∷ [])) ⟩
    L.map suc (3 ∷ [])                   ≡⟨⟩
    ⟨ 4 ∷ [] ⟩                           ≡⟨ ⟨by⟩ (to-List-foldl-enqueue-empty (_ ∷ [])) ⟩∎
    ⌊ enqueue 4 empty ⌋                  ∎)

  example₂ :
    dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty))) ≡
    just (10 , enqueue 6 empty)
  example₂ =
    dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))  ≡⟨ cong dequeue′ lemma ⟩
    ⟨ dequeue′ (cons 10 (enqueue 6 empty)) ⟩             ≡⟨ ⟨by⟩ (_↔_.right-inverse-of (Queue↔Maybe[×Queue] _)) ⟩∎
    just (10 , enqueue 6 empty)                          ∎
    where
    lemma = _↔_.to ≡-for-lists↔≡ (
      ⟨ ⌊ map (_* 2) (enqueue 3 (enqueue 5 empty)) ⌋ ⟩  ≡⟨ ⟨by⟩ to-List-map ⟩
      L.map (_* 2) ⟨ ⌊ enqueue 3 (enqueue 5 empty) ⌋ ⟩  ≡⟨ ⟨by⟩ (to-List-foldl-enqueue-empty (_ ∷ _ ∷ [])) ⟩
      L.map (_* 2) (5 ∷ 3 ∷ [])                         ≡⟨⟩
      10 ∷ ⟨ 6 ∷ [] ⟩                                   ≡⟨ ⟨by⟩ (to-List-foldl-enqueue-empty (_ ∷ [])) ⟩
      ⟨ 10 ∷ ⌊ enqueue 6 empty ⌋ ⟩                      ≡⟨ ⟨by⟩ to-List-cons ⟩∎
      ⌊ cons 10 (enqueue 6 empty) ⌋                     ∎)

  example₃ :
    (do x , q ← dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        return (enqueue (3 * x) q)) ≡
    just (enqueue 30 (enqueue 6 empty))
  example₃ =
    (do x , q ← ⟨ dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty))) ⟩
        return (enqueue (3 * x) q))                                      ≡⟨ ⟨by⟩ example₂ ⟩

    (do x , q ← just (10 , enqueue 6 empty)
        return (enqueue (3 * x) (q ⦂ Queue Q ℕ)))                        ≡⟨⟩

    just (enqueue 30 (enqueue 6 empty))                                  ∎

  example₄ :
    (do x , q ← dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        let q = enqueue (3 * x) q
        return ⌊ q ⌋) ≡
    just (6 ∷ 30 ∷ [])
  example₄ =
    (do x , q ← ⟨ dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty))) ⟩
        let q = enqueue (3 * x) q
        return ⌊ q ⌋)                                                    ≡⟨ ⟨by⟩ example₂ ⟩

    (do x , q ← just (10 , enqueue 6 empty)
        let q = enqueue (3 * x) (q ⦂ Queue Q ℕ)
        return ⌊ q ⌋)                                                    ≡⟨⟩

    just ⟨ ⌊ enqueue 30 (enqueue 6 empty) ⌋ ⟩                            ≡⟨ ⟨by⟩ (to-List-foldl-enqueue-empty (_ ∷ _ ∷ [])) ⟩∎

    just (6 ∷ 30 ∷ [])                                                   ∎

  example₅ :
    ∀ {xs} →
    dequeue′ (from-List (1 ∷ 2 ∷ 3 ∷ xs)) ≡
    just (1 , from-List (2 ∷ 3 ∷ xs))
  example₅ {xs = xs} =
    dequeue′ (from-List (1 ∷ 2 ∷ 3 ∷ xs))           ≡⟨ cong dequeue′ lemma ⟩
    ⟨ dequeue′ (cons 1 (from-List (2 ∷ 3 ∷ xs))) ⟩  ≡⟨ ⟨by⟩ (_↔_.right-inverse-of (Queue↔Maybe[×Queue] _)) ⟩∎
    just (1 , from-List (2 ∷ 3 ∷ xs))               ∎
    where
    lemma = _↔_.to ≡-for-lists↔≡ (
      ⟨ ⌊ from-List (1 ∷ 2 ∷ 3 ∷ xs) ⌋ ⟩   ≡⟨ ⟨by⟩ (_↔_.right-inverse-of (Queue↔List _)) ⟩
      1 ∷ ⟨ 2 ∷ 3 ∷ xs ⟩                   ≡⟨ ⟨by⟩ (sym ∘ _↔_.right-inverse-of (Queue↔List _)) ⟩
      ⟨ 1 ∷ ⌊ from-List (2 ∷ 3 ∷ xs) ⌋ ⟩   ≡⟨ ⟨by⟩ to-List-cons ⟩∎
      ⌊ cons 1 (from-List (2 ∷ 3 ∷ xs)) ⌋  ∎)

  example₆ :
    foldr enqueue empty′ (3 ∷ 2 ∷ 1 ∷ []) ≡
    from-List (1 ∷ 2 ∷ 3 ∷ [])
  example₆ = sym $ from-List≡foldl-enqueue-empty (λ {_ _} → ℕ-set)
