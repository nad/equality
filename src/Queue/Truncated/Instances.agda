------------------------------------------------------------------------
-- Queue instances for the queues in Queue.Truncated
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality
open import Prelude
import Queue

module Queue.Truncated.Instances
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)

  {Q : ∀ {ℓ} → @0 Set ℓ → Set ℓ}
  ⦃ is-queue : ∀ {ℓ} → Queue.Is-queue eq Q (λ _ → ↑ _ ⊤) ℓ ⦄
  ⦃ is-queue-with-map : ∀ {ℓ₁ ℓ₂} → Queue.Is-queue-with-map eq Q ℓ₁ ℓ₂ ⦄
  where

open Derived-definitions-and-properties eq

open Queue eq
open import Queue.Truncated eq as Q using (Queue)

open import Bijection eq using (_↔_)
open import Erased.Cubical eq hiding (map)
open import H-level.Closure eq
open import List eq as L hiding (map)
open import Maybe eq
open import Monad eq hiding (map)
import Nat eq as Nat
open import Tactic.By.Parametrised eq

private

  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A         : Set a
    xs        : List A

  module N = Q.Non-indexed

instance

  -- Instances.

  Queue-is-queue : Is-queue (Queue Q) Very-stable-≡ ℓ
  Queue-is-queue .Is-queue.to-List           = Q.to-List
  Queue-is-queue .Is-queue.from-List         = Q.from-List
  Queue-is-queue .Is-queue.to-List-from-List = _↔_.right-inverse-of
                                                 (Q.Queue↔List _) _
  Queue-is-queue .Is-queue.enqueue           = N.enqueue
  Queue-is-queue .Is-queue.to-List-enqueue   = N.to-List-enqueue
  Queue-is-queue .Is-queue.dequeue           = N.dequeue
  Queue-is-queue .Is-queue.to-List-dequeue   = N.to-List-dequeue
  Queue-is-queue .Is-queue.dequeue⁻¹         = N.dequeue⁻¹
  Queue-is-queue .Is-queue.to-List-dequeue⁻¹ = N.to-List-dequeue⁻¹

  Queue-is-queue-with-map : Is-queue-with-map (Queue Q) ℓ₁ ℓ₂
  Queue-is-queue-with-map .Is-queue-with-map.map         = N.map
  Queue-is-queue-with-map .Is-queue-with-map.to-List-map = N.to-List-map

  Queue-is-queue-with-unique-representations :
    Is-queue-with-unique-representations (Queue Q) ℓ
  Queue-is-queue-with-unique-representations
    .Is-queue-with-unique-representations.from-List-to-List =
    _↔_.left-inverse-of (Q.Queue↔List _) _

------------------------------------------------------------------------
-- Some examples

private

  ns       = Decidable-equality→Very-stable-≡ Nat._≟_
  dequeue′ = dequeue ns
  to-List′ = to-List ns
  empty′   = empty ⦂ Queue Q ℕ

  example₁ : map suc (enqueue 3 empty) ≡ enqueue 4 empty′
  example₁ = _↔_.to Q.≡-for-indices↔≡ [ refl _ ]

  example₂ : dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty))) ≡
             just (10 , enqueue 6 empty)
  example₂ =
    dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))  ≡⟨ cong dequeue′ (_↔_.to Q.≡-for-indices↔≡ [ refl _ ]) ⟩
    ⟨ dequeue′ (cons 10 (enqueue 6 empty)) ⟩             ≡⟨ ⟨by⟩ 3 (_↔_.right-inverse-of (Queue↔Maybe[×Queue] _)) ⟩∎
    just (10 , enqueue 6 empty)                          ∎

  example₃ :
    (do x , q ← dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        return (enqueue (3 * x) q)) ≡
    just (enqueue 30 (enqueue 6 empty))
  example₃ =
    (do x , q ← ⟨ dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty))) ⟩
        return (enqueue (3 * x) q ⦂ Queue Q ℕ))                          ≡⟨ ⟨by⟩ 3 example₂ ⟩

    (do x , q ← just (10 , enqueue 6 empty)
        return (enqueue (3 * x) (q ⦂ Queue Q ℕ)))                        ≡⟨⟩

    just (enqueue 30 (enqueue 6 empty))                                  ∎

  example₄ :
    (do x , q ← dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        let q = enqueue (3 * x) q
        return (to-List′ q)) ≡
    just (6 ∷ 30 ∷ [])
  example₄ =
    (do x , q ← ⟨ dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty))) ⟩
        return (to-List′ (enqueue (3 * x) q)))                           ≡⟨ ⟨by⟩ 3 example₂ ⟩

    (do x , q ← just (10 , enqueue 6 empty)
        return (to-List′ (enqueue (3 * x) (q ⦂ Queue Q ℕ))))             ≡⟨⟩

    just ⟨ to-List′ (enqueue 30 (enqueue 6 empty)) ⟩                     ≡⟨ ⟨by⟩ 3 to-List-foldl-enqueue-empty ⟩∎

    just (6 ∷ 30 ∷ [])                                                   ∎

  example₅ :
    ∀ {xs} →
    dequeue′ (from-List (1 ∷ 2 ∷ 3 ∷ xs)) ≡
    just (1 , from-List (2 ∷ 3 ∷ xs))
  example₅ {xs = xs} =
    dequeue′ (from-List (1 ∷ 2 ∷ 3 ∷ xs))           ≡⟨ cong dequeue′ (_↔_.to Q.≡-for-indices↔≡ [ refl _ ]) ⟩
    ⟨ dequeue′ (cons 1 (from-List (2 ∷ 3 ∷ xs))) ⟩  ≡⟨ ⟨by⟩ 4 (_↔_.right-inverse-of (Queue↔Maybe[×Queue] _)) ⟩∎
    just (1 , from-List (2 ∷ 3 ∷ xs))               ∎

  example₆ :
    foldr enqueue empty′ (3 ∷ 2 ∷ 1 ∷ []) ≡
    from-List (1 ∷ 2 ∷ 3 ∷ [])
  example₆ = _↔_.to Q.≡-for-indices↔≡ [ refl _ ]
