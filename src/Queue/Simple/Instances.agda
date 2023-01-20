------------------------------------------------------------------------
-- Queue instances for the queues in Queue.Simple
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Queue.Simple.Instances
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺)
  where

open Derived-definitions-and-properties eq

open import Prelude

open import Queue eq
open import Queue.Simple eq as Q using (Queue)

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

instance

  -- Instances.

  Queue-is-queue : Is-queue (λ A → Queue A) (λ _ → ↑ _ ⊤) ℓ
  Queue-is-queue .Is-queue.to-List               = λ _ → Q.to-List
  Queue-is-queue .Is-queue.from-List             = Q.from-List
  Queue-is-queue .Is-queue.to-List-from-List     = Q.to-List-from-List
  Queue-is-queue .Is-queue.enqueue               = Q.enqueue
  Queue-is-queue .Is-queue.to-List-enqueue {q}   = Q.to-List-enqueue q
  Queue-is-queue .Is-queue.dequeue               = λ _ → Q.dequeue
  Queue-is-queue .Is-queue.to-List-dequeue {q}   = Q.to-List-dequeue q
  Queue-is-queue .Is-queue.dequeue⁻¹             = Q.dequeue⁻¹
  Queue-is-queue .Is-queue.to-List-dequeue⁻¹ {x} = Q.to-List-dequeue⁻¹ x

  Queue-is-queue-with-map : Is-queue-with-map (λ A → Queue A) ℓ₁ ℓ₂
  Queue-is-queue-with-map .Is-queue-with-map.map             = Q.map
  Queue-is-queue-with-map .Is-queue-with-map.to-List-map {q} =
    Q.to-List-map q
