------------------------------------------------------------------------
-- Queue instances for the queues in Queue.Truncated
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe #-}

import Equality.Path as P
open import Prelude
import Queue

module Queue.Truncated.Instances
  {e⁺}
  (eq : ∀ {a p} → P.Equality-with-paths a p e⁺)
  (open P.Derived-definitions-and-properties eq)

  {Q : ∀ {ℓ} → Type ℓ → Type ℓ}
  ⦃ is-queue :
      ∀ {ℓ} →
      Queue.Is-queue equality-with-J Q (λ _ → ↑ _ ⊤) ℓ ⦄
  ⦃ is-queue-with-map :
      ∀ {ℓ₁ ℓ₂} →
      Queue.Is-queue-with-map equality-with-J Q ℓ₁ ℓ₂ ⦄
  where

open Queue equality-with-J
open import Queue.Truncated eq as Q using (Queue)

open import Bijection equality-with-J using (_↔_)
open import Erased.Cubical eq hiding (map)
open import H-level.Closure equality-with-J
open import List equality-with-J as L hiding (map)
open import Maybe equality-with-J
open import Monad equality-with-J hiding (map)
import Nat equality-with-J as Nat

private

  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A         : Type a
    xs        : List A

  module N = Q.Non-indexed

instance

  -- Instances.

  Queue-is-queue : Is-queue (Queue Q) Very-stableᴱ-≡ ℓ
  Queue-is-queue .Is-queue.to-List             = Q.to-List
  Queue-is-queue .Is-queue.from-List           = Q.from-List
  Queue-is-queue .Is-queue.to-List-from-List   = _↔_.right-inverse-of
                                                   (Q.Queue↔List _) _
  Queue-is-queue .Is-queue.enqueue             = N.enqueue
  Queue-is-queue .Is-queue.to-List-enqueue {q} = N.to-List-enqueue q
  Queue-is-queue .Is-queue.dequeue             = N.dequeue
  Queue-is-queue .Is-queue.to-List-dequeue {q} = N.to-List-dequeue q
  Queue-is-queue .Is-queue.dequeue⁻¹           = N.dequeue⁻¹
  Queue-is-queue .Is-queue.to-List-dequeue⁻¹   = N.to-List-dequeue⁻¹

  Queue-is-queue-with-map : Is-queue-with-map (Queue Q) ℓ₁ ℓ₂
  Queue-is-queue-with-map .Is-queue-with-map.map             = N.map
  Queue-is-queue-with-map .Is-queue-with-map.to-List-map {q} =
    N.to-List-map q

  Queue-is-queue-with-unique-representations :
    Is-queue-with-unique-representations (Queue Q) ℓ
  Queue-is-queue-with-unique-representations
    .Is-queue-with-unique-representations.from-List-to-List =
    _↔_.left-inverse-of (Q.Queue↔List _) _

------------------------------------------------------------------------
-- Some examples

private

  ns       = Very-stable→Very-stableᴱ 1 $
             Decidable-equality→Very-stable-≡ Nat._≟_
  dequeue′ = dequeue ns
  to-List′ = to-List ns
  empty′   = empty ⦂ Queue Q ℕ

  example₁ : map suc (enqueue 3 empty) ≡ enqueue 4 empty′
  example₁ = _↔_.to Q.≡-for-indices↔≡ [ refl _ ]

  example₂ : dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty))) ≡
             just (10 , enqueue 6 empty)
  example₂ =
    dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))  ≡⟨ cong dequeue′
                                                              (_↔_.to
                                                                 (Q.≡-for-indices↔≡
                                                                    {xs = map _ (enqueue _ (enqueue _ empty))}
                                                                    {ys = cons _ _})
                                                                 [ refl _ ]) ⟩
    dequeue′ (cons 10 (enqueue 6 empty))                 ≡⟨ _↔_.right-inverse-of (Queue↔Maybe[×Queue] _) _ ⟩∎
    just (10 , enqueue 6 empty)                          ∎

  example₃ :
    (do x , q ← dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        return (enqueue (3 * x) q)) ≡
    just (enqueue 30 (enqueue 6 empty))
  example₃ =
    (do x , q ← dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        return (enqueue (3 * x) q ⦂ Queue Q ℕ))                      ≡⟨ cong (_>>= λ (_ , q) → return (enqueue _ q)) example₂ ⟩

    (do x , q ← just (10 , enqueue 6 empty)
        return (enqueue (3 * x) (q ⦂ Queue Q ℕ)))                    ≡⟨⟩

    just (enqueue 30 (enqueue 6 empty))                              ∎

  example₄ :
    (do x , q ← dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        let q = enqueue (3 * x) q
        return (to-List′ q)) ≡
    just (6 ∷ 30 ∷ [])
  example₄ =
    (do x , q ← dequeue′ (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        return (to-List′ (enqueue (3 * x) q)))                       ≡⟨ cong (_>>= λ (_ , q) → return (to-List′ (enqueue _ q))) example₂ ⟩

    (do x , q ← just (10 , enqueue 6 empty)
        return (to-List′ (enqueue (3 * x) (q ⦂ Queue Q ℕ))))         ≡⟨⟩

    just (to-List′ (enqueue 30 (enqueue 6 empty)))                   ≡⟨ cong just $ to-List-foldl-enqueue-empty _ ⟩∎

    just (6 ∷ 30 ∷ [])                                               ∎

  example₅ :
    ∀ {xs} →
    dequeue′ (from-List (1 ∷ 2 ∷ 3 ∷ xs)) ≡
    just (1 , from-List (2 ∷ 3 ∷ xs))
  example₅ {xs} =
    dequeue′ (from-List (1 ∷ 2 ∷ 3 ∷ xs))       ≡⟨ cong dequeue′ (_↔_.to (Q.≡-for-indices↔≡ {xs = from-List _} {ys = cons _ _}) [ refl _ ]) ⟩
    dequeue′ (cons 1 (from-List (2 ∷ 3 ∷ xs)))  ≡⟨ _↔_.right-inverse-of (Queue↔Maybe[×Queue] _) _ ⟩∎
    just (1 , from-List (2 ∷ 3 ∷ xs))           ∎

  example₆ :
    foldr enqueue empty′ (3 ∷ 2 ∷ 1 ∷ []) ≡
    from-List (1 ∷ 2 ∷ 3 ∷ [])
  example₆ = _↔_.to Q.≡-for-indices↔≡ [ refl _ ]
