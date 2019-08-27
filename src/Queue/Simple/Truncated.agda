------------------------------------------------------------------------
-- Truncated simple queues: any two queues representing the same
-- sequence are equal, and things are set up so that at compile-time
-- (but not at run-time) some queue operations compute in roughly the
-- same way as the corresponding list operations
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Queue.Simple.Truncated
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Erased eq
open import Function-universe eq as F hiding (id; _∘_)
open import List eq as L hiding (map)
open import Maybe eq
open import Monad eq hiding (map)
import Nat eq as Nat
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
import Queue.Simple eq as Q
open import Sum eq
open import Surjection eq using (_↠_)
open import Tactic.By.Parametrised eq

private
  variable
    a   : Level
    A B : Set a
    p q : A
    xs  : List A
    s   : Very-stable-≡ A

------------------------------------------------------------------------
-- Queues

abstract

  -- Queues indexed by corresponding lists, and truncated so that any
  -- two queues that stand for the same list are seen as equal.
  --
  -- The type is abstract to ensure that a change to a different
  -- representation (for instance banker's queues) does not break code
  -- that uses this module.

  Queue-[_] : {@0 A : Set a} → @0 List A → Set a
  Queue-[_] {A = A} xs =
    ∥ (∃ λ (q : Q.Queue A) → Erased (Q.to-List q ≡ xs)) ∥

  -- Queue-[ xs ] is a proposition.

  Queue-[]-propositional :
    {@0 xs : List A} →
    Is-proposition Queue-[ xs ]
  Queue-[]-propositional = truncation-is-proposition

-- Queues.

Queue : Set a → Set a
Queue A = ∃ λ (xs : Erased (List A)) → Queue-[ erased xs ]

-- Returns the (erased) index.

@0 ⌊_⌋ : Queue A → List A
⌊_⌋ = erased ∘ proj₁

-- There is a bijection between equality of two values of type Queue A
-- and erased equality of the corresponding list indices.

≡-for-indices↔≡ :
  {xs ys : Queue A} →
  Erased (⌊ xs ⌋ ≡ ⌊ ys ⌋) ↔ xs ≡ ys
≡-for-indices↔≡ {xs = xs} {ys = ys} =
  Erased (⌊ xs ⌋ ≡ ⌊ ys ⌋)  ↝⟨ Erased-≡↔[]≡[] ⟩
  proj₁ xs ≡ proj₁ ys       ↝⟨ ignore-propositional-component Queue-[]-propositional ⟩□
  xs ≡ ys                   □

------------------------------------------------------------------------
-- Conversion functions

abstract

  -- If ys : List A and equality is very stable for A, then
  -- Queue-[ ys ] is isomorphic to the type of lists equal (with
  -- erased equality proofs) to ys.
  --
  -- Note that equality is very stable for A if A comes with decidable
  -- equality.

  Queue-[]↔Σ-List :
    {@0 ys : List A} →
    Very-stable-≡ A →
    Queue-[ ys ] ↔ ∃ λ xs → Erased (xs ≡ ys)
  Queue-[]↔Σ-List s = ↠→↔Erased-singleton
    Q.Queue↠List
    (Very-stable-≡-List s)

  -- The right-to-left direction of the previous lemma does not depend
  -- on the assumption of stability.

  Σ-List→Queue-[] :
    {@0 ys : List A} →
    (∃ λ xs → Erased (xs ≡ ys)) → Queue-[ ys ]
  Σ-List→Queue-[] = ↠→Erased-singleton→ Q.Queue↠List

  from-Queue-[]↔Σ-List :
    _↔_.from (Queue-[]↔Σ-List s) p ≡ Σ-List→Queue-[] p
  from-Queue-[]↔Σ-List = refl _

-- If equality is very stable for A, then Queue A is isomorphic to
-- List A.

Queue↔List : Very-stable-≡ A → Queue A ↔ List A
Queue↔List {A = A} s =
  Queue A                                                          ↔⟨⟩
  (∃ λ (xs : Erased (List A)) → Queue-[ erased xs ])               ↝⟨ (∃-cong λ _ → Queue-[]↔Σ-List s) ⟩
  (∃ λ (xs : Erased (List A)) → ∃ λ ys → Erased (ys ≡ erased xs))  ↝⟨ Σ-Erased-Erased-singleton↔ ⟩□
  List A                                                           □

-- The forward direction of Queue↔List s. (Equality is required to be
-- very stable for the carrier type.)

to-List : Very-stable-≡ A → Queue A → List A
to-List s = _↔_.to (Queue↔List s)

abstract

  private

    -- The function to-List converts the queue representation to a
    -- list.

    to-List-, : to-List s ([ xs ] , ∣ q , p ∣) ≡ Q.to-List q
    to-List-, = refl _

-- Converts lists to queues. (Equality is not required to be very
-- stable for the carrier type.)

from-List : List A → Queue A
from-List {A = A} =
  List A                                                           ↔⟨ inverse Σ-Erased-Erased-singleton↔ ⟩
  (∃ λ (xs : Erased (List A)) → ∃ λ ys → Erased (ys ≡ erased xs))  ↝⟨ (∃-cong λ _ → Σ-List→Queue-[]) ⟩
  (∃ λ (xs : Erased (List A)) → Queue-[ erased xs ])               ↔⟨⟩
  Queue A                                                          □

-- The function from-List matches the right-to-left direction of
-- Queue↔List s.

from-Queue↔List : _↔_.from (Queue↔List s) xs ≡ from-List xs
from-Queue↔List {s = s} {xs = xs} =
  Σ-map id (_↔_.from (Queue-[]↔Σ-List s))
    (_↔_.from Σ-Erased-Erased-singleton↔ xs)                         ≡⟨ cong (_ ,_) from-Queue-[]↔Σ-List ⟩∎

  Σ-map id Σ-List→Queue-[] (_↔_.from Σ-Erased-Erased-singleton↔ xs)  ∎

abstract

  -- The forward direction of Queue↔List s returns the index.

  @0 ≡⌊⌋ : to-List s q ≡ ⌊ q ⌋
  ≡⌊⌋ {s = s} {q = q} =
    to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡
      Q.Queue↠List (Very-stable-≡-List s) q

-- Queue A is isomorphic to List A in an erased context. The forward
-- direction of this isomorphism returns the index directly.

@0 Queue↔Listⁱ : Queue A ↔ List A
Queue↔Listⁱ {A = A} =
  Queue A                                             ↔⟨⟩
  (∃ λ (xs : Erased (List A)) → Queue-[ erased xs ])  ↝⟨ drop-⊤-right (λ _ → _⇔_.to contractible⇔↔⊤ $
                                                         propositional⇒inhabited⇒contractible Queue-[]-propositional $
                                                         _↔_.from (Queue-[]↔Σ-List (erased Erased-Very-stable)) (_ , [ refl _ ])) ⟩
  Erased (List A)                                     ↝⟨ Very-stable→Stable $ erased Erased-Very-stable ⟩□
  List A                                              □

private

  to-Queue↔Listⁱ-, : _↔_.to Queue↔Listⁱ q ≡ ⌊ q ⌋
  to-Queue↔Listⁱ-, = refl _

-- The forward directions of Queue↔List and Queue↔Listⁱ match.

@0 to-Queue↔List : _↔_.to (Queue↔List s) q ≡ _↔_.to Queue↔Listⁱ q
to-Queue↔List = ≡⌊⌋

-- Variants of Queue↔List and Queue↔Listⁱ.

Maybe[×Queue]↔List :
  Very-stable-≡ A →
  Maybe (A × Queue A) ↔ List A
Maybe[×Queue]↔List {A = A} s =
  Maybe (A × Queue A)  ↝⟨ F.id ⊎-cong F.id ×-cong Queue↔List s ⟩
  Maybe (A × List A)   ↝⟨ inverse List↔Maybe[×List] ⟩□
  List A               □

@0 Maybe[×Queue]↔Listⁱ :
  Maybe (A × Queue A) ↔ List A
Maybe[×Queue]↔Listⁱ {A = A} =
  Maybe (A × Queue A)  ↝⟨ F.id ⊎-cong F.id ×-cong Queue↔Listⁱ ⟩
  Maybe (A × List A)   ↝⟨ inverse List↔Maybe[×List] ⟩□
  List A               □

@0 to-Maybe[×Queue]↔List :
  ∀ xs →
  _↔_.to (Maybe[×Queue]↔List s) xs ≡
  _↔_.to Maybe[×Queue]↔Listⁱ xs
to-Maybe[×Queue]↔List {s = s} xs =
  _↔_.from List↔Maybe[×List]
    (⊎-map id (Σ-map id (_↔_.to (Queue↔List s))) xs)  ≡⟨ cong (λ f → _↔_.from List↔Maybe[×List] (⊎-map id (Σ-map id f) xs)) (⟨ext⟩ λ _ →
                                                         to-Queue↔List) ⟩∎
  _↔_.from List↔Maybe[×List]
    (⊎-map id (Σ-map id (_↔_.to Queue↔Listⁱ)) xs)     ∎

------------------------------------------------------------------------
-- Some queue operations, implemented for Queue-[_]

module Indexed where

  abstract

    private

      -- A helper function that can be used to define unary functions
      -- on queues.

      unary :
        {@0 xs : List A} {@0 f : List A → List B}
        (g : Q.Queue A → Q.Queue B) →
        @0 (∀ q → Q.to-List (g q) ≡ f (Q.to-List q)) →
        Queue-[ xs ] → Queue-[ f xs ]
      unary {xs = xs} {f = f} g hyp = Trunc.rec
        truncation-is-proposition
        (uncurry λ q p →
           ∣ g q
           , [ Q.to-List (g q)  ≡⟨ hyp _ ⟩
               f (Q.to-List q)  ≡⟨ cong f (erased p) ⟩∎
               f xs             ∎
             ]
           ∣)

    -- An empty queue.

    empty : Queue-[ [] {A = A} ]
    empty = ∣ Q.empty , [ refl _ ] ∣

    -- Enqueues an element.

    enqueue :
      {@0 xs : List A}
      (x : A) → Queue-[ xs ] → Queue-[ xs ++ x ∷ [] ]
    enqueue x = unary (Q.enqueue x) Q.to-List-enqueue

    -- A map function.

    map :
      {@0 xs : List A} →
      (f : A → B) → Queue-[ xs ] → Queue-[ L.map f xs ]
    map f = unary (Q.map f) Q.to-List-map

  -- The result of trying to dequeue an element from an indexed queue.

  Result-[_] : {A : Set a} → @0 List A → Set a
  Result-[_] {A = A} xs =
    ∃ λ (q : Maybe (A × Queue A)) →
      Erased (_↔_.to Maybe[×Queue]↔Listⁱ q ≡ xs)

  -- If equality is very stable for A, then Result-[ xs ] is a
  -- proposition for lists xs of type List A.

  Result-[]-propositional :
    {@0 xs : List A} →
    Very-stable-≡ A →
    Is-proposition Result-[ xs ]
  Result-[]-propositional {A = A} {xs = xs} s =
                                          $⟨ erased-singleton-with-erased-center-propositional (Very-stable-≡-List s) ⟩
    Is-proposition (Erased-singleton xs)  ↝⟨ H-level-cong _ 1 (inverse lemma) ⦂ (_ → _) ⟩□
    Is-proposition Result-[ xs ]          □
    where
    lemma : _ ↔ _
    lemma =
      Result-[ xs ]                                       ↔⟨⟩

      (∃ λ (ys : Maybe (A × Queue A)) →
         Erased (_↔_.to Maybe[×Queue]↔Listⁱ ys ≡ xs))     ↝⟨ ∃-cong (λ ys → Erased-cong (≡⇒↝ _ $ cong (_≡ xs) $ sym $
                                                             to-Maybe[×Queue]↔List ys)) ⟩
      (∃ λ (ys : Maybe (A × Queue A)) →
         Erased (_↔_.to (Maybe[×Queue]↔List s) ys ≡ xs))  ↝⟨ Σ-cong (Maybe[×Queue]↔List s) (λ _ → F.id) ⟩

      (∃ λ (ys : List A) → Erased (ys ≡ xs))              ↔⟨⟩

      Erased-singleton xs                                 □

  abstract

    -- Dequeuing.

    dequeue :
      {@0 xs : List A} →
      Very-stable-≡ A →
      Queue-[ xs ] →
      Result-[ xs ]
    dequeue {xs = xs} s = Trunc.rec
      (Result-[]-propositional s)
      (λ (q , [ eq ]) →

           ⊎-map id (Σ-map id λ q → _ , ∣ q , [ refl _ ] ∣)
             (Q.dequeue q)

         , [ _↔_.to Maybe[×Queue]↔Listⁱ
               (⊎-map id (Σ-map id (λ q → _ , ∣ q , [ refl _ ] ∣))
                  (Q.dequeue q))                                        ≡⟨⟩

             _↔_.from List↔Maybe[×List]
               ⟨ ⊎-map id (Σ-map id (_↔_.to Queue↔Listⁱ))
                   (⊎-map id (Σ-map id (λ q → _ , ∣ q , [ refl _ ] ∣))
                      (Q.dequeue q)) ⟩                                  ≡⟨ ⟨by⟩ 5 (⊎-map-∘ (Q.dequeue q)) ⟩

             _↔_.from List↔Maybe[×List]
               ⟨ ⊎-map id (Σ-map id Q.to-List) (Q.dequeue q) ⟩          ≡⟨ ⟨by⟩ 5 (Q.to-List-dequeue q) ⟩

             _↔_.from List↔Maybe[×List]
               (_↔_.to List↔Maybe[×List] (Q.to-List q))                 ≡⟨ _↔_.left-inverse-of List↔Maybe[×List] _ ⟩

             Q.to-List q                                                ≡⟨ eq ⟩∎

             xs                                                         ∎
           ])

    -- The inverse of the dequeue operation. This operation does not
    -- depend on stability.

    dequeue⁻¹ :
      {@0 xs : List A} →
      Result-[ xs ] → Queue-[ xs ]
    dequeue⁻¹           (nothing , eq)           = ∣ Q.empty , eq ∣
    dequeue⁻¹ {xs = xs} (just (x , ys , q) , eq) =
      ∥∥-map (Σ-map (Q.cons x)
                    (λ {q′} → Erased-cong λ eq′ →
                                Q.to-List (Q.cons x q′)  ≡⟨ cong (x ∷_) eq′ ⟩
                                x ∷ erased ys            ≡⟨ erased eq ⟩∎
                                xs                       ∎))
             q

  -- The dequeue and dequeue⁻¹ operations are inverses.

  Queue-[]↔Result-[] :
    {@0 xs : List A} →
    Very-stable-≡ A →
    Queue-[ xs ] ↔ Result-[ xs ]
  Queue-[]↔Result-[] s = record
    { surjection = record
      { logical-equivalence = record
        { to   = dequeue s
        ; from = dequeue⁻¹
        }
      ; right-inverse-of = λ _ → Result-[]-propositional s _ _
      }
    ; left-inverse-of = λ _ → Queue-[]-propositional _ _
    }

------------------------------------------------------------------------
-- Some queue operations, implemented for Queue

-- Note that none of these operations are abstract.

module Non-indexed where

  -- An empty queue.

  empty : Queue A
  empty = _ , Indexed.empty

  -- Enqueues an element.

  enqueue : A → Queue A → Queue A
  enqueue x = Σ-map _ (Indexed.enqueue x)

  -- A map function.

  map : (A → B) → Queue A → Queue B
  map f = Σ-map _ (Indexed.map f)

  private

    -- A variant of the result of the dequeue operation.

    Result : Set a → Set a
    Result A =
      ∃ λ (xs : Erased (List A)) → Indexed.Result-[ erased xs ]

    -- Conversion lemmas for Result.

    Result↠Maybe[×Queue] : Result A ↠ Maybe (A × Queue A)
    Result↠Maybe[×Queue] = record
      { logical-equivalence = record
        { to   = proj₁ ∘ proj₂
        ; from = λ q → _ , q , [ refl _ ]
        }
      ; right-inverse-of = refl
      }

    Result↔Maybe[×Queue] :
      Very-stable-≡ A →
      Result A ↔ Maybe (A × Queue A)
    Result↔Maybe[×Queue] s = record
      { surjection      = Result↠Maybe[×Queue]
      ; left-inverse-of = λ r →               $⟨ from∘to r ⟩
          Erased (⌊ from (to r) ⌋ʳ ≡ ⌊ r ⌋ʳ)  ↝⟨ Erased-≡↔[]≡[] ⟩
          proj₁ (from (to r)) ≡ proj₁ r       ↝⟨ ignore-propositional-component (Indexed.Result-[]-propositional s) ⟩□
          from (to r) ≡ r                     □
      }
      where
      open _↠_ Result↠Maybe[×Queue]

      @0 ⌊_⌋ʳ : Result A → List A
      ⌊_⌋ʳ = erased ∘ proj₁

      from∘to : ∀ r → Erased (⌊ from (to r) ⌋ʳ ≡ ⌊ r ⌋ʳ)
      from∘to (_ , _ , eq) = eq

  -- Queue A is isomorphic to Maybe (A × Queue A), assuming that
  -- equality is very stable for A.

  Queue↔Maybe[×Queue] :
    Very-stable-≡ A →
    Queue A ↔ Maybe (A × Queue A)
  Queue↔Maybe[×Queue] {A = A} s =
    Queue A              ↝⟨ ∃-cong (λ _ → Indexed.Queue-[]↔Result-[] s) ⟩
    Result A             ↝⟨ Result↔Maybe[×Queue] s ⟩□
    Maybe (A × Queue A)  □

  -- Dequeues an element, if possible.

  dequeue : Very-stable-≡ A → Queue A → Maybe (A × Queue A)
  dequeue s = _↔_.to (Queue↔Maybe[×Queue] s)

  -- The inverse of the dequeue operation. This operation does not
  -- depend on stability.

  dequeue⁻¹ : Maybe (A × Queue A) → Queue A
  dequeue⁻¹ q = _ , Indexed.dequeue⁻¹ (q , [ refl _ ])

  private

    from-Queue↔Maybe[×Queue] :
      _↔_.from (Queue↔Maybe[×Queue] s) ≡ dequeue⁻¹
    from-Queue↔Maybe[×Queue] = refl _

  -- A special case of dequeue⁻¹.

  cons : A → Queue A → Queue A
  cons = curry (dequeue⁻¹ ∘ just)

  -- The function from-List can be expressed using enqueue and empty.

  from-List≡foldl-enqueue-empty :
    from-List xs ≡ foldl (flip enqueue) empty xs
  from-List≡foldl-enqueue-empty {xs = xs} = _↔_.to ≡-for-indices↔≡
    [ ⌊ from-List xs ⌋                   ≡⟨ _↔_.right-inverse-of Queue↔Listⁱ _ ⟩
      xs                                 ≡⟨⟩
      ⌊ empty ⌋ ++ xs                    ≡⟨ lemma xs _ ⟩∎
      ⌊ foldl (flip enqueue) empty xs ⌋  ∎
    ]
    where
    @0 lemma : ∀ xs q → ⌊ q ⌋ ++ xs ≡ ⌊ foldl (flip enqueue) q xs ⌋
    lemma [] q =
      ⌊ q ⌋ ++ []  ≡⟨ ++-right-identity _ ⟩∎
      ⌊ q ⌋        ∎
    lemma (x ∷ xs) q =
      ⟨ ⌊ q ⌋ ++ x ∷ xs ⟩                        ≡⟨ ⟨by⟩ 6 (++-associative ⌊ q ⌋) ⟩
      (⌊ q ⌋ ++ x ∷ []) ++ xs                    ≡⟨⟩
      ⌊ enqueue x q ⌋ ++ xs                      ≡⟨ lemma xs _ ⟩
      ⌊ foldl (flip enqueue) (enqueue x q) xs ⌋  ≡⟨⟩
      ⌊ foldl (flip enqueue) q (x ∷ xs) ⌋        ∎

  -- A corollary.

  to-List-foldl-enqueue-empty :
    to-List s (foldl (flip enqueue) empty xs) ≡ xs
  to-List-foldl-enqueue-empty {s = s} {xs = xs} =
    to-List s ⟨ foldl (flip enqueue) empty xs ⟩  ≡⟨ ⟨by⟩ 4 from-List≡foldl-enqueue-empty ⟩
    to-List s ⟨ from-List xs ⟩                   ≡⟨ ⟨by⟩ 4 from-Queue↔List ⟩
    to-List s (_↔_.from (Queue↔List s) xs)       ≡⟨ _↔_.right-inverse-of (Queue↔List _) _ ⟩∎
    xs                                           ∎

------------------------------------------------------------------------
-- Some examples

private

  open Non-indexed

  ns = Decidable-equality→Very-stable-≡ Nat._≟_

  example₁ : map suc (enqueue 3 empty) ≡ enqueue 4 empty
  example₁ = _↔_.to ≡-for-indices↔≡ [ refl _ ]

  example₂ : dequeue ns (map (_* 2) (enqueue 3 (enqueue 5 empty))) ≡
             just (10 , enqueue 6 empty)
  example₂ =
    dequeue ns ⟨ map (_* 2) (enqueue 3 (enqueue 5 empty)) ⟩  ≡⟨ ⟨by⟩ 0 (_↔_.to ≡-for-indices↔≡ [ refl _ ]) ⟩
    ⟨ dequeue ns (cons 10 (enqueue 6 empty)) ⟩               ≡⟨ ⟨by⟩ 0 (_↔_.right-inverse-of (Queue↔Maybe[×Queue] _)) ⟩∎
    just (10 , enqueue 6 empty)                              ∎

  example₃ :
    (do x , q ← dequeue ns (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        return (enqueue (3 * x) q)) ≡
    just (enqueue 30 (enqueue 6 empty))
  example₃ =
    (do x , q ← ⟨ dequeue ns (map (_* 2) (enqueue 3 (enqueue 5 empty))) ⟩
        return (enqueue (3 * x) q))                                        ≡⟨ ⟨by⟩ 0 example₂ ⟩

    (do x , q ← just (10 , enqueue 6 empty)
        return (enqueue (3 * x) q))                                        ≡⟨⟩

    just (enqueue 30 (enqueue 6 empty))                                    ∎

  example₄ :
    (do x , q ← dequeue ns (map (_* 2) (enqueue 3 (enqueue 5 empty)))
        let q = enqueue (3 * x) q
        return (to-List ns q)) ≡
    just (6 ∷ 30 ∷ [])
  example₄ =
    (do x , q ← ⟨ dequeue ns (map (_* 2) (enqueue 3 (enqueue 5 empty))) ⟩
        let q = enqueue (3 * x) q
        return (to-List ns q))                                             ≡⟨ ⟨by⟩ 0 example₂ ⟩

    (do x , q ← just (10 , enqueue 6 empty)
        let q = enqueue (3 * x) q
        return (to-List ns q))                                             ≡⟨⟩

    just ⟨ to-List ns (enqueue 30 (enqueue 6 empty)) ⟩                     ≡⟨ ⟨by⟩ 0 to-List-foldl-enqueue-empty ⟩∎

    just (6 ∷ 30 ∷ [])                                                     ∎

  example₅ :
    dequeue ns (from-List (1 ∷ 2 ∷ 3 ∷ xs)) ≡
    just (1 , from-List (2 ∷ 3 ∷ xs))
  example₅ {xs = xs} =
    dequeue ns ⟨ from-List (1 ∷ 2 ∷ 3 ∷ xs) ⟩         ≡⟨ ⟨by⟩ 1 (_↔_.to ≡-for-indices↔≡ [ refl _ ]) ⟩
    ⟨ dequeue ns (cons 1 (from-List (2 ∷ 3 ∷ xs))) ⟩  ≡⟨ ⟨by⟩ 1 (_↔_.right-inverse-of (Queue↔Maybe[×Queue] _)) ⟩∎
    just (1 , from-List (2 ∷ 3 ∷ xs))                 ∎

  example₆ :
    foldr enqueue empty (3 ∷ 2 ∷ 1 ∷ []) ≡ from-List (1 ∷ 2 ∷ 3 ∷ [])
  example₆ = _↔_.to ≡-for-indices↔≡ [ refl _ ]
