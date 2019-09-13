------------------------------------------------------------------------
-- Truncated queues: any two queues representing the same sequence are
-- equal, and things are set up so that at compile-time (but not at
-- run-time) some queue operations compute in roughly the same way as
-- the corresponding list operations
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Queue.Truncated
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Erased.Cubical eq
open import Erased.Cubical.Singleton eq
open import Function-universe eq as F hiding (id; _∘_)
open import List eq as L hiding (map)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
import Queue eq as Q
open import Sum eq
open import Surjection eq using (_↠_)
open import Tactic.By.Parametrised eq

private
  variable
    a b     : Level
    A B     : Set a
    p q x   : A
    f       : A → B
    xs      : List A
    s s₁ s₂ : Very-stable-≡ A

------------------------------------------------------------------------
-- Queues

-- The queue type family is parametrised.

module _
  -- The underlying queue type family.
  (Q : ∀ {ℓ} → @0 Set ℓ → Set ℓ)

  -- Note that the predicate is required to be trivial. Perhaps the
  -- code could be made more general, but I have not found a use for
  -- such generality.
  ⦃ is-queue : ∀ {ℓ} → Q.Is-queue Q (λ _ → ↑ _ ⊤) ℓ ⦄
  where

  abstract

    -- Queues indexed by corresponding lists, and truncated so that
    -- any two queues that stand for the same list are seen as equal.
    --
    -- The type is abstract to ensure that a change to a different
    -- underlying queue type family does not break code that uses this
    -- module.
    --
    -- Ulf Norell suggested to me that I could use parametrisation
    -- instead of abstract. (Because if the underlying queue type
    -- family is a parameter, then the underlying queues do not
    -- compute.) I decided to use both. (Because I want to have the
    -- flexibility that comes with parametrisation, but I do not want
    -- to force users to work in a parametrised setting.)

    Queue_⟪_⟫ : {@0 A : Set a} → @0 List A → Set a
    Queue_⟪_⟫ {A = A} xs =
      ∥ (∃ λ (q : Q A) → Erased (Q.to-List _ q ≡ xs)) ∥

  -- Queues.

  Queue : Set a → Set a
  Queue A = ∃ λ (xs : Erased (List A)) → Queue_⟪_⟫ (erased xs)

-- The remainder of the code uses an implicit underlying queue type
-- family parameter, and an extra instance argument.

module _
  {Q : ∀ {ℓ} → @0 Set ℓ → Set ℓ}
  ⦃ is-queue : ∀ {ℓ} → Q.Is-queue Q (λ _ → ↑ _ ⊤) ℓ ⦄
  ⦃ is-queue-with-map : ∀ {ℓ₁ ℓ₂} → Q.Is-queue-with-map Q ℓ₁ ℓ₂ ⦄
  where

  abstract

    -- Queue Q ⟪ xs ⟫ is a proposition.

    Queue-⟪⟫-propositional :
      {@0 xs : List A} →
      Is-proposition (Queue Q ⟪ xs ⟫)
    Queue-⟪⟫-propositional = truncation-is-proposition

  -- Returns the (erased) index.

  @0 ⌊_⌋ : Queue Q A → List A
  ⌊_⌋ = erased ∘ proj₁

  -- There is a bijection between equality of two values of type
  -- Queue Q A and erased equality of the corresponding list indices.

  ≡-for-indices↔≡ :
    {xs ys : Queue Q A} →
    Erased (⌊ xs ⌋ ≡ ⌊ ys ⌋) ↔ xs ≡ ys
  ≡-for-indices↔≡ {xs = xs} {ys = ys} =
    Erased (⌊ xs ⌋ ≡ ⌊ ys ⌋)  ↝⟨ Erased-≡↔[]≡[] ⟩
    proj₁ xs ≡ proj₁ ys       ↝⟨ ignore-propositional-component Queue-⟪⟫-propositional ⟩□
    xs ≡ ys                   □

  -- If a queue equality holds under the (non-dependent) assumption
  -- that equality is very stable for the carrier type, then it also
  -- holds without this assumption.
  --
  -- For an example of a lemma which has this kind of assumption, see
  -- Queue.from-List≡foldl-enqueue-empty.

  strengthen-queue-equality :
    {q₁ q₂ : Queue Q A} → (Very-stable-≡ A → q₁ ≡ q₂) → q₁ ≡ q₂
  strengthen-queue-equality {q₁ = q₁} {q₂ = q₂} eq =
    _↔_.to ≡-for-indices↔≡
      [ ⌊ q₁ ⌋  ≡⟨ cong ⌊_⌋ (eq (erased Erased-Very-stable)) ⟩∎
        ⌊ q₂ ⌋  ∎
      ]

------------------------------------------------------------------------
-- Conversion functions

  mutual

    abstract

      -- The right-to-left direction of Queue-⟪⟫↔Σ-List (defined
      -- below). Note that there is no assumption of stability.

      Σ-List→Queue-⟪⟫ :
        {@0 ys : List A} →
        (∃ λ xs → Erased (xs ≡ ys)) → Queue Q ⟪ ys ⟫
      Σ-List→Queue-⟪⟫ = _  -- Agda can infer the definition.

    -- If ys : List A and equality is very stable for A, then
    -- Queue Q ⟪ ys ⟫ is isomorphic to the type of lists equal (with
    -- erased equality proofs) to ys.
    --
    -- Note that equality is very stable for A if A has decidable
    -- equality.

    Queue-⟪⟫↔Σ-List :
      {@0 ys : List A} →
      Very-stable-≡ A →
      Queue Q ⟪ ys ⟫ ↔ ∃ λ xs → Erased (xs ≡ ys)
    Queue-⟪⟫↔Σ-List {ys = ys} s = Bijection.with-other-inverse
      Queue-⟪⟫↔Σ-List′
      Σ-List→Queue-⟪⟫
      (λ _ → from-Queue-⟪⟫↔Σ-List′)
      where
      abstract

        Queue-⟪⟫↔Σ-List′ : Queue Q ⟪ ys ⟫ ↔ ∃ λ xs → Erased (xs ≡ ys)
        Queue-⟪⟫↔Σ-List′ = ↠→↔Erased-singleton
          (Q.Queue↠List _)
          (Very-stable-≡-List s)

        from-Queue-⟪⟫↔Σ-List′ :
          _≡_ {A = Queue Q ⟪ ys ⟫}
              (_↔_.from Queue-⟪⟫↔Σ-List′ p)
              (Σ-List→Queue-⟪⟫ p)
        from-Queue-⟪⟫↔Σ-List′ = refl _

  -- If equality is very stable for A, then Queue Q A is isomorphic to
  -- List A.

  Queue↔List : Very-stable-≡ A → Queue Q A ↔ List A
  Queue↔List {A = A} s =
    Queue Q A                                                        ↔⟨⟩
    (∃ λ (xs : Erased (List A)) → Queue Q ⟪ erased xs ⟫)             ↝⟨ (∃-cong λ _ → Queue-⟪⟫↔Σ-List s) ⟩
    (∃ λ (xs : Erased (List A)) → ∃ λ ys → Erased (ys ≡ erased xs))  ↝⟨ Σ-Erased-Erased-singleton↔ ⟩□
    List A                                                           □

  mutual

    -- The right-to-left direction of Queue↔List. (Note that equality
    -- is not required to be very stable for the carrier type.)

    from-List : List A → Queue Q A
    from-List = _  -- Agda can infer the definition.

    _ : _↔_.from (Queue↔List s) ≡ from-List
    _ = refl _

  -- The forward direction of Queue↔List s.

  to-List : Very-stable-≡ A → Queue Q A → List A
  to-List s = _↔_.to (Queue↔List s)

  abstract

    private

      -- The function to-List converts the queue representation to a
      -- list.

      to-List-, :
        ∀ {A : Set a} {s : Very-stable-≡ A} {xs q p} →
        to-List s ([ xs ] , ∣ q , p ∣) ≡ Q.to-List _ q
      to-List-, = refl _

    -- The function to-List returns the index.

    @0 ≡⌊⌋ : to-List s q ≡ ⌊ q ⌋
    ≡⌊⌋ {s = s} {q = q} =
      to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡
        (Q.Queue↠List _) (Very-stable-≡-List s) q

  -- Queue Q A is isomorphic to List A in an erased context. The
  -- forward direction of this isomorphism returns the index directly.

  @0 Queue↔Listⁱ : Queue Q A ↔ List A
  Queue↔Listⁱ {A = A} =
    Queue Q A                                             ↔⟨⟩
    (∃ λ (xs : Erased (List A)) → Queue Q ⟪ erased xs ⟫)  ↝⟨ drop-⊤-right (λ _ → _⇔_.to contractible⇔↔⊤ $
                                                             propositional⇒inhabited⇒contractible Queue-⟪⟫-propositional $
                                                             _↔_.from (Queue-⟪⟫↔Σ-List (erased Erased-Very-stable)) (_ , [ refl _ ])) ⟩
    Erased (List A)                                       ↝⟨ Very-stable→Stable $ erased Erased-Very-stable ⟩□
    List A                                                □

  private

    to-Queue↔Listⁱ-, : _↔_.to Queue↔Listⁱ q ≡ ⌊ q ⌋
    to-Queue↔Listⁱ-, = refl _

  -- The forward directions of Queue↔List and Queue↔Listⁱ match.

  @0 to-Queue↔List : _↔_.to (Queue↔List s) q ≡ _↔_.to Queue↔Listⁱ q
  to-Queue↔List = ≡⌊⌋

  -- Variants of Queue↔List and Queue↔Listⁱ.

  Maybe[×Queue]↔List :
    Very-stable-≡ A →
    Maybe (A × Queue Q A) ↔ List A
  Maybe[×Queue]↔List {A = A} s =
    Maybe (A × Queue Q A)  ↝⟨ F.id ⊎-cong F.id ×-cong Queue↔List s ⟩
    Maybe (A × List A)     ↝⟨ inverse List↔Maybe[×List] ⟩□
    List A                 □

  @0 Maybe[×Queue]↔Listⁱ :
    Maybe (A × Queue Q A) ↔ List A
  Maybe[×Queue]↔Listⁱ {A = A} =
    Maybe (A × Queue Q A)  ↝⟨ F.id ⊎-cong F.id ×-cong Queue↔Listⁱ ⟩
    Maybe (A × List A)     ↝⟨ inverse List↔Maybe[×List] ⟩□
    List A                 □

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

  -- A lemma that can be used to prove "to-List lemmas".

  ⌊⌋≡→to-List≡ :
    Erased (⌊ q ⌋ ≡ xs) →
    to-List s q ≡ xs
  ⌊⌋≡→to-List≡ {q = q} {xs = xs} {s = s} eq =
    to-List s q               ≡⟨ cong (to-List _) (_↔_.to ≡-for-indices↔≡ eq) ⟩
    to-List s (from-List xs)  ≡⟨ _↔_.right-inverse-of (Queue↔List _) _ ⟩∎
    xs                        ∎

------------------------------------------------------------------------
-- Some queue operations, implemented for Queue ⟪_⟫

  module Indexed where

    abstract

      private

        -- A helper function that can be used to define unary
        -- functions on queues.

        unary :
          {@0 A : Set a} {@0 B : Set b}
          {@0 xs : List A} {@0 f : List A → List B}
          (g : Q A → Q B) →
          @0 (∀ {q} → Q.to-List _ (g q) ≡ f (Q.to-List _ q)) →
          Queue Q ⟪ xs ⟫ → Queue Q ⟪ f xs ⟫
        unary {xs = xs} {f = f} g hyp = Trunc.rec
          truncation-is-proposition
          (uncurry λ q p →
             ∣ g q
             , [ Q.to-List _ (g q)  ≡⟨ hyp ⟩
                 f (Q.to-List _ q)  ≡⟨ cong f (erased p) ⟩∎
                 f xs               ∎
               ]
             ∣)

      -- Enqueues an element.

      enqueue :
        {@0 xs : List A}
        (x : A) → Queue Q ⟪ xs ⟫ → Queue Q ⟪ xs ++ x ∷ [] ⟫
      enqueue x = unary (Q.enqueue x) Q.to-List-enqueue

      -- A map function.

      map :
        {@0 xs : List A} →
        (f : A → B) → Queue Q ⟪ xs ⟫ → Queue Q ⟪ L.map f xs ⟫
      map f = unary (Q.map f) Q.to-List-map

    -- The result of trying to dequeue an element from an indexed
    -- queue.
    --
    -- TODO: Perhaps it makes sense to make Q an explicit argument of
    -- this definition.

    Result-⟪_⟫ : {A : Set a} → @0 List A → Set a
    Result-⟪_⟫ {A = A} xs =
      ∃ λ (q : Maybe (A × Queue Q A)) →
        Erased (_↔_.to Maybe[×Queue]↔Listⁱ q ≡ xs)

    -- If equality is very stable for A, then Result-⟪ xs ⟫ is a
    -- proposition for lists xs of type List A.

    Result-⟪⟫-propositional :
      {@0 xs : List A} →
      Very-stable-≡ A →
      Is-proposition Result-⟪ xs ⟫
    Result-⟪⟫-propositional {A = A} {xs = xs} s =
                                            $⟨ erased-singleton-with-erased-center-propositional (Very-stable-≡-List s) ⟩
      Is-proposition (Erased-singleton xs)  ↝⟨ H-level-cong _ 1 (inverse lemma) ⦂ (_ → _) ⟩□
      Is-proposition Result-⟪ xs ⟫          □
      where
      lemma : _ ↔ _
      lemma =
        Result-⟪ xs ⟫                                       ↔⟨⟩

        (∃ λ (ys : Maybe (A × Queue Q A)) →
           Erased (_↔_.to Maybe[×Queue]↔Listⁱ ys ≡ xs))     ↝⟨ ∃-cong (λ ys → Erased-cong (≡⇒↝ _ $ cong (_≡ xs) $ sym $
                                                               to-Maybe[×Queue]↔List ys)) ⟩
        (∃ λ (ys : Maybe (A × Queue Q A)) →
           Erased (_↔_.to (Maybe[×Queue]↔List s) ys ≡ xs))  ↝⟨ Σ-cong (Maybe[×Queue]↔List s) (λ _ → F.id) ⟩

        (∃ λ (ys : List A) → Erased (ys ≡ xs))              ↔⟨⟩

        Erased-singleton xs                                 □

    abstract

      -- Dequeuing.

      dequeue :
        {@0 xs : List A} →
        Very-stable-≡ A →
        Queue Q ⟪ xs ⟫ →
        Result-⟪ xs ⟫
      dequeue {xs = xs} s = Trunc.rec
        (Result-⟪⟫-propositional s)
        (λ (q , [ eq ]) →

             ⊎-map id (Σ-map id λ q → _ , ∣ q , [ refl _ ] ∣)
               (Q.dequeue _ q)

           , [ _↔_.to Maybe[×Queue]↔Listⁱ
                 (⊎-map id (Σ-map id (λ q → _ , ∣ q , [ refl _ ] ∣))
                    (Q.dequeue _ q))                                      ≡⟨⟩

               _↔_.from List↔Maybe[×List]
                 ⟨ ⊎-map id (Σ-map id (_↔_.to Queue↔Listⁱ))
                     (⊎-map id (Σ-map id (λ q → _ , ∣ q , [ refl _ ] ∣))
                        (Q.dequeue _ q)) ⟩                                ≡⟨ ⟨by⟩ 8 (sym $ ⊎-map-∘ (Q.dequeue _ q)) ⟩

               _↔_.from List↔Maybe[×List]
                 ⟨ ⊎-map id (Σ-map id (Q.to-List _)) (Q.dequeue _ q) ⟩    ≡⟨ ⟨by⟩ 8 (Q.to-List-dequeue {q = q}) ⟩

               _↔_.from List↔Maybe[×List]
                 (_↔_.to List↔Maybe[×List] (Q.to-List _ q))               ≡⟨ _↔_.left-inverse-of List↔Maybe[×List] _ ⟩

               Q.to-List _ q                                              ≡⟨ eq ⟩∎

               xs                                                         ∎
             ])

      -- The inverse of the dequeue operation. This operation does not
      -- depend on stability.

      dequeue⁻¹ :
        {@0 xs : List A} →
        Result-⟪ xs ⟫ → Queue Q ⟪ xs ⟫
      dequeue⁻¹ {xs = xs} (nothing , eq) =
        ∣ Q.empty
        , [ Q.to-List _ (Q.empty ⦂ Q _)  ≡⟨ Q.to-List-empty ⟩
            []                           ≡⟨ erased eq ⟩∎
            xs                           ∎
          ]
        ∣
      dequeue⁻¹ {xs = xs} (just (x , ys , q) , eq) =
        ∥∥-map (Σ-map (Q.cons x)
                      (λ {q′} → Erased-cong λ eq′ →
                                  Q.to-List _ (Q.cons x q′)  ≡⟨ Q.to-List-cons ⟩
                                  x ∷ Q.to-List _ q′         ≡⟨ cong (x ∷_) eq′ ⟩
                                  x ∷ erased ys              ≡⟨ erased eq ⟩∎
                                  xs                         ∎))
               q

    -- The dequeue and dequeue⁻¹ operations are inverses.

    Queue-⟪⟫↔Result-⟪⟫ :
      {@0 xs : List A} →
      Very-stable-≡ A →
      Queue Q ⟪ xs ⟫ ↔ Result-⟪ xs ⟫
    Queue-⟪⟫↔Result-⟪⟫ s = record
      { surjection = record
        { logical-equivalence = record
          { to   = dequeue s
          ; from = dequeue⁻¹
          }
        ; right-inverse-of = λ _ → Result-⟪⟫-propositional s _ _
        }
      ; left-inverse-of = λ _ → Queue-⟪⟫-propositional _ _
      }

------------------------------------------------------------------------
-- Some queue operations, implemented for Queue

  -- Note that none of these operations are abstract.

  module Non-indexed where

    -- Enqueues an element.

    enqueue : A → Queue Q A → Queue Q A
    enqueue x = Σ-map _ (Indexed.enqueue x)

    to-List-enqueue : to-List s (enqueue x q) ≡ to-List s q ++ x ∷ []
    to-List-enqueue {s = s} {x = x} {q = q} = ⌊⌋≡→to-List≡
      [ ⌊ q ⌋ ++ x ∷ []        ≡⟨ cong (_++ _) $ sym ≡⌊⌋ ⟩∎
        to-List s q ++ x ∷ []  ∎
      ]

    -- A map function.

    map : (A → B) → Queue Q A → Queue Q B
    map f = Σ-map _ (Indexed.map f)

    to-List-map : to-List s₁ (map f q) ≡ L.map f (to-List s₂ q)
    to-List-map {f = f} {q = q} {s₂ = s₂} = ⌊⌋≡→to-List≡
      [ L.map f ⌊ q ⌋           ≡⟨ cong (L.map f) $ sym ≡⌊⌋ ⟩∎
        L.map f (to-List s₂ q)  ∎
      ]

    private

      -- A variant of the result of the dequeue operation.

      Result : Set a → Set a
      Result A =
        ∃ λ (xs : Erased (List A)) → Indexed.Result-⟪ erased xs ⟫

      -- Conversion lemmas for Result.

      Result↠Maybe[×Queue] : Result A ↠ Maybe (A × Queue Q A)
      Result↠Maybe[×Queue] = record
        { logical-equivalence = record
          { to   = proj₁ ∘ proj₂
          ; from = λ q → _ , q , [ refl _ ]
          }
        ; right-inverse-of = refl
        }

      Result↔Maybe[×Queue] :
        Very-stable-≡ A →
        Result A ↔ Maybe (A × Queue Q A)
      Result↔Maybe[×Queue] s = record
        { surjection      = Result↠Maybe[×Queue]
        ; left-inverse-of = λ r →               $⟨ from∘to r ⟩
            Erased (⌊ from (to r) ⌋ʳ ≡ ⌊ r ⌋ʳ)  ↝⟨ Erased-≡↔[]≡[] ⟩
            proj₁ (from (to r)) ≡ proj₁ r       ↝⟨ ignore-propositional-component (Indexed.Result-⟪⟫-propositional s) ⟩□
            from (to r) ≡ r                     □
        }
        where
        open _↠_ Result↠Maybe[×Queue]

        @0 ⌊_⌋ʳ : Result A → List A
        ⌊_⌋ʳ = erased ∘ proj₁

        from∘to : ∀ r → Erased (⌊ from (to r) ⌋ʳ ≡ ⌊ r ⌋ʳ)
        from∘to (_ , _ , eq) = eq

    -- Queue Q A is isomorphic to Maybe (A × Queue Q A), assuming
    -- that equality is very stable for A.

    Queue↔Maybe[×Queue] :
      Very-stable-≡ A →
      Queue Q A ↔ Maybe (A × Queue Q A)
    Queue↔Maybe[×Queue] {A = A} s =
      Queue Q A              ↝⟨ ∃-cong (λ _ → Indexed.Queue-⟪⟫↔Result-⟪⟫ s) ⟩
      Result A               ↝⟨ Result↔Maybe[×Queue] s ⟩□
      Maybe (A × Queue Q A)  □

    mutual

      -- The inverse of the dequeue operation. This operation does not
      -- depend on stability.

      dequeue⁻¹ : Maybe (A × Queue Q A) → Queue Q A
      dequeue⁻¹ q = _  -- Agda can infer the definition.

      _ : _↔_.from (Queue↔Maybe[×Queue] s) ≡ dequeue⁻¹
      _ = refl _

    to-List-dequeue⁻¹ :
      to-List s (dequeue⁻¹ x) ≡
      _↔_.from List↔Maybe[×List] (⊎-map id (Σ-map id (to-List s)) x)
    to-List-dequeue⁻¹ {x = nothing} = ⌊⌋≡→to-List≡ [ refl _ ]

    to-List-dequeue⁻¹ {s = s} {x = just (x , q)} = ⌊⌋≡→to-List≡
      [ x ∷ ⌊ q ⌋        ≡⟨ cong (_ ∷_) $ sym ≡⌊⌋ ⟩∎
        x ∷ to-List s q  ∎
      ]

    -- Dequeues an element, if possible.

    dequeue : Very-stable-≡ A → Queue Q A → Maybe (A × Queue Q A)
    dequeue s = _↔_.to (Queue↔Maybe[×Queue] s)

    to-List-dequeue :
      ⊎-map id (Σ-map id (to-List s)) (dequeue s q) ≡
      _↔_.to List↔Maybe[×List] (to-List s q)
    to-List-dequeue {s = s} {q = q} =
      ⊎-map id (Σ-map id (to-List s)) (dequeue s q)                   ≡⟨ _↔_.to (from≡↔≡to (from-isomorphism List↔Maybe[×List])) $
                                                                         sym to-List-dequeue⁻¹ ⟩
      _↔_.to List↔Maybe[×List] (to-List s (dequeue⁻¹ (dequeue s q)))  ≡⟨ cong (_↔_.to List↔Maybe[×List] ∘ to-List s) $
                                                                         _↔_.left-inverse-of (Queue↔Maybe[×Queue] _) _ ⟩∎
      _↔_.to List↔Maybe[×List] (to-List s q)                          ∎
