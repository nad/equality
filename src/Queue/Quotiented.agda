------------------------------------------------------------------------
-- Quotiented queues: any two queues representing the same sequence
-- are equal
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Queue.Quotiented
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level.Closure equality-with-J
open import List equality-with-J as L hiding (map)
import Queue equality-with-J as Q
open import Quotient eq as Quotient
open import Sum equality-with-J

private
  variable
    a b             : Level
    A B             : Type a
    s s′ s₁ s₂      : Is-set A
    q q₁ q₂ x x₁ x₂ : A
    f g             : A → B
    xs              : List A

------------------------------------------------------------------------
-- Queues

-- The queue type family is parametrised.

module _
  -- The underlying queue type family.
  (Q : ∀ {ℓ} → Type ℓ → Type ℓ)

  -- Note that the predicate is required to be trivial. Perhaps the
  -- code could be made more general, but I have not found a use for
  -- such generality.
  ⦃ is-queue : ∀ {ℓ} → Q.Is-queue Q (λ _ → ↑ _ ⊤) ℓ ⦄
  where

  abstract

    private

      -- The quotienting relation: Two queues are seen as equal if
      -- they represent the same list.

      _∼_ : {A : Type a} (_ _ : Q A) → Type a
      q₁ ∼ q₂ = Q.to-List _ q₁ ≡ Q.to-List _ q₂

    -- Queues.
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

    Queue : Type a → Type a
    Queue A = Q A / _∼_

-- The remainder of the code uses an implicit underlying queue type
-- family parameter, and an extra instance argument.

module _
  {Q : ∀ {ℓ} → Type ℓ → Type ℓ}
  ⦃ is-queue : ∀ {ℓ} → Q.Is-queue Q (λ _ → ↑ _ ⊤) ℓ ⦄
  ⦃ is-queue-with-map : ∀ {ℓ₁ ℓ₂} → Q.Is-queue-with-map Q ℓ₁ ℓ₂ ⦄
  where

  abstract

    -- Queue A is a set.

    Queue-is-set : Is-set (Queue Q A)
    Queue-is-set = /-is-set

------------------------------------------------------------------------
-- Conversion functions

  abstract

    -- Converts queues to lists. (The carrier type is required to be a
    -- set.)

    to-List : Is-set A → Queue Q A → List A
    to-List s = Quotient.rec λ where
      .[]ʳ                   → Q.to-List _
      .[]-respects-relationʳ → id
      .is-setʳ               → H-level-List 0 s

    -- Converts lists to queues.

    from-List : List A → Queue Q A
    from-List = [_] ∘ Q.from-List

    -- The function from-List is a right inverse of to-List s.

    to-List-from-List : to-List s (from-List q) ≡ q
    to-List-from-List = Q.to-List-from-List {Q = Q}

    -- The function from-List is a left inverse of to-List s.

    from-List-to-List :
      (q : Queue Q A) → _≡_ {A = Queue Q A} (from-List (to-List s q)) q
    from-List-to-List = Quotient.elim-prop λ where
      .[]ʳ q → []-respects-relation (
        Q.to-List ⦃ is-queue = is-queue ⦄ _
          (Q.from-List (Q.to-List _ q))      ≡⟨ Q.to-List-from-List {Q = Q} ⟩∎

        Q.to-List _ q                        ∎)
      .is-propositionʳ _ → Queue-is-set

  -- If A is a set, then there is a bijection between Queue Q A and
  -- List A.

  Queue↔List : Is-set A → Queue Q A ↔ List A
  Queue↔List s = record
    { surjection = record
      { logical-equivalence = record
        { to   = to-List s
        ; from = from-List
        }
      ; right-inverse-of = λ _ → to-List-from-List
      }
    ; left-inverse-of = from-List-to-List
    }

------------------------------------------------------------------------
-- Queue operations

  abstract

    private

      -- Helper functions that can be used to define unary functions
      -- on queues.

      unary :
        {A : Type a} {B : Type b}
        (f : List A → List B)
        (g : Q A → Q B) →
        (∀ {q} → Q.to-List _ (g q) ≡ f (Q.to-List _ q)) →
        Queue Q A → Queue Q B
      unary f g h =
        g /-map λ q₁ q₂ q₁∼q₂ →
          Q.to-List _ (g q₁)  ≡⟨ h ⟩
          f (Q.to-List _ q₁)  ≡⟨ cong f q₁∼q₂ ⟩
          f (Q.to-List _ q₂)  ≡⟨ sym h ⟩∎
          Q.to-List _ (g q₂)  ∎

      to-List-unary :
        ∀ {h : ∀ {q} → _} q →
        to-List s₁ (unary f g (λ {q} → h {q = q}) q) ≡ f (to-List s₂ q)
      to-List-unary {s₁} {f} {g} {s₂} {h} =
        Quotient.elim-prop λ where
          .[]ʳ q →
            to-List s₁ (unary f g h [ q ])  ≡⟨⟩
            Q.to-List _ (g q)               ≡⟨ h ⟩
            f (Q.to-List _ q)               ≡⟨⟩
            f (to-List s₂ [ q ])            ∎
          .is-propositionʳ _ → H-level-List 0 s₁

      -- Generalisations of the functions above.

      unary′ :
        {A : Type a} {F : Type a → Type b} →
        (∀ {A} → Is-set A → Is-set (F A)) →
        (map : ∀ {A B} → (A → B) → F A → F B) →
        (∀ {A} {x : F A} → map id x ≡ x) →
        (∀ {A B C} {f : B → C} {g : A → B} x →
         map (f ∘ g) x ≡ map f (map g x)) →
        (f : List A → F (List B))
        (g : Q A → F (Q B)) →
        (∀ {q} → map (Q.to-List _) (g q) ≡ f (Q.to-List _ q)) →
        Is-set B →
        Queue Q A → F (Queue Q B)
      unary′ F-set map map-id map-∘ f g h s = Quotient.rec λ where
          .[]ʳ → map [_] ∘ g

          .[]-respects-relationʳ {x = q₁} {y = q₂} q₁∼q₂ → lemma₂ (
            map (to-List s) (map [_] (g q₁))  ≡⟨ sym $ map-∘ _ ⟩
            map (Q.to-List _) (g q₁)          ≡⟨ h ⟩
            f (Q.to-List _ q₁)                ≡⟨ cong f q₁∼q₂ ⟩
            f (Q.to-List _ q₂)                ≡⟨ sym h ⟩
            map (Q.to-List _) (g q₂)          ≡⟨ map-∘ _ ⟩∎
            map (to-List s) (map [_] (g q₂))  ∎)

          .is-setʳ → F-set Queue-is-set
        where
        lemma₁ : map from-List (map (to-List s) x) ≡ x
        lemma₁ {x} =
          map from-List (map (to-List s) x)  ≡⟨ sym $ map-∘ _ ⟩
          map (from-List ∘ to-List s) x      ≡⟨ cong (flip map x) $ ⟨ext⟩ $ _↔_.left-inverse-of (Queue↔List s) ⟩
          map id x                           ≡⟨ map-id ⟩∎
          x                                  ∎

        lemma₂ :
          map (to-List s) x₁ ≡ map (to-List s) x₂ →
          x₁ ≡ x₂
        lemma₂ {x₁} {x₂} eq =
          x₁                                  ≡⟨ sym lemma₁ ⟩
          map from-List (map (to-List s) x₁)  ≡⟨ cong (map from-List) eq ⟩
          map from-List (map (to-List s) x₂)  ≡⟨ lemma₁ ⟩∎
          x₂                                  ∎

      to-List-unary′ :
        {F      : Type a → Type b}
        (F-set  : ∀ {A} → Is-set A → Is-set (F A))
        (map    : ∀ {A B} → (A → B) → F A → F B)
        (map-id : ∀ {A} {x : F A} → map id x ≡ x)
        (map-∘  : ∀ {A B C} {f : B → C} {g : A → B} x →
                  map (f ∘ g) x ≡ map f (map g x))
        (f : List A → F (List B))
        (g : Q A → F (Q B))
        (h : ∀ {q} → map (Q.to-List _) (g q) ≡ f (Q.to-List _ q))
        (s : Is-set B) →
        ∀ q →
        map (to-List s) (unary′ F-set map map-id map-∘ f g h s q) ≡
        f (to-List s′ q)
      to-List-unary′ {s′} F-set map map-id map-∘ f g h s =
        Quotient.elim-prop λ where
          .[]ʳ q →
            map (to-List s)
                (unary′ F-set map map-id map-∘ f g h s [ q ])  ≡⟨⟩

            map (to-List s) (map [_] (g q))                    ≡⟨ sym $ map-∘ _ ⟩

            map (Q.to-List _) (g q)                            ≡⟨ h ⟩

            f (Q.to-List _ q)                                  ≡⟨⟩

            f (to-List s′ [ q ])                               ∎
          .is-propositionʳ _ → F-set (H-level-List 0 s)

    -- Enqueues an element.

    enqueue : A → Queue Q A → Queue Q A
    enqueue x =
      unary (_++ x ∷ []) (Q.enqueue x) (Q.to-List-enqueue {Q = Q})

    to-List-enqueue : to-List s (enqueue x q) ≡ to-List s q ++ x ∷ []
    to-List-enqueue {q} = to-List-unary q

    -- Dequeues an element, if possible. (The carrier type is required
    -- to be a set.)

    dequeue : Is-set A → Queue Q A → Maybe (A × Queue Q A)
    dequeue s = unary′
      (Maybe-closure 0 ∘ ×-closure 2 s)
      (λ f → ⊎-map id (Σ-map id f))
      ⊎-map-id
      ⊎-map-∘
      (_↔_.to List↔Maybe[×List])
      (Q.dequeue _)
      (Q.to-List-dequeue {Q = Q})
      s

    to-List-dequeue :
      ⊎-map id (Σ-map id (to-List s)) (dequeue s q) ≡
      _↔_.to List↔Maybe[×List] (to-List s q)
    to-List-dequeue {q} = to-List-unary′
      (Maybe-closure 0 ∘ ×-closure 2 _)
      (λ f → ⊎-map id (Σ-map id f))
      ⊎-map-id
      ⊎-map-∘
      _
      (Q.dequeue _)
      _
      _
      q

    -- The "inverse" of the dequeue operation.

    dequeue⁻¹ : Maybe (A × Queue Q A) → Queue Q A
    dequeue⁻¹ nothing        = [ Q.empty ]
    dequeue⁻¹ (just (x , q)) =
      unary (x ∷_) (Q.cons x) (Q.to-List-cons {Q = Q}) q

    to-List-dequeue⁻¹ :
      to-List s (dequeue⁻¹ x) ≡
      _↔_.from List↔Maybe[×List] (⊎-map id (Σ-map id (to-List s)) x)
    to-List-dequeue⁻¹ {x = nothing}      = Q.to-List-empty {Q = Q}
    to-List-dequeue⁻¹ {x = just (_ , q)} = to-List-unary q

    -- A map function.

    map : (A → B) → Queue Q A → Queue Q B
    map f = unary (L.map f) (Q.map f) (Q.to-List-map {Q = Q})

    to-List-map : to-List s₁ (map f q) ≡ L.map f (to-List s₂ q)
    to-List-map {q} = to-List-unary q
