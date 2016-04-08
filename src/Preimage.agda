------------------------------------------------------------------------
-- Preimages
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module Preimage
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection hiding (id; _∘_)
open Derived-definitions-and-properties eq
open import H-level eq as H-level
open import Injection eq hiding (id; _∘_)
open import Logical-equivalence using (module _⇔_)
open import Prelude
open import Surjection eq hiding (id; _∘_)

-- The preimage of y under f is denoted by f ⁻¹ y.

infix 5 _⁻¹_

_⁻¹_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Set (a ⊔ b)
f ⁻¹ y = ∃ λ x → f x ≡ y

-- Preimages under the identity function are contractible. (Note that
-- Singleton x is equal to id ⁻¹ x.)

id⁻¹-contractible : ∀ {a} {A : Set a} (y : A) →
                    Contractible (id ⁻¹ y)
id⁻¹-contractible = singleton-contractible

-- _⁻¹_ respects extensional equality of functions.

respects-extensional-equality :
  ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {y} →
  (∀ x → f x ≡ g x) → (f ⁻¹ y) ↔ (g ⁻¹ y)
respects-extensional-equality {f = f} {g} {y} f≡g = record
  { surjection = record
    { logical-equivalence = record
      { to   = to′
      ; from = from′
      }
    ; right-inverse-of = right-inverse-of
    }
  ; left-inverse-of = left-inverse-of
  }
  where
  to′ : f ⁻¹ y → g ⁻¹ y
  to′ (x , fx≡y) = x , (
    g x  ≡⟨ sym $ f≡g x ⟩
    f x  ≡⟨ fx≡y ⟩∎
    y    ∎)

  from′ : g ⁻¹ y → f ⁻¹ y
  from′ (x , gx≡y) = x , (
    f x  ≡⟨ f≡g x ⟩
    g x  ≡⟨ gx≡y ⟩∎
    y    ∎)

  abstract
    right-inverse-of : ∀ p → to′ (from′ p) ≡ p
    right-inverse-of = λ g⁻¹y → cong (_,_ (proj₁ g⁻¹y)) (
      let p = f≡g (proj₁ g⁻¹y); q = proj₂ g⁻¹y in
      trans (sym p) (trans p q)  ≡⟨ sym $ trans-assoc _ _ _ ⟩
      trans (trans (sym p) p) q  ≡⟨ cong (λ p → trans p q) (trans-symˡ _) ⟩
      trans (refl _) q           ≡⟨ trans-reflˡ _ ⟩∎
      q                          ∎)

    left-inverse-of : ∀ p → from′ (to′ p) ≡ p
    left-inverse-of = λ f⁻¹y → cong (_,_ (proj₁ f⁻¹y))
      let p = f≡g (proj₁ f⁻¹y); q = proj₂ f⁻¹y in
      trans p (trans (sym p) q)  ≡⟨ sym $ trans-assoc _ _ _ ⟩
      trans (trans p (sym p)) q  ≡⟨ cong (λ p → trans p q) (trans-symʳ _) ⟩
      trans (refl _) q           ≡⟨ trans-reflˡ _ ⟩∎
      q                          ∎

-- Split surjections can be lifted to preimages.

lift-surjection :
  ∀ {a b} {A : Set a} {B : Set b} (A↠B : A ↠ B) → let open _↠_ A↠B in
  ∀ {y} → (from ∘ to ⁻¹ y) ↠ (from ⁻¹ y)
lift-surjection {A = A} {B} A↠B {y} = record
  { logical-equivalence = record
    { to   = drop-∘
    ; from = add-∘
    }
  ; right-inverse-of = right-inv
  }
  where
  open _↠_ A↠B

  -- Given a preimage under (f ∘ g) a preimage under f can be
  -- constructed.

  drop-∘ : (from ∘ to) ⁻¹ y → from ⁻¹ y
  drop-∘ = Σ-map to id

  -- If f is a left inverse of g then the other direction also
  -- holds.

  abstract
    add-∘-lemma : ∀ {x} → from x ≡ y → from (to (from x)) ≡ y
    add-∘-lemma {x} from-x≡y =
      from (to (from x))  ≡⟨ cong from (right-inverse-of x) ⟩
      from x              ≡⟨ from-x≡y ⟩∎
      y                   ∎

  add-∘ : from ⁻¹ y → (from ∘ to) ⁻¹ y
  add-∘ (x , from-x≡y) = (from x , add-∘-lemma from-x≡y)

  abstract

    -- add-∘ is a right inverse of drop-∘.

    right-inv : (from⁻¹y : from ⁻¹ y) → drop-∘ (add-∘ from⁻¹y) ≡ from⁻¹y
    right-inv (x , from-x≡y) =
        (to (from x) , trans (cong from (right-inverse-of x)) from-x≡y)  ≡⟨ sym $ lemma (right-inverse-of x) from-x≡y ⟩∎
        (x           , from-x≡y)                                         ∎
      where
      lemma : ∀ {x y z} {f : B → A}
              (y≡x : y ≡ x) (p : f x ≡ z) →
              _≡_ {A = f ⁻¹ z} (x , p) (y , trans (cong f y≡x) p)
      lemma {z = z} {f} = elim
        (λ {y x} y≡x → (p : f x ≡ z) →
           _≡_ {A = f ⁻¹ z} (x , p) (y , trans (cong f y≡x) p))
        (λ x p → cong (_,_ x) (
           p                          ≡⟨ sym $ trans-reflˡ _ ⟩
           trans (refl (f x)) p       ≡⟨ cong (λ q → trans q p) (sym (cong-refl f)) ⟩∎
           trans (cong f (refl x)) p  ∎))

-- A consequence of the lemmas above is that preimages under a
-- bijection are contractible.

bijection⁻¹-contractible :
  ∀ {a b} {A : Set a} {B : Set b} (A↔B : A ↔ B) → let open _↔_ A↔B in
  ∀ y → Contractible (to ⁻¹ y)
bijection⁻¹-contractible A↔B =
  H-level.respects-surjection surj 0 ∘ id⁻¹-contractible
  where
  open _↔_ (Bijection.inverse A↔B)

  surj : ∀ {y} → id ⁻¹ y ↠ from ⁻¹ y
  surj {y} =
    id ⁻¹ y         ↠⟨ _↔_.surjection $
                         respects-extensional-equality (sym ∘ left-inverse-of) ⟩
    from ∘ to ⁻¹ y  ↠⟨ lift-surjection surjection ⟩□
    from ⁻¹ y       □

abstract

  -- Preimages under an injection into a set are propositional.

  injection⁻¹-propositional :
    ∀ {a b} {A : Set a} {B : Set b} (A↣B : A ↣ B) → let open _↣_ A↣B in
    Is-set B →
    ∀ y → Is-proposition (to ⁻¹ y)
  injection⁻¹-propositional A↣B B-set y =
    _⇔_.from propositional⇔irrelevant λ { (x₁ , tox₁≡y) (x₂ , tox₂≡y) →
      Σ-≡,≡→≡ (injective (to x₁  ≡⟨ tox₁≡y ⟩
                          y      ≡⟨ sym tox₂≡y ⟩∎
                          to x₂  ∎))
              (subst (λ x → to x ≡ y)
                     (injective (trans tox₁≡y (sym tox₂≡y)))
                     tox₁≡y                                   ≡⟨ _⇔_.to set⇔UIP B-set _ _ ⟩∎
               tox₂≡y                                         ∎) }
    where
    open _↣_ A↣B
