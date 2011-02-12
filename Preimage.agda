------------------------------------------------------------------------
-- Preimages
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

module Preimage where

open import Bijection hiding (id; _∘_)
open import Equality
import Equality.Groupoid as EG
private module G {A : Set} = EG.Groupoid (EG.groupoid A)
import Equality.Tactic as Tactic; open Tactic.Eq
open import H-level
open import Prelude
open import Surjection hiding (id; _∘_)

-- The preimage of y under f is denoted by f ⁻¹ y.

infix 5 _⁻¹_

_⁻¹_ : {A B : Set} → (A → B) → B → Set
f ⁻¹ y = ∃ λ x → f x ≡ y

-- Preimages under the identity function are contractible. (Note that
-- Singleton x is equal to id ⁻¹ x.)

id⁻¹-contractible : ∀ {A} (y : A) → Contractible (id ⁻¹ y)
id⁻¹-contractible = singleton-contractible

-- _⁻¹_ respects extensional equality of functions.

respects-extensional-equality :
  ∀ {A B} {f g : A → B} {y} →
  (∀ x → f x ≡ g x) → (f ⁻¹ y) ↔ (g ⁻¹ y)
respects-extensional-equality {f = f} {g} {y} f≡g = record
  { surjection = record
    { equivalence = record
      { to   = Σ-map id to₂
      ; from = Σ-map id from₂
      }
    ; right-inverse-of = right-inverse-of
    }
  ; left-inverse-of = left-inverse-of
  }
  where
  abstract
    to₂ : ∀ {x} → f x ≡ y → g x ≡ y
    to₂ {x} fx≡y = g x  ≡⟨ sym $ f≡g x ⟩
                   f x  ≡⟨ fx≡y ⟩∎
                   y    ∎

    from₂ : ∀ {x} → g x ≡ y → f x ≡ y
    from₂ {x} gx≡y = f x  ≡⟨ f≡g x ⟩
                     g x  ≡⟨ gx≡y ⟩∎
                     y    ∎

    right-inverse-of = λ g⁻¹y → cong (_,_ (proj₁ g⁻¹y)) (
      let p = f≡g (proj₁ g⁻¹y); q = proj₂ g⁻¹y in
      trans (sym p) (trans p q)  ≡⟨ Tactic.prove (Trans (Sym (Lift p)) (Trans (Lift p) (Lift q)))
                                                 (Trans (Trans (Sym (Lift p)) (Lift p)) (Lift q))
                                                 (refl _) ⟩
      trans (trans (sym p) p) q  ≡⟨ cong (λ p → trans p q) (G.right-inverse _) ⟩
      trans (refl _) q           ≡⟨ Tactic.prove (Trans Refl (Lift q)) (Lift q) (refl _) ⟩∎
      q                          ∎)

    left-inverse-of = λ f⁻¹y → cong (_,_ (proj₁ f⁻¹y))
      let p = f≡g (proj₁ f⁻¹y); q = proj₂ f⁻¹y in
      trans p (trans (sym p) q)  ≡⟨ Tactic.prove (Trans (Lift p) (Trans (Sym (Lift p)) (Lift q)))
                                                 (Trans (Trans (Lift p) (Sym (Lift p))) (Lift q))
                                                 (refl _) ⟩
      trans (trans p (sym p)) q  ≡⟨ cong (λ p → trans p q) (G.left-inverse _) ⟩
      trans (refl _) q           ≡⟨ Tactic.prove (Trans Refl (Lift q)) (Lift q) (refl _) ⟩∎
      q                          ∎

-- Surjections can be lifted to preimages.

lift-surjection :
  ∀ {A B} (A↠B : A ↠ B) → let open _↠_ A↠B in
  ∀ {y} → (from ∘ to ⁻¹ y) ↠ (from ⁻¹ y)
lift-surjection A↠B {y} = record
  { equivalence = record
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
      lemma : ∀ {A B} {x y z} {f : A → B}
              (y≡x : y ≡ x) (p : f x ≡ z) →
              _≡_ {A = f ⁻¹ z} (x , p) (y , trans (cong f y≡x) p)
      lemma {z = z} {f} = elim
        (λ {y x} y≡x → (p : f x ≡ z) →
           _≡_ {A = f ⁻¹ z} (x , p) (y , trans (cong f y≡x) p))
        (λ x p → cong (_,_ x) (Tactic.prove (Lift p)
                                            (Trans (Cong f Refl) (Lift p))
                                            (refl _)))

-- A consequence of the lemmas above is that preimages under a
-- bijection are contractible.

bijection⁻¹-contractible :
  ∀ {A B} (A↔B : A ↔ B) → let open _↔_ A↔B in
  ∀ y → Contractible (to ⁻¹ y)
bijection⁻¹-contractible A↔B =
  H-level.respects-surjection surj 0 ∘ id⁻¹-contractible
  where
  open _↔_ (Bijection.inverse A↔B)

  surj : ∀ {y} → id ⁻¹ y ↠ from ⁻¹ y
  surj {y} =
    id ⁻¹ y         ↠⟨ _↔_.surjection $
                         respects-extensional-equality (sym ∘ left-inverse-of) ⟩
    from ∘ to ⁻¹ y  ↠⟨ lift-surjection surjection ⟩∎
    from ⁻¹ y       ∎
