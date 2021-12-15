------------------------------------------------------------------------
-- Joins
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Join {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import Pushout eq as PO

private
  variable
    a b ℓ : Level
    A B   : Type a

------------------------------------------------------------------------
-- The join type former

-- Joins.
--
-- This definition is taken from the HoTT book.

Join : Type a → Type b → Type (a ⊔ b)
Join A B = Pushout (record
  { Middle = A × B
  ; left   = proj₁
  ; right  = proj₂
  })

------------------------------------------------------------------------
-- Some simple properties

-- Join is symmetric.

Join-symmetric : Join A B ≃ Join B A
Join-symmetric = Eq.↔→≃
  to
  to
  to-to
  to-to
  where
  to : Join A B → Join B A
  to = rec inr inl (sym ∘ glue ∘ swap)

  to-to : (x : Join A B) → to (to x) ≡ x
  to-to =
    PO.elim _ (λ _ → refl _) (λ _ → refl _)
      (λ p →
         subst (λ x → to (to x) ≡ x) (glue p) (refl _)         ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans (sym (cong (to ∘ to) (glue p)))
           (trans (refl _) (cong id (glue p)))                 ≡⟨ cong₂ (trans ∘ sym)
                                                                    (sym $ cong-∘ _ _ _)
                                                                    (trans (trans-reflˡ _) $
                                                                     sym $ cong-id _) ⟩

         trans (sym (cong to (cong to (glue p)))) (glue p)     ≡⟨ cong (flip trans _) $ cong (sym ∘ cong to) rec-glue ⟩

         trans (sym (cong to (sym (glue (swap p))))) (glue p)  ≡⟨ cong (flip trans _) $ cong sym $ cong-sym _ _ ⟩

         trans (sym (sym (cong to (glue (swap p))))) (glue p)  ≡⟨ cong (flip trans _) $ sym-sym _ ⟩

         trans (cong to (glue (swap p))) (glue p)              ≡⟨ cong (flip trans _) rec-glue ⟩

         trans (sym (glue (swap (swap p)))) (glue p)           ≡⟨⟩

         trans (sym (glue p)) (glue p)                         ≡⟨ trans-symˡ _ ⟩∎

         refl _                                                ∎)

-- The empty type is a right identity for Join.

Join-⊥ʳ : Join A (⊥ {ℓ = ℓ}) ≃ A
Join-⊥ʳ = Eq.↔→≃
  (rec id ⊥-elim (λ { (_ , ()) }))
  inl
  refl
  (PO.elim _ (λ _ → refl _) (λ ()) (λ { (_ , ()) }))

-- The empty type is a left identity for Join.

Join-⊥ˡ : Join (⊥ {ℓ = ℓ}) A ≃ A
Join-⊥ˡ {A = A} =
  Join ⊥ A  ↝⟨ Join-symmetric ⟩
  Join A ⊥  ↝⟨ Join-⊥ʳ ⟩□
  A         □
