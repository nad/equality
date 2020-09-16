------------------------------------------------------------------------
-- A definition of the propositional truncation operator that does not
-- use recursive higher inductive types
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- The definition does use natural numbers. The code is based on van
-- Doorn's "Constructing the Propositional Truncation using
-- Non-recursive HITs".

import Equality.Path as P

module H-level.Truncation.Propositional.Non-recursive
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

private
  open module PD = P.Derived-definitions-and-properties eq
    hiding (elim)

open import Prelude

open import Colimit.Sequential eq as C using (Colimit)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import H-level.Closure equality-with-J
import H-level.Truncation.Propositional eq as T
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹; ∥_∥¹-out-^; ∣_∣-out-^)

private
  variable
    a p : Level
    A   : Set a
    P   : A → Set p
    e x : A

-- The propositional truncation operator.

∥_∥ : Set a → Set a
∥ A ∥ = Colimit ∥ A ∥¹-out-^ O.∣_∣

-- The point constructor.

∣_∣ : A → ∥ A ∥
∣_∣ = C.∣_∣

-- The eliminator.

record Elim {A : Set a} (P : ∥ A ∥ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ             : ∀ x → P ∣ x ∣
    is-propositionʳ : ∀ x → Is-proposition (P x)

open Elim public

elim : Elim P → (x : ∥ A ∥) → P x
elim {A = A} {P = P} e = C.elim λ where
    .C.Elim.∣∣ʳ {n = n} → helper n
    .C.Elim.∣∣≡∣∣ʳ _    → E.is-propositionʳ _ _ _
  where
  module E = Elim e

  helper : ∀ n (x : ∥ A ∥¹-out-^ n) → P C.∣ x ∣
  helper zero    = E.∣∣ʳ
  helper (suc n) = O.elim λ where
    .O.Elim.∣∣ʳ x            → subst P (sym (C.∣∣≡∣∣ x)) (helper n x)
    .O.Elim.∣∣-constantʳ _ _ → E.is-propositionʳ _ _ _

_ : elim e ∣ x ∣ ≡ e .∣∣ʳ x
_ = refl _

-- The propositional truncation operator returns propositions.

∥∥-proposition : Is-proposition ∥ A ∥
∥∥-proposition {A = A} = elim λ where
    .is-propositionʳ → Π≡-proposition ext
    .∣∣ʳ x → C.elim λ where
      .C.Elim.∣∣ʳ              → lemma₁ _ x
      .C.Elim.∣∣≡∣∣ʳ {n = n} y →
        subst (∣ x ∣ ≡_) (C.∣∣≡∣∣ y) (lemma₁ (suc n) x O.∣ y ∣)   ≡⟨ sym trans-subst ⟩

        trans (lemma₁ (1 + n) x O.∣ y ∣) (C.∣∣≡∣∣ y)              ≡⟨⟩

        trans (trans (sym (trans (C.∣∣≡∣∣ (∣ x ∣-out-^ (1 + n)))
                             (lemma₀ (1 + n) x)))
                 (trans (cong C.∣_∣
                           (O.∣∣-constant
                              (∣ x ∣-out-^ (1 + n)) O.∣ y ∣))
                    (C.∣∣≡∣∣ O.∣ y ∣)))
          (C.∣∣≡∣∣ y)                                             ≡⟨ trans (cong (λ eq → trans (trans eq
                                                                                                  (trans (cong C.∣_∣ (O.∣∣-constant _ _))
                                                                                                     (C.∣∣≡∣∣ _)))
                                                                                           (C.∣∣≡∣∣ _)) $
                                                                            sym-trans _ _) $
                                                                     trans (trans-assoc _ _ _) $
                                                                     trans (trans-assoc _ _ _) $
                                                                     cong (trans (sym (lemma₀ (1 + n) _))) $
                                                                     sym $ trans-assoc _ _ _ ⟩
        trans (sym (lemma₀ (1 + n) x))
          (trans (trans (sym (C.∣∣≡∣∣ (∣ x ∣-out-^ (1 + n))))
                    (trans (cong C.∣_∣
                              (O.∣∣-constant
                                 (∣ x ∣-out-^ (1 + n)) O.∣ y ∣))
                       (C.∣∣≡∣∣ O.∣ y ∣)))
             (C.∣∣≡∣∣ y))                                         ≡⟨ cong (λ eq → trans (sym (lemma₀ (1 + n) _))
                                                                                    (trans (trans (sym (C.∣∣≡∣∣ _)) eq) (C.∣∣≡∣∣ _))) $ sym $
                                                                     lemma₂ _ _ _ _ _ ⟩
        trans (sym (lemma₀ (1 + n) x))
          (trans (trans (sym (C.∣∣≡∣∣ (∣ x ∣-out-^ (1 + n))))
                    (trans (C.∣∣≡∣∣ (∣ x ∣-out-^ (1 + n)))
                       (cong C.∣_∣ (O.∣∣-constant _ _))))
             (C.∣∣≡∣∣ y))                                         ≡⟨ cong (λ eq → trans (sym (lemma₀ (1 + n) _)) (trans eq (C.∣∣≡∣∣ _))) $
                                                                     trans-sym-[trans] _ _ ⟩
        trans (sym (lemma₀ (1 + n) x))
          (trans (cong C.∣_∣ (O.∣∣-constant _ _)) (C.∣∣≡∣∣ y))    ≡⟨⟩

        lemma₁ n x y                                              ∎
  where
  lemma₀ : ∀ n (x : A) → C.∣ ∣ x ∣-out-^ n ∣ ≡ ∣ x ∣
  lemma₀ zero    x = ∣ x ∣  ∎
  lemma₀ (suc n) x =
    C.∣ O.∣ ∣ x ∣-out-^ n ∣ ∣  ≡⟨ C.∣∣≡∣∣ (∣ x ∣-out-^ n) ⟩
    C.∣ ∣ x ∣-out-^ n ∣        ≡⟨ lemma₀ n x ⟩∎
    ∣ x ∣                      ∎

  lemma₁ : ∀ n (x : A) (y : ∥ A ∥¹-out-^ n) → ∣ x ∣ ≡ C.∣ y ∣
  lemma₁ n x y =
    ∣ x ∣                      ≡⟨ sym (lemma₀ (suc n) x) ⟩
    C.∣ ∣ x ∣-out-^ (suc n) ∣  ≡⟨⟩
    C.∣ O.∣ ∣ x ∣-out-^ n ∣ ∣  ≡⟨ cong C.∣_∣ (O.∣∣-constant _ _) ⟩
    C.∣ O.∣ y ∣ ∣              ≡⟨ C.∣∣≡∣∣ y ⟩∎
    C.∣ y ∣                    ∎

  lemma₂ :
    ∀ n (x y : ∥ A ∥¹-out-^ n) (p : x ≡ y) (q : O.∣ x ∣ ≡ O.∣ y ∣) →
    trans (C.∣∣≡∣∣ {P = ∥ A ∥¹-out-^} x) (cong C.∣_∣ p) ≡
    trans (cong C.∣_∣ q) (C.∣∣≡∣∣ y)
  lemma₂ n x y p q =
    trans (C.∣∣≡∣∣ x) (cong C.∣_∣ p)                        ≡⟨ PD.elim
                                                                 (λ {x y} p → trans (C.∣∣≡∣∣ x) (cong C.∣_∣ p) ≡
                                                                              trans (cong C.∣_∣ (cong O.∣_∣ p)) (C.∣∣≡∣∣ y))
                                                                 (λ x →
      trans (C.∣∣≡∣∣ x) (cong C.∣_∣ (refl _))                       ≡⟨ cong (trans _) $ cong-refl _ ⟩
      trans (C.∣∣≡∣∣ x) (refl _)                                    ≡⟨ trans-reflʳ _ ⟩
      C.∣∣≡∣∣ x                                                     ≡⟨ sym $ trans-reflˡ _ ⟩
      trans (refl _) (C.∣∣≡∣∣ x)                                    ≡⟨ cong (flip trans _) $ sym $
                                                                       trans (cong (cong C.∣_∣) $ cong-refl _) $
                                                                       cong-refl _ ⟩∎
      trans (cong C.∣_∣ (cong O.∣_∣ (refl _))) (C.∣∣≡∣∣ x)          ∎)
                                                                 p ⟩

    trans (cong C.∣_∣ (cong O.∣_∣ p)) (C.∣∣≡∣∣ y)           ≡⟨ cong (flip trans _) $
                                                               cong-preserves-Constant
                                                                 (λ u v →
      C.∣ u ∣                                                       ≡⟨ sym (C.∣∣≡∣∣ u) ⟩
      C.∣ O.∣ u ∣ ∣                                                 ≡⟨ cong C.∣_∣ (O.∣∣-constant _ _) ⟩
      C.∣ O.∣ v ∣ ∣                                                 ≡⟨ C.∣∣≡∣∣ v ⟩∎
      C.∣ v ∣                                                       ∎)
                                                                 _ _ ⟩∎
    trans (cong C.∣_∣ q) (C.∣∣≡∣∣ y)                        ∎

-- ∥_∥ is pointwise equivalent to T.∥_∥.

∥∥≃∥∥ : ∥ A ∥ ≃ T.∥ A ∥
∥∥≃∥∥ {A = A} = Eq.⇔→≃
  ∥∥-proposition
  T.truncation-is-proposition
  (elim λ where
     .∣∣ʳ               → T.∣_∣
     .is-propositionʳ _ → T.truncation-is-proposition)
  (T.rec ∥∥-proposition ∣_∣)
