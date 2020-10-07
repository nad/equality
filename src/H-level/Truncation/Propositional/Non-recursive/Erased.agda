------------------------------------------------------------------------
-- A non-recursive variant of H-level.Truncation.Propositional.Erased
------------------------------------------------------------------------

-- The definition does use natural numbers. The code is based on van
-- Doorn's "Constructing the Propositional Truncation using
-- Non-recursive HITs".

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module H-level.Truncation.Propositional.Non-recursive.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

private
  open module PD = P.Derived-definitions-and-properties eq
    hiding (elim)

open import Prelude

open import Colimit.Sequential eq as C using (Colimit)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
import H-level.Truncation.Propositional.Erased eq as T
open import H-level.Truncation.Propositional.Non-recursive eq as N
  using (∥_∥)
open import H-level.Truncation.Propositional.One-step.Erased eq as O
  using (∥_∥¹ᴱ-out-^)

private
  variable
    a p : Level
    A   : Set a
    P   : A → Set p
    e x : A

------------------------------------------------------------------------
-- The type

-- The propositional truncation operator.

∥_∥ᴱ : Set a → Set a
∥ A ∥ᴱ = Colimit ∥ A ∥¹ᴱ-out-^ O.∣_∣

-- The point constructor.

∣_∣ : A → ∥ A ∥ᴱ
∣_∣ = C.∣_∣

-- The eliminator.

record Elim {A : Set a} (P : ∥ A ∥ᴱ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ                : ∀ x → P ∣ x ∣
    @0 is-propositionʳ : ∀ x → Is-proposition (P x)

open Elim public

elim : Elim P → (x : ∥ A ∥ᴱ) → P x
elim {A = A} {P = P} e = C.elim λ where
    .C.Elim.∣∣ʳ {n = n}      → helper n
    .C.Elim.∣∣≡∣∣ʳ {n = n} x →
      subst P (C.∣∣≡∣∣ x) (subst P (sym (C.∣∣≡∣∣ x)) (helper n x))  ≡⟨ subst-subst-sym _ _ _ ⟩∎
      helper n x                                                    ∎
  where
  module E = Elim e

  helper : ∀ n (x : ∥ A ∥¹ᴱ-out-^ n) → P C.∣ x ∣
  helper zero    = E.∣∣ʳ
  helper (suc n) = O.elim λ where
    .O.Elim.∣∣ʳ x            → subst P (sym (C.∣∣≡∣∣ x)) (helper n x)
    .O.Elim.∣∣-constantʳ _ _ → E.is-propositionʳ _ _ _

_ : elim e ∣ x ∣ ≡ e .∣∣ʳ x
_ = refl _

-- The propositional truncation operator returns propositions (in
-- erased contexts).

@0 ∥∥ᴱ-proposition : Is-proposition ∥ A ∥ᴱ
∥∥ᴱ-proposition {A = A} = elim lemma₄
  where
  lemma₀ : ∀ n (x : A) → C.∣ O.∣ x ∣-out-^ n ∣ ≡ ∣ x ∣
  lemma₀ zero    x = ∣ x ∣  ∎
  lemma₀ (suc n) x =
    C.∣ O.∣ O.∣ x ∣-out-^ n ∣ ∣  ≡⟨ C.∣∣≡∣∣ (O.∣ x ∣-out-^ n) ⟩
    C.∣ O.∣ x ∣-out-^ n ∣        ≡⟨ lemma₀ n x ⟩∎
    ∣ x ∣                        ∎

  lemma₁ : ∀ n (x : A) (y : ∥ A ∥¹ᴱ-out-^ n) → ∣ x ∣ ≡ C.∣ y ∣
  lemma₁ n x y =
    ∣ x ∣                        ≡⟨ sym (lemma₀ (suc n) x) ⟩
    C.∣ O.∣ x ∣-out-^ (suc n) ∣  ≡⟨⟩
    C.∣ O.∣ O.∣ x ∣-out-^ n ∣ ∣  ≡⟨ cong C.∣_∣ (O.∣∣-constant _ _) ⟩
    C.∣ O.∣ y ∣ ∣                ≡⟨ C.∣∣≡∣∣ y ⟩∎
    C.∣ y ∣                      ∎

  lemma₂ :
    ∀ n (x y : ∥ A ∥¹ᴱ-out-^ n) (p : x ≡ y) (q : O.∣ x ∣ ≡ O.∣ y ∣) →
    trans (C.∣∣≡∣∣ {P = ∥ A ∥¹ᴱ-out-^} x) (cong C.∣_∣ p) ≡
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

  lemma₃ : ∀ _ → C.Elim _
  lemma₃ x .C.Elim.∣∣ʳ              = lemma₁ _ x
  lemma₃ x .C.Elim.∣∣≡∣∣ʳ {n = n} y =
    subst (∣ x ∣ ≡_) (C.∣∣≡∣∣ y) (lemma₁ (suc n) x O.∣ y ∣)     ≡⟨ sym trans-subst ⟩

    trans (lemma₁ (1 + n) x O.∣ y ∣) (C.∣∣≡∣∣ y)                ≡⟨⟩

    trans (trans (sym (trans (C.∣∣≡∣∣ (O.∣ x ∣-out-^ (1 + n)))
                         (lemma₀ (1 + n) x)))
             (trans (cong C.∣_∣
                       (O.∣∣-constant
                          (O.∣ x ∣-out-^ (1 + n)) O.∣ y ∣))
                (C.∣∣≡∣∣ O.∣ y ∣)))
      (C.∣∣≡∣∣ y)                                               ≡⟨ trans (cong (λ eq → trans (trans eq
                                                                                                (trans (cong C.∣_∣ (O.∣∣-constant _ _))
                                                                                                   (C.∣∣≡∣∣ _)))
                                                                                         (C.∣∣≡∣∣ _)) $
                                                                          sym-trans _ _) $
                                                                   trans (trans-assoc _ _ _) $
                                                                   trans (trans-assoc _ _ _) $
                                                                   cong (trans (sym (lemma₀ (1 + n) _))) $
                                                                   sym $ trans-assoc _ _ _ ⟩
    trans (sym (lemma₀ (1 + n) x))
      (trans (trans (sym (C.∣∣≡∣∣ (O.∣ x ∣-out-^ (1 + n))))
                (trans (cong C.∣_∣
                          (O.∣∣-constant
                             (O.∣ x ∣-out-^ (1 + n)) O.∣ y ∣))
                   (C.∣∣≡∣∣ O.∣ y ∣)))
         (C.∣∣≡∣∣ y))                                           ≡⟨ cong (λ eq → trans (sym (lemma₀ (1 + n) _))
                                                                                  (trans (trans (sym (C.∣∣≡∣∣ _)) eq) (C.∣∣≡∣∣ _))) $ sym $
                                                                   lemma₂ _ _ _ _ _ ⟩
    trans (sym (lemma₀ (1 + n) x))
      (trans (trans (sym (C.∣∣≡∣∣ (O.∣ x ∣-out-^ (1 + n))))
                (trans (C.∣∣≡∣∣ (O.∣ x ∣-out-^ (1 + n)))
                   (cong C.∣_∣ (O.∣∣-constant _ _))))
         (C.∣∣≡∣∣ y))                                           ≡⟨ cong (λ eq → trans (sym (lemma₀ (1 + n) _)) (trans eq (C.∣∣≡∣∣ _))) $
                                                                   trans-sym-[trans] _ _ ⟩
    trans (sym (lemma₀ (1 + n) x))
      (trans (cong C.∣_∣ (O.∣∣-constant _ _)) (C.∣∣≡∣∣ y))      ≡⟨⟩

    lemma₁ n x y                                                ∎

  lemma₄ : Elim _
  lemma₄ .is-propositionʳ = Π≡-proposition ext
  lemma₄ .∣∣ʳ x           = C.elim (lemma₃ x)

------------------------------------------------------------------------
-- Some conversion functions

-- ∥_∥ᴱ is pointwise equivalent to T.∥_∥ᴱ.

∥∥ᴱ≃∥∥ᴱ : ∥ A ∥ᴱ ≃ T.∥ A ∥ᴱ
∥∥ᴱ≃∥∥ᴱ = Eq.↔→≃
  (elim λ where
     .∣∣ʳ               → T.∣_∣
     .is-propositionʳ _ → T.truncation-is-proposition)
  (T.rec λ where
     .T.∣∣ʳ                        → ∣_∣
     .T.truncation-is-propositionʳ → ∥∥ᴱ-proposition)
  (T.elim λ where
     .T.∣∣ʳ _                        → refl _
     .T.truncation-is-propositionʳ _ →
       mono₁ 1 T.truncation-is-proposition)
  (elim λ where
     .∣∣ʳ _             → refl _
     .is-propositionʳ _ → mono₁ 1 ∥∥ᴱ-proposition)

-- ∥ A ∥ᴱ implies ∥ A ∥.

∥∥ᴱ→∥∥ : ∥ A ∥ᴱ → ∥ A ∥
∥∥ᴱ→∥∥ = elim λ where
  .∣∣ʳ               → N.∣_∣
  .is-propositionʳ _ → N.∥∥-proposition

-- In erased contexts ∥ A ∥ᴱ and ∥ A ∥ are equivalent.

@0 ∥∥ᴱ≃∥∥ : ∥ A ∥ᴱ ≃ ∥ A ∥
∥∥ᴱ≃∥∥ = Eq.↔→≃
  ∥∥ᴱ→∥∥
  (N.elim e₁)
  (N.elim e₂)
  (elim λ where
     .Elim.∣∣ʳ _             → refl _
     .Elim.is-propositionʳ _ → mono₁ 1 ∥∥ᴱ-proposition)
  where
  e₁ : N.Elim _
  e₁ .N.Elim.∣∣ʳ               = ∣_∣
  e₁ .N.Elim.is-propositionʳ _ = ∥∥ᴱ-proposition

  e₂ : N.Elim _
  e₂ .N.Elim.∣∣ʳ _             = refl _
  e₂ .N.Elim.is-propositionʳ _ = mono₁ 1 N.∥∥-proposition
