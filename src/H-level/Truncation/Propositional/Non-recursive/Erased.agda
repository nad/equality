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

open import Colimit.Sequential.Very-erased eq as C using (Colimitᴱ)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.Non-recursive eq as N
  using (∥_∥)
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹-out-^)

private
  variable
    a p   : Level
    A     : Type a
    P     : A → Type p
    e x z : A

------------------------------------------------------------------------
-- The type

-- The propositional truncation operator.

∥_∥ᴱ : Type a → Type a
∥ A ∥ᴱ = Colimitᴱ A (∥ A ∥¹-out-^ ∘ suc) O.∣_∣ O.∣_∣

-- The point constructor.

∣_∣ : A → ∥ A ∥ᴱ
∣_∣ = C.∣_∣₀

-- The eliminator.

record Elim {A : Type a} (P : ∥ A ∥ᴱ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ                : ∀ x → P ∣ x ∣
    @0 is-propositionʳ : ∀ x → Is-proposition (P x)

open Elim public

elim : Elim P → (x : ∥ A ∥ᴱ) → P x
elim {A = A} {P = P} e = C.elim λ where
    .C.Elim.∣∣₀ʳ         → E.∣∣ʳ
    .C.Elim.∣∣₊ʳ {n = n} → helper n
    .C.Elim.∣∣₊≡∣∣₀ʳ x   →
      subst P (C.∣∣₊≡∣∣₀ x) (subst P (sym (C.∣∣₊≡∣∣₀ x)) (E.∣∣ʳ x))  ≡⟨ subst-subst-sym _ _ _ ⟩∎
      E.∣∣ʳ x                                                        ∎
    .C.Elim.∣∣₊≡∣∣₊ʳ {n = n} x →
      subst P (C.∣∣₊≡∣∣₊ x) (subst P (sym (C.∣∣₊≡∣∣₊ x)) (helper n x))  ≡⟨ subst-subst-sym _ _ _ ⟩∎
      helper n x                                                        ∎
  where
  module E = Elim e

  @0 helper : ∀ n (x : ∥ A ∥¹-out-^ (suc n)) → P C.∣ x ∣₊

  helper zero = O.elim e₀
    where
    e₀ : O.Elim _
    e₀ .O.Elim.∣∣ʳ x            = subst P (sym (C.∣∣₊≡∣∣₀ x)) (E.∣∣ʳ x)
    e₀ .O.Elim.∣∣-constantʳ _ _ = E.is-propositionʳ _ _ _

  helper (suc n) = O.elim e₊
    where
    e₊ : O.Elim _
    e₊ .O.Elim.∣∣ʳ x            = subst P (sym (C.∣∣₊≡∣∣₊ x))
                                    (helper n x)
    e₊ .O.Elim.∣∣-constantʳ _ _ = E.is-propositionʳ _ _ _

_ : elim e ∣ x ∣ ≡ e .∣∣ʳ x
_ = refl _

-- The propositional truncation operator returns propositions (in
-- erased contexts).

@0 ∥∥ᴱ-proposition : Is-proposition ∥ A ∥ᴱ
∥∥ᴱ-proposition {A = A} = elim lemma₅
  where
  lemma₀ : ∀ n (x : A) → C.∣ O.∣ x ∣-out-^ (1 + n) ∣₊ ≡ ∣ x ∣
  lemma₀ zero x =
    C.∣ O.∣ x ∣ ∣₊  ≡⟨ C.∣∣₊≡∣∣₀ x ⟩∎
    C.∣ x ∣₀        ∎
  lemma₀ (suc n) x =
    C.∣ O.∣ O.∣ x ∣-out-^ (1 + n) ∣ ∣₊  ≡⟨ C.∣∣₊≡∣∣₊ (O.∣ x ∣-out-^ (1 + n)) ⟩
    C.∣ O.∣ x ∣-out-^ (1 + n) ∣₊        ≡⟨ lemma₀ n x ⟩∎
    ∣ x ∣                               ∎

  lemma₁₀ : ∀ (x y : A) → ∣ x ∣ ≡ C.∣ y ∣₀
  lemma₁₀ x y =
    ∣ x ∣                         ≡⟨ sym (lemma₀ 0 x) ⟩
    C.∣ O.∣ x ∣-out-^ 1 ∣₊        ≡⟨⟩
    C.∣ O.∣ O.∣ x ∣-out-^ 0 ∣ ∣₊  ≡⟨ cong C.∣_∣₊ (O.∣∣-constant _ _) ⟩
    C.∣ O.∣ y ∣ ∣₊                ≡⟨ C.∣∣₊≡∣∣₀ y ⟩∎
    C.∣ y ∣₀                      ∎

  lemma₁₊ : ∀ n (x : A) (y : ∥ A ∥¹-out-^ (1 + n)) → ∣ x ∣ ≡ C.∣ y ∣₊
  lemma₁₊ n x y =
    ∣ x ∣                               ≡⟨ sym (lemma₀ (1 + n) x) ⟩
    C.∣ O.∣ x ∣-out-^ (2 + n) ∣₊        ≡⟨⟩
    C.∣ O.∣ O.∣ x ∣-out-^ (1 + n) ∣ ∣₊  ≡⟨ cong C.∣_∣₊ (O.∣∣-constant _ _) ⟩
    C.∣ O.∣ y ∣ ∣₊                      ≡⟨ C.∣∣₊≡∣∣₊ y ⟩∎
    C.∣ y ∣₊                            ∎

  lemma₂ :
    ∀ n (x y : ∥ A ∥¹-out-^ (1 + n))
    (p : x ≡ y) (q : O.∣ x ∣ ≡ O.∣ y ∣) →
    trans (C.∣∣₊≡∣∣₊ {P₊ = ∥ A ∥¹-out-^ ∘ suc} {step₀ = O.∣_∣} x)
      (cong C.∣_∣₊ p) ≡
    trans (cong C.∣_∣₊ q) (C.∣∣₊≡∣∣₊ y)
  lemma₂ n x y p q =
    trans (C.∣∣₊≡∣∣₊ x) (cong C.∣_∣₊ p)                        ≡⟨ PD.elim
                                                                    (λ {x y} p → trans (C.∣∣₊≡∣∣₊ x) (cong C.∣_∣₊ p) ≡
                                                                                 trans (cong C.∣_∣₊ (cong O.∣_∣ p)) (C.∣∣₊≡∣∣₊ y))
                                                                    (λ x →
      trans (C.∣∣₊≡∣∣₊ x) (cong C.∣_∣₊ (refl _))                       ≡⟨ cong (trans _) $ cong-refl _ ⟩
      trans (C.∣∣₊≡∣∣₊ x) (refl _)                                     ≡⟨ trans-reflʳ _ ⟩
      C.∣∣₊≡∣∣₊ x                                                      ≡⟨ sym $ trans-reflˡ _ ⟩
      trans (refl _) (C.∣∣₊≡∣∣₊ x)                                     ≡⟨ cong (flip trans _) $ sym $
                                                                          trans (cong (cong C.∣_∣₊) $ cong-refl _) $
                                                                          cong-refl _ ⟩∎
      trans (cong C.∣_∣₊ (cong O.∣_∣ (refl _))) (C.∣∣₊≡∣∣₊ x)          ∎)
                                                                    p ⟩

    trans (cong C.∣_∣₊ (cong O.∣_∣ p)) (C.∣∣₊≡∣∣₊ y)           ≡⟨ cong (flip trans _) $
                                                                  cong-preserves-Constant
                                                                    (λ u v →
      C.∣ u ∣₊                                                          ≡⟨ sym (C.∣∣₊≡∣∣₊ u) ⟩
      C.∣ O.∣ u ∣ ∣₊                                                    ≡⟨ cong C.∣_∣₊ (O.∣∣-constant _ _) ⟩
      C.∣ O.∣ v ∣ ∣₊                                                    ≡⟨ C.∣∣₊≡∣∣₊ v ⟩∎
      C.∣ v ∣₊                                                          ∎)
                                                                    _ _ ⟩∎
    trans (cong C.∣_∣₊ q) (C.∣∣₊≡∣∣₊ y)                        ∎

  lemma₃ :
    ∀ n x y (p : C.∣ O.∣ y ∣ ∣₊ ≡ z) →
    subst (∣ x ∣ ≡_) p (lemma₁₊ n x O.∣ y ∣) ≡
    trans (sym (lemma₀ n x))
      (trans (cong C.∣_∣₊ (O.∣∣-constant _ _)) p)
  lemma₃ n x y p =
    subst (∣ x ∣ ≡_) p (lemma₁₊ n x O.∣ y ∣)                      ≡⟨ sym trans-subst ⟩

    trans (lemma₁₊ n x O.∣ y ∣) p                                 ≡⟨⟩

    trans (trans (sym (trans (C.∣∣₊≡∣∣₊ (O.∣ x ∣-out-^ (1 + n)))
                         (lemma₀ n x)))
             (trans (cong C.∣_∣₊
                       (O.∣∣-constant
                          (O.∣ x ∣-out-^ (1 + n)) O.∣ y ∣))
                (C.∣∣₊≡∣∣₊ O.∣ y ∣)))
      p                                                           ≡⟨ trans (cong (λ eq →
                                                                                    trans (trans eq
                                                                                             (trans (cong C.∣_∣₊ (O.∣∣-constant _ _))
                                                                                                (C.∣∣₊≡∣∣₊ _)))
                                                                                      p) $
                                                                            sym-trans _ _) $
                                                                     trans (trans-assoc _ _ _) $
                                                                     trans (trans-assoc _ _ _) $
                                                                     cong (trans (sym (lemma₀ n _))) $
                                                                     sym $ trans-assoc _ _ _ ⟩
    trans (sym (lemma₀ n x))
      (trans (trans (sym (C.∣∣₊≡∣∣₊ (O.∣ x ∣-out-^ (1 + n))))
                (trans (cong C.∣_∣₊
                          (O.∣∣-constant
                             (O.∣ x ∣-out-^ (1 + n)) O.∣ y ∣))
                   (C.∣∣₊≡∣∣₊ O.∣ y ∣)))
         p)                                                       ≡⟨ cong (λ eq → trans (sym (lemma₀ n _))
                                                                                    (trans (trans (sym (C.∣∣₊≡∣∣₊ _)) eq) p)) $ sym $
                                                                     lemma₂ _ _ _ _ _ ⟩
    trans (sym (lemma₀ n x))
      (trans (trans (sym (C.∣∣₊≡∣∣₊ (O.∣ x ∣-out-^ (1 + n))))
                (trans (C.∣∣₊≡∣∣₊ (O.∣ x ∣-out-^ (1 + n)))
                   (cong C.∣_∣₊ (O.∣∣-constant _ _))))
         p)                                                       ≡⟨ cong (λ eq → trans (sym (lemma₀ n _)) (trans eq p)) $
                                                                     trans-sym-[trans] _ _ ⟩∎
    trans (sym (lemma₀ n x))
      (trans (cong C.∣_∣₊ (O.∣∣-constant _ _)) p)                 ∎

  lemma₄ : ∀ _ → C.Elim _
  lemma₄ x .C.Elim.∣∣₀ʳ       = lemma₁₀ x
  lemma₄ x .C.Elim.∣∣₊ʳ       = lemma₁₊ _ x
  lemma₄ x .C.Elim.∣∣₊≡∣∣₀ʳ y =
    subst (∣ x ∣ ≡_) (C.∣∣₊≡∣∣₀ y) (lemma₁₊ 0 x O.∣ y ∣)       ≡⟨ lemma₃ _ _ _ _ ⟩

    trans (sym (lemma₀ 0 x))
      (trans (cong C.∣_∣₊ (O.∣∣-constant _ _)) (C.∣∣₊≡∣∣₀ y))  ≡⟨⟩

    lemma₁₀ x y                                                ∎
  lemma₄ x .C.Elim.∣∣₊≡∣∣₊ʳ {n = n} y =
    subst (∣ x ∣ ≡_) (C.∣∣₊≡∣∣₊ y) (lemma₁₊ (1 + n) x O.∣ y ∣)  ≡⟨ lemma₃ _ _ _ _ ⟩

    trans (sym (lemma₀ (1 + n) x))
      (trans (cong C.∣_∣₊ (O.∣∣-constant _ _)) (C.∣∣₊≡∣∣₊ y))   ≡⟨⟩

    lemma₁₊ n x y                                               ∎

  lemma₅ : Elim _
  lemma₅ .is-propositionʳ = Π≡-proposition ext
  lemma₅ .∣∣ʳ x           = C.elim (lemma₄ x)

------------------------------------------------------------------------
-- Some conversion functions

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
