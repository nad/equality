------------------------------------------------------------------------
-- A non-recursive variant of H-level.Truncation.Propositional.Erased
------------------------------------------------------------------------

-- The definition does use natural numbers. The code is based on van
-- Doorn's "Constructing the Propositional Truncation using
-- Non-recursive HITs".

{-# OPTIONS --cubical=no-glue --safe #-}

import Equality.Path as P

module H-level.Truncation.Propositional.Non-recursive.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

private
  open module PD = P.Derived-definitions-and-properties eq
    hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude hiding ([_,_])

open import Colimit.Sequential.Very-erased eq as C using (Colimitᴱ)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import Erased.Cubical eq
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
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
elim {A} {P} e = C.elim λ where
    .C.Elim.∣∣₀ʳ     → E.∣∣ʳ
    .C.Elim.∣∣₊ʳ {n} → helper n
    .C.Elim.∣∣₊≡∣∣₀ʳ x   →
      subst P (C.∣∣₊≡∣∣₀ x) (subst P (sym (C.∣∣₊≡∣∣₀ x)) (E.∣∣ʳ x))  ≡⟨ subst-subst-sym _ _ _ ⟩∎
      E.∣∣ʳ x                                                        ∎
    .C.Elim.∣∣₊≡∣∣₊ʳ {n} x →
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
∥∥ᴱ-proposition {A} = elim lemma₅
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
  lemma₄ x .C.Elim.∣∣₊≡∣∣₊ʳ {n} y =
    subst (∣ x ∣ ≡_) (C.∣∣₊≡∣∣₊ y) (lemma₁₊ (1 + n) x O.∣ y ∣)  ≡⟨ lemma₃ _ _ _ _ ⟩

    trans (sym (lemma₀ (1 + n) x))
      (trans (cong C.∣_∣₊ (O.∣∣-constant _ _)) (C.∣∣₊≡∣∣₊ y))   ≡⟨⟩

    lemma₁₊ n x y                                               ∎

  lemma₅ : Elim _
  lemma₅ .is-propositionʳ = Π≡-proposition ext
  lemma₅ .∣∣ʳ x           = C.elim (lemma₄ x)

------------------------------------------------------------------------
-- A lemma

-- A function of type (x : ∥ A ∥ᴱ) → P x, along with an erased proof
-- showing that the function is equal to some erased function, is
-- equivalent to a function of type (x : A) → P ∣ x ∣, along with an
-- erased equality proof.

Σ-Π-∥∥ᴱ-Erased-≡-≃ :
  {@0 g : (x : ∥ A ∥ᴱ) → P x} →
  (∃ λ (f : (x : ∥ A ∥ᴱ) → P x) → Erased (f ≡ g)) ≃
  (∃ λ (f : (x : A) → P ∣ x ∣) → Erased (f ≡ g ∘ ∣_∣))
Σ-Π-∥∥ᴱ-Erased-≡-≃ {A} {P} {g} =
  (∃ λ (f : (x : ∥ A ∥ᴱ) → P x) → Erased (f ≡ g))                         ↝⟨ (inverse $
                                                                              Σ-cong (inverse C.universal-property-Π) λ _ → F.id) ⟩
  (∃ λ (f :
        ∃ λ (f₀ : (x : A) → P ∣ x ∣) →
        Erased (
        ∃ λ (f₊ : ∀ n (x : ∥ A ∥¹-out-^ (suc n)) → P C.∣ x ∣₊) →
        (∀ x → subst P (C.∣∣₊≡∣∣₀ x) (f₊ zero O.∣ x ∣) ≡ f₀ x) ×
        (∀ n x → subst P (C.∣∣₊≡∣∣₊ x) (f₊ (suc n) O.∣ x ∣) ≡
                         f₊ n x))) →
   Erased (u⁻¹ f ≡ g))                                                    ↔⟨ inverse $
                                                                             Σ-assoc F.∘
                                                                             (∃-cong λ _ →
                                                                              (∃-cong λ { [ _ ] → F.id }) F.∘
                                                                              Erased-Σ↔Σ F.∘
                                                                              (from-equivalence $ Erased-cong (∃-cong λ _ →
                                                                               Eq.extensionality-isomorphism ext))) ⟩
  (∃ λ (f : (x : A) → P ∣ x ∣) →
   Erased (
   ∃ λ (e :
        ∃ λ (f₊ : ∀ n (x : ∥ A ∥¹-out-^ (suc n)) → P C.∣ x ∣₊) →
        (∀ x → subst P (C.∣∣₊≡∣∣₀ x) (f₊ zero O.∣ x ∣) ≡ f x) ×
        (∀ n x → subst P (C.∣∣₊≡∣∣₊ x) (f₊ (suc n) O.∣ x ∣) ≡ f₊ n x)) →
   ∀ x → u⁻¹ (f , [ e ]) x ≡ g x))                                        ↝⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ →
                                                                              (∃-cong λ _ → from-bijection $ erased Erased↔) F.∘
                                                                              C.universal-property-Π)) ⟩
  (∃ λ (f : (x : A) → P ∣ x ∣) →
   Erased (
   ∃ λ ((f₊ , eq₀ , eq₊) :
        ∃ λ (f₊ : ∀ n (x : ∥ A ∥¹-out-^ (suc n)) → P C.∣ x ∣₊) →
        (∀ x → subst P (C.∣∣₊≡∣∣₀ x) (f₊ zero O.∣ x ∣) ≡ f x) ×
        (∀ n x → subst P (C.∣∣₊≡∣∣₊ x) (f₊ (suc n) O.∣ x ∣) ≡ f₊ n x)) →
   ∃ λ (f≡g₀ : (x : A) → f x ≡ g ∣ x ∣) →
   ∃ λ (f≡g₊ : ∀ n (x : ∥ A ∥¹-out-^ (suc n)) → f₊ n x ≡ g C.∣ x ∣₊) →
   (∀ x → subst (λ x → u⁻¹ (f , [ f₊ , eq₀ , eq₊ ]) x ≡ g x)
            (C.∣∣₊≡∣∣₀ x) (f≡g₊ zero O.∣ x ∣) ≡
          f≡g₀ x) ×
   (∀ n (x : ∥ A ∥¹-out-^ (suc n)) →
    subst (λ x → u⁻¹ (f , [ f₊ , eq₀ , eq₊ ]) x ≡ g x)
      (C.∣∣₊≡∣∣₊ x) (f≡g₊ (suc n) O.∣ x ∣) ≡
    f≡g₊ n x)))                                                           ↔⟨ (∃-cong λ _ → Erased-cong (
                                                                              (∃-cong λ _ →
                                                                               (∃-cong λ _ →
                                                                                inverse Σ-assoc) F.∘
                                                                               Σ-assoc F.∘
                                                                               (∃-cong λ _ →
                                                                                (inverse $
                                                                                 Σ-cong (inverse $
                                                                                         Eq.extensionality-isomorphism ext F.∘
                                                                                         (∀-cong ext λ _ →
                                                                                          Eq.extensionality-isomorphism ext)) λ _ →
                                                                                 F.id) F.∘
                                                                                ∃-comm) F.∘
                                                                               inverse Σ-assoc) F.∘
                                                                              ∃-comm)) ⟩
  (∃ λ (f : (x : A) → P ∣ x ∣) →
   Erased (
   ∃ λ (f≡g₀ : (x : A) → f x ≡ g ∣ x ∣) →
   ∃ λ ((f₊ , f≡g₊) :
        ∃ λ (f₊ : ∀ n (x : ∥ A ∥¹-out-^ (suc n)) → P C.∣ x ∣₊) →
        f₊ ≡ λ _ x → g C.∣ x ∣₊) →
   ∃ λ (eq₀ : ∀ x → subst P (C.∣∣₊≡∣∣₀ x) (f₊ zero O.∣ x ∣) ≡ f x) →
   ∃ λ (eq₊ : ∀ n x →
              subst P (C.∣∣₊≡∣∣₊ x) (f₊ (suc n) O.∣ x ∣) ≡ f₊ n x) →
   (∀ x → subst (λ x → u⁻¹ (f , [ f₊ , eq₀ , eq₊ ]) x ≡ g x)
            (C.∣∣₊≡∣∣₀ x) (cong (_$ O.∣ x ∣) (cong (_$ zero) f≡g₊)) ≡
          f≡g₀ x) ×
   (∀ n (x : ∥ A ∥¹-out-^ (suc n)) →
    subst (λ x → u⁻¹ (f , [ f₊ , eq₀ , eq₊ ]) x ≡ g x)
      (C.∣∣₊≡∣∣₊ x) (cong (_$ O.∣ x ∣) (cong (_$ suc n) f≡g₊)) ≡
    cong (_$ x) (cong (_$ n) f≡g₊))))                                     ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ →
                                                                              (∃-cong λ _ → ∃-cong λ _ →
                                                                               (∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $
                                                                                cong (subst (λ x → u⁻¹ (_ , [ _ ]) x ≡ g x) _) $
                                                                                trans (cong (cong (_$ _)) $ cong-refl _) $
                                                                                cong-refl _)
                                                                                 ×-cong
                                                                               (∀-cong ext λ _ → ∀-cong ext λ _ → ≡⇒↝ _ $ cong₂ _≡_
                                                                                  (cong (subst (λ x → u⁻¹ (_ , [ _ ]) x ≡ g x) _) $
                                                                                   trans (cong (cong (_$ _)) $ cong-refl _) $
                                                                                   cong-refl _)
                                                                                  (trans (cong (cong (_$ _)) $ cong-refl _) $
                                                                                   cong-refl _))) F.∘
                                                                              (drop-⊤-left-Σ $
                                                                               _⇔_.to contractible⇔↔⊤ $
                                                                               singleton-contractible _))) ⟩
  (∃ λ (f : (x : A) → P ∣ x ∣) →
   Erased (
   ∃ λ (f≡g₀ : (x : A) → f x ≡ g ∣ x ∣) →
   ∃ λ (eq₀ : ∀ x → subst P (C.∣∣₊≡∣∣₀ x) (g C.∣ O.∣ x ∣ ∣₊) ≡ f x) →
   ∃ λ (eq₊ : ∀ n x →
              subst P (C.∣∣₊≡∣∣₊ x) (g C.∣ O.∣ x ∣ ∣₊) ≡ g C.∣ x ∣₊) →
   (∀ x → subst
            (λ x → u⁻¹ (f , [ (λ _ → g ∘ C.∣_∣₊) , eq₀ , eq₊ ]) x ≡ g x)
            (C.∣∣₊≡∣∣₀ x) (refl _) ≡
          f≡g₀ x) ×
   (∀ n (x : ∥ A ∥¹-out-^ (suc n)) →
    subst (λ x → u⁻¹ (f , [ (λ _ → g ∘ C.∣_∣₊) , eq₀ , eq₊ ]) x ≡ g x)
      (C.∣∣₊≡∣∣₊ x) (refl _) ≡
    refl _)))                                                             ↝⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                              (∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $
                                                                               lemma₀ _ _ _ _)
                                                                                ×-cong
                                                                              (∀-cong ext λ _ → ∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ refl _) $
                                                                               lemma₊ _ _ _ _ _))) ⟩
  (∃ λ (f : (x : A) → P ∣ x ∣) →
   Erased (
   ∃ λ (f≡g₀ : (x : A) → f x ≡ g ∣ x ∣) →
   ∃ λ (eq₀ : ∀ x → subst P (C.∣∣₊≡∣∣₀ x) (g C.∣ O.∣ x ∣ ∣₊) ≡ f x) →
   ∃ λ (eq₊ : ∀ n x →
              subst P (C.∣∣₊≡∣∣₊ x) (g C.∣ O.∣ x ∣ ∣₊) ≡ g C.∣ x ∣₊) →
   (∀ x → trans (sym (eq₀ x)) (dcong g (C.∣∣₊≡∣∣₀ x)) ≡ f≡g₀ x) ×
   (∀ n (x : ∥ A ∥¹-out-^ (suc n)) →
    trans (sym (eq₊ n x)) (dcong g (C.∣∣₊≡∣∣₊ x)) ≡ refl _)))             ↝⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ → ∃-cong λ eq₀ → ∃-cong λ eq₊ →
                                                                              (Eq.extensionality-isomorphism ext F.∘
                                                                               (∀-cong ext λ _ →
                                                                                Eq.≃-≡ (Eq.↔⇒≃ ≡-comm) F.∘
                                                                                (≡⇒↝ _ $
                                                                                 trans ([trans≡]≡[≡trans-symʳ] _ _ _) $
                                                                                 cong (sym (eq₀ _) ≡_) $ sym $ sym-sym _)))
                                                                                ×-cong
                                                                              (Eq.extensionality-isomorphism ext F.∘
                                                                               (∀-cong ext λ _ →
                                                                                Eq.extensionality-isomorphism ext F.∘
                                                                                (∀-cong ext λ _ →
                                                                                 Eq.≃-≡ (Eq.↔⇒≃ ≡-comm) F.∘
                                                                                 (≡⇒↝ _ $
                                                                                  trans ([trans≡]≡[≡trans-symʳ] _ _ _) $
                                                                                  cong (sym (eq₊ _ _) ≡_) $ sym $ sym-sym _)))))) ⟩
  (∃ λ (f : (x : A) → P ∣ x ∣) →
   Erased (
   ∃ λ (f≡g₀ : (x : A) → f x ≡ g ∣ x ∣) →
   ∃ λ (eq₀ : ∀ x → subst P (C.∣∣₊≡∣∣₀ x) (g C.∣ O.∣ x ∣ ∣₊) ≡ f x) →
   ∃ λ (eq₊ : ∀ n x →
              subst P (C.∣∣₊≡∣∣₊ x) (g C.∣ O.∣ x ∣ ∣₊) ≡ g C.∣ x ∣₊) →
   eq₀ ≡ (λ x → sym (trans (f≡g₀ x) (sym (dcong g (C.∣∣₊≡∣∣₀ x))))) ×
   eq₊ ≡ (λ _ x → sym (trans (refl _) (sym (dcong g (C.∣∣₊≡∣∣₊ x)))))))   ↔⟨ (∃-cong λ _ → Erased-cong (∃-cong λ _ → ∃-cong λ _ →
                                                                              (drop-⊤-right λ _ →
                                                                               _⇔_.to contractible⇔↔⊤ $
                                                                               singleton-contractible _) F.∘
                                                                              ∃-comm)) ⟩
  (∃ λ (f : (x : A) → P ∣ x ∣) →
   Erased (
   ∃ λ (f≡g₀ : (x : A) → f x ≡ g ∣ x ∣) →
   ∃ λ (eq₀ : ∀ x → subst P (C.∣∣₊≡∣∣₀ x) (g C.∣ O.∣ x ∣ ∣₊) ≡ f x) →
   eq₀ ≡ (λ x → sym (trans (f≡g₀ x) (sym (dcong g (C.∣∣₊≡∣∣₀ x)))))))     ↔⟨ (∃-cong λ _ → Erased-cong (
                                                                              drop-⊤-right λ _ →
                                                                              _⇔_.to contractible⇔↔⊤ $
                                                                              singleton-contractible _)) ⟩

  (∃ λ (f : (x : A) → P ∣ x ∣) → Erased ((x : A) → f x ≡ g ∣ x ∣))        ↝⟨ (∃-cong λ _ → Erased-cong (
                                                                              Eq.extensionality-isomorphism ext)) ⟩□
  (∃ λ (f : (x : A) → P ∣ x ∣) → Erased (f ≡ g ∘ ∣_∣))                    □
  where
  u⁻¹ = _≃_.from C.universal-property-Π

  @0 lemma₀ : ∀ _ _ _ _ → _
  lemma₀ f eq₀ eq₊ x =
    subst (λ x → u⁻¹ (f , [ (λ _ → g ∘ C.∣_∣₊) , eq₀ , eq₊ ]) x ≡ g x)
      (C.∣∣₊≡∣∣₀ x) (refl _)                                            ≡⟨ subst-in-terms-of-trans-and-dcong ⟩

    trans (sym (dcong (u⁻¹ (f , [ (λ _ → g ∘ C.∣_∣₊) , eq₀ , eq₊ ]))
                  (C.∣∣₊≡∣∣₀ x)))
      (trans (cong (subst P (C.∣∣₊≡∣∣₀ x)) (refl _))
         (dcong g (C.∣∣₊≡∣∣₀ x)))                                       ≡⟨ cong₂ (trans ∘ sym)
                                                                             C.elim-∣∣₊≡∣∣₀
                                                                             (trans (cong (flip trans _) $
                                                                                     cong-refl _) $
                                                                              trans-reflˡ _) ⟩∎
    trans (sym (eq₀ x)) (dcong g (C.∣∣₊≡∣∣₀ x))                         ∎

  @0 lemma₊ : ∀ _ _ _ _ _ → _
  lemma₊ f eq₀ eq₊ n x =
    subst (λ x → u⁻¹ (f , [ (λ _ → g ∘ C.∣_∣₊) , eq₀ , eq₊ ]) x ≡ g x)
      (C.∣∣₊≡∣∣₊ x) (refl _)                                            ≡⟨ subst-in-terms-of-trans-and-dcong ⟩

    trans (sym (dcong (u⁻¹ (f , [ (λ _ → g ∘ C.∣_∣₊) , eq₀ , eq₊ ]))
                  (C.∣∣₊≡∣∣₊ x)))
      (trans (cong (subst P (C.∣∣₊≡∣∣₊ x)) (refl _))
         (dcong g (C.∣∣₊≡∣∣₊ x)))                                       ≡⟨ cong₂ (trans ∘ sym)
                                                                             C.elim-∣∣₊≡∣∣₊
                                                                             (trans (cong (flip trans _) $
                                                                                     cong-refl _) $
                                                                              trans-reflˡ _) ⟩∎
    trans (sym (eq₊ n x)) (dcong g (C.∣∣₊≡∣∣₊ x))                       ∎
