------------------------------------------------------------------------
-- Sequential colimits
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- The definition of sequential colimits and the statement of the
-- non-dependent universal property are based on those in van Doorn's
-- "Constructing the Propositional Truncation using Non-recursive
-- HITs".

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining sequential colimits uses path
-- equality, but the supplied notion of equality is used for many
-- other things.

import Equality.Path as P

module Colimit.Sequential
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude

open import Bijection equality-with-J using (_↔_)
import Colimit.Sequential.Erased eq as E
import Colimit.Sequential.Very-erased eq as VE
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence P.equality-with-J as PEq
open import Function-universe equality-with-J hiding (id; _∘_)

private
  variable
    a b p q : Level
    A B     : Type a
    P       : A → Type p
    n       : ℕ
    e x     : A

------------------------------------------------------------------------
-- The type

-- Sequential colimits.

data Colimit (P : ℕ → Type p) (step : ∀ {n} → P n → P (suc n)) :
             Type p where
  ∣_∣    : P n → Colimit P step
  ∣∣≡∣∣ᴾ : (x : P n) → ∣ step x ∣ P.≡ ∣ x ∣

-- A variant of ∣∣≡∣∣ᴾ.

∣∣≡∣∣ : {step : ∀ {n} → P n → P (suc n)} (x : P n) →
        _≡_ {A = Colimit P step} ∣ step x ∣ ∣ x ∣
∣∣≡∣∣ x = _↔_.from ≡↔≡ (∣∣≡∣∣ᴾ x)

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ
         {P : ℕ → Type p} {step : ∀ {n} → P n → P (suc n)}
         (Q : Colimit P step → Type q) : Type (p ⊔ q) where
  no-eta-equality
  field
    ∣∣ʳ    : (x : P n) → Q ∣ x ∣
    ∣∣≡∣∣ʳ :
      (x : P n) →
      P.[ (λ i → Q (∣∣≡∣∣ᴾ x i)) ] ∣∣ʳ (step x) ≡ ∣∣ʳ x

open Elimᴾ public

elimᴾ :
  {step : ∀ {n} → P n → P (suc n)} {Q : Colimit P step → Type q} →
  Elimᴾ Q → (x : Colimit P step) → Q x
elimᴾ {P = P} {step = step} {Q = Q} e = helper
  where
  module E′ = Elimᴾ e

  helper : (x : Colimit P step) → Q x
  helper ∣ x ∣        = E′.∣∣ʳ x
  helper (∣∣≡∣∣ᴾ x i) = E′.∣∣≡∣∣ʳ x i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ
         (P : ℕ → Type p) (step : ∀ {n} → P n → P (suc n))
         (B : Type b) : Type (p ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ    : P n → B
    ∣∣≡∣∣ʳ : (x : P n) → ∣∣ʳ (step x) P.≡ ∣∣ʳ x

open Recᴾ public

recᴾ :
  {step : ∀ {n} → P n → P (suc n)} →
  Recᴾ P step B → Colimit P step → B
recᴾ r = elimᴾ λ where
    .∣∣ʳ    → R.∣∣ʳ
    .∣∣≡∣∣ʳ → R.∣∣≡∣∣ʳ
  where
  module R = Recᴾ r

-- A dependent eliminator.

record Elim
         {P : ℕ → Type p} {step : ∀ {n} → P n → P (suc n)}
         (Q : Colimit P step → Type q) : Type (p ⊔ q) where
  no-eta-equality
  field
    ∣∣ʳ    : (x : P n) → Q ∣ x ∣
    ∣∣≡∣∣ʳ : (x : P n) → subst Q (∣∣≡∣∣ x) (∣∣ʳ (step x)) ≡ ∣∣ʳ x

open Elim public

elim :
  {step : ∀ {n} → P n → P (suc n)} {Q : Colimit P step → Type q} →
  Elim Q → (x : Colimit P step) → Q x
elim e = elimᴾ λ where
    .∣∣ʳ      → E′.∣∣ʳ
    .∣∣≡∣∣ʳ x → subst≡→[]≡ (E′.∣∣≡∣∣ʳ x)
  where
  module E′ = Elim e

-- A "computation" rule.

elim-∣∣≡∣∣ : dcong (elim e) (∣∣≡∣∣ x) ≡ Elim.∣∣≡∣∣ʳ e x
elim-∣∣≡∣∣ = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec
         (P : ℕ → Type p) (step : ∀ {n} → P n → P (suc n))
         (B : Type b) : Type (p ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ    : P n → B
    ∣∣≡∣∣ʳ : (x : P n) → ∣∣ʳ (step x) ≡ ∣∣ʳ x

open Rec public

rec :
  {step : ∀ {n} → P n → P (suc n)} →
  Rec P step B → Colimit P step → B
rec r = recᴾ λ where
    .∣∣ʳ      → R.∣∣ʳ
    .∣∣≡∣∣ʳ x → _↔_.to ≡↔≡ (R.∣∣≡∣∣ʳ x)
  where
  module R = Rec r

-- A "computation" rule.

rec-∣∣≡∣∣ :
  {step : ∀ {n} → P n → P (suc n)} {r : Rec P step B} {x : P n} →
  cong (rec r) (∣∣≡∣∣ x) ≡ Rec.∣∣≡∣∣ʳ r x
rec-∣∣≡∣∣ = cong-≡↔≡ (refl _)

------------------------------------------------------------------------
-- The universal property

-- The universal property of the sequential colimit.

universal-property :
  {step : ∀ {n} → P n → P (suc n)} →
  (Colimit P step → B) ≃
  (∃ λ (f : ∀ n → P n → B) → ∀ n x → f (suc n) (step x) ≡ f n x)
universal-property {P = P} {B = B} {step = step} =
  Eq.↔→≃ to from to∘from from∘to
  where
  to :
    (Colimit P step → B) →
    ∃ λ (f : ∀ n → P n → B) → ∀ n x → f (suc n) (step x) ≡ f n x
  to h = (λ _ → h ∘ ∣_∣)
       , (λ _ x →
            h ∣ step x ∣  ≡⟨ cong h (∣∣≡∣∣ x) ⟩∎
            h ∣ x ∣       ∎)

  from :
    (∃ λ (f : ∀ n → P n → B) → ∀ n x → f (suc n) (step x) ≡ f n x) →
    Colimit P step → B
  from (f , g) = rec λ where
    .∣∣ʳ    → f _
    .∣∣≡∣∣ʳ → g _

  to∘from : ∀ p → to (from p) ≡ p
  to∘from (f , g) = cong (f ,_) $ ⟨ext⟩ λ n → ⟨ext⟩ λ x →
    cong (rec _) (∣∣≡∣∣ x)  ≡⟨ rec-∣∣≡∣∣ ⟩∎
    g n x                   ∎

  from∘to : ∀ h → from (to h) ≡ h
  from∘to h = ⟨ext⟩ $ elim λ where
    .∣∣ʳ    _ → refl _
    .∣∣≡∣∣ʳ x →
      subst (λ z → from (to h) z ≡ h z) (∣∣≡∣∣ x) (refl _)  ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans (sym (cong (from (to h)) (∣∣≡∣∣ x)))
        (trans (refl _) (cong h (∣∣≡∣∣ x)))                 ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                 rec-∣∣≡∣∣
                                                                 (trans-reflˡ _) ⟩

      trans (sym (cong h (∣∣≡∣∣ x))) (cong h (∣∣≡∣∣ x))     ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                ∎

-- A dependently typed variant of the sequential colimit's universal
-- property.

universal-property-Π :
  {step : ∀ {n} → P n → P (suc n)} →
  {Q : Colimit P step → Type q} →
  ((x : Colimit P step) → Q x) ≃
  (∃ λ (f : ∀ n (x : P n) → Q ∣ x ∣) →
     ∀ n x → subst Q (∣∣≡∣∣ x) (f (suc n) (step x)) ≡ f n x)
universal-property-Π {P = P} {step = step} {Q = Q} =
  Eq.↔→≃ to from to∘from from∘to
  where
  to :
    ((x : Colimit P step) → Q x) →
    ∃ λ (f : ∀ n (x : P n) → Q ∣ x ∣) →
      ∀ n x → subst Q (∣∣≡∣∣ x) (f (suc n) (step x)) ≡ f n x
  to h = (λ _ → h ∘ ∣_∣)
       , (λ _ x →
            subst Q (∣∣≡∣∣ x) (h ∣ step x ∣)  ≡⟨ dcong h (∣∣≡∣∣ x) ⟩∎
            h ∣ x ∣                           ∎)

  from :
    (∃ λ (f : ∀ n (x : P n) → Q ∣ x ∣) →
       ∀ n x → subst Q (∣∣≡∣∣ x) (f (suc n) (step x)) ≡ f n x) →
    (x : Colimit P step) → Q x
  from (f , g) = elim λ where
    .∣∣ʳ    → f _
    .∣∣≡∣∣ʳ → g _

  to∘from : ∀ p → to (from p) ≡ p
  to∘from (f , g) = cong (f ,_) $ ⟨ext⟩ λ n → ⟨ext⟩ λ x →
    dcong (elim _) (∣∣≡∣∣ x)  ≡⟨ elim-∣∣≡∣∣ ⟩∎
    g n x                     ∎

  from∘to : ∀ h → from (to h) ≡ h
  from∘to h = ⟨ext⟩ $ elim λ where
    .∣∣ʳ    _ → refl _
    .∣∣≡∣∣ʳ x →
      subst (λ z → from (to h) z ≡ h z) (∣∣≡∣∣ x) (refl _)  ≡⟨ subst-in-terms-of-trans-and-dcong ⟩

      trans (sym (dcong (from (to h)) (∣∣≡∣∣ x)))
        (trans (cong (subst Q (∣∣≡∣∣ x)) (refl _))
           (dcong h (∣∣≡∣∣ x)))                             ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                 elim-∣∣≡∣∣
                                                                 (trans (cong (flip trans _) $
                                                                         cong-refl _) $
                                                                  trans-reflˡ _) ⟩

      trans (sym (dcong h (∣∣≡∣∣ x))) (dcong h (∣∣≡∣∣ x))   ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                ∎

------------------------------------------------------------------------
-- Some conversion functions

-- E.Colimitᴱ P step implies Colimit P step.

Colimitᴱ→Colimit :
  {step : ∀ {n} → P n → P (suc n)} →
  E.Colimitᴱ P step → Colimit P step
Colimitᴱ→Colimit = E.rec λ where
  .E.∣∣ʳ    → ∣_∣
  .E.∣∣≡∣∣ʳ → ∣∣≡∣∣

-- In erased contexts E.Colimitᴱ P step is equivalent to
-- Colimit P step.

@0 Colimitᴱ≃Colimit :
  {step : ∀ {n} → P n → P (suc n)} →
  E.Colimitᴱ P step ≃ Colimit P step
Colimitᴱ≃Colimit = Eq.↔→≃
  Colimitᴱ→Colimit
  Colimit→Colimitᴱ
  (elim λ @0 where
     .∣∣ʳ _    → refl _
     .∣∣≡∣∣ʳ x →
       subst (λ x → Colimitᴱ→Colimit (Colimit→Colimitᴱ x) ≡ x)
         (∣∣≡∣∣ x) (refl _)                                     ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (Colimitᴱ→Colimit ∘ Colimit→Colimitᴱ)
                     (∣∣≡∣∣ x)))
         (trans (refl _) (cong id (∣∣≡∣∣ x)))                   ≡⟨ cong₂ (trans ∘ sym)
                                                                     (trans (sym $ cong-∘ _ _ _) $
                                                                      trans (cong (cong Colimitᴱ→Colimit) rec-∣∣≡∣∣) $
                                                                      E.rec-∣∣≡∣∣)
                                                                     (trans (trans-reflˡ _) $
                                                                      sym $ cong-id _) ⟩

       trans (sym (∣∣≡∣∣ x)) (∣∣≡∣∣ x)                          ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                   ∎)
  (E.elim λ where
     .E.∣∣ʳ _    → refl _
     .E.∣∣≡∣∣ʳ x →
       subst (λ x → Colimit→Colimitᴱ (Colimitᴱ→Colimit x) ≡ x)
         (E.∣∣≡∣∣ x) (refl _)                                   ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (Colimit→Colimitᴱ ∘ Colimitᴱ→Colimit)
                     (E.∣∣≡∣∣ x)))
         (trans (refl _) (cong id (E.∣∣≡∣∣ x)))                 ≡⟨ cong₂ (trans ∘ sym)
                                                                     (trans (sym $ cong-∘ _ _ _) $
                                                                      trans (cong (cong Colimit→Colimitᴱ) E.rec-∣∣≡∣∣) $
                                                                      rec-∣∣≡∣∣)
                                                                     (trans (trans-reflˡ _) $
                                                                      sym $ cong-id _) ⟩

       trans (sym (E.∣∣≡∣∣ x)) (E.∣∣≡∣∣ x)                      ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                   ∎)
  where
  Colimit→Colimitᴱ = rec λ @0 where
    .∣∣ʳ    → E.∣_∣
    .∣∣≡∣∣ʳ → E.∣∣≡∣∣

-- Some instances of VE.Colimitᴱ can be converted to instances of
-- Colimit. Note that P₀ and P₊ target the same universe.

Very-Colimitᴱ→Colimit :
  {P₀ : Type p}
  {P₊ : ℕ → Type p}
  {step₀ : P₀ → P₊ zero} →
  {step₊ : ∀ {n} → P₊ n → P₊ (suc n)} →
  VE.Colimitᴱ P₀ P₊ step₀ step₊ →
  Colimit
    (ℕ-rec P₀ (λ n _ → P₊ n))
    (λ {n} → ℕ-rec {P = λ n → ℕ-rec P₀ (λ n _ → P₊ n) n → P₊ n}
                   step₀ (λ _ _ → step₊) n)
Very-Colimitᴱ→Colimit = VE.rec λ where
  .VE.∣∣₀ʳ     → ∣_∣ {n = 0}
  .VE.∣∣₊ʳ     → ∣_∣
  .VE.∣∣₊≡∣∣₀ʳ → ∣∣≡∣∣
  .VE.∣∣₊≡∣∣₊ʳ → ∣∣≡∣∣

-- In erased contexts there are equivalences between some instances of
-- VE.Colimitᴱ and some instances of Colimit.

@0 Very-Colimitᴱ≃Colimit :
  {P₀ : Type p}
  {P₊ : ℕ → Type p}
  {step₀ : P₀ → P₊ zero} →
  {step₊ : ∀ {n} → P₊ n → P₊ (suc n)} →
  VE.Colimitᴱ P₀ P₊ step₀ step₊ ≃
  Colimit
    (ℕ-rec P₀ (λ n _ → P₊ n))
    (λ {n} → ℕ-rec {P = λ n → ℕ-rec P₀ (λ n _ → P₊ n) n → P₊ n}
                   step₀ (λ _ _ → step₊) n)
Very-Colimitᴱ≃Colimit = Eq.↔→≃
  Very-Colimitᴱ→Colimit
  Colimit→Colimitᴱ
  (elim λ @0 where
     .∣∣ʳ {n = zero} _    → refl _
     .∣∣ʳ {n = suc _} _   → refl _
     .∣∣≡∣∣ʳ {n = zero} x →
       subst (λ x → Very-Colimitᴱ→Colimit (Colimit→Colimitᴱ x) ≡ x)
         (∣∣≡∣∣ x) (refl _)                                          ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (Very-Colimitᴱ→Colimit ∘ Colimit→Colimitᴱ)
                     (∣∣≡∣∣ x)))
         (trans (refl _) (cong id (∣∣≡∣∣ x)))                        ≡⟨ cong₂ (trans ∘ sym)
                                                                          (trans (sym $ cong-∘ _ _ _) $
                                                                           trans (cong (cong Very-Colimitᴱ→Colimit) rec-∣∣≡∣∣) $
                                                                           VE.rec-∣∣₊≡∣∣₀)
                                                                          (trans (trans-reflˡ _) $
                                                                           sym $ cong-id _) ⟩

       trans (sym (∣∣≡∣∣ x)) (∣∣≡∣∣ x)                               ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                        ∎
     .∣∣≡∣∣ʳ {n = suc _} x →
       subst (λ x → Very-Colimitᴱ→Colimit (Colimit→Colimitᴱ x) ≡ x)
         (∣∣≡∣∣ x) (refl _)                                          ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (Very-Colimitᴱ→Colimit ∘ Colimit→Colimitᴱ)
                     (∣∣≡∣∣ x)))
         (trans (refl _) (cong id (∣∣≡∣∣ x)))                        ≡⟨ cong₂ (trans ∘ sym)
                                                                          (trans (sym $ cong-∘ _ _ _) $
                                                                           trans (cong (cong Very-Colimitᴱ→Colimit) rec-∣∣≡∣∣) $
                                                                           VE.rec-∣∣₊≡∣∣₊)
                                                                          (trans (trans-reflˡ _) $
                                                                           sym $ cong-id _) ⟩

       trans (sym (∣∣≡∣∣ x)) (∣∣≡∣∣ x)                               ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                        ∎)
  (VE.elim λ where
     .VE.∣∣₀ʳ _     → refl _
     .VE.∣∣₊ʳ _     → refl _
     .VE.∣∣₊≡∣∣₀ʳ x →
       subst (λ x → Colimit→Colimitᴱ (Very-Colimitᴱ→Colimit x) ≡ x)
         (VE.∣∣₊≡∣∣₀ x) (refl _)                                     ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (Colimit→Colimitᴱ ∘ Very-Colimitᴱ→Colimit)
                     (VE.∣∣₊≡∣∣₀ x)))
         (trans (refl _) (cong id (VE.∣∣₊≡∣∣₀ x)))                   ≡⟨ cong₂ (trans ∘ sym)
                                                                          (trans (sym $ cong-∘ _ _ _) $
                                                                           trans (cong (cong Colimit→Colimitᴱ) VE.rec-∣∣₊≡∣∣₀) $
                                                                           rec-∣∣≡∣∣)
                                                                          (trans (trans-reflˡ _) $
                                                                           sym $ cong-id _) ⟩

       trans (sym (VE.∣∣₊≡∣∣₀ x)) (VE.∣∣₊≡∣∣₀ x)                     ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                        ∎
     .VE.∣∣₊≡∣∣₊ʳ x →
       subst (λ x → Colimit→Colimitᴱ (Very-Colimitᴱ→Colimit x) ≡ x)
         (VE.∣∣₊≡∣∣₊ x) (refl _)                                     ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (Colimit→Colimitᴱ ∘ Very-Colimitᴱ→Colimit)
                     (VE.∣∣₊≡∣∣₊ x)))
         (trans (refl _) (cong id (VE.∣∣₊≡∣∣₊ x)))                   ≡⟨ cong₂ (trans ∘ sym)
                                                                          (trans (sym $ cong-∘ _ _ _) $
                                                                           trans (cong (cong Colimit→Colimitᴱ) VE.rec-∣∣₊≡∣∣₊) $
                                                                           rec-∣∣≡∣∣)
                                                                          (trans (trans-reflˡ _) $
                                                                           sym $ cong-id _) ⟩

       trans (sym (VE.∣∣₊≡∣∣₊ x)) (VE.∣∣₊≡∣∣₊ x)                     ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                        ∎)
  where
  Colimit→Colimitᴱ = rec λ @0 where
    .∣∣ʳ {n = zero}     → VE.∣_∣₀
    .∣∣ʳ {n = suc _}    → VE.∣_∣₊
    .∣∣≡∣∣ʳ {n = zero}  → VE.∣∣₊≡∣∣₀
    .∣∣≡∣∣ʳ {n = suc _} → VE.∣∣₊≡∣∣₊
