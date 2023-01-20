------------------------------------------------------------------------
-- A sequential colimit for which everything except for the "base
-- case" is erased
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

module Colimit.Sequential.Very-erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude hiding ([_,_])

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Erased.Cubical eq

private
  variable
    a b p₀ p₊ q : Level
    A B P₀      : Type a
    P₊          : A → Type p₊
    n           : ℕ
    e step₀ x   : A

------------------------------------------------------------------------
-- The type

-- A sequential colimit for which everything except for the "base
-- case" is erased.

data Colimitᴱ
       (P₀ : Type p₀)
       (@0 P₊ : ℕ → Type p₊)
       (@0 step₀ : P₀ → P₊ zero)
       (@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)) :
       Type (p₀ ⊔ p₊) where
  ∣_∣₀        : P₀ → Colimitᴱ P₀ P₊ step₀ step₊
  @0 ∣_∣₊     : P₊ n → Colimitᴱ P₀ P₊ step₀ step₊
  @0 ∣∣₊≡∣∣₀ᴾ : (x : P₀) → ∣ step₀ x ∣₊ P.≡ ∣ x ∣₀
  @0 ∣∣₊≡∣∣₊ᴾ : (x : P₊ n) → ∣ step₊ x ∣₊ P.≡ ∣ x ∣₊

-- A variant of ∣∣₊≡∣∣₀ᴾ.

@0 ∣∣₊≡∣∣₀ :
  {step₊ : ∀ {n} → P₊ n → P₊ (suc n)} (x : P₀) →
  _≡_ {A = Colimitᴱ P₀ P₊ step₀ step₊} ∣ step₀ x ∣₊ ∣ x ∣₀
∣∣₊≡∣∣₀ x = _↔_.from ≡↔≡ (∣∣₊≡∣∣₀ᴾ x)

-- A variant of ∣∣₊≡∣∣₊ᴾ.

@0 ∣∣₊≡∣∣₊ :
  {step₊ : ∀ {n} → P₊ n → P₊ (suc n)} (x : P₊ n) →
  _≡_ {A = Colimitᴱ P₀ P₊ step₀ step₊} ∣ step₊ x ∣₊ ∣ x ∣₊
∣∣₊≡∣∣₊ x = _↔_.from ≡↔≡ (∣∣₊≡∣∣₊ᴾ x)

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ
         {P₀ : Type p₀}
         {@0 P₊ : ℕ → Type p₊}
         {@0 step₀ : P₀ → P₊ zero}
         {@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)}
         (Q : Colimitᴱ P₀ P₊ step₀ step₊ → Type q) :
         Type (p₀ ⊔ p₊ ⊔ q) where
  no-eta-equality
  field
    ∣∣₀ʳ        : (x : P₀) → Q ∣ x ∣₀
    @0 ∣∣₊ʳ     : (x : P₊ n) → Q ∣ x ∣₊
    @0 ∣∣₊≡∣∣₀ʳ : (x : P₀) →
                  P.[ (λ i → Q (∣∣₊≡∣∣₀ᴾ x i)) ] ∣∣₊ʳ (step₀ x) ≡ ∣∣₀ʳ x
    @0 ∣∣₊≡∣∣₊ʳ : (x : P₊ n) →
                  P.[ (λ i → Q (∣∣₊≡∣∣₊ᴾ x i)) ] ∣∣₊ʳ (step₊ x) ≡ ∣∣₊ʳ x

open Elimᴾ public

elimᴾ :
  {@0 P₊ : ℕ → Type p₊}
  {@0 step₀ : P₀ → P₊ zero}
  {@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)}
  {Q : Colimitᴱ P₀ P₊ step₀ step₊ → Type q} →
  Elimᴾ Q → (x : Colimitᴱ P₀ P₊ step₀ step₊) → Q x
elimᴾ {P₀} {P₊} {step₀} {step₊} {Q} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Colimitᴱ P₀ P₊ step₀ step₊) → Q x
  helper ∣ x ∣₀         = E.∣∣₀ʳ x
  helper ∣ x ∣₊         = E.∣∣₊ʳ x
  helper (∣∣₊≡∣∣₀ᴾ x i) = E.∣∣₊≡∣∣₀ʳ x i
  helper (∣∣₊≡∣∣₊ᴾ x i) = E.∣∣₊≡∣∣₊ʳ x i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ
         (P₀ : Type p₀)
         (@0 P₊ : ℕ → Type p₊)
         (@0 step₀ : P₀ → P₊ zero)
         (@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n))
         (B : Type b) : Type (p₀ ⊔ p₊ ⊔ b) where
  no-eta-equality
  field
    ∣∣₀ʳ        : P₀ → B
    @0 ∣∣₊ʳ     : P₊ n → B
    @0 ∣∣₊≡∣∣₀ʳ : (x : P₀) → ∣∣₊ʳ (step₀ x) P.≡ ∣∣₀ʳ x
    @0 ∣∣₊≡∣∣₊ʳ : (x : P₊ n) → ∣∣₊ʳ (step₊ x) P.≡ ∣∣₊ʳ x

open Recᴾ public

recᴾ :
  {@0 P₊ : ℕ → Type p₊}
  {@0 step₀ : P₀ → P₊ zero}
  {@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)} →
  Recᴾ P₀ P₊ step₀ step₊ B → Colimitᴱ P₀ P₊ step₀ step₊ → B
recᴾ r = elimᴾ λ where
    .∣∣₀ʳ     → R.∣∣₀ʳ
    .∣∣₊ʳ     → R.∣∣₊ʳ
    .∣∣₊≡∣∣₀ʳ → R.∣∣₊≡∣∣₀ʳ
    .∣∣₊≡∣∣₊ʳ → R.∣∣₊≡∣∣₊ʳ
  where
  module R = Recᴾ r

-- A dependent eliminator.

record Elim
         {P₀ : Type p₀}
         {@0 P₊ : ℕ → Type p₊}
         {@0 step₀ : P₀ → P₊ zero}
         {@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)}
         (Q : Colimitᴱ P₀ P₊ step₀ step₊ → Type q) :
         Type (p₀ ⊔ p₊ ⊔ q) where
  no-eta-equality
  field
    ∣∣₀ʳ        : (x : P₀) → Q ∣ x ∣₀
    @0 ∣∣₊ʳ     : (x : P₊ n) → Q ∣ x ∣₊
    @0 ∣∣₊≡∣∣₀ʳ : (x : P₀) →
                  subst Q (∣∣₊≡∣∣₀ x) (∣∣₊ʳ (step₀ x)) ≡ ∣∣₀ʳ x
    @0 ∣∣₊≡∣∣₊ʳ : (x : P₊ n) →
                  subst Q (∣∣₊≡∣∣₊ x) (∣∣₊ʳ (step₊ x)) ≡ ∣∣₊ʳ x

open Elim public

elim :
  {@0 P₊ : ℕ → Type p₊}
  {@0 step₀ : P₀ → P₊ zero}
  {@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)}
  {Q : Colimitᴱ P₀ P₊ step₀ step₊ → Type q} →
  Elim Q → (x : Colimitᴱ P₀ P₊ step₀ step₊) → Q x
elim e = elimᴾ λ where
    .∣∣₀ʳ       → E.∣∣₀ʳ
    .∣∣₊ʳ       → E.∣∣₊ʳ
    .∣∣₊≡∣∣₀ʳ x → subst≡→[]≡ (E.∣∣₊≡∣∣₀ʳ x)
    .∣∣₊≡∣∣₊ʳ x → subst≡→[]≡ (E.∣∣₊≡∣∣₊ʳ x)
  where
  module E = Elim e

-- Two "computation" rules.

@0 elim-∣∣₊≡∣∣₀ : dcong (elim e) (∣∣₊≡∣∣₀ x) ≡ Elim.∣∣₊≡∣∣₀ʳ e x
elim-∣∣₊≡∣∣₀ = dcong-subst≡→[]≡ (refl _)

@0 elim-∣∣₊≡∣∣₊ : dcong (elim e) (∣∣₊≡∣∣₊ x) ≡ Elim.∣∣₊≡∣∣₊ʳ e x
elim-∣∣₊≡∣∣₊ = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec
         (P₀ : Type p₀)
         (@0 P₊ : ℕ → Type p₊)
         (@0 step₀ : P₀ → P₊ zero)
         (@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n))
         (B : Type b) : Type (p₀ ⊔ p₊ ⊔ b) where
  no-eta-equality
  field
    ∣∣₀ʳ        : P₀ → B
    @0 ∣∣₊ʳ     : P₊ n → B
    @0 ∣∣₊≡∣∣₀ʳ : (x : P₀) → ∣∣₊ʳ (step₀ x) ≡ ∣∣₀ʳ x
    @0 ∣∣₊≡∣∣₊ʳ : (x : P₊ n) → ∣∣₊ʳ (step₊ x) ≡ ∣∣₊ʳ x

open Rec public

rec :
  {@0 P₊ : ℕ → Type p₊}
  {@0 step₀ : P₀ → P₊ zero}
  {@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)} →
  Rec P₀ P₊ step₀ step₊ B → Colimitᴱ P₀ P₊ step₀ step₊ → B
rec r = recᴾ λ where
    .∣∣₀ʳ       → R.∣∣₀ʳ
    .∣∣₊ʳ       → R.∣∣₊ʳ
    .∣∣₊≡∣∣₀ʳ x → _↔_.to ≡↔≡ (R.∣∣₊≡∣∣₀ʳ x)
    .∣∣₊≡∣∣₊ʳ x → _↔_.to ≡↔≡ (R.∣∣₊≡∣∣₊ʳ x)
  where
  module R = Rec r

-- Two "computation" rules.

@0 rec-∣∣₊≡∣∣₀ :
  {step₊ : ∀ {n} → P₊ n → P₊ (suc n)}
  {r : Rec P₀ P₊ step₀ step₊ B}
  {x : P₀} →
  cong (rec r) (∣∣₊≡∣∣₀ x) ≡ Rec.∣∣₊≡∣∣₀ʳ r x
rec-∣∣₊≡∣∣₀ = cong-≡↔≡ (refl _)

@0 rec-∣∣₊≡∣∣₊ :
  {step₊ : ∀ {n} → P₊ n → P₊ (suc n)}
  {r : Rec P₀ P₊ step₀ step₊ B}
  {x : P₊ n} →
  cong (rec r) (∣∣₊≡∣∣₊ x) ≡ Rec.∣∣₊≡∣∣₊ʳ r x
rec-∣∣₊≡∣∣₊ = cong-≡↔≡ (refl _)

------------------------------------------------------------------------
-- The universal property

-- The universal property of the sequential colimit.

universal-property :
  {@0 P₊ : ℕ → Type p₊}
  {@0 step₀ : P₀ → P₊ zero}
  {@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)} →
  (Colimitᴱ P₀ P₊ step₀ step₊ → B)
    ≃
  (∃ λ (f₀ : P₀ → B) →
     Erased (∃ λ (f₊ : ∀ n → P₊ n → B) →
               (∀ x → f₊ zero (step₀ x) ≡ f₀ x) ×
               (∀ n x → f₊ (suc n) (step₊ x) ≡ f₊ n x)))
universal-property {P₀} {B} {P₊} {step₀} {step₊} =
  Eq.↔→≃ to from to∘from from∘to
  where
  to :
    (Colimitᴱ P₀ P₊ step₀ step₊ → B) →
    ∃ λ (f₀ : P₀ → B) →
      Erased (∃ λ (f₊ : ∀ n → P₊ n → B) →
                (∀ x → f₊ zero (step₀ x) ≡ f₀ x) ×
                (∀ n x → f₊ (suc n) (step₊ x) ≡ f₊ n x))
  to h = h ∘ ∣_∣₀
       , [ (λ _ → h ∘ ∣_∣₊)
         , (λ x →
              h ∣ step₀ x ∣₊  ≡⟨ cong h (∣∣₊≡∣∣₀ x) ⟩∎
              h ∣ x ∣₀        ∎)
         , (λ _ x →
              h ∣ step₊ x ∣₊  ≡⟨ cong h (∣∣₊≡∣∣₊ x) ⟩∎
              h ∣ x ∣₊        ∎)
         ]

  from :
    (∃ λ (f₀ : P₀ → B) →
       Erased (∃ λ (f₊ : ∀ n → P₊ n → B) →
                 (∀ x → f₊ zero (step₀ x) ≡ f₀ x) ×
                 (∀ n x → f₊ (suc n) (step₊ x) ≡ f₊ n x))) →
    Colimitᴱ P₀ P₊ step₀ step₊ → B
  from (f₀ , [ f₊ , g₀ , g₊ ]) = rec λ where
    .∣∣₀ʳ     → f₀
    .∣∣₊ʳ     → f₊ _
    .∣∣₊≡∣∣₀ʳ → g₀
    .∣∣₊≡∣∣₊ʳ → g₊ _

  to∘from : ∀ p → to (from p) ≡ p
  to∘from (f₀ , [ f₊ , g₀ , g₊ ]) =
    cong (f₀ ,_) $ []-cong
      [ cong (f₊ ,_) $ cong₂ _,_
          (⟨ext⟩ λ x →
             cong (rec _) (∣∣₊≡∣∣₀ x)  ≡⟨ rec-∣∣₊≡∣∣₀ ⟩∎
             g₀ x                      ∎)
          (⟨ext⟩ λ n → ⟨ext⟩ λ x →
             cong (rec _) (∣∣₊≡∣∣₊ x)  ≡⟨ rec-∣∣₊≡∣∣₊ ⟩∎
             g₊ n x                    ∎)
      ]

  from∘to : ∀ h → from (to h) ≡ h
  from∘to h = ⟨ext⟩ $ elim λ where
    .∣∣₀ʳ _     → refl _
    .∣∣₊ʳ _     → refl _
    .∣∣₊≡∣∣₀ʳ x →
      subst (λ z → from (to h) z ≡ h z) (∣∣₊≡∣∣₀ x) (refl _)  ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans (sym (cong (from (to h)) (∣∣₊≡∣∣₀ x)))
        (trans (refl _) (cong h (∣∣₊≡∣∣₀ x)))                 ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                   rec-∣∣₊≡∣∣₀
                                                                   (trans-reflˡ _) ⟩

      trans (sym (cong h (∣∣₊≡∣∣₀ x))) (cong h (∣∣₊≡∣∣₀ x))   ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                  ∎
    .∣∣₊≡∣∣₊ʳ x →
      subst (λ z → from (to h) z ≡ h z) (∣∣₊≡∣∣₊ x) (refl _)  ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans (sym (cong (from (to h)) (∣∣₊≡∣∣₊ x)))
        (trans (refl _) (cong h (∣∣₊≡∣∣₊ x)))                 ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                   rec-∣∣₊≡∣∣₊
                                                                   (trans-reflˡ _) ⟩

      trans (sym (cong h (∣∣₊≡∣∣₊ x))) (cong h (∣∣₊≡∣∣₊ x))   ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                  ∎

-- A dependently typed variant of the sequential colimit's universal
-- property.

universal-property-Π :
  {@0 P₊ : ℕ → Type p₊}
  {@0 step₀ : P₀ → P₊ zero}
  {@0 step₊ : ∀ {n} → P₊ n → P₊ (suc n)}
  {Q : Colimitᴱ P₀ P₊ step₀ step₊ → Type q} →
  ((x : Colimitᴱ P₀ P₊ step₀ step₊) → Q x)
    ≃
  (∃ λ (f₀ : (x : P₀) → Q ∣ x ∣₀) →
     Erased (∃ λ (f₊ : ∀ n (x : P₊ n) → Q ∣ x ∣₊) →
               (∀ x → subst Q (∣∣₊≡∣∣₀ x) (f₊ zero (step₀ x)) ≡ f₀ x) ×
               (∀ n x → subst Q (∣∣₊≡∣∣₊ x) (f₊ (suc n) (step₊ x)) ≡
                        f₊ n x)))
universal-property-Π {P₀} {P₊} {step₀} {step₊} {Q} =
  Eq.↔→≃ to from to∘from from∘to
  where
  RHS =
    ∃ λ (f₀ : (x : P₀) → Q ∣ x ∣₀) →
      Erased (∃ λ (f₊ : ∀ n (x : P₊ n) → Q ∣ x ∣₊) →
                (∀ x → subst Q (∣∣₊≡∣∣₀ x) (f₊ zero (step₀ x)) ≡ f₀ x) ×
                (∀ n x → subst Q (∣∣₊≡∣∣₊ x) (f₊ (suc n) (step₊ x)) ≡
                         f₊ n x))

  to : ((x : Colimitᴱ P₀ P₊ step₀ step₊) → Q x) → RHS
  to h = h ∘ ∣_∣₀
       , [ (λ _ → h ∘ ∣_∣₊)
         , (λ x →
              subst Q (∣∣₊≡∣∣₀ x) (h ∣ step₀ x ∣₊)  ≡⟨ dcong h (∣∣₊≡∣∣₀ x) ⟩∎
              h ∣ x ∣₀                              ∎)
         , (λ _ x →
              subst Q (∣∣₊≡∣∣₊ x) (h ∣ step₊ x ∣₊)  ≡⟨ dcong h (∣∣₊≡∣∣₊ x) ⟩∎
              h ∣ x ∣₊                              ∎)
         ]

  from :
    RHS → (x : Colimitᴱ P₀ P₊ step₀ step₊) → Q x
  from (f₀ , [ f₊ , g₀ , g₊ ]) = elim λ where
    .∣∣₀ʳ     → f₀
    .∣∣₊ʳ     → f₊ _
    .∣∣₊≡∣∣₀ʳ → g₀
    .∣∣₊≡∣∣₊ʳ → g₊ _

  to∘from : ∀ p → to (from p) ≡ p
  to∘from (f₀ , [ f₊ , g₀ , g₊ ]) =
    cong (f₀ ,_) $ []-cong
      [ cong (f₊ ,_) $ cong₂ _,_
          (⟨ext⟩ λ x →
             dcong (elim _) (∣∣₊≡∣∣₀ x)  ≡⟨ elim-∣∣₊≡∣∣₀ ⟩∎
             g₀ x                        ∎)
          (⟨ext⟩ λ n → ⟨ext⟩ λ x →
             dcong (elim _) (∣∣₊≡∣∣₊ x)  ≡⟨ elim-∣∣₊≡∣∣₊ ⟩∎
             g₊ n x                      ∎)
      ]

  from∘to : ∀ h → from (to h) ≡ h
  from∘to h = ⟨ext⟩ $ elim λ where
    .∣∣₀ʳ _     → refl _
    .∣∣₊ʳ _     → refl _
    .∣∣₊≡∣∣₀ʳ x →
      subst (λ z → from (to h) z ≡ h z) (∣∣₊≡∣∣₀ x) (refl _)   ≡⟨ subst-in-terms-of-trans-and-dcong ⟩

      trans (sym (dcong (from (to h)) (∣∣₊≡∣∣₀ x)))
        (trans (cong (subst Q (∣∣₊≡∣∣₀ x)) (refl _))
           (dcong h (∣∣₊≡∣∣₀ x)))                              ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                    elim-∣∣₊≡∣∣₀
                                                                    (trans (cong (flip trans _) $ cong-refl _) $
                                                                     trans-reflˡ _) ⟩

      trans (sym (dcong h (∣∣₊≡∣∣₀ x))) (dcong h (∣∣₊≡∣∣₀ x))  ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                   ∎
    .∣∣₊≡∣∣₊ʳ x →
      subst (λ z → from (to h) z ≡ h z) (∣∣₊≡∣∣₊ x) (refl _)   ≡⟨ subst-in-terms-of-trans-and-dcong ⟩

      trans (sym (dcong (from (to h)) (∣∣₊≡∣∣₊ x)))
        (trans (cong (subst Q (∣∣₊≡∣∣₊ x)) (refl _))
           (dcong h (∣∣₊≡∣∣₊ x)))                              ≡⟨ cong₂ (λ p q → trans (sym p) q)
                                                                    elim-∣∣₊≡∣∣₊
                                                                    (trans (cong (flip trans _) $ cong-refl _) $
                                                                     trans-reflˡ _) ⟩

      trans (sym (dcong h (∣∣₊≡∣∣₊ x))) (dcong h (∣∣₊≡∣∣₊ x))  ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                   ∎
