------------------------------------------------------------------------
-- The sequential colimit HIT with an erased higher constructor
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- The definition of sequential colimits and the statement of the
-- non-dependent universal property are based on those in van Doorn's
-- "Constructing the Propositional Truncation using Non-recursive
-- HITs".

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining sequential colimits uses path
-- equality, but the supplied notion of equality is used for many
-- other things.

import Equality.Path as P

module Colimit.Sequential.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Erased.Cubical eq

private
  variable
    a b p q : Level
    A B     : Type a
    P       : A → Type p
    n       : ℕ
    e x     : A

------------------------------------------------------------------------
-- The type

-- Sequential colimits, with an erased higher constructor.

data Colimitᴱ (P : ℕ → Type p) (@0 step : ∀ {n} → P n → P (suc n)) :
             Type p where
  ∣_∣       : P n → Colimitᴱ P step
  @0 ∣∣≡∣∣ᴾ : (x : P n) → ∣ step x ∣ P.≡ ∣ x ∣

-- A variant of ∣∣≡∣∣ᴾ.

@0 ∣∣≡∣∣ :
  {step : ∀ {n} → P n → P (suc n)} (x : P n) →
  _≡_ {A = Colimitᴱ P step} ∣ step x ∣ ∣ x ∣
∣∣≡∣∣ x = _↔_.from ≡↔≡ (∣∣≡∣∣ᴾ x)

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ
         {P : ℕ → Type p} {@0 step : ∀ {n} → P n → P (suc n)}
         (Q : Colimitᴱ P step → Type q) : Type (p ⊔ q) where
  no-eta-equality
  field
    ∣∣ʳ       : (x : P n) → Q ∣ x ∣
    @0 ∣∣≡∣∣ʳ :
      (x : P n) →
      P.[ (λ i → Q (∣∣≡∣∣ᴾ x i)) ] ∣∣ʳ (step x) ≡ ∣∣ʳ x

open Elimᴾ public

elimᴾ :
  {@0 step : ∀ {n} → P n → P (suc n)} {Q : Colimitᴱ P step → Type q} →
  Elimᴾ Q → (x : Colimitᴱ P step) → Q x
elimᴾ {P = P} {step = step} {Q = Q} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Colimitᴱ P step) → Q x
  helper ∣ x ∣        = E.∣∣ʳ x
  helper (∣∣≡∣∣ᴾ x i) = E.∣∣≡∣∣ʳ x i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ
         (P : ℕ → Type p) (@0 step : ∀ {n} → P n → P (suc n))
         (B : Type b) : Type (p ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ       : P n → B
    @0 ∣∣≡∣∣ʳ : (x : P n) → ∣∣ʳ (step x) P.≡ ∣∣ʳ x

open Recᴾ public

recᴾ :
  {@0 step : ∀ {n} → P n → P (suc n)} →
  Recᴾ P step B → Colimitᴱ P step → B
recᴾ r = elimᴾ λ where
    .∣∣ʳ    → R.∣∣ʳ
    .∣∣≡∣∣ʳ → R.∣∣≡∣∣ʳ
  where
  module R = Recᴾ r

-- A dependent eliminator.

record Elim
         {P : ℕ → Type p} {@0 step : ∀ {n} → P n → P (suc n)}
         (Q : Colimitᴱ P step → Type q) : Type (p ⊔ q) where
  no-eta-equality
  field
    ∣∣ʳ       : (x : P n) → Q ∣ x ∣
    @0 ∣∣≡∣∣ʳ : (x : P n) → subst Q (∣∣≡∣∣ x) (∣∣ʳ (step x)) ≡ ∣∣ʳ x

open Elim public

elim :
  {@0 step : ∀ {n} → P n → P (suc n)} {Q : Colimitᴱ P step → Type q} →
  Elim Q → (x : Colimitᴱ P step) → Q x
elim e = elimᴾ λ where
    .∣∣ʳ      → E.∣∣ʳ
    .∣∣≡∣∣ʳ x → subst≡→[]≡ (E.∣∣≡∣∣ʳ x)
  where
  module E = Elim e

-- A "computation" rule.

@0 elim-∣∣≡∣∣ : dcong (elim e) (∣∣≡∣∣ x) ≡ Elim.∣∣≡∣∣ʳ e x
elim-∣∣≡∣∣ = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec
         (P : ℕ → Type p) (@0 step : ∀ {n} → P n → P (suc n))
         (B : Type b) : Type (p ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ    : P n → B
    @0 ∣∣≡∣∣ʳ : (x : P n) → ∣∣ʳ (step x) ≡ ∣∣ʳ x

open Rec public

rec :
  {@0 step : ∀ {n} → P n → P (suc n)} →
  Rec P step B → Colimitᴱ P step → B
rec r = recᴾ λ where
    .∣∣ʳ      → R.∣∣ʳ
    .∣∣≡∣∣ʳ x → _↔_.to ≡↔≡ (R.∣∣≡∣∣ʳ x)
  where
  module R = Rec r

-- A "computation" rule.

@0 rec-∣∣≡∣∣ :
  {step : ∀ {n} → P n → P (suc n)} {r : Rec P step B} {x : P n} →
  cong (rec r) (∣∣≡∣∣ x) ≡ Rec.∣∣≡∣∣ʳ r x
rec-∣∣≡∣∣ = cong-≡↔≡ (refl _)

------------------------------------------------------------------------
-- The universal property

-- The universal property of the sequential colimit.

universal-property :
  {@0 step : ∀ {n} → P n → P (suc n)} →
  (Colimitᴱ P step → B) ≃
  (∃ λ (f : ∀ n → P n → B) →
     Erased (∀ n x → f (suc n) (step x) ≡ f n x))
universal-property {P = P} {B = B} {step = step} =
  Eq.↔→≃ to from to∘from from∘to
  where
  to :
    (Colimitᴱ P step → B) →
    ∃ λ (f : ∀ n → P n → B) →
      Erased (∀ n x → f (suc n) (step x) ≡ f n x)
  to h = (λ _ → h ∘ ∣_∣)
       , [ (λ _ x →
              h ∣ step x ∣  ≡⟨ cong h (∣∣≡∣∣ x) ⟩∎
              h ∣ x ∣       ∎)
         ]

  from :
    (∃ λ (f : ∀ n → P n → B) →
       Erased (∀ n x → f (suc n) (step x) ≡ f n x)) →
    Colimitᴱ P step → B
  from (f , g) = rec λ where
    .∣∣ʳ    → f _
    .∣∣≡∣∣ʳ → erased g _

  to∘from : ∀ p → to (from p) ≡ p
  to∘from (f , g) =
    cong (f ,_) $
    []-cong
      [ (⟨ext⟩ λ n → ⟨ext⟩ λ x →
           cong (rec _) (∣∣≡∣∣ x)  ≡⟨ rec-∣∣≡∣∣ ⟩∎
           erased g n x            ∎)
      ]

  from∘to : ∀ h → from (to h) ≡ h
  from∘to h = ⟨ext⟩ $ elim λ where
    .∣∣ʳ _    → refl _
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
  {@0 step : ∀ {n} → P n → P (suc n)} →
  {Q : Colimitᴱ P step → Type q} →
  ((x : Colimitᴱ P step) → Q x) ≃
  (∃ λ (f : ∀ n (x : P n) → Q ∣ x ∣) →
     Erased (∀ n x → subst Q (∣∣≡∣∣ x) (f (suc n) (step x)) ≡ f n x))
universal-property-Π {P = P} {step = step} {Q = Q} =
  Eq.↔→≃ to from to∘from from∘to
  where
  to :
    ((x : Colimitᴱ P step) → Q x) →
    ∃ λ (f : ∀ n (x : P n) → Q ∣ x ∣) →
      Erased (∀ n x → subst Q (∣∣≡∣∣ x) (f (suc n) (step x)) ≡ f n x)
  to h = (λ _ → h ∘ ∣_∣)
       , [ (λ _ x →
              subst Q (∣∣≡∣∣ x) (h ∣ step x ∣)  ≡⟨ dcong h (∣∣≡∣∣ x) ⟩∎
              h ∣ x ∣                           ∎)
         ]

  from :
    (∃ λ (f : ∀ n (x : P n) → Q ∣ x ∣) →
       Erased (∀ n x →
               subst Q (∣∣≡∣∣ x) (f (suc n) (step x)) ≡ f n x)) →
    (x : Colimitᴱ P step) → Q x
  from (f , [ g ]) = elim λ where
    .∣∣ʳ    → f _
    .∣∣≡∣∣ʳ → g _

  to∘from : ∀ p → to (from p) ≡ p
  to∘from (f , [ g ]) = cong (f ,_) $ []-cong
    [ (⟨ext⟩ λ n → ⟨ext⟩ λ x →
         dcong (elim _) (∣∣≡∣∣ x)  ≡⟨ elim-∣∣≡∣∣ ⟩∎
         g n x                     ∎)
    ]

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
