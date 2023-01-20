------------------------------------------------------------------------
-- The one-step truncation
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the one-step truncation operator
-- uses path equality, but the supplied notion of equality is used for
-- many other things.

import Equality.Path as P

module H-level.Truncation.Propositional.One-step
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J using (Constant)
import Equality.Decidable-UIP P.equality-with-J as PD
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence.Erased.Basics equality-with-J as EEq
  using (_≃ᴱ_)
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.One-step.Erased eq as O
  using (∥_∥¹ᴱ; ∥_∥¹ᴱ-out-^; ∥_∥¹ᴱ-in-^)
open import Surjection equality-with-J using (_↠_)

private
  variable
    a b p   : Level
    A B     : Type a
    P       : A → Type p
    e r x y : A
    n       : ℕ

------------------------------------------------------------------------
-- The type

-- One-step truncation.
--
-- This definition is based on that in van Doorn's "Constructing the
-- Propositional Truncation using Non-recursive HITs".

data ∥_∥¹ (A : Type a) : Type a where
  ∣_∣          : A → ∥ A ∥¹
  ∣∣-constantᴾ : PD.Constant ∣_∣

-- The function ∣_∣ is constant.

∣∣-constant : Constant (∣_∣ {A = A})
∣∣-constant x y = _↔_.from ≡↔≡ (∣∣-constantᴾ x y)

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : ∥ A ∥¹ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ          : ∀ x → P ∣ x ∣
    ∣∣-constantʳ :
      (x y : A) →
      P.[ (λ i → P (∣∣-constantᴾ x y i)) ] ∣∣ʳ x ≡ ∣∣ʳ y

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : ∥ A ∥¹) → P x
elimᴾ {A} {P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : ∥ A ∥¹) → P x
  helper ∣ x ∣                = E.∣∣ʳ x
  helper (∣∣-constantᴾ x y i) = E.∣∣-constantʳ x y i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ          : A → B
    ∣∣-constantʳ : PD.Constant ∣∣ʳ

open Recᴾ public

recᴾ : Recᴾ A B → ∥ A ∥¹ → B
recᴾ r = elimᴾ λ where
    .∣∣ʳ          → R.∣∣ʳ
    .∣∣-constantʳ → R.∣∣-constantʳ
  where
  module R = Recᴾ r

-- A dependent eliminator.

record Elim {A : Type a} (P : ∥ A ∥¹ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ          : ∀ x → P ∣ x ∣
    ∣∣-constantʳ :
      (x y : A) → subst P (∣∣-constant x y) (∣∣ʳ x) ≡ ∣∣ʳ y

open Elim public

elim : Elim P → (x : ∥ A ∥¹) → P x
elim e = elimᴾ λ where
    .∣∣ʳ              → E.∣∣ʳ
    .∣∣-constantʳ x y → subst≡→[]≡ (E.∣∣-constantʳ x y)
  where
  module E = Elim e

-- A "computation" rule.

elim-∣∣-constant :
  dcong (elim e) (∣∣-constant x y) ≡ Elim.∣∣-constantʳ e x y
elim-∣∣-constant = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ          : A → B
    ∣∣-constantʳ : Constant ∣∣ʳ

open Rec public

rec : Rec A B → ∥ A ∥¹ → B
rec r = recᴾ λ where
    .∣∣ʳ              → R.∣∣ʳ
    .∣∣-constantʳ x y → _↔_.to ≡↔≡ (R.∣∣-constantʳ x y)
  where
  module R = Rec r

-- A "computation" rule.

rec-∣∣-constant :
  cong (rec r) (∣∣-constant x y) ≡ Rec.∣∣-constantʳ r x y
rec-∣∣-constant = cong-≡↔≡ (refl _)

-- A variant of rec.

rec′ : (f : A → B) → Constant f → ∥ A ∥¹ → B
rec′ f c = rec λ where
  .Rec.∣∣ʳ          → f
  .Rec.∣∣-constantʳ → c

------------------------------------------------------------------------
-- Some preservation lemmas

-- A map function for ∥_∥¹.

∥∥¹-map : (A → B) → ∥ A ∥¹ → ∥ B ∥¹
∥∥¹-map f = rec λ where
  .∣∣ʳ x            → ∣ f x ∣
  .∣∣-constantʳ x y → ∣∣-constant (f x) (f y)

-- The truncation operator preserves logical equivalences.

∥∥¹-cong-⇔ : A ⇔ B → ∥ A ∥¹ ⇔ ∥ B ∥¹
∥∥¹-cong-⇔ A⇔B = record
  { to   = ∥∥¹-map (_⇔_.to   A⇔B)
  ; from = ∥∥¹-map (_⇔_.from A⇔B)
  }

private

  -- A lemma used below.

  ∥∥¹-cong-lemma :
    (f : A → B) (g : B → A) (eq : ∀ x → f (g x) ≡ x) →
    subst (λ z → ∥∥¹-map f (∥∥¹-map g z) ≡ z)
      (∣∣-constant x y) (cong ∣_∣ (eq x)) ≡
    cong ∣_∣ (eq y)
  ∥∥¹-cong-lemma {x} {y} f g eq =
    subst
      (λ z → ∥∥¹-map f (∥∥¹-map g z) ≡ z)
      (∣∣-constant x y) (cong ∣_∣ (eq x))                         ≡⟨ subst-in-terms-of-trans-and-cong ⟩

    trans (sym (cong (∥∥¹-map f ∘ ∥∥¹-map g) (∣∣-constant x y)))
      (trans (cong ∣_∣ (eq x)) (cong id (∣∣-constant x y)))       ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong ∣_∣ (eq x)) q))
                                                                       (trans (sym $ cong-∘ _ _ _) $
                                                                        trans (cong (cong (∥∥¹-map f)) rec-∣∣-constant) $
                                                                        rec-∣∣-constant)
                                                                       (sym $ cong-id _) ⟩
    trans (sym (∣∣-constant (f (g x)) (f (g y))))
      (trans (cong ∣_∣ (eq x)) (∣∣-constant x y))                 ≡⟨ cong (λ f → trans _ (trans (cong ∣_∣ (f _)) _)) $ sym $
                                                                     _≃_.left-inverse-of Π≡≃≡ eq ⟩
    trans (sym (∣∣-constant (f (g x)) (f (g y))))
      (trans (cong ∣_∣ (ext⁻¹ (⟨ext⟩ eq) x)) (∣∣-constant x y))   ≡⟨ elim₁
                                                                       (λ {f} eq → trans (sym (∣∣-constant (f x) (f y)))
                                                                                     (trans (cong ∣_∣ (ext⁻¹ eq x)) (∣∣-constant x y)) ≡
                                                                                   cong ∣_∣ (ext⁻¹ eq y))
                                                                       (
      trans (sym (∣∣-constant x y))
        (trans (cong ∣_∣ (ext⁻¹ (refl id) x)) (∣∣-constant x y))        ≡⟨ cong (trans _) $
                                                                           trans (cong (flip trans _) $
                                                                                  trans (cong (cong _) $ cong-refl _) $
                                                                                  cong-refl _) $
                                                                           trans-reflˡ _ ⟩

      trans (sym (∣∣-constant x y)) (∣∣-constant x y)                   ≡⟨ trans-symˡ _ ⟩

      refl _                                                            ≡⟨ trans (sym $ cong-refl _) $
                                                                           cong (cong _) $ sym $ cong-refl _ ⟩∎
      cong ∣_∣ (ext⁻¹ (refl _) y)                                       ∎)
                                                                       _ ⟩

    cong ∣_∣ (ext⁻¹ (⟨ext⟩ eq) y)                                 ≡⟨ cong (λ f → cong ∣_∣ (f _)) $
                                                                     _≃_.left-inverse-of Π≡≃≡ eq ⟩∎
    cong ∣_∣ (eq y)                                               ∎

-- The truncation operator preserves split surjections.

∥∥¹-cong-↠ : A ↠ B → ∥ A ∥¹ ↠ ∥ B ∥¹
∥∥¹-cong-↠ A↠B = record
  { logical-equivalence = ∥∥¹-cong-⇔ (_↠_.logical-equivalence A↠B)
  ; right-inverse-of    = elim λ where
      .∣∣ʳ x            → cong ∣_∣ (_↠_.right-inverse-of A↠B x)
      .∣∣-constantʳ x y →
        ∥∥¹-cong-lemma (_↠_.to A↠B) (_↠_.from A↠B)
          (_↠_.right-inverse-of A↠B)
  }

-- The truncation operator preserves bijections.

∥∥¹-cong-↔ : A ↔ B → ∥ A ∥¹ ↔ ∥ B ∥¹
∥∥¹-cong-↔ A↔B = record
  { surjection      = ∥∥¹-cong-↠ (_↔_.surjection A↔B)
  ; left-inverse-of = elim λ where
      .∣∣ʳ x            → cong ∣_∣ (_↔_.left-inverse-of A↔B x)
      .∣∣-constantʳ x y →
        ∥∥¹-cong-lemma (_↔_.from A↔B) (_↔_.to A↔B)
          (_↔_.left-inverse-of A↔B)
  }

-- The truncation operator preserves equivalences.

∥∥¹-cong-≃ : A ≃ B → ∥ A ∥¹ ≃ ∥ B ∥¹
∥∥¹-cong-≃ = from-isomorphism ∘ ∥∥¹-cong-↔ ∘ from-isomorphism

-- The truncation operator preserves equivalences with erased proofs.

∥∥¹-cong-≃ᴱ : A ≃ᴱ B → ∥ A ∥¹ ≃ᴱ ∥ B ∥¹
∥∥¹-cong-≃ᴱ A≃B = EEq.[≃]→≃ᴱ (EEq.[proofs] (∥∥¹-cong-≃ (EEq.≃ᴱ→≃ A≃B)))

------------------------------------------------------------------------
-- Iterated applications of the one-step truncation operator

-- Applies the one-step truncation the given number of times, from the
-- "outside".
--
-- This definition and the next one are taken from van Doorn's
-- "Constructing the Propositional Truncation using Non-recursive
-- HITs".

∥_∥¹-out-^ : Type a → ℕ → Type a
∥ A ∥¹-out-^ zero    = A
∥ A ∥¹-out-^ (suc n) = ∥ ∥ A ∥¹-out-^ n ∥¹

-- A "constructor" for ∥_∥¹-out-^.

∣_∣-out-^ : A → ∀ n → ∥ A ∥¹-out-^ n
∣ x ∣-out-^ zero    = x
∣ x ∣-out-^ (suc n) = ∣ ∣ x ∣-out-^ n ∣

-- A rearrangement lemma.

∥∥¹-out-^+≃ : ∀ m → ∥ A ∥¹-out-^ (m + n) ≃ ∥ ∥ A ∥¹-out-^ n ∥¹-out-^ m
∥∥¹-out-^+≃         zero    = F.id
∥∥¹-out-^+≃ {A} {n} (suc m) =
  ∥ ∥ A ∥¹-out-^ (m + n) ∥¹         ↝⟨ ∥∥¹-cong-≃ (∥∥¹-out-^+≃ m) ⟩□
  ∥ ∥ ∥ A ∥¹-out-^ n ∥¹-out-^ m ∥¹  □

-- ∥_∥¹ commutes with ∥_∥¹-out-^ n.

∥∥¹-∥∥¹-out-^-commute : ∀ n → ∥ ∥ A ∥¹-out-^ n ∥¹ ↔ ∥ ∥ A ∥¹ ∥¹-out-^ n
∥∥¹-∥∥¹-out-^-commute     zero    = F.id
∥∥¹-∥∥¹-out-^-commute {A} (suc n) =
  ∥ ∥ ∥ A ∥¹-out-^ n ∥¹ ∥¹  ↝⟨ ∥∥¹-cong-↔ (∥∥¹-∥∥¹-out-^-commute n) ⟩□
  ∥ ∥ ∥ A ∥¹ ∥¹-out-^ n ∥¹  □

private

  -- The lemma above is defined using _↔_ rather than _≃_ because the
  -- following equalities hold by definition when _↔_ is used, but (at
  -- the time of writing) the second one does not hold when _≃_ is
  -- used.

  _ :
    {x : A} →
    _↔_.left-inverse-of (∥∥¹-∥∥¹-out-^-commute 0) ∣ x ∣ ≡ refl ∣ x ∣
  _ = refl _

  _ :
    {A : Type a} {x : ∥ A ∥¹-out-^ (suc n)} →
    _↔_.left-inverse-of (∥∥¹-∥∥¹-out-^-commute (1 + n)) ∣ x ∣ ≡
    cong ∣_∣ (_↔_.left-inverse-of (∥∥¹-∥∥¹-out-^-commute n) x)
  _ = refl _

-- A variant of ∥_∥¹-out-^ which applies the one-step truncation the
-- given number of times from the "inside".

∥_∥¹-in-^ : Type a → ℕ → Type a
∥ A ∥¹-in-^ zero    = A
∥ A ∥¹-in-^ (suc n) = ∥ ∥ A ∥¹ ∥¹-in-^ n

-- The two variants of ∥_∥¹^ are pointwise equivalent.

∥∥¹-out-^≃∥∥¹-in-^ : ∀ n → ∥ A ∥¹-out-^ n ≃ ∥ A ∥¹-in-^ n
∥∥¹-out-^≃∥∥¹-in-^     zero    = F.id
∥∥¹-out-^≃∥∥¹-in-^ {A} (suc n) =
  ∥ ∥ A ∥¹-out-^ n ∥¹  ↔⟨ ∥∥¹-∥∥¹-out-^-commute n ⟩
  ∥ ∥ A ∥¹ ∥¹-out-^ n  ↝⟨ ∥∥¹-out-^≃∥∥¹-in-^ n ⟩□
  ∥ ∥ A ∥¹ ∥¹-in-^ n   □

-- ∥_∥¹ commutes with ∥_∥¹-in-^ n.

∥∥¹-∥∥¹-in-^-commute : ∀ n → ∥ ∥ A ∥¹-in-^ n ∥¹ ≃ ∥ ∥ A ∥¹ ∥¹-in-^ n
∥∥¹-∥∥¹-in-^-commute {A} n =
  ∥ ∥ A ∥¹-in-^ n ∥¹    ↝⟨ ∥∥¹-cong-≃ (inverse $ ∥∥¹-out-^≃∥∥¹-in-^ n) ⟩
  ∥ ∥ A ∥¹-out-^ n ∥¹   ↔⟨⟩
  ∥ A ∥¹-out-^ (suc n)  ↝⟨ ∥∥¹-out-^≃∥∥¹-in-^ (suc n) ⟩
  ∥ A ∥¹-in-^ (suc n)   ↔⟨⟩
  ∥ ∥ A ∥¹ ∥¹-in-^ n    □

-- A "constructor" for ∥_∥¹-in-^.

∣_,_∣-in-^ : ∀ n → ∥ A ∥¹-in-^ n → ∥ A ∥¹-in-^ (suc n)
∣ zero  , x ∣-in-^ = ∣ x ∣
∣ suc n , x ∣-in-^ = ∣ n , x ∣-in-^

-- ∣_,_∣-in-^ is related to ∣_∣.

∣∣≡∣,∣-in-^ :
  ∀ n {x : ∥ A ∥¹-out-^ n} →
  _≃_.to (∥∥¹-out-^≃∥∥¹-in-^ (suc n)) ∣ x ∣ ≡
  ∣ n , _≃_.to (∥∥¹-out-^≃∥∥¹-in-^ n) x ∣-in-^
∣∣≡∣,∣-in-^ zero    {x} = ∣ x ∣  ∎
∣∣≡∣,∣-in-^ (suc n) {x} =
  _≃_.to (∥∥¹-out-^≃∥∥¹-in-^ (2 + n)) ∣ x ∣            ≡⟨⟩

  _≃_.to (∥∥¹-out-^≃∥∥¹-in-^ (1 + n))
    ∣ _↔_.to (∥∥¹-∥∥¹-out-^-commute n) x ∣             ≡⟨ ∣∣≡∣,∣-in-^ n ⟩∎

  ∣ n , _≃_.to (∥∥¹-out-^≃∥∥¹-in-^ n)
          (_↔_.to (∥∥¹-∥∥¹-out-^-commute n) x) ∣-in-^  ∎

-- A variant of ∣∣≡∣,∣-in-^.

∣,∣-in-^≡∣∣ :
  ∀ n {x : ∥ A ∥¹-in-^ n} →
  _≃_.from (∥∥¹-out-^≃∥∥¹-in-^ (suc n)) ∣ n , x ∣-in-^ ≡
  ∣ _≃_.from (∥∥¹-out-^≃∥∥¹-in-^ n) x ∣
∣,∣-in-^≡∣∣ zero    {x} = ∣ x ∣  ∎
∣,∣-in-^≡∣∣ (suc n) {x} =
  _≃_.from (∥∥¹-out-^≃∥∥¹-in-^ (2 + n)) ∣ 1 + n , x ∣-in-^  ≡⟨⟩

  _↔_.from (∥∥¹-∥∥¹-out-^-commute (1 + n))
    (_≃_.from (∥∥¹-out-^≃∥∥¹-in-^ (1 + n)) ∣ n , x ∣-in-^)  ≡⟨ cong (_↔_.from (∥∥¹-∥∥¹-out-^-commute (1 + n))) $ ∣,∣-in-^≡∣∣ n ⟩∎

  _↔_.from (∥∥¹-∥∥¹-out-^-commute (1 + n))
    ∣ _≃_.from (∥∥¹-out-^≃∥∥¹-in-^ n) x ∣                   ∎

------------------------------------------------------------------------
-- Some conversion functions

-- ∥ A ∥¹ᴱ implies ∥ A ∥¹.

∥∥¹ᴱ→∥∥¹ : ∥ A ∥¹ᴱ → ∥ A ∥¹
∥∥¹ᴱ→∥∥¹ = O.rec λ where
  .O.∣∣ʳ          → ∣_∣
  .O.∣∣-constantʳ → ∣∣-constant

-- In erased contexts ∥ A ∥¹ᴱ is equivalent to ∥ A ∥¹.

@0 ∥∥¹ᴱ≃∥∥¹ : ∥ A ∥¹ᴱ ≃ ∥ A ∥¹
∥∥¹ᴱ≃∥∥¹ = Eq.↔→≃
  ∥∥¹ᴱ→∥∥¹
  ∥∥¹→∥∥¹ᴱ
  (elim λ @0 where
     .∣∣ʳ _            → refl _
     .∣∣-constantʳ x y →
       subst (λ x → ∥∥¹ᴱ→∥∥¹ (∥∥¹→∥∥¹ᴱ x) ≡ x)
         (∣∣-constant x y) (refl _)                                ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (∥∥¹ᴱ→∥∥¹ ∘ ∥∥¹→∥∥¹ᴱ) (∣∣-constant x y)))
         (trans (refl _) (cong id (∣∣-constant x y)))              ≡⟨ cong₂ (trans ∘ sym)
                                                                        (trans (sym $ cong-∘ _ _ _) $
                                                                        trans (cong (cong ∥∥¹ᴱ→∥∥¹) rec-∣∣-constant) $
                                                                        O.rec-∣∣-constant)
                                                                        (trans (trans-reflˡ _) $
                                                                         sym $ cong-id _) ⟩

       trans (sym (∣∣-constant x y)) (∣∣-constant x y)             ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                      ∎)
  (O.elim λ where
     .O.∣∣ʳ _            → refl _
     .O.∣∣-constantʳ x y →
       subst (λ x → ∥∥¹→∥∥¹ᴱ (∥∥¹ᴱ→∥∥¹ x) ≡ x)
         (O.∣∣-constant x y) (refl _)                                ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (∥∥¹→∥∥¹ᴱ ∘ ∥∥¹ᴱ→∥∥¹) (O.∣∣-constant x y)))
         (trans (refl _) (cong id (O.∣∣-constant x y)))              ≡⟨ cong₂ (trans ∘ sym)
                                                                          (trans (sym $ cong-∘ _ _ _) $
                                                                          trans (cong (cong ∥∥¹→∥∥¹ᴱ) O.rec-∣∣-constant) $
                                                                          rec-∣∣-constant)
                                                                          (trans (trans-reflˡ _) $
                                                                           sym $ cong-id _) ⟩

       trans (sym (O.∣∣-constant x y)) (O.∣∣-constant x y)           ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                        ∎)
  where
  ∥∥¹→∥∥¹ᴱ = rec′ O.∣_∣ O.∣∣-constant

-- ∥ A ∥¹ᴱ-out-^ n implies ∥ A ∥¹-out-^ n.

∥∥¹ᴱ-out-^→∥∥¹-out-^ : ∀ n → ∥ A ∥¹ᴱ-out-^ n → ∥ A ∥¹-out-^ n
∥∥¹ᴱ-out-^→∥∥¹-out-^     zero    = id
∥∥¹ᴱ-out-^→∥∥¹-out-^ {A} (suc n) =
  ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ→∥∥¹ ⟩
  ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹   ↝⟨ ∥∥¹-map (∥∥¹ᴱ-out-^→∥∥¹-out-^ n) ⟩□
  ∥ ∥ A ∥¹-out-^ n ∥¹    □

-- In erased contexts ∥ A ∥¹ᴱ-out-^ n is equivalent to ∥ A ∥¹-out-^ n.

@0 ∥∥¹ᴱ-out-^≃∥∥¹-out-^ : ∀ n → ∥ A ∥¹ᴱ-out-^ n ≃ ∥ A ∥¹-out-^ n
∥∥¹ᴱ-out-^≃∥∥¹-out-^ n =
  Eq.with-other-function
    (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ n)
    (∥∥¹ᴱ-out-^→∥∥¹-out-^ n)
    (lemma n)
  where
  ∥∥¹ᴱ-out-^≃∥∥¹-out-^′ : ∀ n → ∥ A ∥¹ᴱ-out-^ n ≃ ∥ A ∥¹-out-^ n
  ∥∥¹ᴱ-out-^≃∥∥¹-out-^′     zero    = F.id
  ∥∥¹ᴱ-out-^≃∥∥¹-out-^′ {A} (suc n) =
    ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ≃∥∥¹ ⟩
    ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹   ↝⟨ ∥∥¹-cong-≃ (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ n) ⟩□
    ∥ ∥ A ∥¹-out-^ n ∥¹    □

  lemma :
    ∀ n (x : ∥ A ∥¹ᴱ-out-^ n) →
    _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ n) x ≡ ∥∥¹ᴱ-out-^→∥∥¹-out-^ n x
  lemma zero    _ = refl _
  lemma (suc n) x =
    _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ (suc n)) x                 ≡⟨⟩
    ∥∥¹-map (_≃_.to (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ n)) (∥∥¹ᴱ→∥∥¹ x)  ≡⟨ cong (λ f → ∥∥¹-map f (∥∥¹ᴱ→∥∥¹ x)) $
                                                                ⟨ext⟩ (lemma n) ⟩
    ∥∥¹-map (∥∥¹ᴱ-out-^→∥∥¹-out-^ n) (∥∥¹ᴱ→∥∥¹ x)            ≡⟨⟩
    ∥∥¹ᴱ-out-^→∥∥¹-out-^ (suc n) x                           ∎

-- ∥ A ∥¹ᴱ-in-^ n implies ∥ A ∥¹-in-^ n.

∥∥¹ᴱ-in-^→∥∥¹-in-^ : ∀ n → ∥ A ∥¹ᴱ-in-^ n → ∥ A ∥¹-in-^ n
∥∥¹ᴱ-in-^→∥∥¹-in-^     zero    = id
∥∥¹ᴱ-in-^→∥∥¹-in-^ {A} (suc n) =
  ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-in-^ n  ↔⟨ inverse $ O.∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n ⟩
  ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ→∥∥¹ ⟩
  ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹   ↝⟨ ∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n) ⟩
  ∥ ∥ A ∥¹-in-^ n ∥¹    ↔⟨ ∥∥¹-∥∥¹-in-^-commute n ⟩□
  ∥ ∥ A ∥¹ ∥¹-in-^ n    □

-- In erased contexts ∥ A ∥¹ᴱ-in-^ n is equivalent to ∥ A ∥¹-in-^ n.

@0 ∥∥¹ᴱ-in-^≃∥∥¹-in-^ : ∀ n → ∥ A ∥¹ᴱ-in-^ n ≃ ∥ A ∥¹-in-^ n
∥∥¹ᴱ-in-^≃∥∥¹-in-^ n =
  Eq.with-other-function
    (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ n)
    (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
    (lemma n)
  where
  ∥∥¹ᴱ-in-^≃∥∥¹-in-^′ : ∀ n → ∥ A ∥¹ᴱ-in-^ n ≃ ∥ A ∥¹-in-^ n
  ∥∥¹ᴱ-in-^≃∥∥¹-in-^′     zero    = F.id
  ∥∥¹ᴱ-in-^≃∥∥¹-in-^′ {A} (suc n) =
    ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-in-^ n  ↝⟨ inverse $ O.∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n ⟩
    ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ≃∥∥¹ ⟩
    ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹   ↝⟨ ∥∥¹-cong-≃ (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ n) ⟩
    ∥ ∥ A ∥¹-in-^ n ∥¹    ↝⟨ ∥∥¹-∥∥¹-in-^-commute n ⟩□
    ∥ ∥ A ∥¹ ∥¹-in-^ n    □

  lemma :
    ∀ n (x : ∥ A ∥¹ᴱ-in-^ n) →
    _≃_.to (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ n) x ≡ ∥∥¹ᴱ-in-^→∥∥¹-in-^ n x
  lemma zero    _ = refl _
  lemma (suc n) x =
    _≃_.to (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ (suc n)) x                      ≡⟨⟩

    _≃_.to (∥∥¹-∥∥¹-in-^-commute n)
      (∥∥¹-map (_≃_.to (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ n))
         (∥∥¹ᴱ→∥∥¹ (_≃_.from (O.∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n) x)))  ≡⟨ cong (λ f → _≃_.to (∥∥¹-∥∥¹-in-^-commute n)
                                                                                 (∥∥¹-map f (∥∥¹ᴱ→∥∥¹ (_≃_.from (O.∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n) x)))) $
                                                                   ⟨ext⟩ (lemma n) ⟩
    _≃_.to (∥∥¹-∥∥¹-in-^-commute n)
      (∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
         (∥∥¹ᴱ→∥∥¹ (_≃_.from (O.∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n) x)))  ≡⟨⟩

    ∥∥¹ᴱ-in-^→∥∥¹-in-^ (suc n) x                                ∎

-- ∥∥¹ᴱ-in-^→∥∥¹-in-^ commutes (kind of) with O.∣_,_∣-in-^/∣_,_∣-in-^.

∥∥¹ᴱ-in-^→∥∥¹-in-^-∣,∣-in-^ :
  ∀ n {x : ∥ A ∥¹ᴱ-in-^ n} →
  ∥∥¹ᴱ-in-^→∥∥¹-in-^ (suc n) O.∣ n , x ∣-in-^ ≡
  ∣ n , ∥∥¹ᴱ-in-^→∥∥¹-in-^ n x ∣-in-^
∥∥¹ᴱ-in-^→∥∥¹-in-^-∣,∣-in-^ n {x} =
  ∥∥¹ᴱ-in-^→∥∥¹-in-^ (1 + n) O.∣ n , x ∣-in-^                ≡⟨⟩

  _≃_.to (∥∥¹-∥∥¹-in-^-commute n)
    (∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
       (∥∥¹ᴱ→∥∥¹
          (O.∥∥¹ᴱ-map (_≃_.to (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n))
             (_≃_.from (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (1 + n))
                O.∣ n , x ∣-in-^))))                         ≡⟨ cong (λ x → _≃_.to (∥∥¹-∥∥¹-in-^-commute n)
                                                                              (∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
                                                                                 (∥∥¹ᴱ→∥∥¹ (O.∥∥¹ᴱ-map (_≃_.to (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n)) x)))) $
                                                                O.∣,∣-in-^≡∣∣ n ⟩
  _≃_.to (∥∥¹-∥∥¹-in-^-commute n)
    (∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
       (∥∥¹ᴱ→∥∥¹
          (O.∥∥¹ᴱ-map (_≃_.to (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n))
             O.∣ _≃_.from (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x ∣)))  ≡⟨⟩

  _≃_.to (∥∥¹-out-^≃∥∥¹-in-^ (1 + n))
    ∣ _≃_.from (∥∥¹-out-^≃∥∥¹-in-^ n)
        (∥∥¹ᴱ-in-^→∥∥¹-in-^ n
           (_≃_.to (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n)
              (_≃_.from (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x))) ∣    ≡⟨ ∣∣≡∣,∣-in-^ n ⟩

  ∣ n
  , _≃_.to (∥∥¹-out-^≃∥∥¹-in-^ n)
      (_≃_.from (∥∥¹-out-^≃∥∥¹-in-^ n)
         (∥∥¹ᴱ-in-^→∥∥¹-in-^ n
            (_≃_.to (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n)
               (_≃_.from (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x))))
  ∣-in-^                                                     ≡⟨ cong ∣ n ,_∣-in-^ $
                                                                trans (_≃_.right-inverse-of (∥∥¹-out-^≃∥∥¹-in-^ n) _) $
                                                                cong (∥∥¹ᴱ-in-^→∥∥¹-in-^ n) $
                                                                _≃_.right-inverse-of (O.∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) _ ⟩∎
  ∣ n , ∥∥¹ᴱ-in-^→∥∥¹-in-^ n x ∣-in-^                        ∎

-- A variant of ∥∥¹ᴱ-in-^→∥∥¹-in-^-∣,∣-in-^.

@0 from-∥∥¹ᴱ-in-^≃∥∥¹-in-^-∣,∣-in-^ :
  ∀ n {x : ∥ A ∥¹-in-^ n} →
  _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n)) ∣ n , x ∣-in-^ ≡
  O.∣ n , _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n) x ∣-in-^
from-∥∥¹ᴱ-in-^≃∥∥¹-in-^-∣,∣-in-^ n {x} =
  _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n)) ∣ n , x ∣-in-^  ≡⟨ cong (λ x → _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n)) ∣ n , x ∣-in-^) $ sym $
                                                           _≃_.right-inverse-of (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n) _ ⟩
  _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n))
    ∣ n , _≃_.to (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n)
            (_≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n) x) ∣-in-^  ≡⟨ _≃_.to-from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n)) (∥∥¹ᴱ-in-^→∥∥¹-in-^-∣,∣-in-^ n) ⟩∎

  O.∣ n , _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n) x ∣-in-^      ∎
