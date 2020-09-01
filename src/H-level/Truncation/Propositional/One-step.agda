------------------------------------------------------------------------
-- The one-step truncation
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

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
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level.Closure equality-with-J
open import Surjection equality-with-J using (_↠_)

private
  variable
    a b p   : Level
    A B     : Set a
    P       : A → Set p
    e r x y : A
    n       : ℕ

------------------------------------------------------------------------
-- The type

-- One-step truncation.
--
-- This definition is based on that in van Doorn's "Constructing the
-- Propositional Truncation using Non-recursive HITs".

data ∥_∥₁ (A : Set a) : Set a where
  ∣_∣          : A → ∥ A ∥₁
  ∣∣-constantᴾ : PD.Constant (∣_∣ {A = A})

-- The function ∣_∣ is constant.

∣∣-constant : Constant (∣_∣ {A = A})
∣∣-constant x y = _↔_.from ≡↔≡ (∣∣-constantᴾ x y)

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Set a} (P : ∥ A ∥₁ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ          : ∀ x → P ∣ x ∣
    ∣∣-constantʳ :
      (x y : A) →
      P.[ (λ i → P (∣∣-constantᴾ x y i)) ] ∣∣ʳ x ≡ ∣∣ʳ y

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : ∥ A ∥₁) → P x
elimᴾ {A = A} {P = P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : ∥ A ∥₁) → P x
  helper ∣ x ∣                = E.∣∣ʳ x
  helper (∣∣-constantᴾ x y i) = E.∣∣-constantʳ x y i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ          : A → B
    ∣∣-constantʳ : PD.Constant ∣∣ʳ

open Recᴾ public

recᴾ : Recᴾ A B → ∥ A ∥₁ → B
recᴾ r = elimᴾ λ where
    .∣∣ʳ          → R.∣∣ʳ
    .∣∣-constantʳ → R.∣∣-constantʳ
  where
  module R = Recᴾ r

-- A dependent eliminator.

record Elim {A : Set a} (P : ∥ A ∥₁ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ          : ∀ x → P ∣ x ∣
    ∣∣-constantʳ :
      (x y : A) → subst P (∣∣-constant x y) (∣∣ʳ x) ≡ ∣∣ʳ y

open Elim public

elim : Elim P → (x : ∥ A ∥₁) → P x
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

record Rec (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ          : A → B
    ∣∣-constantʳ : Constant ∣∣ʳ

open Rec public

rec : Rec A B → ∥ A ∥₁ → B
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

rec′ : (f : A → B) → Constant f → ∥ A ∥₁ → B
rec′ f c = rec λ where
  .Rec.∣∣ʳ          → f
  .Rec.∣∣-constantʳ → c

------------------------------------------------------------------------
-- Some preservation lemmas

-- A map function for ∥_∥₁.

∥∥₁-map : (A → B) → ∥ A ∥₁ → ∥ B ∥₁
∥∥₁-map f = rec λ where
  .∣∣ʳ x            → ∣ f x ∣
  .∣∣-constantʳ x y → ∣∣-constant (f x) (f y)

-- The truncation operator preserves logical equivalences.

∥∥₁-cong-⇔ : A ⇔ B → ∥ A ∥₁ ⇔ ∥ B ∥₁
∥∥₁-cong-⇔ A⇔B = record
  { to   = ∥∥₁-map (_⇔_.to   A⇔B)
  ; from = ∥∥₁-map (_⇔_.from A⇔B)
  }

private

  -- A lemma used below.

  ∥∥₁-cong-lemma :
    (f : A → B) (g : B → A) (eq : ∀ x → f (g x) ≡ x) →
    subst (λ z → ∥∥₁-map f (∥∥₁-map g z) ≡ z)
      (∣∣-constant x y) (cong ∣_∣ (eq x)) ≡
    cong ∣_∣ (eq y)
  ∥∥₁-cong-lemma {x = x} {y = y} f g eq =
    subst
      (λ z → ∥∥₁-map f (∥∥₁-map g z) ≡ z)
      (∣∣-constant x y) (cong ∣_∣ (eq x))                         ≡⟨ subst-in-terms-of-trans-and-cong ⟩

    trans (sym (cong (∥∥₁-map f ∘ ∥∥₁-map g) (∣∣-constant x y)))
      (trans (cong ∣_∣ (eq x)) (cong id (∣∣-constant x y)))       ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong ∣_∣ (eq x)) q))
                                                                       (trans (sym $ cong-∘ _ _ _) $
                                                                        trans (cong (cong (∥∥₁-map f)) rec-∣∣-constant) $
                                                                        rec-∣∣-constant)
                                                                       (sym $ cong-id _) ⟩
    trans (sym (∣∣-constant (f (g x)) (f (g y))))
      (trans (cong ∣_∣ (eq x)) (∣∣-constant x y))                 ≡⟨ cong (λ f → trans _ (trans (cong ∣_∣ (f _)) _)) $ sym $
                                                                     _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext) eq ⟩
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
                                                                     _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext) eq ⟩∎
    cong ∣_∣ (eq y)                                               ∎

-- The truncation operator preserves split surjections.

∥∥₁-cong-↠ : A ↠ B → ∥ A ∥₁ ↠ ∥ B ∥₁
∥∥₁-cong-↠ A↠B = record
  { logical-equivalence = ∥∥₁-cong-⇔ (_↠_.logical-equivalence A↠B)
  ; right-inverse-of    = elim λ where
      .∣∣ʳ x            → cong ∣_∣ (_↠_.right-inverse-of A↠B x)
      .∣∣-constantʳ x y →
        ∥∥₁-cong-lemma (_↠_.to A↠B) (_↠_.from A↠B)
          (_↠_.right-inverse-of A↠B)
  }

-- The truncation operator preserves bijections.

∥∥₁-cong-↔ : A ↔ B → ∥ A ∥₁ ↔ ∥ B ∥₁
∥∥₁-cong-↔ A↔B = record
  { surjection      = ∥∥₁-cong-↠ (_↔_.surjection A↔B)
  ; left-inverse-of = elim λ where
      .∣∣ʳ x            → cong ∣_∣ (_↔_.left-inverse-of A↔B x)
      .∣∣-constantʳ x y →
        ∥∥₁-cong-lemma (_↔_.from A↔B) (_↔_.to A↔B)
          (_↔_.left-inverse-of A↔B)
  }

-- The truncation operator preserves equivalences.

∥∥₁-cong-≃ : A ≃ B → ∥ A ∥₁ ≃ ∥ B ∥₁
∥∥₁-cong-≃ = from-isomorphism ∘ ∥∥₁-cong-↔ ∘ from-isomorphism

-- The truncation operator preserves equivalences with erased proofs.

∥∥₁-cong-≃ᴱ : A ≃ᴱ B → ∥ A ∥₁ ≃ᴱ ∥ B ∥₁
∥∥₁-cong-≃ᴱ A≃B = EEq.[≃]→≃ᴱ (EEq.[proofs] (∥∥₁-cong-≃ (EEq.≃ᴱ→≃ A≃B)))

------------------------------------------------------------------------
-- Iterated applications of the one-step truncation operator

-- Applies the one-step truncation the given number of times, from the
-- "outside".
--
-- This definition and the next one are taken from van Doorn's
-- "Constructing the Propositional Truncation using Non-recursive
-- HITs".

∥_∥₁-out-^ : Set a → ℕ → Set a
∥ A ∥₁-out-^ zero    = A
∥ A ∥₁-out-^ (suc n) = ∥ ∥ A ∥₁-out-^ n ∥₁

-- A "constructor" for ∥_∥₁-out-^.

∣_∣-out-^ : A → ∀ n → ∥ A ∥₁-out-^ n
∣ x ∣-out-^ zero    = x
∣ x ∣-out-^ (suc n) = ∣ ∣ x ∣-out-^ n ∣

-- A rearrangement lemma.

∥∥₁-out-^+≃ : ∀ m → ∥ A ∥₁-out-^ (m + n) ≃ ∥ ∥ A ∥₁-out-^ n ∥₁-out-^ m
∥∥₁-out-^+≃                 zero    = F.id
∥∥₁-out-^+≃ {A = A} {n = n} (suc m) =
  ∥ ∥ A ∥₁-out-^ (m + n) ∥₁         ↝⟨ ∥∥₁-cong-≃ (∥∥₁-out-^+≃ m) ⟩□
  ∥ ∥ ∥ A ∥₁-out-^ n ∥₁-out-^ m ∥₁  □

-- ∥_∥₁ commutes with ∥_∥₁-out-^ n.

∥∥₁-∥∥₁-out-^-commute : ∀ n → ∥ ∥ A ∥₁-out-^ n ∥₁ ↔ ∥ ∥ A ∥₁ ∥₁-out-^ n
∥∥₁-∥∥₁-out-^-commute         zero    = F.id
∥∥₁-∥∥₁-out-^-commute {A = A} (suc n) =
  ∥ ∥ ∥ A ∥₁-out-^ n ∥₁ ∥₁  ↝⟨ ∥∥₁-cong-↔ (∥∥₁-∥∥₁-out-^-commute n) ⟩□
  ∥ ∥ ∥ A ∥₁ ∥₁-out-^ n ∥₁  □

private

  -- The lemma above is defined using _↔_ rather than _≃_ because the
  -- following equalities hold by definition when _↔_ is used, but (at
  -- the time of writing) not when _≃_ is used.

  _ :
    {x : A} →
    _↔_.left-inverse-of (∥∥₁-∥∥₁-out-^-commute 0) ∣ x ∣ ≡ refl ∣ x ∣
  _ = refl _

  _ :
    {A : Set a} {x : ∥ A ∥₁-out-^ (suc n)} →
    _↔_.left-inverse-of (∥∥₁-∥∥₁-out-^-commute (1 + n)) ∣ x ∣ ≡
    cong ∣_∣ (_↔_.left-inverse-of (∥∥₁-∥∥₁-out-^-commute n) x)
  _ = refl _

-- A variant of ∥_∥₁-out-^ which applies the one-step truncation the
-- given number of times from the "inside".

∥_∥₁-in-^ : Set a → ℕ → Set a
∥ A ∥₁-in-^ zero    = A
∥ A ∥₁-in-^ (suc n) = ∥ ∥ A ∥₁ ∥₁-in-^ n

-- The two variants of ∥_∥₁^ are pointwise equivalent.

∥∥₁-out-^≃∥∥₁-in-^ : ∀ n → ∥ A ∥₁-out-^ n ≃ ∥ A ∥₁-in-^ n
∥∥₁-out-^≃∥∥₁-in-^         zero    = F.id
∥∥₁-out-^≃∥∥₁-in-^ {A = A} (suc n) =
  ∥ ∥ A ∥₁-out-^ n ∥₁  ↔⟨ ∥∥₁-∥∥₁-out-^-commute n ⟩
  ∥ ∥ A ∥₁ ∥₁-out-^ n  ↝⟨ ∥∥₁-out-^≃∥∥₁-in-^ n ⟩□
  ∥ ∥ A ∥₁ ∥₁-in-^ n   □

-- ∥_∥₁ commutes with ∥_∥₁-in-^ n.

∥∥₁-∥∥₁-in-^-commute : ∀ n → ∥ ∥ A ∥₁-in-^ n ∥₁ ≃ ∥ ∥ A ∥₁ ∥₁-in-^ n
∥∥₁-∥∥₁-in-^-commute {A = A} n =
  ∥ ∥ A ∥₁-in-^ n ∥₁   ↝⟨ ∥∥₁-cong-≃ (inverse $ ∥∥₁-out-^≃∥∥₁-in-^ n) ⟩
  ∥ ∥ A ∥₁-out-^ n ∥₁  ↔⟨ ∥∥₁-∥∥₁-out-^-commute n ⟩
  ∥ ∥ A ∥₁ ∥₁-out-^ n  ↝⟨ ∥∥₁-out-^≃∥∥₁-in-^ n ⟩□
  ∥ ∥ A ∥₁ ∥₁-in-^ n   □

-- A "constructor" for ∥_∥₁-in-^.

∣_,_∣-in-^ : ∀ n → ∥ A ∥₁-in-^ n → ∥ A ∥₁-in-^ (suc n)
∣ zero  , x ∣-in-^ = ∣ x ∣
∣ suc n , x ∣-in-^ = ∣ n , x ∣-in-^

-- ∣_,_∣-in-^ is related to ∣_∣.

∣∣≡∣,∣-in-^ :
  ∀ n {x : ∥ A ∥₁-out-^ n} →
  _≃_.to (∥∥₁-out-^≃∥∥₁-in-^ (suc n)) ∣ x ∣ ≡
  ∣ n , _≃_.to (∥∥₁-out-^≃∥∥₁-in-^ n) x ∣-in-^
∣∣≡∣,∣-in-^ zero    {x = x} = ∣ x ∣  ∎
∣∣≡∣,∣-in-^ (suc n) {x = x} =
  _≃_.to (∥∥₁-out-^≃∥∥₁-in-^ (2 + n)) ∣ x ∣            ≡⟨⟩

  _≃_.to (∥∥₁-out-^≃∥∥₁-in-^ (1 + n))
    ∣ _↔_.to (∥∥₁-∥∥₁-out-^-commute n) x ∣             ≡⟨ ∣∣≡∣,∣-in-^ n ⟩∎

  ∣ n , _≃_.to (∥∥₁-out-^≃∥∥₁-in-^ n)
          (_↔_.to (∥∥₁-∥∥₁-out-^-commute n) x) ∣-in-^  ∎

-- A variant of ∣∣≡∣,∣-in-^.

∣,∣-in-^≡∣∣ :
  ∀ n {x : ∥ A ∥₁-in-^ n} →
  _≃_.from (∥∥₁-out-^≃∥∥₁-in-^ (suc n)) ∣ n , x ∣-in-^ ≡
  ∣ _≃_.from (∥∥₁-out-^≃∥∥₁-in-^ n) x ∣
∣,∣-in-^≡∣∣ zero    {x = x} = ∣ x ∣  ∎
∣,∣-in-^≡∣∣ (suc n) {x = x} =
  _≃_.from (∥∥₁-out-^≃∥∥₁-in-^ (2 + n)) ∣ 1 + n , x ∣-in-^  ≡⟨⟩

  _↔_.from (∥∥₁-∥∥₁-out-^-commute (1 + n))
    (_≃_.from (∥∥₁-out-^≃∥∥₁-in-^ (1 + n)) ∣ n , x ∣-in-^)  ≡⟨ cong (_↔_.from (∥∥₁-∥∥₁-out-^-commute (1 + n))) $ ∣,∣-in-^≡∣∣ n ⟩∎

  _↔_.from (∥∥₁-∥∥₁-out-^-commute (1 + n))
    ∣ _≃_.from (∥∥₁-out-^≃∥∥₁-in-^ n) x ∣                   ∎
