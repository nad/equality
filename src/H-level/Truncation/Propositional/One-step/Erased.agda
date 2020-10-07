------------------------------------------------------------------------
-- The one-step truncation HIT with an erased higher constructor
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the one-step truncation operator
-- uses path equality, but the supplied notion of equality is used for
-- many other things.

import Equality.Path as P

module H-level.Truncation.Propositional.One-step.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J using (Constant)
import Equality.Decidable-UIP P.equality-with-J as PD
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence.Erased.Cubical eq as EEq using (_≃ᴱ_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹; ∥_∥¹-out-^; ∥_∥¹-in-^)
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
-- Propositional Truncation using Non-recursive HITs", but has an
-- erased higher constructor.

data ∥_∥¹ᴱ (A : Set a) : Set a where
  ∣_∣             : A → ∥ A ∥¹ᴱ
  @0 ∣∣-constantᴾ : PD.Constant (∣_∣ {A = A})

-- The function ∣_∣ is constant (in erased contexts).

@0 ∣∣-constant : Constant (∣_∣ {A = A})
∣∣-constant x y = _↔_.from ≡↔≡ (∣∣-constantᴾ x y)

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Set a} (P : ∥ A ∥¹ᴱ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ             : ∀ x → P ∣ x ∣
    @0 ∣∣-constantʳ :
      (x y : A) →
      P.[ (λ i → P (∣∣-constantᴾ x y i)) ] ∣∣ʳ x ≡ ∣∣ʳ y

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : ∥ A ∥¹ᴱ) → P x
elimᴾ {A = A} {P = P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : ∥ A ∥¹ᴱ) → P x
  helper ∣ x ∣                = E.∣∣ʳ x
  helper (∣∣-constantᴾ x y i) = E.∣∣-constantʳ x y i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ             : A → B
    @0 ∣∣-constantʳ : PD.Constant ∣∣ʳ

open Recᴾ public

recᴾ : Recᴾ A B → ∥ A ∥¹ᴱ → B
recᴾ r = elimᴾ λ where
    .∣∣ʳ          → R.∣∣ʳ
    .∣∣-constantʳ → R.∣∣-constantʳ
  where
  module R = Recᴾ r

-- A dependent eliminator.

record Elim {A : Set a} (P : ∥ A ∥¹ᴱ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ             : ∀ x → P ∣ x ∣
    @0 ∣∣-constantʳ :
      (x y : A) → subst P (∣∣-constant x y) (∣∣ʳ x) ≡ ∣∣ʳ y

open Elim public

elim : Elim P → (x : ∥ A ∥¹ᴱ) → P x
elim e = elimᴾ λ where
    .∣∣ʳ              → E.∣∣ʳ
    .∣∣-constantʳ x y → subst≡→[]≡ (E.∣∣-constantʳ x y)
  where
  module E = Elim e

-- A "computation" rule.

@0 elim-∣∣-constant :
  dcong (elim e) (∣∣-constant x y) ≡ Elim.∣∣-constantʳ e x y
elim-∣∣-constant = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ             : A → B
    @0 ∣∣-constantʳ : Constant ∣∣ʳ

open Rec public

rec : Rec A B → ∥ A ∥¹ᴱ → B
rec r = recᴾ λ where
    .∣∣ʳ              → R.∣∣ʳ
    .∣∣-constantʳ x y → _↔_.to ≡↔≡ (R.∣∣-constantʳ x y)
  where
  module R = Rec r

-- A "computation" rule.

@0 rec-∣∣-constant :
  cong (rec r) (∣∣-constant x y) ≡ Rec.∣∣-constantʳ r x y
rec-∣∣-constant = cong-≡↔≡ (refl _)

-- A variant of rec.

rec′ : (f : A → B) → @0 Constant f → ∥ A ∥¹ᴱ → B
rec′ f c = rec λ where
  .Rec.∣∣ʳ          → f
  .Rec.∣∣-constantʳ → c

------------------------------------------------------------------------
-- Some preservation lemmas

-- A map function for ∥_∥¹ᴱ.

∥∥¹ᴱ-map : (A → B) → ∥ A ∥¹ᴱ → ∥ B ∥¹ᴱ
∥∥¹ᴱ-map f = rec λ where
  .∣∣ʳ x            → ∣ f x ∣
  .∣∣-constantʳ x y → ∣∣-constant (f x) (f y)

-- The truncation operator preserves logical equivalences.

∥∥¹ᴱ-cong-⇔ : A ⇔ B → ∥ A ∥¹ᴱ ⇔ ∥ B ∥¹ᴱ
∥∥¹ᴱ-cong-⇔ A⇔B = record
  { to   = ∥∥¹ᴱ-map (_⇔_.to   A⇔B)
  ; from = ∥∥¹ᴱ-map (_⇔_.from A⇔B)
  }

private

  -- A lemma used below.

  @0 ∥∥¹ᴱ-cong-lemma :
    (f : A → B) (g : B → A) (eq : ∀ x → f (g x) ≡ x) →
    subst (λ z → ∥∥¹ᴱ-map f (∥∥¹ᴱ-map g z) ≡ z)
      (∣∣-constant x y) (cong ∣_∣ (eq x)) ≡
    cong ∣_∣ (eq y)
  ∥∥¹ᴱ-cong-lemma {x = x} {y = y} f g eq =
    subst
      (λ z → ∥∥¹ᴱ-map f (∥∥¹ᴱ-map g z) ≡ z)
      (∣∣-constant x y) (cong ∣_∣ (eq x))                           ≡⟨ subst-in-terms-of-trans-and-cong ⟩

    trans (sym (cong (∥∥¹ᴱ-map f ∘ ∥∥¹ᴱ-map g) (∣∣-constant x y)))
      (trans (cong ∣_∣ (eq x)) (cong id (∣∣-constant x y)))         ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong ∣_∣ (eq x)) q))
                                                                         (trans (sym $ cong-∘ _ _ _) $
                                                                          trans (cong (cong (∥∥¹ᴱ-map f)) rec-∣∣-constant) $
                                                                          rec-∣∣-constant)
                                                                         (sym $ cong-id _) ⟩
    trans (sym (∣∣-constant (f (g x)) (f (g y))))
      (trans (cong ∣_∣ (eq x)) (∣∣-constant x y))                   ≡⟨ cong (λ f → trans _ (trans (cong ∣_∣ (f _)) _)) $ sym $
                                                                       _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext) eq ⟩
    trans (sym (∣∣-constant (f (g x)) (f (g y))))
      (trans (cong ∣_∣ (ext⁻¹ (⟨ext⟩ eq) x)) (∣∣-constant x y))     ≡⟨ elim₁
                                                                         (λ {f} eq → trans (sym (∣∣-constant (f x) (f y)))
                                                                                       (trans (cong ∣_∣ (ext⁻¹ eq x)) (∣∣-constant x y)) ≡
                                                                                     cong ∣_∣ (ext⁻¹ eq y))
                                                                         (
      trans (sym (∣∣-constant x y))
        (trans (cong ∣_∣ (ext⁻¹ (refl id) x)) (∣∣-constant x y))          ≡⟨ cong (trans _) $
                                                                             trans (cong (flip trans _) $
                                                                                    trans (cong (cong _) $ cong-refl _) $
                                                                                    cong-refl _) $
                                                                             trans-reflˡ _ ⟩

      trans (sym (∣∣-constant x y)) (∣∣-constant x y)                     ≡⟨ trans-symˡ _ ⟩

      refl _                                                              ≡⟨ trans (sym $ cong-refl _) $
                                                                             cong (cong _) $ sym $ cong-refl _ ⟩∎
      cong ∣_∣ (ext⁻¹ (refl _) y)                                         ∎)
                                                                         _ ⟩

    cong ∣_∣ (ext⁻¹ (⟨ext⟩ eq) y)                                   ≡⟨ cong (λ f → cong ∣_∣ (f _)) $
                                                                       _≃_.left-inverse-of (Eq.extensionality-isomorphism bad-ext) eq ⟩∎
    cong ∣_∣ (eq y)                                                 ∎

-- The truncation operator preserves split surjections.

∥∥¹ᴱ-cong-↠ : A ↠ B → ∥ A ∥¹ᴱ ↠ ∥ B ∥¹ᴱ
∥∥¹ᴱ-cong-↠ A↠B = record
  { logical-equivalence = ∥∥¹ᴱ-cong-⇔ (_↠_.logical-equivalence A↠B)
  ; right-inverse-of    = elim λ where
      .∣∣ʳ x            → cong ∣_∣ (_↠_.right-inverse-of A↠B x)
      .∣∣-constantʳ x y →
        ∥∥¹ᴱ-cong-lemma (_↠_.to A↠B) (_↠_.from A↠B)
          (_↠_.right-inverse-of A↠B)
  }

-- The truncation operator preserves bijections.

∥∥¹ᴱ-cong-↔ : A ↔ B → ∥ A ∥¹ᴱ ↔ ∥ B ∥¹ᴱ
∥∥¹ᴱ-cong-↔ A↔B = record
  { surjection      = ∥∥¹ᴱ-cong-↠ (_↔_.surjection A↔B)
  ; left-inverse-of = elim λ where
      .∣∣ʳ x            → cong ∣_∣ (_↔_.left-inverse-of A↔B x)
      .∣∣-constantʳ x y →
        ∥∥¹ᴱ-cong-lemma (_↔_.from A↔B) (_↔_.to A↔B)
          (_↔_.left-inverse-of A↔B)
  }

-- The truncation operator preserves equivalences.

∥∥¹ᴱ-cong-≃ : A ≃ B → ∥ A ∥¹ᴱ ≃ ∥ B ∥¹ᴱ
∥∥¹ᴱ-cong-≃ = from-isomorphism ∘ ∥∥¹ᴱ-cong-↔ ∘ from-isomorphism

-- The truncation operator preserves equivalences with erased proofs.

∥∥¹ᴱ-cong-≃ᴱ : A ≃ᴱ B → ∥ A ∥¹ᴱ ≃ᴱ ∥ B ∥¹ᴱ
∥∥¹ᴱ-cong-≃ᴱ A≃B =
  EEq.[≃]→≃ᴱ (EEq.[proofs] (∥∥¹ᴱ-cong-≃ (EEq.≃ᴱ→≃ A≃B)))

------------------------------------------------------------------------
-- Iterated applications of the one-step truncation operator

-- Applies the one-step truncation the given number of times, from the
-- "outside".
--
-- This definition and the next one are taken from van Doorn's
-- "Constructing the Propositional Truncation using Non-recursive
-- HITs".

∥_∥¹ᴱ-out-^ : Set a → ℕ → Set a
∥ A ∥¹ᴱ-out-^ zero    = A
∥ A ∥¹ᴱ-out-^ (suc n) = ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ

-- A "constructor" for ∥_∥¹ᴱ-out-^.

∣_∣-out-^ : A → ∀ n → ∥ A ∥¹ᴱ-out-^ n
∣ x ∣-out-^ zero    = x
∣ x ∣-out-^ (suc n) = ∣ ∣ x ∣-out-^ n ∣

-- A rearrangement lemma.

∥∥¹ᴱ-out-^+≃ :
  ∀ m → ∥ A ∥¹ᴱ-out-^ (m + n) ≃ ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ-out-^ m
∥∥¹ᴱ-out-^+≃                 zero    = F.id
∥∥¹ᴱ-out-^+≃ {A = A} {n = n} (suc m) =
  ∥ ∥ A ∥¹ᴱ-out-^ (m + n) ∥¹ᴱ          ↝⟨ ∥∥¹ᴱ-cong-≃ (∥∥¹ᴱ-out-^+≃ m) ⟩□
  ∥ ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ-out-^ m ∥¹ᴱ  □

-- ∥_∥¹ᴱ commutes with ∥_∥¹ᴱ-out-^ n.

∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute :
  ∀ n → ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ ↔ ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-out-^ n
∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute         zero    = F.id
∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute {A = A} (suc n) =
  ∥ ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ-cong-↔ (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute n) ⟩□
  ∥ ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-out-^ n ∥¹ᴱ  □

private

  -- The lemma above is defined using _↔_ rather than _≃_ because the
  -- following equalities hold by definition when _↔_ is used, but (at
  -- the time of writing) not when _≃_ is used.

  _ :
    {x : A} →
    _↔_.left-inverse-of (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute 0) ∣ x ∣ ≡ refl ∣ x ∣
  _ = refl _

  _ :
    {A : Set a} {x : ∥ A ∥¹ᴱ-out-^ (suc n)} →
    _↔_.left-inverse-of (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute (1 + n)) ∣ x ∣ ≡
    cong ∣_∣ (_↔_.left-inverse-of (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute n) x)
  _ = refl _

-- A variant of ∥_∥¹ᴱ-out-^ which applies the one-step truncation the
-- given number of times from the "inside".

∥_∥¹ᴱ-in-^ : Set a → ℕ → Set a
∥ A ∥¹ᴱ-in-^ zero    = A
∥ A ∥¹ᴱ-in-^ (suc n) = ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-in-^ n

-- The two variants of ∥_∥¹ᴱ^ are pointwise equivalent.

∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ : ∀ n → ∥ A ∥¹ᴱ-out-^ n ≃ ∥ A ∥¹ᴱ-in-^ n
∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^         zero    = F.id
∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ {A = A} (suc n) =
  ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ  ↔⟨ ∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute n ⟩
  ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-out-^ n  ↝⟨ ∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n ⟩□
  ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-in-^ n   □

-- ∥_∥¹ᴱ commutes with ∥_∥¹ᴱ-in-^ n.

∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute : ∀ n → ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹ᴱ ≃ ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-in-^ n
∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute {A = A} n =
  ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹ᴱ   ↝⟨ ∥∥¹ᴱ-cong-≃ (inverse $ ∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) ⟩
  ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ  ↔⟨⟩
  ∥ A ∥¹ᴱ-out-^ (suc n)  ↝⟨ ∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (suc n) ⟩
  ∥ A ∥¹ᴱ-in-^ (suc n)   ↔⟨⟩
  ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-in-^ n   □

-- A "constructor" for ∥_∥¹ᴱ-in-^.

∣_,_∣-in-^ : ∀ n → ∥ A ∥¹ᴱ-in-^ n → ∥ A ∥¹ᴱ-in-^ (suc n)
∣ zero  , x ∣-in-^ = ∣ x ∣
∣ suc n , x ∣-in-^ = ∣ n , x ∣-in-^

-- ∣_,_∣-in-^ is related to ∣_∣.

∣∣≡∣,∣-in-^ :
  ∀ n {x : ∥ A ∥¹ᴱ-out-^ n} →
  _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (suc n)) ∣ x ∣ ≡
  ∣ n , _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x ∣-in-^
∣∣≡∣,∣-in-^ zero    {x = x} = ∣ x ∣  ∎
∣∣≡∣,∣-in-^ (suc n) {x = x} =
  _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (2 + n)) ∣ x ∣            ≡⟨⟩

  _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (1 + n))
    ∣ _↔_.to (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute n) x ∣             ≡⟨ ∣∣≡∣,∣-in-^ n ⟩∎

  ∣ n , _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n)
          (_↔_.to (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute n) x) ∣-in-^  ∎

-- A variant of ∣∣≡∣,∣-in-^.

∣,∣-in-^≡∣∣ :
  ∀ n {x : ∥ A ∥¹ᴱ-in-^ n} →
  _≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (suc n)) ∣ n , x ∣-in-^ ≡
  ∣ _≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x ∣
∣,∣-in-^≡∣∣ zero    {x = x} = ∣ x ∣  ∎
∣,∣-in-^≡∣∣ (suc n) {x = x} =
  _≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (2 + n)) ∣ 1 + n , x ∣-in-^  ≡⟨⟩

  _↔_.from (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute (1 + n))
    (_≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (1 + n)) ∣ n , x ∣-in-^)  ≡⟨ cong (_↔_.from (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute (1 + n))) $ ∣,∣-in-^≡∣∣ n ⟩∎

  _↔_.from (∥∥¹ᴱ-∥∥¹ᴱ-out-^-commute (1 + n))
    ∣ _≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x ∣                   ∎

------------------------------------------------------------------------
-- Some conversion functions

-- ∥ A ∥¹ᴱ implies ∥ A ∥¹.

∥∥¹ᴱ→∥∥¹ : ∥ A ∥¹ᴱ → ∥ A ∥¹
∥∥¹ᴱ→∥∥¹ = rec λ where
  .Rec.∣∣ʳ          → O.∣_∣
  .Rec.∣∣-constantʳ → O.∣∣-constant

-- In erased contexts ∥ A ∥¹ᴱ is equivalent to ∥ A ∥¹.

@0 ∥∥¹ᴱ≃∥∥¹ : ∥ A ∥¹ᴱ ≃ ∥ A ∥¹
∥∥¹ᴱ≃∥∥¹ = Eq.↔→≃
  ∥∥¹ᴱ→∥∥¹
  (O.rec′ ∣_∣ ∣∣-constant)
  (O.elim e′)
  (elim λ where
     .Elim.∣∣ʳ _            → refl _
     .Elim.∣∣-constantʳ x y →
       subst (λ x → O.rec′ ∣_∣ ∣∣-constant (∥∥¹ᴱ→∥∥¹ x) ≡ x)
         (∣∣-constant x y) (refl _)                           ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (O.rec′ ∣_∣ ∣∣-constant ∘ ∥∥¹ᴱ→∥∥¹)
                     (∣∣-constant x y)))
         (trans (refl _) (cong id (∣∣-constant x y)))         ≡⟨ cong₂ (trans ∘ sym)
                                                                   (trans (sym $ cong-∘ _ _ _) $
                                                                   trans (cong (cong (O.rec′ ∣_∣ ∣∣-constant)) rec-∣∣-constant) $
                                                                   O.rec-∣∣-constant)
                                                                   (trans (trans-reflˡ _) $
                                                                    sym $ cong-id _) ⟩

       trans (sym (∣∣-constant x y)) (∣∣-constant x y)        ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                 ∎)
  where
  e′ : O.Elim _
  e′ .O.Elim.∣∣ʳ _            = refl _
  e′ .O.Elim.∣∣-constantʳ x y =
    subst (λ x → ∥∥¹ᴱ→∥∥¹ (O.rec′ ∣_∣ ∣∣-constant x) ≡ x)
      (O.∣∣-constant x y) (refl _)                         ≡⟨ subst-in-terms-of-trans-and-cong ⟩

    trans (sym (cong (∥∥¹ᴱ→∥∥¹ ∘ O.rec′ ∣_∣ ∣∣-constant)
                  (O.∣∣-constant x y)))
      (trans (refl _) (cong id (O.∣∣-constant x y)))       ≡⟨ cong₂ (trans ∘ sym)
                                                                (trans (sym $ cong-∘ _ _ _) $
                                                                trans (cong (cong ∥∥¹ᴱ→∥∥¹) O.rec-∣∣-constant) $
                                                                rec-∣∣-constant)
                                                                (trans (trans-reflˡ _) $
                                                                 sym $ cong-id _) ⟩

    trans (sym (O.∣∣-constant x y)) (O.∣∣-constant x y)    ≡⟨ trans-symˡ _ ⟩∎

    refl _                                                 ∎

-- ∥ A ∥¹ᴱ-out-^ n implies ∥ A ∥¹-out-^ n.

∥∥¹ᴱ-out-^→∥∥¹-out-^ : ∀ n → ∥ A ∥¹ᴱ-out-^ n → ∥ A ∥¹-out-^ n
∥∥¹ᴱ-out-^→∥∥¹-out-^ zero            = id
∥∥¹ᴱ-out-^→∥∥¹-out-^ {A = A} (suc n) =
  ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ→∥∥¹ ⟩
  ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹   ↝⟨ O.∥∥¹-map (∥∥¹ᴱ-out-^→∥∥¹-out-^ n) ⟩□
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
  ∥∥¹ᴱ-out-^≃∥∥¹-out-^′ zero            = F.id
  ∥∥¹ᴱ-out-^≃∥∥¹-out-^′ {A = A} (suc n) =
    ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ≃∥∥¹ ⟩
    ∥ ∥ A ∥¹ᴱ-out-^ n ∥¹   ↝⟨ O.∥∥¹-cong-≃ (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ n) ⟩□
    ∥ ∥ A ∥¹-out-^ n ∥¹    □

  lemma :
    ∀ n (x : ∥ A ∥¹ᴱ-out-^ n) →
    _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ n) x ≡ ∥∥¹ᴱ-out-^→∥∥¹-out-^ n x
  lemma zero    _ = refl _
  lemma (suc n) x =
    _≃_.to (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ (suc n)) x                   ≡⟨⟩
    O.∥∥¹-map (_≃_.to (∥∥¹ᴱ-out-^≃∥∥¹-out-^′ n)) (∥∥¹ᴱ→∥∥¹ x)  ≡⟨ cong (λ f → O.∥∥¹-map f (∥∥¹ᴱ→∥∥¹ x)) $
                                                                  ⟨ext⟩ (lemma n) ⟩
    O.∥∥¹-map (∥∥¹ᴱ-out-^→∥∥¹-out-^ n) (∥∥¹ᴱ→∥∥¹ x)            ≡⟨⟩
    ∥∥¹ᴱ-out-^→∥∥¹-out-^ (suc n) x                             ∎

-- ∥ A ∥¹ᴱ-in-^ n implies ∥ A ∥¹-in-^ n.

∥∥¹ᴱ-in-^→∥∥¹-in-^ : ∀ n → ∥ A ∥¹ᴱ-in-^ n → ∥ A ∥¹-in-^ n
∥∥¹ᴱ-in-^→∥∥¹-in-^ zero            = id
∥∥¹ᴱ-in-^→∥∥¹-in-^ {A = A} (suc n) =
  ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-in-^ n  ↔⟨ inverse $ ∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n ⟩
  ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ→∥∥¹ ⟩
  ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹   ↝⟨ O.∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n) ⟩
  ∥ ∥ A ∥¹-in-^ n ∥¹    ↔⟨ O.∥∥¹-∥∥¹-in-^-commute n ⟩□
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
  ∥∥¹ᴱ-in-^≃∥∥¹-in-^′ zero            = F.id
  ∥∥¹ᴱ-in-^≃∥∥¹-in-^′ {A = A} (suc n) =
    ∥ ∥ A ∥¹ᴱ ∥¹ᴱ-in-^ n  ↝⟨ inverse $ ∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n ⟩
    ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹ᴱ  ↝⟨ ∥∥¹ᴱ≃∥∥¹ ⟩
    ∥ ∥ A ∥¹ᴱ-in-^ n ∥¹   ↝⟨ O.∥∥¹-cong-≃ (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ n) ⟩
    ∥ ∥ A ∥¹-in-^ n ∥¹    ↝⟨ O.∥∥¹-∥∥¹-in-^-commute n ⟩□
    ∥ ∥ A ∥¹ ∥¹-in-^ n    □

  lemma :
    ∀ n (x : ∥ A ∥¹ᴱ-in-^ n) →
    _≃_.to (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ n) x ≡ ∥∥¹ᴱ-in-^→∥∥¹-in-^ n x
  lemma zero    _ = refl _
  lemma (suc n) x =
    _≃_.to (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ (suc n)) x                    ≡⟨⟩

    _≃_.to (O.∥∥¹-∥∥¹-in-^-commute n)
      (O.∥∥¹-map (_≃_.to (∥∥¹ᴱ-in-^≃∥∥¹-in-^′ n))
         (∥∥¹ᴱ→∥∥¹ (_≃_.from (∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n) x)))  ≡⟨ cong (λ f → _≃_.to (O.∥∥¹-∥∥¹-in-^-commute n)
                                                                               (O.∥∥¹-map f (∥∥¹ᴱ→∥∥¹ (_≃_.from (∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n) x)))) $
                                                                 ⟨ext⟩ (lemma n) ⟩
    _≃_.to (O.∥∥¹-∥∥¹-in-^-commute n)
      (O.∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
         (∥∥¹ᴱ→∥∥¹ (_≃_.from (∥∥¹ᴱ-∥∥¹ᴱ-in-^-commute n) x)))  ≡⟨⟩

    ∥∥¹ᴱ-in-^→∥∥¹-in-^ (suc n) x                              ∎

-- ∥∥¹ᴱ-in-^→∥∥¹-in-^ commutes (kind of) with ∣_,_∣-in-^/O.∣_,_∣-in-^.

∥∥¹ᴱ-in-^→∥∥¹-in-^-∣,∣-in-^ :
  ∀ n {x : ∥ A ∥¹ᴱ-in-^ n} →
  ∥∥¹ᴱ-in-^→∥∥¹-in-^ (suc n) ∣ n , x ∣-in-^ ≡
  O.∣ n , ∥∥¹ᴱ-in-^→∥∥¹-in-^ n x ∣-in-^
∥∥¹ᴱ-in-^→∥∥¹-in-^-∣,∣-in-^ n {x = x} =
  ∥∥¹ᴱ-in-^→∥∥¹-in-^ (1 + n) ∣ n , x ∣-in-^                ≡⟨⟩

  _≃_.to (O.∥∥¹-∥∥¹-in-^-commute n)
    (O.∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
       (∥∥¹ᴱ→∥∥¹
          (∥∥¹ᴱ-map (_≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n))
             (_≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ (1 + n))
                ∣ n , x ∣-in-^))))                         ≡⟨ cong (λ x → _≃_.to (O.∥∥¹-∥∥¹-in-^-commute n)
                                                                            (O.∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
                                                                               (∥∥¹ᴱ→∥∥¹ (∥∥¹ᴱ-map (_≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n)) x)))) $
                                                              ∣,∣-in-^≡∣∣ n ⟩
  _≃_.to (O.∥∥¹-∥∥¹-in-^-commute n)
    (O.∥∥¹-map (∥∥¹ᴱ-in-^→∥∥¹-in-^ n)
       (∥∥¹ᴱ→∥∥¹
          (∥∥¹ᴱ-map (_≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n))
             ∣ _≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x ∣)))    ≡⟨⟩

  _≃_.to (O.∥∥¹-out-^≃∥∥¹-in-^ (1 + n))
    O.∣ _≃_.from (O.∥∥¹-out-^≃∥∥¹-in-^ n)
          (∥∥¹ᴱ-in-^→∥∥¹-in-^ n
             (_≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n)
                (_≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x))) ∣  ≡⟨ O.∣∣≡∣,∣-in-^ n ⟩

  O.∣ n
    , _≃_.to (O.∥∥¹-out-^≃∥∥¹-in-^ n)
        (_≃_.from (O.∥∥¹-out-^≃∥∥¹-in-^ n)
           (∥∥¹ᴱ-in-^→∥∥¹-in-^ n
              (_≃_.to (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n)
                 (_≃_.from (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) x))))
    ∣-in-^                                                 ≡⟨ cong O.∣ n ,_∣-in-^ $
                                                              trans (_≃_.right-inverse-of (O.∥∥¹-out-^≃∥∥¹-in-^ n) _) $
                                                              cong (∥∥¹ᴱ-in-^→∥∥¹-in-^ n) $
                                                              _≃_.right-inverse-of (∥∥¹ᴱ-out-^≃∥∥¹ᴱ-in-^ n) _ ⟩∎
  O.∣ n , ∥∥¹ᴱ-in-^→∥∥¹-in-^ n x ∣-in-^                    ∎

-- A variant of ∥∥¹ᴱ-in-^→∥∥¹-in-^-∣,∣-in-^.

@0 from-∥∥¹ᴱ-in-^≃∥∥¹-in-^-∣,∣-in-^ :
  ∀ n {x : ∥ A ∥¹-in-^ n} →
  _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n)) O.∣ n , x ∣-in-^ ≡
  ∣ n , _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n) x ∣-in-^
from-∥∥¹ᴱ-in-^≃∥∥¹-in-^-∣,∣-in-^ n {x = x} =
  _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n)) O.∣ n , x ∣-in-^  ≡⟨ cong (λ x → _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n)) O.∣ n , x ∣-in-^) $ sym $
                                                             _≃_.right-inverse-of (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n) _ ⟩
  _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n))
    O.∣ n , _≃_.to (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n)
              (_≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n) x) ∣-in-^  ≡⟨ _≃_.to-from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ (suc n)) (∥∥¹ᴱ-in-^→∥∥¹-in-^-∣,∣-in-^ n) ⟩∎

  ∣ n , _≃_.from (∥∥¹ᴱ-in-^≃∥∥¹-in-^ n) x ∣-in-^          ∎
