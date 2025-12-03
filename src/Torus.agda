------------------------------------------------------------------------
-- The torus, defined as a HIT
------------------------------------------------------------------------

{-# OPTIONS --cubical=erased --safe #-}

-- This module is based on the discussion of the torus in the HoTT
-- book.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining the torus use path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Torus
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Circle eq as Circle using (𝕊¹; base; loopᴾ)

private
  variable
    a p : Level
    A   : Type a
    P   : A → Type p

------------------------------------------------------------------------
-- The torus

mutual

  -- The torus.

  data T² : Type where
    base hub      : T²
    loop₁ᴾ loop₂ᴾ : base P.≡ base
    spokeᴾ        : (x : 𝕊¹) → rimᴾ x P.≡ hub

  private

    -- A synonym used to work around an Agda restriction.

    base′ = base

  -- A function used to define the spoke constructor.
  --
  -- Note that this function is defined using Circle.recᴾ, not
  -- Circle.rec.

  rimᴾ : 𝕊¹ → T²
  rimᴾ = Circle.recᴾ base loop₁₂₋₁₋₂ᴾ

  -- A loop.

  loop₁₂₋₁₋₂ᴾ : base′ P.≡ base′
  loop₁₂₋₁₋₂ᴾ =
    P.htransˡ loop₁ᴾ
      (P.htransˡ loop₂ᴾ
         (P.htransˡ (P.hsym loop₁ᴾ)
            (P.hsym loop₂ᴾ)))

-- The constructors (and loop₁₂₋₁₋₂ᴾ) expressed using _≡_ instead of
-- paths.

loop₁ : base ≡ base
loop₁ = _↔_.from ≡↔≡ loop₁ᴾ

loop₂ : base ≡ base
loop₂ = _↔_.from ≡↔≡ loop₂ᴾ

loop₁₂₋₁₋₂ : base ≡ base
loop₁₂₋₁₋₂ = _↔_.from ≡↔≡ loop₁₂₋₁₋₂ᴾ

spoke : (x : 𝕊¹) → rimᴾ x ≡ hub
spoke = _↔_.from ≡↔≡ ∘ spokeᴾ

-- A variant of rimᴾ, defined using Circle.rec and loop₁₂₋₁₋₂.

rim : 𝕊¹ → T²
rim = Circle.rec base loop₁₂₋₁₋₂

-- The functions rim and rimᴾ are pointwise equal.

rim≡rimᴾ : ∀ x → rim x ≡ rimᴾ x
rim≡rimᴾ = Circle.elim
  _
  (refl _)
  (subst (λ x → rim x ≡ rimᴾ x) Circle.loop (refl _)           ≡⟨ subst-in-terms-of-trans-and-cong ⟩

   trans (sym (cong rim Circle.loop))
     (trans (refl _) (cong rimᴾ Circle.loop))                  ≡⟨ cong (trans _) $ trans-reflˡ _ ⟩

   trans (sym (cong rim Circle.loop)) (cong rimᴾ Circle.loop)  ≡⟨ cong₂ (trans ∘ sym) Circle.rec-loop lemma ⟩

   trans (sym loop₁₂₋₁₋₂) loop₁₂₋₁₋₂                           ≡⟨ trans-symˡ _ ⟩∎

   refl _                                                      ∎)
   where
   lemma =
     cong rimᴾ Circle.loop             ≡⟨ cong≡cong ⟩
     _↔_.from ≡↔≡ (P.cong rimᴾ loopᴾ)  ≡⟨⟩
     _↔_.from ≡↔≡ loop₁₂₋₁₋₂ᴾ          ≡⟨⟩
     loop₁₂₋₁₋₂                        ∎

------------------------------------------------------------------------
-- Eliminators expressed using paths

-- A dependent eliminator, expressed using paths.

record Elimᴾ₀ (P : T² → Type p) : Type p where
  no-eta-equality
  field
    baseʳ  : P base
    loop₁ʳ : P.[ (λ i → P (loop₁ᴾ i)) ] baseʳ ≡ baseʳ
    loop₂ʳ : P.[ (λ i → P (loop₂ᴾ i)) ] baseʳ ≡ baseʳ

  -- A dependent path.

  loop₁₂₋₁₋₂ʳ : P.[ (λ i → P (loop₁₂₋₁₋₂ᴾ i)) ] baseʳ ≡ baseʳ
  loop₁₂₋₁₋₂ʳ =
    baseʳ  P.≡⟨        loop₁ʳ ⟩[ P ]
    baseʳ  P.≡⟨        loop₂ʳ ⟩[ P ]
    baseʳ  P.≡⟨ P.hsym loop₁ʳ ⟩[ P ]
    baseʳ  P.≡⟨ P.hsym loop₂ʳ ⟩∎h
    baseʳ  ∎

  -- A special case of elimᴾ, used in the type of elimᴾ.

  elimᴾ-rimᴾ : (x : 𝕊¹) → P (rimᴾ x)
  elimᴾ-rimᴾ = Circle.elimᴾ (P ∘ rimᴾ) baseʳ loop₁₂₋₁₋₂ʳ

record Elimᴾ (P : T² → Type p) : Type p where
  no-eta-equality
  field
    elimᴾ₀ : Elimᴾ₀ P

  open Elimᴾ₀ elimᴾ₀ public

  field
    hubʳ   : P hub
    spokeʳ : (x : 𝕊¹) → P.[ (λ i → P (spokeᴾ x i)) ] elimᴾ-rimᴾ x ≡ hubʳ

elimᴾ : Elimᴾ P → (x : T²) → P x
elimᴾ {P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : T²) → P x
  helper = λ where
    base                 → E.baseʳ
    hub                  → E.hubʳ
    (loop₁ᴾ i)           → E.loop₁ʳ i
    (loop₂ᴾ i)           → E.loop₂ʳ i
    (spokeᴾ base i)      → E.spokeʳ base i
    (spokeᴾ (loopᴾ j) i) → E.spokeʳ (loopᴾ j) i

-- The special case is a special case.

elimᴾ-rimᴾ≡elimᴾ-rimᴾ :
  (e : Elimᴾ P) (x : 𝕊¹) → elimᴾ e (rimᴾ x) ≡ Elimᴾ.elimᴾ-rimᴾ e x
elimᴾ-rimᴾ≡elimᴾ-rimᴾ _ = Circle.elimᴾ _ (refl _) (λ _ → refl _)

-- A non-dependent eliminator, expressed using paths.

Recᴾ : Type a → Type a
Recᴾ A = Elimᴾ (λ _ → A)

recᴾ : Recᴾ A → T² → A
recᴾ = elimᴾ

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator.

record Elim (P : T² → Type p) : Type p where
  no-eta-equality
  field
    baseʳ  : P base
    loop₁ʳ : subst P loop₁ baseʳ ≡ baseʳ
    loop₂ʳ : subst P loop₂ baseʳ ≡ baseʳ

  -- An instance of Elimᴾ₀ P.

  elimᴾ₀ : Elimᴾ₀ P
  elimᴾ₀ = λ where
    .Elimᴾ₀.baseʳ  → baseʳ
    .Elimᴾ₀.loop₁ʳ → subst≡→[]≡ loop₁ʳ
    .Elimᴾ₀.loop₂ʳ → subst≡→[]≡ loop₂ʳ

  -- A special case of elim, used in the type of elim.

  elim-rimᴾ : (x : 𝕊¹) → P (rimᴾ x)
  elim-rimᴾ = Elimᴾ₀.elimᴾ-rimᴾ elimᴾ₀

  field
    hubʳ   : P hub
    spokeʳ : (x : 𝕊¹) → subst P (spoke x) (elim-rimᴾ x) ≡ hubʳ

  -- The eliminator.

  elim : (x : T²) → P x
  elim = elimᴾ λ where
    .Elimᴾ.elimᴾ₀ → elimᴾ₀
    .Elimᴾ.hubʳ   → hubʳ
    .Elimᴾ.spokeʳ → subst≡→[]≡ ∘ spokeʳ

  -- The special case is a special case.

  elim-rimᴾ≡elim-rimᴾ : (x : 𝕊¹) → elim (rimᴾ x) ≡ elim-rimᴾ x
  elim-rimᴾ≡elim-rimᴾ = elimᴾ-rimᴾ≡elimᴾ-rimᴾ _

  -- A variant of spokeʳ with a slightly different type.

  spokeʳ′ : (x : 𝕊¹) → subst P (spoke x) (elim (rimᴾ x)) ≡ hubʳ
  spokeʳ′ = Circle.elimᴾ _ (spokeʳ base) (λ i → spokeʳ (loopᴾ i))

  -- Computation rules.

  elim-loop₁ : dcong elim loop₁ ≡ loop₁ʳ
  elim-loop₁ = dcong-subst≡→[]≡ (refl _)

  elim-loop₂ : dcong elim loop₂ ≡ loop₂ʳ
  elim-loop₂ = dcong-subst≡→[]≡ (refl _)

  elim-spoke : (x : 𝕊¹) → dcong elim (spoke x) ≡ spokeʳ′ x
  elim-spoke = Circle.elimᴾ _
    (dcong-subst≡→[]≡ (refl _))
    (λ _ → dcong-subst≡→[]≡ (refl _))

-- A non-dependent eliminator.

record Rec (A : Type a) : Type a where
  no-eta-equality
  field
    baseʳ  : A
    loop₁ʳ : baseʳ ≡ baseʳ
    loop₂ʳ : baseʳ ≡ baseʳ

  -- An instance of Elimᴾ₀ P.

  elimᴾ₀ : Elimᴾ₀ (λ _ → A)
  elimᴾ₀ = λ where
    .Elimᴾ₀.baseʳ  → baseʳ
    .Elimᴾ₀.loop₁ʳ → _↔_.to ≡↔≡ loop₁ʳ
    .Elimᴾ₀.loop₂ʳ → _↔_.to ≡↔≡ loop₂ʳ

  -- A special case of recᴾ, used in the type of rec.

  rec-rimᴾ : 𝕊¹ → A
  rec-rimᴾ = Elimᴾ₀.elimᴾ-rimᴾ elimᴾ₀

  field
    hubʳ   : A
    spokeʳ : (x : 𝕊¹) → rec-rimᴾ x ≡ hubʳ

  -- The eliminator.

  rec : T² → A
  rec = recᴾ λ where
    .Elimᴾ.elimᴾ₀ → elimᴾ₀
    .Elimᴾ.hubʳ   → hubʳ
    .Elimᴾ.spokeʳ → _↔_.to ≡↔≡ ∘ spokeʳ

  -- The special case is a special case.

  rec-rimᴾ≡rec-rimᴾ : (x : 𝕊¹) → rec (rimᴾ x) ≡ rec-rimᴾ x
  rec-rimᴾ≡rec-rimᴾ = elimᴾ-rimᴾ≡elimᴾ-rimᴾ _

  -- A variant of spokeʳ with a slightly different type.

  spokeʳ′ : (x : 𝕊¹) → rec (rimᴾ x) ≡ hubʳ
  spokeʳ′ = Circle.elimᴾ _ (spokeʳ base) (λ i → spokeʳ (loopᴾ i))

  -- Computation rules.

  rec-loop₁ : cong rec loop₁ ≡ loop₁ʳ
  rec-loop₁ = cong-≡↔≡ (refl _)

  rec-loop₂ : cong rec loop₂ ≡ loop₂ʳ
  rec-loop₂ = cong-≡↔≡ (refl _)

  rec-spoke : (x : 𝕊¹) → cong rec (spoke x) ≡ spokeʳ′ x
  rec-spoke = Circle.elimᴾ _
    (cong-≡↔≡ (refl _))
    (λ _ → cong-≡↔≡ (refl _))

------------------------------------------------------------------------
-- Some lemmas

-- The remaining results are not taken from the HoTT book.

-- One can express loop₁₂₋₁₋₂ using loop₁ and loop₂.

loop₁₂₋₁₋₂≡ :
  loop₁₂₋₁₋₂ ≡ trans (trans loop₁ loop₂) (sym (trans loop₂ loop₁))
loop₁₂₋₁₋₂≡ =
  _↔_.from ≡↔≡ loop₁₂₋₁₋₂ᴾ                                        ≡⟨⟩

  _↔_.from ≡↔≡
    (P.trans loop₁ᴾ (P.trans loop₂ᴾ
                       (P.trans (P.sym loop₁ᴾ) (P.sym loop₂ᴾ))))  ≡⟨ sym trans≡trans ⟩

  trans loop₁
    (_↔_.from ≡↔≡ (P.trans loop₂ᴾ
                     (P.trans (P.sym loop₁ᴾ) (P.sym loop₂ᴾ))))    ≡⟨ cong (trans _) $ sym trans≡trans ⟩

  trans loop₁
    (trans loop₂
       (_↔_.from ≡↔≡ (P.trans (P.sym loop₁ᴾ) (P.sym loop₂ᴾ))))    ≡⟨ cong (λ eq → trans loop₁ (trans loop₂ eq)) $ sym trans≡trans ⟩

  trans loop₁
    (trans loop₂
       (trans (_↔_.from ≡↔≡ (P.sym loop₁ᴾ))
          (_↔_.from ≡↔≡ (P.sym loop₂ᴾ))))                         ≡⟨ cong₂ (λ p q → trans loop₁ (trans loop₂ (trans p q)))
                                                                       (sym sym≡sym)
                                                                       (sym sym≡sym) ⟩

  trans loop₁ (trans loop₂ (trans (sym loop₁) (sym loop₂)))       ≡⟨ sym $ trans-assoc _ _ _ ⟩

  trans (trans loop₁ loop₂) (trans (sym loop₁) (sym loop₂))       ≡⟨ cong (trans _) $ sym $ sym-trans _ _ ⟩∎

  trans (trans loop₁ loop₂) (sym (trans loop₂ loop₁))             ∎
