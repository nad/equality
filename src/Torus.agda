------------------------------------------------------------------------
-- The torus, defined as a HIT
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- This module is based on the discussion of the torus in the HoTT
-- book.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining the torus use path equality, but
-- the supplied notion of equality is used for many other things.

open import Equality

module Torus
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq hiding (elim)

import Equality.Path as P
open import Prelude

open import Bijection eq using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Circle eq as Circle using (𝕊¹; base; loopᴾ)

private
  variable
    p : Level

mutual

  -- The torus.

  data T² : Set where
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
    base  P.≡⟨ loop₁ᴾ ⟩
    base  P.≡⟨ loop₂ᴾ ⟩
    base  P.≡⟨ P.sym loop₁ᴾ ⟩
    base  P.≡⟨ P.sym loop₂ᴾ ⟩∎
    base  ∎

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

-- A dependent eliminator, expressed using paths.

module _
  (P  : T² → Set p)
  (b  : P base)
  (ℓ₁ : P.[ (λ i → P (loop₁ᴾ i)) ] b ≡ b)
  (ℓ₂ : P.[ (λ i → P (loop₂ᴾ i)) ] b ≡ b)
  where

  -- A dependent path.

  ℓ₁₂₋₁₋₂ : P.[ (λ i → P (loop₁₂₋₁₋₂ᴾ i)) ] b ≡ b
  ℓ₁₂₋₁₋₂ =
    b  P.≡⟨        ℓ₁ ⟩[ P ]
    b  P.≡⟨        ℓ₂ ⟩[ P ]
    b  P.≡⟨ P.hsym ℓ₁ ⟩[ P ]
    b  P.≡⟨ P.hsym ℓ₂ ⟩∎h
    b  ∎

  -- A special case of elimᴾ, used in the type of elimᴾ.

  elimᴾ-rimᴾ : (x : 𝕊¹) → P (rimᴾ x)
  elimᴾ-rimᴾ = Circle.elimᴾ (P ∘ rimᴾ) b ℓ₁₂₋₁₋₂

  module _
    (h : P hub)
    (s : (x : 𝕊¹) → P.[ (λ i → P (spokeᴾ x i)) ] elimᴾ-rimᴾ x ≡ h)
    where

    -- The dependent eliminator.
    --
    -- Note that the eliminator matches on circle constructors. If the
    -- case "(spokeᴾ x i) → s x i" is used instead, then the side
    -- condition elimᴾ (rimᴾ x) = elimᴾ-rimᴾ x fails to hold.

    elimᴾ : (x : T²) → P x
    elimᴾ = λ where
      base                 → b
      hub                  → h
      (loop₁ᴾ i)           → ℓ₁ i
      (loop₂ᴾ i)           → ℓ₂ i
      (spokeᴾ base i)      → s base i
      (spokeᴾ (loopᴾ j) i) → s (loopᴾ j) i

    -- The special case is a special case.

    elimᴾ-rimᴾ≡elimᴾ-rimᴾ : (x : 𝕊¹) → elimᴾ (rimᴾ x) ≡ elimᴾ-rimᴾ x
    elimᴾ-rimᴾ≡elimᴾ-rimᴾ = Circle.elimᴾ _ (refl _) (λ _ → refl _)

-- A dependent eliminator.

module _
  (P : T² → Set p)
  (b : P base)
  (ℓ₁ : subst P loop₁ b ≡ b)
  (ℓ₂ : subst P loop₂ b ≡ b)
  where

  -- A special case of elim, used in the type of elim.

  elim-rimᴾ : (x : 𝕊¹) → P (rimᴾ x)
  elim-rimᴾ = elimᴾ-rimᴾ P b (subst≡→[]≡ ℓ₁) (subst≡→[]≡ ℓ₂)

  module _
    (h : P hub)
    (s : (x : 𝕊¹) → subst P (spoke x) (elim-rimᴾ x) ≡ h)
    where

    -- The eliminator.

    elim : (x : T²) → P x
    elim =
      elimᴾ P b
        (subst≡→[]≡ ℓ₁)
        (subst≡→[]≡ ℓ₂)
        h
        (subst≡→[]≡ ∘ s)

    -- The special case is a special case.

    elim-rimᴾ≡elim-rimᴾ : (x : 𝕊¹) → elim (rimᴾ x) ≡ elim-rimᴾ x
    elim-rimᴾ≡elim-rimᴾ = elimᴾ-rimᴾ≡elimᴾ-rimᴾ _ _ _ _ _ _

    -- A variant of s with a slightly different type.

    s′ : (x : 𝕊¹) → subst P (spoke x) (elim (rimᴾ x)) ≡ h
    s′ = Circle.elimᴾ _ (s base) (λ i → s (loopᴾ i))

    -- Computation rules.

    elim-loop₁ : dcong elim loop₁ ≡ ℓ₁
    elim-loop₁ = dcong-subst≡→[]≡ (refl _)

    elim-loop₂ : dcong elim loop₂ ≡ ℓ₂
    elim-loop₂ = dcong-subst≡→[]≡ (refl _)

    elim-spoke : (x : 𝕊¹) → dcong elim (spoke x) ≡ s′ x
    elim-spoke = Circle.elimᴾ _
      (dcong-subst≡→[]≡ (refl _))
      (λ _ → dcong-subst≡→[]≡ (refl _))
