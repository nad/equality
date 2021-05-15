------------------------------------------------------------------------
-- Completely erased propositional truncation
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the propositional truncation uses
-- path equality, but the supplied notion of equality is used for many
-- other things.

import Equality.Path as P

module H-level.Truncation.Propositional.Completely-erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Equivalence equality-with-J as Eq using (_≃_)
open import Erased.Cubical eq
open import H-level.Truncation.Propositional eq

private
  variable
    a : Level
    A : Type a
    x : A

-- A variant of ∥∥×≃.
--
-- This lemma is defined in this module, which uses --erased-cubical,
-- instead of in H-level.Truncation.Propositional, which uses
-- --cubical. This means that the lemma can be used, without
-- restrictions, in modules that use either of these two flags.

Erased-∥∥×≃ : (Erased ∥ A ∥ × A) ≃ A
Erased-∥∥×≃ = Eq.↔→≃
  proj₂
  (λ x → [ ∣ x ∣ ] , x)
  refl
  (λ (_ , x) → cong (_, x) ([]-cong [ truncation-is-proposition _ _ ]))

_ : _≃_.right-inverse-of Erased-∥∥×≃ x ≡ refl _
_ = refl _
