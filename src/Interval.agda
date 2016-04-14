------------------------------------------------------------------------
-- The "interval"
------------------------------------------------------------------------

-- Note that this module is experimental: it uses rewrite rules and
-- postulates to encode a higher inductive type.

{-# OPTIONS --without-K --rewriting #-}

-- Largely following the HoTT book.

module Interval where

open import Equality.Propositional hiding (elim)
open import Prelude

------------------------------------------------------------------------
-- The interval

postulate

  -- The interval type constructor.

  I : Set

  -- Constructors.

  [0] [1] : I
  0≡1     : [0] ≡ [1]

-- Eliminator.

module _ {p}
         (P : I → Set p)
         (p₀ : P [0])
         (p₁ : P [1])
         (p₀≡p₁ : subst P 0≡1 p₀ ≡ p₁)
         where

  postulate

    elim : (x : I) → P x

    -- Computation rules.
    --
    -- NOTE: Rewriting has not been activated for the "computation" rule
    -- corresponding to 0≡1.

    elim-[0] : elim [0] ≡ p₀
    elim-[1] : elim [1] ≡ p₁

  {-# REWRITE elim-[0] #-}
  {-# REWRITE elim-[1] #-}

  postulate

    elim-0≡1 : dependent-cong elim 0≡1 ≡ p₀≡p₁

-- A non-dependent eliminator.

rec : ∀ {p} {P : Set p}
      (p₀ p₁ : P)
      (p₀≡p₁ : p₀ ≡ p₁) →
      I → P
rec p₀ p₁ p₀≡p₁ =
  elim _ p₀ p₁ (
    subst (const _) 0≡1 p₀  ≡⟨ subst-const 0≡1 ⟩
    p₀                      ≡⟨ p₀≡p₁ ⟩∎
    p₁                      ∎)

------------------------------------------------------------------------
-- Some properties

-- The interval is contractible.

interval-contractible : Contractible I
interval-contractible = [1] , sym ∘ f
  where
  f : (x : I) → x ≡ [1]
  f = elim (_≡ [1]) 0≡1 refl
        (subst (_≡ [1]) 0≡1 0≡1              ≡⟨ cong (λ p → subst (_≡ [1]) p 0≡1)
                                                     (sym $ sym-sym 0≡1) ⟩
         subst (_≡ [1]) (sym (sym 0≡1)) 0≡1  ≡⟨ subst-trans (sym 0≡1) ⟩
         trans (sym 0≡1) 0≡1                 ≡⟨ trans-symˡ 0≡1 ⟩∎
         refl                                ∎)

-- The interval can be used to prove that equality of functions is
-- extensional.

ext : ∀ {a b} → Extensionality a b
ext {A = A} {B = B} {f = f} {g = g} f≡g =
  f      ≡⟨⟩
  h [0]  ≡⟨ cong h 0≡1 ⟩
  h [1]  ≡⟨ refl ⟩∎
  g      ∎
  where
  h : I → ((x : A) → B x)
  h i x = rec (f x) (g x) (f≡g x) i
