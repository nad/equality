------------------------------------------------------------------------
-- The "interval"
------------------------------------------------------------------------

-- Note that this module is experimental: it uses rewrite rules and
-- postulates to encode a higher inductive type.

{-# OPTIONS --without-K --rewriting #-}

-- Partly based on the HoTT book.

module Interval where

open import Equality.Propositional as EP hiding (elim)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import H-level equality-with-J
open import H-level.Closure equality-with-J using (ext⁻¹)

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

------------------------------------------------------------------------
-- Non-dependent eliminator

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

-- A "computation rule" for rec.

rec-0≡1 :
  ∀ {p} {P : Set p}
  (p₀ p₁ : P)
  (p₀≡p₁ : p₀ ≡ p₁) →
  cong (rec p₀ p₁ p₀≡p₁) 0≡1 ≡ p₀≡p₁
rec-0≡1 p₀ p₁ p₀≡p₁ =
  cong (rec p₀ p₁ p₀≡p₁) 0≡1                                             ≡⟨⟩

  cong (elim _ p₀ p₁ (trans (subst-const 0≡1) p₀≡p₁)) 0≡1                ≡⟨ sym $ trans-sym-[trans] _ _ ⟩

  trans (sym $ subst-const 0≡1)
    (trans (subst-const 0≡1)
           (cong (elim _ p₀ p₁ (trans (subst-const 0≡1) p₀≡p₁)) 0≡1))    ≡⟨ cong (trans _) $ sym $ dependent-cong-subst-const-cong _ 0≡1 ⟩

  trans (sym $ subst-const 0≡1)
    (dependent-cong (elim _ p₀ p₁ (trans (subst-const 0≡1) p₀≡p₁)) 0≡1)  ≡⟨ cong (trans _) $ elim-0≡1 _ _ _ _ ⟩

  trans (sym $ subst-const 0≡1) (trans (subst-const 0≡1) p₀≡p₁)          ≡⟨ trans-sym-[trans] _ _ ⟩∎

  p₀≡p₁                                                                  ∎

------------------------------------------------------------------------
-- Contractibility

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

-- A simplification lemma for rec p p.

rec-const :
  ∀ {p} {P : Set p} (p : P) (p≡p : p ≡ p) i →
  rec p p p≡p i ≡ p
rec-const p p≡p i =
  rec p p p≡p i    ≡⟨ cong (rec p p p≡p) (_⇔_.to propositional⇔irrelevant (mono₁ 0 interval-contractible) i [0]) ⟩∎
  rec p p p≡p [0]  ∎

------------------------------------------------------------------------
-- Extensionality

-- The interval can be used to prove that equality of functions is
-- extensional.

private

  -- ext-helper {f = f} {g = g} f≡g reduces to λ x → f x when the
  -- input is [0], and to λ x → g x when the input is [1].

  ext-helper :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
    (∀ x → f x ≡ g x) → I → (x : A) → B x
  ext-helper {f = f} {g} f≡g i =
    λ x → rec (f x) (g x) (f≡g x) i

ext : ∀ {a b} → Extensionality a b
ext {f = f} {g = g} f≡g =
  f                   ≡⟨⟩
  ext-helper f≡g [0]  ≡⟨ cong (ext-helper f≡g) 0≡1 ⟩∎
  ext-helper f≡g [1]  ∎

-- Equality rearrangement lemmas for ext.

cong-ext :
  ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
  (f≡g : ∀ x → f x ≡ g x) {x} →
  cong (_$ x) (ext f≡g) ≡ f≡g x
cong-ext {B = B} {f = f} {g} f≡g {x} =
  cong (_$ x) (cong (ext-helper f≡g) 0≡1)  ≡⟨ cong-∘ (_$ x) (ext-helper f≡g) 0≡1 ⟩
  cong (λ i → ext-helper f≡g i x) 0≡1      ≡⟨⟩
  cong (rec (f x) (g x) (f≡g x)) 0≡1       ≡⟨ rec-0≡1 _ _ _ ⟩∎
  f≡g x                                    ∎

cong-∘-ext :
  ∀ {a b c} {A : Set a} {B : Set b} {C : B → Set c}
    {f g : (x : B) → C x} {h : A → B}
  (f≡g : ∀ x → f x ≡ g x) →
  cong (_∘ h) (ext f≡g) ≡ ext (f≡g ∘ h)
cong-∘-ext {h = h} f≡g =
  cong (_∘ h) (cong (ext-helper f≡g) 0≡1)  ≡⟨ cong-∘ (_∘ h) (ext-helper f≡g) 0≡1 ⟩∎
  cong (λ i → ext-helper f≡g i ∘ h) 0≡1    ∎

subst-ext :
  ∀ {a b p} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} {x}
  (P : B x → Set p) {p} (f≡g : ∀ x → f x ≡ g x) →
  subst (λ f → P (f x)) (ext f≡g) p ≡ subst P (f≡g x) p
subst-ext {f = f} {g} {x = x} P {p} f≡g =
  subst (λ f → P (f x)) (ext f≡g) p  ≡⟨ subst-∘ P (_$ x) (ext f≡g) ⟩
  subst P (cong (_$ x) (ext f≡g)) p  ≡⟨ cong (λ eq → subst P eq p) (cong-ext f≡g) ⟩∎
  subst P (f≡g x) p                  ∎
