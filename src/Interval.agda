------------------------------------------------------------------------
-- The "interval"
------------------------------------------------------------------------

-- Note that this module is experimental: it uses rewrite rules and
-- postulates to encode a higher inductive type.

{-# OPTIONS --without-K --rewriting #-}

-- Partly based on the HoTT book.

module Interval where

open import Equality.Propositional as Eq hiding (elim)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equivalence equality-with-J hiding (_∘_)
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

abstract

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

    ext′ : ∀ {a b} → Extensionality a b
    apply-ext ext′ {f = f} {g = g} f≡g =
      f                   ≡⟨⟩
      ext-helper f≡g [0]  ≡⟨ cong (ext-helper f≡g) 0≡1 ⟩∎
      ext-helper f≡g [1]  ∎

  ext : ∀ {a b} → Extensionality a b
  ext = good-ext ext′

  ⟨ext⟩ : ∀ {a b} {A : Set a} {B : A → Set b} → Extensionality′ A B
  ⟨ext⟩ = apply-ext ext

  -- The function ⟨ext⟩ is an equivalence.

  ext-is-equivalence :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
    Is-equivalence {A = ∀ x → f x ≡ g x} ⟨ext⟩
  ext-is-equivalence = good-ext-is-equivalence ext′

  -- Equality rearrangement lemmas for ⟨ext⟩.

  ext-refl :
    ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) →
    ⟨ext⟩ (λ x → refl {x = f x}) ≡ refl {x = f}
  ext-refl = good-ext-refl ext′

  cong-ext :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) {x} →
    cong (_$ x) (⟨ext⟩ f≡g) ≡ f≡g x
  cong-ext = cong-good-ext ext′

  subst-ext :
    ∀ {a b p} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} {x}
    (P : B x → Set p) {p} (f≡g : ∀ x → f x ≡ g x) →
    subst (λ f → P (f x)) (⟨ext⟩ f≡g) p ≡ subst P (f≡g x) p
  subst-ext = subst-good-ext ext′

  elim-ext :
    ∀ {a b p} {A : Set a} {B : A → Set b} {x : A}
    (P : B x → B x → Set p)
    (p : (y : B x) → P y y)
    {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) →
    Eq.elim (λ {f g} _ → P (f x) (g x)) (p ∘ (_$ x)) (⟨ext⟩ f≡g) ≡
    Eq.elim (λ {x y} _ → P x y) p (f≡g x)
  elim-ext = elim-good-ext ext′

  -- I based the statements of the following three lemmas on code in
  -- the Lean Homotopy Type Theory Library with Jakob von Raumer and
  -- Floris van Doorn listed as authors. The file was claimed to have
  -- been ported from the Coq HoTT library. (The third lemma has later
  -- been generalised.)

  ext-sym :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) →
    ⟨ext⟩ (sym ∘ f≡g) ≡ sym (⟨ext⟩ f≡g)
  ext-sym = good-ext-sym ext′

  ext-trans :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g h : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) (g≡h : ∀ x → g x ≡ h x) →
    ⟨ext⟩ (λ x → trans (f≡g x) (g≡h x)) ≡ trans (⟨ext⟩ f≡g) (⟨ext⟩ g≡h)
  ext-trans = good-ext-trans ext′

  cong-post-∘-ext :
    ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
      {f g : (x : A) → B x} {h : ∀ {x} → B x → C x}
    (f≡g : ∀ x → f x ≡ g x) →
    cong (h ∘_) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (cong h ∘ f≡g)
  cong-post-∘-ext = cong-post-∘-good-ext ext′ ext′

  cong-pre-∘-ext :
    ∀ {a b c} {A : Set a} {B : Set b} {C : B → Set c}
      {f g : (x : B) → C x} {h : A → B}
    (f≡g : ∀ x → f x ≡ g x) →
    cong (_∘ h) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (f≡g ∘ h)
  cong-pre-∘-ext = cong-pre-∘-good-ext ext′ ext′
