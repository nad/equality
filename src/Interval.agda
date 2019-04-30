------------------------------------------------------------------------
-- The "interval"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly based on the HoTT book.

module Interval where

open import Equality.Path as Eq
  hiding (elim; ext; ⟨ext⟩; ext-is-equivalence)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J using (ext⁻¹)

------------------------------------------------------------------------
-- The interval

-- The interval, defined as a higher inductive type.

data Interval : Set where
  [0] [1] : Interval
  0≡1     : [0] ≡ [1]

-- An eliminator.

elim :
  ∀ {p}
  (P : Interval → Set p)
  (p₀ : P [0])
  (p₁ : P [1]) →
  subst P 0≡1 p₀ ≡ p₁ →
  (x : Interval) → P x
elim P p₀ p₁ p₀≡p₁ = λ where
  [0]     → p₀
  [1]     → p₁
  (0≡1 i) → _↔_.from (heterogeneous↔homogeneous (λ i → P (0≡1 i)))
              p₀≡p₁ i

-- A "computation" rule for elim.

elim-0≡1 :
  ∀ {p} {P : Interval → Set p} {p₀ p₁} (p₀≡p₁ : subst P 0≡1 p₀ ≡ p₁) →
  dependent-cong (elim P p₀ p₁ p₀≡p₁) 0≡1 ≡ p₀≡p₁
elim-0≡1 {P = P} {p₀} {p₁} p₀≡p₁ =
  dependent-cong (elim P p₀ p₁ p₀≡p₁) 0≡1  ≡⟨⟩
  _↔_.to h↔h (_↔_.from h↔h p₀≡p₁)          ≡⟨ _↔_.right-inverse-of h↔h _ ⟩∎
  p₀≡p₁                                    ∎
  where
  h↔h = heterogeneous↔homogeneous (λ i → P (0≡1 i))

-- A non-dependent eliminator.

rec : ∀ {p} {P : Set p}
      (p₀ p₁ : P)
      (p₀≡p₁ : p₀ ≡ p₁) →
      Interval → P
rec {P = P} p₀ p₁ p₀≡p₁ = λ where
  [0]     → p₀
  [1]     → p₁
  (0≡1 i) → p₀≡p₁ i

private

  -- A computation rule for rec.

  rec-0≡1 :
    ∀ {p} {P : Set p} {p₀ p₁ : P} {p₀≡p₁ : p₀ ≡ p₁} →
    cong (rec p₀ p₁ p₀≡p₁) 0≡1 ≡ p₀≡p₁
  rec-0≡1 = refl

------------------------------------------------------------------------
-- Contractibility

-- The interval is contractible.

interval-contractible : Contractible Interval
interval-contractible = [1] , sym ∘ f
  where
  f : (x : Interval) → x ≡ [1]
  f = elim (_≡ [1]) 0≡1 refl
        (subst (_≡ [1]) 0≡1 0≡1              ≡⟨ cong (λ p → subst (_≡ [1]) p 0≡1)
                                                     (sym $ sym-sym 0≡1) ⟩
         subst (_≡ [1]) (sym (sym 0≡1)) 0≡1  ≡⟨ subst-trans (sym 0≡1) ⟩
         trans (sym 0≡1) 0≡1                 ≡⟨ trans-symˡ 0≡1 ⟩∎
         refl                                ∎)

  -- An alternative proof.

  f′ : (x : Interval) → x ≡ [1]
  f′ [0]     = 0≡1
  f′ [1]     = refl
  f′ (0≡1 i) = λ j → 0≡1 (max i j)

-- A simplification lemma for rec p p.

rec-const :
  ∀ {p} {P : Set p} (p : P) (p≡p : p ≡ p) i →
  rec p p p≡p i ≡ p
rec-const p p≡p i =
  rec p p p≡p i    ≡⟨ cong (rec p p p≡p) (_⇔_.to propositional⇔irrelevant (mono₁ 0 interval-contractible) i [0]) ⟩∎
  rec p p p≡p [0]  ∎

------------------------------------------------------------------------
-- Extensionality

-- The definition of bad-ext has been placed in a separate abstract
-- block to ensure that the definitions in the other abstract block
-- below do not accidentally depend on the implementation of bad-ext.

private
 module Separate-abstract-block where

  abstract

    -- The interval can be used to prove that equality of functions is
    -- extensional.
    --
    -- The proof bad-ext is perhaps not less "good" than ext (I don't
    -- know), it is called this simply because it is not defined using
    -- good-ext.

    private

      -- ext-helper {f = f} {g = g} f≡g reduces to λ x → f x when the
      -- input is [0], and to λ x → g x when the input is [1].

      ext-helper :
        ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
        (∀ x → f x ≡ g x) → Interval → (x : A) → B x
      ext-helper {f = f} {g} f≡g i =
        λ x → rec (f x) (g x) (f≡g x) i

    bad-ext : ∀ {a b} → Extensionality a b
    apply-ext bad-ext {f = f} {g = g} f≡g =
      f                   ≡⟨⟩
      ext-helper f≡g [0]  ≡⟨ cong (ext-helper f≡g) 0≡1 ⟩∎
      ext-helper f≡g [1]  ∎

open Separate-abstract-block public

ext : ∀ {a b} → Extensionality a b
ext = good-ext bad-ext

⟨ext⟩ : ∀ {a b} {A : Set a} {B : A → Set b} → Extensionality′ A B
⟨ext⟩ = apply-ext ext

abstract

  -- The function ⟨ext⟩ is an equivalence.

  ext-is-equivalence :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
    Is-equivalence {A = ∀ x → f x ≡ g x} ⟨ext⟩
  ext-is-equivalence = good-ext-is-equivalence bad-ext

  -- Equality rearrangement lemmas for ⟨ext⟩.

  ext-refl :
    ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) →
    ⟨ext⟩ (λ x → refl {x = f x}) ≡ refl {x = f}
  ext-refl = good-ext-refl bad-ext

  cong-ext :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) {x} →
    cong (_$ x) (⟨ext⟩ f≡g) ≡ f≡g x
  cong-ext = cong-good-ext bad-ext

  subst-ext :
    ∀ {a b p} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} {x}
    (P : B x → Set p) {p} (f≡g : ∀ x → f x ≡ g x) →
    subst (λ f → P (f x)) (⟨ext⟩ f≡g) p ≡ subst P (f≡g x) p
  subst-ext = subst-good-ext bad-ext

  elim-ext :
    ∀ {a b p} {A : Set a} {B : A → Set b} {x : A}
    (P : B x → B x → Set p)
    (p : (y : B x) → P y y)
    {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) →
    Eq.elim (λ {f g} _ → P (f x) (g x)) (p ∘ (_$ x)) (⟨ext⟩ f≡g) ≡
    Eq.elim (λ {x y} _ → P x y) p (f≡g x)
  elim-ext = elim-good-ext bad-ext

  -- I based the statements of the following three lemmas on code in
  -- the Lean Homotopy Type Theory Library with Jakob von Raumer and
  -- Floris van Doorn listed as authors. The file was claimed to have
  -- been ported from the Coq HoTT library. (The third lemma has later
  -- been generalised.)

  ext-sym :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) →
    ⟨ext⟩ (sym ∘ f≡g) ≡ sym (⟨ext⟩ f≡g)
  ext-sym = good-ext-sym bad-ext

  ext-trans :
    ∀ {a b} {A : Set a} {B : A → Set b} {f g h : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) (g≡h : ∀ x → g x ≡ h x) →
    ⟨ext⟩ (λ x → trans (f≡g x) (g≡h x)) ≡ trans (⟨ext⟩ f≡g) (⟨ext⟩ g≡h)
  ext-trans = good-ext-trans bad-ext

  cong-post-∘-ext :
    ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
      {f g : (x : A) → B x} {h : ∀ {x} → B x → C x}
    (f≡g : ∀ x → f x ≡ g x) →
    cong (h ∘_) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (cong h ∘ f≡g)
  cong-post-∘-ext {h = h} = cong-post-∘-good-ext {h = h} bad-ext bad-ext

  cong-pre-∘-ext :
    ∀ {a b c} {A : Set a} {B : Set b} {C : B → Set c}
      {f g : (x : B) → C x} {h : A → B}
    (f≡g : ∀ x → f x ≡ g x) →
    cong (_∘ h) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (f≡g ∘ h)
  cong-pre-∘-ext = cong-pre-∘-good-ext bad-ext bad-ext
