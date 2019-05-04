------------------------------------------------------------------------
-- The "interval"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly based on the HoTT book.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the interval uses path equality,
-- but the supplied notion of equality is used for many other things.

open import Equality

module Interval
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

private
  open module D = Derived-definitions-and-properties eq hiding (elim)

import Equality.Path as P
open import Logical-equivalence using (_⇔_)
open import Prelude

private
  import Bijection
  module PB = Bijection P.equality-with-J
open import Function-universe eq hiding (_∘_)

open import Bijection eq using (_↔_)
import Equality.Path.Isomorphisms eq as I
open import Equivalence eq hiding (_∘_)
open import H-level eq
open import H-level.Closure eq using (ext⁻¹)

------------------------------------------------------------------------
-- The interval

-- The interval, defined as a higher inductive type.

data Interval : Set where
  [0] [1] : Interval
  0≡1′    : [0] P.≡ [1]

-- [0] is equal to [1].

0≡1 : [0] ≡ [1]
0≡1 = _↔_.from I.≡↔≡ 0≡1′

-- An eliminator.

module Elim
  {p}
  (P : Interval → Set p)
  (p₀ : P [0])
  (p₁ : P [1])
  (p₀≡p₁ : subst P 0≡1 p₀ ≡ p₁)
  where

  -- The eliminator.

  elim : (x : Interval) → P x
  elim [0]      = p₀
  elim [1]      = p₁
  elim (0≡1′ i) = I.subst≡→[]≡ p₀≡p₁ i

  -- A "computation" rule for elim.

  elim-0≡1 : dependent-cong elim 0≡1 ≡ p₀≡p₁
  elim-0≡1 = I.dependent-cong-subst≡→[]≡ (refl _)

open Elim public

-- A non-dependent eliminator.

module Rec
  {p} {P : Set p}
  (p₀ p₁ : P)
  (p₀≡p₁ : p₀ ≡ p₁)
  where

  -- The eliminator.

  rec : Interval → P
  rec [0]      = p₀
  rec [1]      = p₁
  rec (0≡1′ i) = _↔_.to I.≡↔≡ p₀≡p₁ i

  -- A computation rule for rec.

  rec-0≡1 : cong rec 0≡1 ≡ p₀≡p₁
  rec-0≡1 = I.cong-≡↔≡ (refl _)

open Rec public

------------------------------------------------------------------------
-- Contractibility

-- The interval is contractible.

interval-contractible : Contractible Interval
interval-contractible = [1] , sym ∘ f
  where
  f : (x : Interval) → x ≡ [1]
  f = elim (_≡ [1]) 0≡1 (refl _)
        (subst (_≡ [1]) 0≡1 0≡1              ≡⟨ cong (λ p → subst (_≡ [1]) p 0≡1)
                                                     (sym $ sym-sym 0≡1) ⟩
         subst (_≡ [1]) (sym (sym 0≡1)) 0≡1  ≡⟨ subst-trans (sym 0≡1) ⟩
         trans (sym 0≡1) 0≡1                 ≡⟨ trans-symˡ 0≡1 ⟩∎
         refl _                              ∎)

-- A simplification lemma for rec p p.

rec-const :
  ∀ {p} {P : Set p} (p : P) (p≡p : p ≡ p) i →
  rec p p p≡p i ≡ p
rec-const p p≡p i =
  rec p p p≡p i    ≡⟨ cong (rec p p p≡p) (mono₁ 0 interval-contractible i [0]) ⟩∎
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
    ⟨ext⟩ (λ x → refl (f x)) ≡ refl f
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
    D.elim (λ {f g} _ → P (f x) (g x)) (p ∘ (_$ x)) (⟨ext⟩ f≡g) ≡
    D.elim (λ {x y} _ → P x y) p (f≡g x)
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
