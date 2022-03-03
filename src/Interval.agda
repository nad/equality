------------------------------------------------------------------------
-- The "interval"
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- Partly based on the HoTT book.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the interval uses path equality,
-- but the supplied notion of equality is used for many other things.

import Equality.Path as P

module Interval
  {c⁺} (eq : ∀ {a p} → P.Equality-with-paths a p c⁺) where

private
  open module D = P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
import Equality.Path.Isomorphisms eq as I
open import Extensionality equality-with-J
open import H-level equality-with-J

private
  variable
    a p : Level
    A   : Type a
    P   : A → Type p

------------------------------------------------------------------------
-- The interval

-- The interval, defined as a higher inductive type.

data Interval : Type where
  [0] [1] : Interval
  0≡1ᴾ    : [0] P.≡ [1]

-- [0] is equal to [1].

0≡1 : [0] ≡ [1]
0≡1 = _↔_.from ≡↔≡ 0≡1ᴾ

-- An eliminator, expressed using paths.

elimᴾ :
  (P : Interval → Type p)
  (p₀ : P [0])
  (p₁ : P [1]) →
  P.[ (λ i → P (0≡1ᴾ i)) ] p₀ ≡ p₁ →
  (x : Interval) → P x
elimᴾ P p₀ p₁ p₀≡p₁ = λ where
  [0]      → p₀
  [1]      → p₁
  (0≡1ᴾ i) → p₀≡p₁ i

-- A non-dependent eliminator, expressed using paths.

recᴾ : (p₀ p₁ : A) → p₀ P.≡ p₁ → Interval → A
recᴾ = elimᴾ _

-- An eliminator.

module Elim
  (P : Interval → Type p)
  (p₀ : P [0])
  (p₁ : P [1])
  (p₀≡p₁ : subst P 0≡1 p₀ ≡ p₁)
  where

  -- The eliminator.

  elim : (x : Interval) → P x
  elim = elimᴾ P p₀ p₁ (I.subst≡→[]≡ p₀≡p₁)

  -- A "computation" rule for elim.

  elim-0≡1 : dcong elim 0≡1 ≡ p₀≡p₁
  elim-0≡1 = I.dcong-subst≡→[]≡ (refl _)

open Elim public

-- A non-dependent eliminator.

module Rec
  (p₀ p₁ : A)
  (p₀≡p₁ : p₀ ≡ p₁)
  where

  -- The eliminator.

  rec : Interval → A
  rec = recᴾ p₀ p₁ (_↔_.to ≡↔≡ p₀≡p₁)

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
  ∀ {p} {P : Type p} (p : P) (p≡p : p ≡ p) i →
  rec p p p≡p i ≡ p
rec-const p p≡p i =
  rec p p p≡p i    ≡⟨ cong (rec p p p≡p) (mono₁ 0 interval-contractible i [0]) ⟩∎
  rec p p p≡p [0]  ∎

------------------------------------------------------------------------
-- Extensionality

private abstract

  -- The interval can be used to prove that equality of functions is
  -- extensional.

  -- ext-helper {f = f} {g = g} f≡g reduces to λ x → f x when the
  -- input is [0], and to λ x → g x when the input is [1].

  ext-helper :
    {f g : (x : A) → P x} →
    (∀ x → f x ≡ g x) → Interval → (x : A) → P x
  ext-helper {f = f} {g = g} f≡g i =
    λ x → rec (f x) (g x) (f≡g x) i

  ⟨ext⟩′ : Function-extensionality a p
  ⟨ext⟩′ {f = f} {g = g} f≡g =
    f                   ≡⟨⟩
    ext-helper f≡g [0]  ≡⟨ cong (ext-helper f≡g) 0≡1 ⟩∎
    ext-helper f≡g [1]  ∎

-- Function extensionality.

ext : Extensionality a p
ext = _⇔_.from Extensionality⇔Function-extensionality ⟨ext⟩′

⟨ext⟩ : Function-extensionality a p
⟨ext⟩ = apply-ext ext
