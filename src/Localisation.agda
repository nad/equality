------------------------------------------------------------------------
-- Localisation
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- Following "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining localisation use path equality,
-- but the supplied notion of equality is used for many other things.

import Equality.Path as P

module Localisation
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude as P

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq hiding (ext)
open import Pushout eq as Pushout using (Pushout)

private
  variable
    a b c p q r : Level
    A B C       : Type a
    P Q R       : A → Type p
    e f g x y   : A

------------------------------------------------------------------------
-- Localisation

-- A first approximation to localisation.
--
-- This is a slight generalisation of the HIT that Rijke et al. call
-- 𝓙: they require all types to live in the same universe.

data Localisation′
       {A : Type a} {P : A → Type p} {Q : A → Type q}
       (f : ∀ x → P x → Q x) (B : Type b) :
       Type (a ⊔ b ⊔ p ⊔ q) where
  [_]   : B → Localisation′ f B
  ext   : (P x → Localisation′ f B) →
          (Q x → Localisation′ f B)
  ext≡ᴾ : ext g (f x y) P.≡ g y

-- A variant of ext≡ᴾ.

ext≡ :
  {f : (x : A) → P x → Q x} {g : P x → Localisation′ f B} →
  ext g (f x y) ≡ g y
ext≡ = _↔_.from ≡↔≡ ext≡ᴾ

-- Localisation.

Localisation :
  {A : Type a} {P : A → Type p} {Q : A → Type q} →
  (∀ x → P x → Q x) →
  Type b → Type (a ⊔ b ⊔ p ⊔ q)
Localisation {p = p} {q = q} {A = A} {P = P} {Q = Q} f =
  Localisation′ f̂
  where
  P̂ : A ⊎ A → Type (p ⊔ q)
  P̂ = P.[ ↑ q ∘ P
        , (λ x → Pushout (record { left = f x; right = f x }))
        ]

  Q̂ : A ⊎ A → Type q
  Q̂ = P.[ Q , Q ]

  f̂ : (x : A ⊎ A) → P̂ x → Q̂ x
  f̂ = P.[ (λ x → f x ∘ lower)
        , (λ x → Pushout.rec id id (refl ∘ f x))
        ]

------------------------------------------------------------------------
-- Some eliminators for Localisation′

-- A dependent eliminator, expressed using paths.

record Elimᴾ
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         (f : ∀ x → P x → Q x) (B : Type b)
         (R : Localisation′ f B → Type r) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ r) where
  no-eta-equality
  field
    []ʳ   : ∀ x → R [ x ]
    extʳ  : (∀ y → R (g y)) → ∀ y → R (ext {x = x} g y)
    ext≡ʳ : (h : (y : P x) → R (g y)) →
            P.[ (λ i → R (ext≡ᴾ {g = g} {y = y} i)) ] extʳ h (f x y) ≡
            h y

open Elimᴾ public

elimᴾ : Elimᴾ f B R → (x : Localisation′ f B) → R x
elimᴾ {f = f} {B = B} {R = R} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Localisation′ f B) → R x
  helper [ x ]             = E.[]ʳ x
  helper (ext g y)         = E.extʳ (λ y → helper (g y)) y
  helper (ext≡ᴾ {g = g} i) = E.ext≡ʳ (λ y → helper (g y)) i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         (f : ∀ x → P x → Q x) (B : Type b)
         (C : Type c) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ c) where
  no-eta-equality
  field
    []ʳ   : B → C
    extʳ  : (P x → C) → Q x → C
    ext≡ʳ : (g : P x → C) → extʳ g (f x y) P.≡ g y

open Recᴾ public

recᴾ : Recᴾ f B C → Localisation′ f B → C
recᴾ r = elimᴾ λ where
    .[]ʳ   → R.[]ʳ
    .extʳ  → R.extʳ
    .ext≡ʳ → R.ext≡ʳ
  where
  module R = Recᴾ r

-- A dependent eliminator.

record Elim
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         (f : ∀ x → P x → Q x) (B : Type b)
         (R : Localisation′ f B → Type r) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ r) where
  no-eta-equality
  field
    []ʳ   : ∀ x → R [ x ]
    extʳ  : (∀ y → R (g y)) → ∀ y → R (ext {x = x} g y)
    ext≡ʳ : (h : (y : P x) → R (g y)) →
            subst R (ext≡ {y = y} {g = g}) (extʳ h (f x y)) ≡ h y

open Elim public

elim : Elim f B R → (x : Localisation′ f B) → R x
elim e = elimᴾ λ where
    .[]ʳ   → E.[]ʳ
    .extʳ  → E.extʳ
    .ext≡ʳ → subst≡→[]≡ ∘ E.ext≡ʳ
  where
  module E = Elim e

-- A "computation" rule.

elim-ext≡ :
  dcong (elim e) (ext≡ {y = y} {g = g}) ≡
  Elim.ext≡ʳ e (elim e ∘ g)
elim-ext≡ = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         (f : ∀ x → P x → Q x) (B : Type b)
         (C : Type c) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ c) where
  no-eta-equality
  field
    []ʳ   : B → C
    extʳ  : (P x → C) → Q x → C
    ext≡ʳ : (g : P x → C) → extʳ g (f x y) ≡ g y

open Rec public

rec : Rec f B C → Localisation′ f B → C
rec r = recᴾ λ where
    .[]ʳ   → R.[]ʳ
    .extʳ  → R.extʳ
    .ext≡ʳ → _↔_.to ≡↔≡ ∘ R.ext≡ʳ
  where
  module R = Rec r

-- A "computation" rule.

rec-ext≡ :
  {f : ∀ x → P x → Q x}
  {r : Rec f B C}
  {g : P x → Localisation′ f B} →
  cong (rec r) (ext≡ {y = y} {g = g}) ≡
  Rec.ext≡ʳ r (rec r ∘ g)
rec-ext≡ = cong-≡↔≡ (refl _)
