------------------------------------------------------------------------
-- A variant of set quotients with erased higher constructors
------------------------------------------------------------------------

-- This module contains some basic definitions with few dependencies
-- (in particular, not Quotient). See Quotient.Erased for more
-- definitions. The definitions below are reexported from
-- Quotient.Erased.

{-# OPTIONS --erased-cubical --safe #-}

-- Partly following the HoTT book, but adapted for erasure.
--
-- Unlike the HoTT book, but following the cubical library (in which
-- set quotients were implemented by Zesen Qian and Anders Mörtberg),
-- the quotienting relations are not (always) required to be
-- propositional.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining quotients use path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Quotient.Erased.Basics
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Function-universe equality-with-J hiding (_∘_)
open import H-level equality-with-J
import H-level P.equality-with-J as PH
open import H-level.Closure equality-with-J

private
  variable
    a b p r : Level
    A B     : Type a
    R       : A → A → Type r
    x y     : A

------------------------------------------------------------------------
-- Quotients

-- The quotient type constructor.

infix 5 _/ᴱ_

data _/ᴱ_ (A : Type a) (@0 R : A → A → Type r) : Type (a ⊔ r) where
  [_]                      : A → A /ᴱ R
  @0 []-respects-relationᴾ : {x y : A} → R x y → [ x ] P.≡ [ y ]
  @0 /ᴱ-is-setᴾ            : P.Is-set (A /ᴱ R)

-- [_] respects the quotient relation (in erased contexts).

@0 []-respects-relation : R x y → _≡_ {A = A /ᴱ R} [ x ] [ y ]
[]-respects-relation = _↔_.from ≡↔≡ ∘ []-respects-relationᴾ

-- Quotients are sets (in erased contexts).

@0 /ᴱ-is-set : Is-set (A /ᴱ R)
/ᴱ-is-set = _↔_.from (H-level↔H-level 2) /ᴱ-is-setᴾ

------------------------------------------------------------------------
-- Eliminators

-- An eliminator, expressed using paths.

record Elimᴾ′ {A : Type a} {@0 R : A → A → Type r}
              (P : A /ᴱ R → Type p) :
              Type (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    @0 []-respects-relationʳ :
      (r : R x y) →
      P.[ (λ i → P ([]-respects-relationᴾ r i)) ] []ʳ x ≡ []ʳ y

    @0 is-setʳ :
      {eq₁ eq₂ : x P.≡ y} {p : P x} {q : P y}
      (eq₃ : P.[ (λ i → P (eq₁ i)) ] p ≡ q)
      (eq₄ : P.[ (λ i → P (eq₂ i)) ] p ≡ q) →
      P.[ (λ i → P.[ (λ j → P (/ᴱ-is-setᴾ eq₁ eq₂ i j)) ] p ≡ q) ]
        eq₃ ≡ eq₄

open Elimᴾ′ public

elimᴾ′ :
  {@0 R : A → A → Type r}
  {P : A /ᴱ R → Type p} →
  Elimᴾ′ P → (x : A /ᴱ R) → P x
elimᴾ′ {A = A} {R = R} {P = P} e = helper
  where
  module E = Elimᴾ′ e

  helper : (x : A /ᴱ R) → P x
  helper [ x ]                       = E.[]ʳ x
  helper ([]-respects-relationᴾ r i) = E.[]-respects-relationʳ r i
  helper (/ᴱ-is-setᴾ p q i j)        =
    E.is-setʳ (λ i → helper (p i)) (λ i → helper (q i)) i j

-- A possibly more useful eliminator, expressed using paths.

record Elimᴾ {A : Type a} {@0 R : A → A → Type r}
             (P : A /ᴱ R → Type p) :
             Type (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    @0 []-respects-relationʳ :
      (r : R x y) →
      P.[ (λ i → P ([]-respects-relationᴾ r i)) ] []ʳ x ≡ []ʳ y

    @0 is-setʳ : ∀ x → P.Is-set (P x)

open Elimᴾ public

elimᴾ :
  {@0 R : A → A → Type r}
  {P : A /ᴱ R → Type p} →
  Elimᴾ P → (x : A /ᴱ R) → P x
elimᴾ e = elimᴾ′ λ where
    .[]ʳ                   → E.[]ʳ
    .[]-respects-relationʳ → E.[]-respects-relationʳ
    .is-setʳ               → P.heterogeneous-UIP E.is-setʳ _
  where
  module E = Elimᴾ e

private

  -- One can define elimᴾ′ using elimᴾ.

  elimᴾ′₂ :
    {@0 R : A → A → Type r}
    {P : A /ᴱ R → Type p} →
    Elimᴾ′ P → (x : A /ᴱ R) → P x
  elimᴾ′₂ {P = P} e = elimᴾ λ where
      .[]ʳ                   → E.[]ʳ
      .[]-respects-relationʳ → E.[]-respects-relationʳ
      .is-setʳ x {y} {z} p q →                                          $⟨ E.is-setʳ p q ⟩
        P.[ (λ i →
               P.[ (λ j → P (/ᴱ-is-setᴾ P.refl P.refl i j)) ] y ≡ z) ]
          p ≡ q                                                         ↝⟨ P.subst (λ eq → P.[ (λ i → P.[ (λ j → P (eq i j)) ] y ≡ z) ] p ≡ q)
                                                                                   (PH.mono₁ 2 /ᴱ-is-setᴾ _ _) ⟩
        P.[ (λ _ → P.[ (λ _ → P x) ] y ≡ z) ] p ≡ q                     ↔⟨⟩

        p P.≡ q                                                         □
    where
    module E = Elimᴾ′ e

-- A non-dependent eliminator, expressed using paths.

record Recᴾ {A : Type a} (@0 R : A → A → Type r) (B : Type b) :
            Type (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ                      : A → B
    @0 []-respects-relationʳ : (r : R x y) → []ʳ x P.≡ []ʳ y
    @0 is-setʳ               : P.Is-set B

open Recᴾ public

recᴾ :
  {@0 R : A → A → Type r} →
  Recᴾ R B → A /ᴱ R → B
recᴾ r = elimᴾ λ where
    .[]ʳ                   → R.[]ʳ
    .[]-respects-relationʳ → R.[]-respects-relationʳ
    .is-setʳ _             → R.is-setʳ
  where
  module R = Recᴾ r

-- An eliminator.

record Elim {A : Type a} {@0 R : A → A → Type r}
            (P : A /ᴱ R → Type p) :
            Type (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    @0 []-respects-relationʳ :
      (r : R x y) →
      subst P ([]-respects-relation r) ([]ʳ x) ≡ []ʳ y

    @0 is-setʳ : ∀ x → Is-set (P x)

open Elim public

elim :
  {@0 R : A → A → Type r}
  {P : A /ᴱ R → Type p} →
  Elim P → (x : A /ᴱ R) → P x
elim e = elimᴾ λ where
    .[]ʳ                   → E.[]ʳ
    .[]-respects-relationʳ → subst≡→[]≡ ∘ E.[]-respects-relationʳ
    .is-setʳ               → _↔_.to (H-level↔H-level 2) ∘ E.is-setʳ
  where
  module E = Elim e

-- A non-dependent eliminator.

record Rec {A : Type a} (@0 R : A → A → Type r) (B : Type b) :
           Type (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ                      : A → B
    @0 []-respects-relationʳ : (r : R x y) → []ʳ x ≡ []ʳ y
    @0 is-setʳ               : Is-set B

open Rec public

rec :
  {@0 R : A → A → Type r} →
  Rec R B → A /ᴱ R → B
rec r = recᴾ λ where
    .[]ʳ                   → R.[]ʳ
    .[]-respects-relationʳ → _↔_.to ≡↔≡ ∘ R.[]-respects-relationʳ
    .is-setʳ               → _↔_.to (H-level↔H-level 2) R.is-setʳ
  where
  module R = Rec r

-- A variant of elim that can be used if the motive composed with [_]
-- is a family of propositions.
--
-- I took the idea for this eliminator from Nicolai Kraus.

record Elim-prop
         {A : Type a} {@0 R : A → A → Type r}
         (P : A /ᴱ R → Type p) :
         Type (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ                : ∀ x → P [ x ]
    @0 is-propositionʳ : ∀ x → Is-proposition (P [ x ])

open Elim-prop public

elim-prop :
  {@0 R : A → A → Type r}
  {P : A /ᴱ R → Type p} →
  Elim-prop P → (x : A /ᴱ R) → P x
elim-prop e = elim λ where
    .[]ʳ                     → E.[]ʳ
    .[]-respects-relationʳ _ → E.is-propositionʳ _ _ _
    .is-setʳ                 → elim λ @0 where
      .[]ʳ                     → mono₁ 1 ∘ E.is-propositionʳ
      .[]-respects-relationʳ _ → H-level-propositional ext 2 _ _
      .is-setʳ _               → mono₁ 1 (H-level-propositional ext 2)
  where
  module E = Elim-prop e

-- A variant of rec that can be used if the motive is a proposition.

record Rec-prop (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    []ʳ                : A → B
    @0 is-propositionʳ : Is-proposition B

open Rec-prop public

rec-prop :
  {@0 R : A → A → Type r} →
  Rec-prop A B → A /ᴱ R → B
rec-prop r = elim-prop λ where
    .[]ʳ               → R.[]ʳ
    .is-propositionʳ _ → R.is-propositionʳ
  where
  module R = Rec-prop r
