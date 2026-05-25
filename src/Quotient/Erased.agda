------------------------------------------------------------------------
-- A variant of set quotients with erased higher constructors
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe #-}

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

module Quotient.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Extensionality equality-with-J
open import Function-universe equality-with-J hiding (_∘_)
import H-level P.equality-with-J as PH
open import H-level.Truncation.Propositional eq as PT
  using (∣_∣; Surjective)
import H-level.Truncation.Propositional.Erased eq as PTᴱ
open import Quotient.Erased.Axiomatised equality-with-J

private variable
  a b p r : Level
  A B     : Type _
  P       : A → Type _
  @0 R    : A → A → Type r
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

elimᴾ′ : Elimᴾ′ P → (x : A /ᴱ R) → P x
elimᴾ′ {A} {R} {P} e = helper
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

elimᴾ : Elimᴾ P → (x : A /ᴱ R) → P x
elimᴾ e = elimᴾ′ λ where
    .[]ʳ                   → E.[]ʳ
    .[]-respects-relationʳ → E.[]-respects-relationʳ
    .is-setʳ               → P.heterogeneous-UIP E.is-setʳ _
  where
  module E = Elimᴾ e

private

  -- One can define elimᴾ′ using elimᴾ.

  elimᴾ′₂ : Elimᴾ′ P → (x : A /ᴱ R) → P x
  elimᴾ′₂ {P} e = elimᴾ λ where
      .[]ʳ                           → E.[]ʳ
      .[]-respects-relationʳ         → E.[]-respects-relationʳ
      .is-setʳ x {x = y} {y = z} p q →                                  $⟨ E.is-setʳ p q ⟩
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

recᴾ : Recᴾ R B → A /ᴱ R → B
recᴾ r = elimᴾ λ where
    .[]ʳ                   → R.[]ʳ
    .[]-respects-relationʳ → R.[]-respects-relationʳ
    .is-setʳ _             → R.is-setʳ
  where
  module R = Recᴾ r

------------------------------------------------------------------------
-- An instantiation of Quotientᴱ

-- _/ᴱ_ is a quotient operator.

quotient : Quotientᴱ
quotient .Quotientᴱ._/ᴱ_                 = _/ᴱ_
quotient .Quotientᴱ.[_]                  = [_]
quotient .Quotientᴱ.[]-respects-relation = []-respects-relation
quotient .Quotientᴱ./ᴱ-is-set            = /ᴱ-is-set
quotient .Quotientᴱ.eliminator {P} f r s = elimᴾ λ where
  .[]ʳ                   → f
  .[]-respects-relationʳ → subst≡→[]≡ ∘ r
  .is-setʳ               → _↔_.to (H-level↔H-level 2) ∘ s
quotient .Quotientᴱ.eliminator-[] = refl _

open Quotientᴱ quotient public
  hiding (_/ᴱ_; [_]; []-respects-relation; /ᴱ-is-set; module Truncation)

open Quotientᴱ.Truncation quotient PTᴱ.truncation public

------------------------------------------------------------------------
-- A property

-- [_] is surjective.

[]-surjective : Surjective ([_] {R = R})
[]-surjective = elim-prop λ where
  .[]ʳ x             → ∣ x , refl _ ∣
  .is-propositionʳ _ → PT.truncation-is-proposition

------------------------------------------------------------------------
-- Function extensionality

opaque
  unfolding rec

  -- One form of erased function extensionality for set-valued
  -- functions can be proved using quotient types.
  --
  -- This result is based on one in Martin Hofmann's PhD thesis (see
  -- §3.2.7).
  --
  -- Perhaps one cannot make the proof below work in a setting where
  -- the computation rule for [_] only holds propositionally (and
  -- function extensionality is not already available), because this
  -- computation rule is used under a binder.

  @0 function-extensionality :
    {A : Type a} {P : A → Type p} →
    (∀ x → Is-set (P x)) →
    Function-extensionality′ A P
  function-extensionality {a} {p} {A} {P} P-set {f} {g} f∼g =
    f              ≡⟨⟩
    extract [ f ]  ≡⟨ cong extract ([]-respects-relation f∼g) ⟩
    extract [ g ]  ≡⟨⟩
    g              ∎
    where
    infix 4 _∼_

    _∼_ : (_ _ : (x : A) → P x) → Type (a ⊔ p)
    f ∼ g = (x : A) → f x ≡ g x

    extract : ((x : A) → P x) /ᴱ _∼_ → (x : A) → P x
    extract f x = rec
      (λ where
         .[]ʳ                   → _$ x
         .[]-respects-relationʳ → _$ x
         .is-setʳ               → P-set _)
      f
