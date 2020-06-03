------------------------------------------------------------------------
-- A variant of set quotients with erased higher constructors
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

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

open P.Derived-definitions-and-properties eq hiding (elim)

import H-level
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as Er using (Erased; [_])
open import Function-universe equality-with-J as F hiding (_∘_; id)
open H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as PT
  using (∥_∥; ∣_∣; Surjective)
open import H-level.Truncation.Propositional.Erased eq as PTᴱ
  using (∥_∥ᴱ; ∣_∣; Surjectiveᴱ)
open import Quotient eq as Q using (_/_)
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

private
  module PH = H-level P.equality-with-J

private
  variable
    a a₁ a₂ b p r r₁ r₂ : Level
    A A₁ A₂ B           : Set a
    P                   : A → Set p
    R R₁ R₂             : A → A → Set r
    f k x y             : A

------------------------------------------------------------------------
-- Quotients

-- The quotient type constructor.

infix 5 _/ᴱ_

data _/ᴱ_ (@0 A : Set a) (@0 R : A → A → Set r) : Set (a ⊔ r) where
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

record Elimᴾ′ {@0 A : Set a} {@0 R : A → A → Set r}
              (@0 P : A /ᴱ R → Set p) :
              Set (a ⊔ r ⊔ p) where
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
  {@0 A : Set a}
  {@0 R : A → A → Set r}
  {@0 P : A /ᴱ R → Set p} →
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

record Elimᴾ {@0 A : Set a} {@0 R : A → A → Set r}
             (@0 P : A /ᴱ R → Set p) :
             Set (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    @0 []-respects-relationʳ :
      (r : R x y) →
      P.[ (λ i → P ([]-respects-relationᴾ r i)) ] []ʳ x ≡ []ʳ y

    @0 is-setʳ : ∀ x → P.Is-set (P x)

open Elimᴾ public

elimᴾ :
  {@0 A : Set a}
  {@0 R : A → A → Set r}
  {@0 P : A /ᴱ R → Set p} →
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
    {@0 A : Set a}
    {@0 R : A → A → Set r}
    {@0 P : A /ᴱ R → Set p} →
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

record Recᴾ {@0 A : Set a} (@0 R : A → A → Set r) (@0 B : Set b) :
            Set (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ                      : A → B
    @0 []-respects-relationʳ : (r : R x y) → []ʳ x P.≡ []ʳ y
    @0 is-setʳ               : P.Is-set B

open Recᴾ public

recᴾ :
  {@0 A : Set a} {@0 B : Set b} {@0 R : A → A → Set r} →
  Recᴾ R B → A /ᴱ R → B
recᴾ r = elimᴾ λ where
    .[]ʳ                   → R.[]ʳ
    .[]-respects-relationʳ → R.[]-respects-relationʳ
    .is-setʳ _             → R.is-setʳ
  where
  module R = Recᴾ r

-- An eliminator.

record Elim {@0 A : Set a} {@0 R : A → A → Set r}
            (@0 P : A /ᴱ R → Set p) :
            Set (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    @0 []-respects-relationʳ :
      (r : R x y) →
      subst P ([]-respects-relation r) ([]ʳ x) ≡ []ʳ y

    @0 is-setʳ : ∀ x → Is-set (P x)

open Elim public

elim :
  {@0 A : Set a}
  {@0 R : A → A → Set r}
  {@0 P : A /ᴱ R → Set p} →
  Elim P → (x : A /ᴱ R) → P x
elim e = elimᴾ λ where
    .[]ʳ                   → E.[]ʳ
    .[]-respects-relationʳ → subst≡→[]≡ ∘ E.[]-respects-relationʳ
    .is-setʳ               → _↔_.to (H-level↔H-level 2) ∘ E.is-setʳ
  where
  module E = Elim e

-- A non-dependent eliminator.

record Rec {@0 A : Set a} (@0 R : A → A → Set r) (@0 B : Set b) :
           Set (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ                      : A → B
    @0 []-respects-relationʳ : (r : R x y) → []ʳ x ≡ []ʳ y
    @0 is-setʳ               : Is-set B

open Rec public

rec :
  {@0 A : Set a} {@0 B : Set b} {@0 R : A → A → Set r} →
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
         {@0 A : Set a} {@0 R : A → A → Set r}
         (@0 P : A /ᴱ R → Set p) :
         Set (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ                : ∀ x → P [ x ]
    @0 is-propositionʳ : ∀ x → Is-proposition (P [ x ])

open Elim-prop public

elim-prop :
  {@0 A : Set a}
  {@0 R : A → A → Set r}
  {@0 P : A /ᴱ R → Set p} →
  Elim-prop P → (x : A /ᴱ R) → P x
elim-prop {P = P} e = elim λ where
    .[]ʳ                     → E.[]ʳ
    .[]-respects-relationʳ _ → E.is-propositionʳ _ _ _
    .is-setʳ                 → elim e′
  where
  module E = Elim-prop e

  @0 e′ : Elim (Is-set ∘ P)
  e′ .[]ʳ                     = mono₁ 1 ∘ E.is-propositionʳ
  e′ .[]-respects-relationʳ _ = H-level-propositional ext 2 _ _
  e′ .is-setʳ _               = mono₁ 1 (H-level-propositional ext 2)

-- A variant of rec that can be used if the motive is a proposition.

record Rec-prop (@0 A : Set a) (@0 B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  field
    []ʳ                : A → B
    @0 is-propositionʳ : Is-proposition B

open Rec-prop public

rec-prop :
  {@0 A : Set a} {@0 B : Set b} {@0 R : A → A → Set r} →
  Rec-prop A B → A /ᴱ R → B
rec-prop r = elim-prop λ where
    .[]ʳ               → R.[]ʳ
    .is-propositionʳ _ → R.is-propositionʳ
  where
  module R = Rec-prop r

------------------------------------------------------------------------
-- Conversion functions

-- One can convert from quotients with erased higher constructors to
-- quotients with regular higher constructors.

/ᴱ→/ : A /ᴱ R → A / R
/ᴱ→/ = rec λ where
  .[]ʳ                   → Q.[_]
  .[]-respects-relationʳ → Q.[]-respects-relation
  .is-setʳ               → Q./-is-set

-- In an erased context quotients with erased higher constructors are
-- equivalent to quotients with regular higher constructors.

@0 /ᴱ≃/ : A /ᴱ R ≃ A / R
/ᴱ≃/ {A = A} {R = R} = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = /ᴱ→/
      ; from = Q.rec r′
      }
    ; right-inverse-of = Q.elim e
    }
  ; left-inverse-of = elim λ where
      .[]ʳ _                   → refl _
      .[]-respects-relationʳ _ → /ᴱ-is-set _ _
      .is-setʳ _               → mono₁ 2 /ᴱ-is-set
  })
  where
  r′ : Q.Rec R (A /ᴱ R)
  r′ .Q.[]ʳ                   = [_]
  r′ .Q.[]-respects-relationʳ = []-respects-relation
  r′ .Q.is-setʳ               = /ᴱ-is-set

  e : Q.Elim (λ x → /ᴱ→/ (Q.rec r′ x) ≡ x)
  e .Q.[]ʳ _                   = refl _
  e .Q.[]-respects-relationʳ _ = Q./-is-set _ _
  e .Q.is-setʳ _               = mono₁ 2 Q./-is-set

------------------------------------------------------------------------
-- Preservation lemmas

-- Two preservation lemmas for functions.

infix 5 _/ᴱ-map-∥∥_ _/ᴱ-map_

_/ᴱ-map-∥∥_ :
  (A₁→A₂ : A₁ → A₂) →
  @0 (∀ x y → ∥ R₁ x y ∥ → ∥ R₂ (A₁→A₂ x) (A₁→A₂ y) ∥) →
  A₁ /ᴱ R₁ → A₂ /ᴱ R₂
_/ᴱ-map-∥∥_ {R₁ = R₁} {R₂ = R₂} A₁→A₂ R₁→R₂ = rec λ where
  .[]ʳ                                   → [_] ∘ A₁→A₂
  .is-setʳ                               → /ᴱ-is-set
  .[]-respects-relationʳ {x = x} {y = y} →
     R₁ x y                      ↝⟨ ∣_∣ ⟩
     ∥ R₁ x y ∥                  ↝⟨ R₁→R₂ _ _ ⟩
     ∥ R₂ (A₁→A₂ x) (A₁→A₂ y) ∥  ↝⟨ PT.rec /ᴱ-is-set []-respects-relation ⟩□
     [ A₁→A₂ x ] ≡ [ A₁→A₂ y ]   □

_/ᴱ-map_ :
  (A₁→A₂ : A₁ → A₂) →
  @0 (∀ x y → R₁ x y → R₂ (A₁→A₂ x) (A₁→A₂ y)) →
  A₁ /ᴱ R₁ → A₂ /ᴱ R₂
A₁→A₂ /ᴱ-map R₁→R₂ = A₁→A₂ /ᴱ-map-∥∥ λ x y → PT.∥∥-map (R₁→R₂ x y)

-- Two preservation lemmas for logical equivalences.

/ᴱ-cong-∥∥-⇔ :
  (A₁⇔A₂ : A₁ ⇔ A₂) →
  @0 (∀ x y → ∥ R₁ x y ∥ → ∥ R₂ (_⇔_.to   A₁⇔A₂ x) (_⇔_.to   A₁⇔A₂ y) ∥) →
  @0 (∀ x y → ∥ R₂ x y ∥ → ∥ R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y) ∥) →
  A₁ /ᴱ R₁ ⇔ A₂ /ᴱ R₂
/ᴱ-cong-∥∥-⇔ A₁⇔A₂ R₁→R₂ R₂→R₁ = record
  { to   = _⇔_.to   A₁⇔A₂ /ᴱ-map-∥∥ R₁→R₂
  ; from = _⇔_.from A₁⇔A₂ /ᴱ-map-∥∥ R₂→R₁
  }

/ᴱ-cong-⇔ :
  (A₁⇔A₂ : A₁ ⇔ A₂) →
  @0 (∀ x y → R₁ x y → R₂ (_⇔_.to   A₁⇔A₂ x) (_⇔_.to   A₁⇔A₂ y)) →
  @0 (∀ x y → R₂ x y → R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y)) →
  A₁ /ᴱ R₁ ⇔ A₂ /ᴱ R₂
/ᴱ-cong-⇔ A₁⇔A₂ R₁→R₂ R₂→R₁ =
  /ᴱ-cong-∥∥-⇔ A₁⇔A₂ (λ x y → PT.∥∥-map (R₁→R₂ x y))
                     (λ x y → PT.∥∥-map (R₂→R₁ x y))

-- Two preservation lemmas for split surjections.

infix 5 _/ᴱ-cong-∥∥-↠_ _/ᴱ-cong-↠_

_/ᴱ-cong-∥∥-↠_ :
  (A₁↠A₂ : A₁ ↠ A₂) →
  @0 (∀ x y → ∥ R₁ x y ∥ ⇔ ∥ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y) ∥) →
  A₁ /ᴱ R₁ ↠ A₂ /ᴱ R₂
_/ᴱ-cong-∥∥-↠_ {R₁ = R₁} {R₂ = R₂} A₁↠A₂ R₁⇔R₂ = record
  { logical-equivalence = /ᴱ-cong-∥∥-⇔
      (_↠_.logical-equivalence A₁↠A₂)
      (λ x y → _⇔_.to (R₁⇔R₂ x y))
      (λ x y → ∥ R₂ x y ∥                          ↝⟨ ≡⇒↝ _ (sym $ cong₂ (λ x y → ∥ R₂ x y ∥) (right-inverse-of x) (right-inverse-of y)) ⟩
               ∥ R₂ (to (from x)) (to (from y)) ∥  ↝⟨ _⇔_.from (R₁⇔R₂ _ _) ⟩□
               ∥ R₁ (from x) (from y) ∥            □)
  ; right-inverse-of = elim-prop λ where
      .[]ʳ x →
        [ to (from x) ]  ≡⟨ cong [_] $ right-inverse-of x ⟩∎
        [ x ]            ∎
      .is-propositionʳ _ → /ᴱ-is-set
  }
  where
  open _↠_ A₁↠A₂

_/ᴱ-cong-↠_ :
  (A₁↠A₂ : A₁ ↠ A₂) →
  @0 (∀ x y → R₁ x y ⇔ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y)) →
  A₁ /ᴱ R₁ ↠ A₂ /ᴱ R₂
A₁↠A₂ /ᴱ-cong-↠ R₁⇔R₂ =
  A₁↠A₂ /ᴱ-cong-∥∥-↠ λ x y → PT.∥∥-cong-⇔ (R₁⇔R₂ x y)

-- Two preservation lemmas for isomorphisms.

infix 5 _/ᴱ-cong-∥∥_ _/ᴱ-cong_

_/ᴱ-cong-∥∥_ :
  {A₁ : Set a₁} {A₂ : Set a₂}
  {R₁ : A₁ → A₁ → Set r₁}
  {R₂ : A₂ → A₂ → Set r₂} →
  (A₁↔A₂ : A₁ ↔[ k ] A₂) →
  @0 (∀ x y →
        ∥ R₁ x y ∥ ⇔
        ∥ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y) ∥) →
  A₁ /ᴱ R₁ ↔[ k ] A₂ /ᴱ R₂
_/ᴱ-cong-∥∥_ {k = k} {R₁ = R₁} {R₂ = R₂} A₁↔A₂′ R₁⇔R₂ =
  from-bijection (record
    { surjection = from-isomorphism A₁↔A₂ /ᴱ-cong-∥∥-↠ λ x y →
        ∥ R₁ x y ∥                                                  ↝⟨ R₁⇔R₂ x y ⟩
        ∥ R₂ (to-implication A₁↔A₂′ x) (to-implication A₁↔A₂′ y) ∥  ↝⟨ ≡⇒↝ _ $ cong₂ (λ f g → ∥ R₂ (f x) (g y) ∥)
                                                                                     (to-implication∘from-isomorphism k bijection)
                                                                                     (to-implication∘from-isomorphism k bijection) ⟩□
        ∥ R₂ (to x) (to y) ∥                                        □
    ; left-inverse-of = elim-prop λ where
        .[]ʳ x →
          [ from (to x) ]  ≡⟨ cong [_] $ left-inverse-of x ⟩∎
          [ x ]            ∎
        .is-propositionʳ _ → /ᴱ-is-set
    })
  where
  A₁↔A₂ = from-isomorphism A₁↔A₂′

  open _↔_ A₁↔A₂

_/ᴱ-cong_ :
  {A₁ : Set a₁} {A₂ : Set a₂}
  {R₁ : A₁ → A₁ → Set r₁}
  {R₂ : A₂ → A₂ → Set r₂} →
  (A₁↔A₂ : A₁ ↔[ k ] A₂) →
  @0 (∀ x y →
        R₁ x y ⇔ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y)) →
  A₁ /ᴱ R₁ ↔[ k ] A₂ /ᴱ R₂
_/ᴱ-cong_ A₁↔A₂ R₁⇔R₂ =
  A₁↔A₂ /ᴱ-cong-∥∥ λ x y → PT.∥∥-cong-⇔ (R₁⇔R₂ x y)

------------------------------------------------------------------------
-- Some properties

-- [_] is surjective.

Surjective-[] : Surjective ([_] {R = R})
Surjective-[] = elim-prop λ where
  .[]ʳ x             → ∣ x , refl _ ∣
  .is-propositionʳ _ → PT.truncation-is-proposition

-- [_] is surjective with erased proofs.

Surjectiveᴱ-[] : Surjectiveᴱ ([_] {R = R})
Surjectiveᴱ-[] = elim-prop λ where
  .[]ʳ x             → ∣ x , [ refl _ ] ∣
  .is-propositionʳ _ → PTᴱ.truncation-is-proposition

-- Quotienting by the propositional truncation of a relation is
-- equivalent to quotienting by the relation itself.

/ᴱ-∥∥≃/ᴱ : A /ᴱ (λ x y → ∥ R x y ∥) ≃ A /ᴱ R
/ᴱ-∥∥≃/ᴱ {R = R} = F.id /ᴱ-cong-∥∥ λ x y →
  ∥ ∥ R x y ∥ ∥  ↔⟨ PT.flatten ⟩□
  ∥ R x y ∥      □

-- If the quotient relation is a propositional equivalence relation,
-- then it is equivalent to equality under [_] (in erased contexts).

@0 related≃[equal] :
  {R : A → A → Set r} →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  R x y ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
related≃[equal] {A = A} {r = r} {x = x} {y = y} {R = R}
                R-equiv R-prop =
  R x y                             ↝⟨ Q.related≃[equal] R-equiv R-prop ⟩
  _≡_ {A = A /  R} Q.[ x ] Q.[ y ]  ↝⟨ Eq.≃-≡ /ᴱ≃/ ⟩□
  _≡_ {A = A /ᴱ R}   [ x ]   [ y ]  □

-- A variant of related≃[equal].

@0 ∥related∥≃[equal] :
  Is-equivalence-relation R →
  ∥ R x y ∥ ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
∥related∥≃[equal] {A = A} {R = R} {x = x} {y = y} R-equiv =
  ∥ R x y ∥                         ↝⟨ Q.∥related∥≃[equal] R-equiv ⟩
  _≡_ {A = A /  R} Q.[ x ] Q.[ y ]  ↝⟨ Eq.≃-≡ /ᴱ≃/ ⟩□
  _≡_ {A = A /ᴱ R}   [ x ]   [ y ]  □

-- Quotienting with equality (for a set) amounts to the same thing as
-- not quotienting at all.

/ᴱ≡↔ : @0 Is-set A → A /ᴱ _≡_ ↔ A
/ᴱ≡↔ A-set = record
  { surjection = record
    { logical-equivalence = record
      { from = [_]
      ; to   = rec λ where
          .[]ʳ                   → id
          .[]-respects-relationʳ → id
          .is-setʳ               → A-set
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = elim-prop λ where
      .[]ʳ _             → refl _
      .is-propositionʳ _ → /ᴱ-is-set
  }

-- Quotienting with a trivial relation amounts to the same thing as
-- using the propositional truncation (with erased proofs).

/ᴱtrivial↔∥∥ᴱ : @0 (∀ x y → R x y) → A /ᴱ R ↔ ∥ A ∥ᴱ
/ᴱtrivial↔∥∥ᴱ {A = A} {R = R} trivial = record
  { surjection = record
    { logical-equivalence = record
      { to = rec-prop λ where
          .[]ʳ             → ∣_∣
          .is-propositionʳ → PTᴱ.truncation-is-proposition
      ; from = PTᴱ.rec λ where
          .PTᴱ.∣∣ʳ                        → [_]
          .PTᴱ.truncation-is-propositionʳ → elim-prop e₁
      }
    ; right-inverse-of = PTᴱ.elim λ where
        .PTᴱ.∣∣ʳ _                        → refl _
        .PTᴱ.truncation-is-propositionʳ _ →
          ⇒≡ 1 PTᴱ.truncation-is-proposition
    }
  ; left-inverse-of = elim-prop λ where
      .[]ʳ _             → refl _
      .is-propositionʳ _ → /ᴱ-is-set
  }
  where
  @0 e₂ : ∀ x → Elim-prop ([ x ] ≡_)
  e₂ x .[]ʳ y             = []-respects-relation (trivial x y)
  e₂ _ .is-propositionʳ _ = /ᴱ-is-set

  @0 e₁ : Elim-prop (λ x → (y : A /ᴱ R) → x ≡ y)
  e₁ .[]ʳ               = elim-prop ∘ e₂
  e₁ .is-propositionʳ _ =
       Π-closure ext 1 λ _ →
       /ᴱ-is-set

------------------------------------------------------------------------
-- A property related to ∥_∥ᴱ, proved using _/ᴱ_

-- Having a constant function (with an erased proof of constancy) into
-- a set is equivalent to having a function from a propositionally
-- truncated type (with erased proofs) into the set.
--
-- The statement of this result is adapted from that of
-- Proposition 2.2 in "The General Universal Property of the
-- Propositional Truncation" by Kraus.

Σ→Erased-Constant≃∥∥ᴱ→ :
  @0 Is-set B →
  (∃ λ (f : A → B) → Erased (Constant f)) ≃ (∥ A ∥ᴱ → B)
Σ→Erased-Constant≃∥∥ᴱ→ {B = B} {A = A} B-set =
  (∃ λ (f : A → B) → Erased (Constant f))  ↔⟨ lemma ⟩
  (A /ᴱ (λ _ _ → ⊤) → B)                   ↝⟨ →-cong₁ ext (/ᴱtrivial↔∥∥ᴱ _) ⟩□
  (∥ A ∥ᴱ → B)                             □
  where
  lemma : _ ↔ _
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ (f , [ c ]) → rec λ where
                   .[]ʳ                     → f
                   .[]-respects-relationʳ _ → c _ _
                   .is-setʳ                 → B-set
        ; from = λ f → (f ∘ [_])
                     , [ (λ _ _ → cong f ([]-respects-relation _)) ]
        }
      ; right-inverse-of = λ f → ⟨ext⟩ $ elim λ where
          .[]ʳ _                   → refl _
          .[]-respects-relationʳ _ → B-set _ _
          .is-setʳ _               → mono₁ 2 B-set
      }
    ; left-inverse-of = λ _ → Σ-≡,≡→≡
        (refl _)
        (Er.H-level-Erased 1
           (Π-closure ext 1 λ _ →
            Π-closure ext 1 λ _ →
            B-set)
           _ _)
    }

-- The two directions of the proposition above compute in the
-- "right" way.

_ :
  (@0 B-set : Is-set B) →
  _≃_.to (Σ→Erased-Constant≃∥∥ᴱ→ B-set) f ∣ x ∣ ≡ proj₁ f x
_ = λ _ → refl _

_ :
  (@0 B-set : Is-set B) →
  proj₁ (_≃_.from (Σ→Erased-Constant≃∥∥ᴱ→ B-set) f) x ≡ f ∣ x ∣
_ = λ _ → refl _
