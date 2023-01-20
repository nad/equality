------------------------------------------------------------------------
-- Quotients (set-quotients), defined using a higher inductive type
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- Partly following the HoTT book.
--
-- Unlike the HoTT book, but following the cubical library (in which
-- set quotients were implemented by Zesen Qian and Anders Mörtberg),
-- the quotienting relations are not (always) required to be
-- propositional.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining quotients use path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Quotient
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

private
  open module D = P.Derived-definitions-and-properties eq hiding (elim)

import H-level
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as E
  using (Erased; Erasedᴾ; Stable; Very-stable; Very-stable-≡)
open import Function-universe equality-with-J as F hiding (_∘_; id)
open import H-level.Closure equality-with-J
import H-level.Truncation.Church equality-with-J as Trunc
open import H-level.Truncation.Propositional eq as TruncP
  using (∥_∥; ∣_∣; Surjective; Axiom-of-countable-choice)
open import Monad equality-with-J
open import Preimage equality-with-J using (_⁻¹_)
open import Quotient.Erased.Basics eq as QE using (_/ᴱ_)
import Quotient.Families-of-equivalence-classes equality-with-J
  as Quotient
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

private
  module PH = H-level P.equality-with-J
  open module H = H-level equality-with-J

private
  variable
    a a₁ a₂ b p r r₁ r₂ : Level
    k                   : Isomorphism-kind
    A A₁ A₂ B           : Type a
    P                   : A → Type p
    R R₁ R₂             : A → A → Type r
    f x y               : A

------------------------------------------------------------------------
-- Quotients

-- The quotient type constructor.

infix 5 _/_

data _/_ (A : Type a) (R : A → A → Type r) : Type (a ⊔ r) where
  [_]                   : A → A / R
  []-respects-relationᴾ : R x y → [ x ] P.≡ [ y ]
  /-is-setᴾ             : P.Is-set (A / R)

-- [_] respects the quotient relation.

[]-respects-relation : R x y → _≡_ {A = A / R} [ x ] [ y ]
[]-respects-relation = _↔_.from ≡↔≡ ∘ []-respects-relationᴾ

-- Quotients are sets.

/-is-set : Is-set (A / R)
/-is-set = _↔_.from (H-level↔H-level 2) /-is-setᴾ

-- An eliminator, expressed using paths.

record Elimᴾ′ {A : Type a} {R : A → A → Type r} (P : A / R → Type p) :
              Type (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    []-respects-relationʳ :
      (r : R x y) →
      P.[ (λ i → P ([]-respects-relationᴾ r i)) ] []ʳ x ≡ []ʳ y

    is-setʳ :
      {eq₁ eq₂ : x P.≡ y} {p : P x} {q : P y}
      (eq₃ : P.[ (λ i → P (eq₁ i)) ] p ≡ q)
      (eq₄ : P.[ (λ i → P (eq₂ i)) ] p ≡ q) →
      P.[ (λ i → P.[ (λ j → P (/-is-setᴾ eq₁ eq₂ i j)) ] p ≡ q) ]
        eq₃ ≡ eq₄

open Elimᴾ′ public

elimᴾ′ : Elimᴾ′ P → (x : A / R) → P x
elimᴾ′ {A} {R} {P} e = helper
  where
  module E′ = Elimᴾ′ e

  helper : (x : A / R) → P x
  helper [ x ]                       = E′.[]ʳ x
  helper ([]-respects-relationᴾ r i) = E′.[]-respects-relationʳ r i
  helper (/-is-setᴾ p q i j)         =
    E′.is-setʳ (λ i → helper (p i)) (λ i → helper (q i)) i j

-- A possibly more useful eliminator, expressed using paths.

record Elimᴾ {A : Type a} {R : A → A → Type r} (P : A / R → Type p) :
             Type (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    []-respects-relationʳ :
      (r : R x y) →
      P.[ (λ i → P ([]-respects-relationᴾ r i)) ] []ʳ x ≡ []ʳ y

    is-setʳ : ∀ x → P.Is-set (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : A / R) → P x
elimᴾ e = elimᴾ′ λ where
    .[]ʳ                   → E′.[]ʳ
    .[]-respects-relationʳ → E′.[]-respects-relationʳ
    .is-setʳ               → P.heterogeneous-UIP E′.is-setʳ _
  where
  module E′ = Elimᴾ e

private

  -- One can define elimᴾ′ using elimᴾ.

  elimᴾ′₂ : Elimᴾ′ P → (x : A / R) → P x
  elimᴾ′₂ {P} e = elimᴾ λ where
      .[]ʳ                           → E′.[]ʳ
      .[]-respects-relationʳ         → E′.[]-respects-relationʳ
      .is-setʳ x {x = y} {y = z} p q →                                 $⟨ E′.is-setʳ p q ⟩
        P.[ (λ i →
               P.[ (λ j → P (/-is-setᴾ P.refl P.refl i j)) ] y ≡ z) ]
          p ≡ q                                                        ↝⟨ P.subst (λ eq → P.[ (λ i → P.[ (λ j → P (eq i j)) ] y ≡ z) ] p ≡ q)
                                                                                  (PH.mono₁ 2 /-is-setᴾ _ _) ⟩
        P.[ (λ _ → P.[ (λ _ → P x) ] y ≡ z) ] p ≡ q                    ↔⟨⟩

        p P.≡ q                                                        □
    where
    module E′ = Elimᴾ′ e

-- A non-dependent eliminator, expressed using paths.

record Recᴾ {A : Type a} (R : A → A → Type r) (B : Type b) :
            Type (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ                   : A → B
    []-respects-relationʳ : (r : R x y) → []ʳ x P.≡ []ʳ y
    is-setʳ               : P.Is-set B

open Recᴾ public

recᴾ : Recᴾ R B → A / R → B
recᴾ r = elimᴾ λ where
    .[]ʳ                   → R.[]ʳ
    .[]-respects-relationʳ → R.[]-respects-relationʳ
    .is-setʳ _             → R.is-setʳ
  where
  module R = Recᴾ r

-- An eliminator.

record Elim {A : Type a} {R : A → A → Type r} (P : A / R → Type p) :
            Type (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    []-respects-relationʳ :
      (r : R x y) →
      subst P ([]-respects-relation r) ([]ʳ x) ≡ []ʳ y

    is-setʳ : ∀ x → Is-set (P x)

open Elim public

elim : Elim P → (x : A / R) → P x
elim e = elimᴾ λ where
    .[]ʳ                   → E′.[]ʳ
    .[]-respects-relationʳ → subst≡→[]≡ ∘ E′.[]-respects-relationʳ
    .is-setʳ               → _↔_.to (H-level↔H-level 2) ∘ E′.is-setʳ
  where
  module E′ = Elim e

-- A non-dependent eliminator.

record Rec {A : Type a} (R : A → A → Type r) (B : Type b) :
           Type (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ                   : A → B
    []-respects-relationʳ : (r : R x y) → []ʳ x ≡ []ʳ y
    is-setʳ               : Is-set B

open Rec public

rec : Rec R B → A / R → B
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
         {A : Type a} {R : A → A → Type r} (P : A / R → Type p) :
         Type (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ             : ∀ x → P [ x ]
    is-propositionʳ : ∀ x → Is-proposition (P [ x ])

open Elim-prop public

elim-prop : Elim-prop P → (x : A / R) → P x
elim-prop e = elim λ where
    .[]ʳ                     → E′.[]ʳ
    .[]-respects-relationʳ _ → E′.is-propositionʳ _ _ _
    .is-setʳ                 → elim λ where
      .[]ʳ                     → mono₁ 1 ∘ E′.is-propositionʳ
      .[]-respects-relationʳ _ → H-level-propositional ext 2 _ _
      .is-setʳ _               → mono₁ 1 (H-level-propositional ext 2)
  where
  module E′ = Elim-prop e

-- A variant of rec that can be used if the motive is a proposition.

record Rec-prop (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    []ʳ             : A → B
    is-propositionʳ : Is-proposition B

open Rec-prop public

rec-prop : Rec-prop A B → A / R → B
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
/ᴱ→/ = QE.rec λ where
  .QE.[]ʳ                   → [_]
  .QE.[]-respects-relationʳ → []-respects-relation
  .QE.is-setʳ               → /-is-set

-- In an erased context quotients with erased higher constructors are
-- equivalent to quotients with regular higher constructors.

@0 /ᴱ≃/ : A /ᴱ R ≃ A / R
/ᴱ≃/ {A} {R} = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = /ᴱ→/
      ; from = rec λ @0 where
          .[]ʳ                   → QE.[_]
          .[]-respects-relationʳ → QE.[]-respects-relation
          .is-setʳ               → QE./ᴱ-is-set
      }
    ; right-inverse-of = elim λ @0 where
        .[]ʳ _                   → refl _
        .[]-respects-relationʳ _ → /-is-set _ _
        .is-setʳ _               → mono₁ 2 /-is-set
    }
  ; left-inverse-of = QE.elim λ where
      .QE.[]ʳ _                   → refl _
      .QE.[]-respects-relationʳ _ → QE./ᴱ-is-set _ _
      .QE.is-setʳ _               → mono₁ 2 QE./ᴱ-is-set
  })

------------------------------------------------------------------------
-- Some properties

-- [_] is surjective.

[]-surjective : Surjective ([_] {R = R})
[]-surjective = elim-prop λ where
  .[]ʳ x             → ∣ x , refl _ ∣
  .is-propositionʳ _ → TruncP.truncation-is-proposition

-- QE.[_] is surjective.
--
-- This result is not proved in Quotient.Erased, because that module
-- uses --erased-cubical.

[]ᴱ-surjective : Surjective (QE.[_] {R = R})
[]ᴱ-surjective = QE.elim-prop λ where
  .QE.[]ʳ x             → ∣ x , refl _ ∣
  .QE.is-propositionʳ _ → TruncP.truncation-is-proposition

-- Some preservation lemmas.

infix 5 _/-map-∥∥_ _/-map_ _/-cong-∥∥-↠_ _/-cong-↠_ _/-cong-∥∥_ _/-cong_

_/-map-∥∥_ :
  (A₁→A₂ : A₁ → A₂) →
  (∀ x y → ∥ R₁ x y ∥ → ∥ R₂ (A₁→A₂ x) (A₁→A₂ y) ∥) →
  A₁ / R₁ → A₂ / R₂
_/-map-∥∥_ {R₁} {R₂} A₁→A₂ R₁→R₂ = rec λ where
  .[]ʳ                           → [_] ∘ A₁→A₂
  .is-setʳ                       → /-is-set
  .[]-respects-relationʳ {x} {y} →
     R₁ x y                      ↝⟨ ∣_∣ ⟩
     ∥ R₁ x y ∥                  ↝⟨ R₁→R₂ _ _ ⟩
     ∥ R₂ (A₁→A₂ x) (A₁→A₂ y) ∥  ↝⟨ TruncP.rec /-is-set []-respects-relation ⟩□
     [ A₁→A₂ x ] ≡ [ A₁→A₂ y ]   □

_/-map_ :
  (A₁→A₂ : A₁ → A₂) →
  (∀ x y → R₁ x y → R₂ (A₁→A₂ x) (A₁→A₂ y)) →
  A₁ / R₁ → A₂ / R₂
A₁→A₂ /-map R₁→R₂ = A₁→A₂ /-map-∥∥ λ x y → TruncP.∥∥-map (R₁→R₂ x y)

/-cong-∥∥-⇔ :
  (A₁⇔A₂ : A₁ ⇔ A₂) →
  (∀ x y → ∥ R₁ x y ∥ → ∥ R₂ (_⇔_.to   A₁⇔A₂ x) (_⇔_.to   A₁⇔A₂ y) ∥) →
  (∀ x y → ∥ R₂ x y ∥ → ∥ R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y) ∥) →
  A₁ / R₁ ⇔ A₂ / R₂
/-cong-∥∥-⇔ A₁⇔A₂ R₁→R₂ R₂→R₁ = record
  { to   = _⇔_.to   A₁⇔A₂ /-map-∥∥ R₁→R₂
  ; from = _⇔_.from A₁⇔A₂ /-map-∥∥ R₂→R₁
  }

/-cong-⇔ :
  (A₁⇔A₂ : A₁ ⇔ A₂) →
  (∀ x y → R₁ x y → R₂ (_⇔_.to   A₁⇔A₂ x) (_⇔_.to   A₁⇔A₂ y)) →
  (∀ x y → R₂ x y → R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y)) →
  A₁ / R₁ ⇔ A₂ / R₂
/-cong-⇔ A₁⇔A₂ R₁→R₂ R₂→R₁ =
  /-cong-∥∥-⇔ A₁⇔A₂ (λ x y → TruncP.∥∥-map (R₁→R₂ x y))
                    (λ x y → TruncP.∥∥-map (R₂→R₁ x y))

_/-cong-∥∥-↠_ :
  (A₁↠A₂ : A₁ ↠ A₂) →
  (∀ x y → ∥ R₁ x y ∥ ⇔ ∥ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y) ∥) →
  A₁ / R₁ ↠ A₂ / R₂
_/-cong-∥∥-↠_ {R₁} {R₂} A₁↠A₂ R₁⇔R₂ = record
  { logical-equivalence = /-cong-∥∥-⇔
      (_↠_.logical-equivalence A₁↠A₂)
      (λ x y → _⇔_.to (R₁⇔R₂ x y))
      (λ x y → ∥ R₂ x y ∥                          ↝⟨ ≡⇒↝ _ (sym $ cong₂ (λ x y → ∥ R₂ x y ∥) (right-inverse-of x) (right-inverse-of y)) ⟩
               ∥ R₂ (to (from x)) (to (from y)) ∥  ↝⟨ _⇔_.from (R₁⇔R₂ _ _) ⟩□
               ∥ R₁ (from x) (from y) ∥            □)
  ; right-inverse-of = elim-prop λ where
      .[]ʳ x →
        [ to (from x) ]  ≡⟨ cong [_] $ right-inverse-of x ⟩∎
        [ x ]            ∎
      .is-propositionʳ _ → /-is-set
  }
  where
  open _↠_ A₁↠A₂

_/-cong-↠_ :
  (A₁↠A₂ : A₁ ↠ A₂) →
  (∀ x y → R₁ x y ⇔ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y)) →
  A₁ / R₁ ↠ A₂ / R₂
A₁↠A₂ /-cong-↠ R₁⇔R₂ =
  A₁↠A₂ /-cong-∥∥-↠ λ x y → TruncP.∥∥-cong-⇔ (R₁⇔R₂ x y)

_/-cong-∥∥_ :
  {A₁ : Type a₁} {A₂ : Type a₂}
  {R₁ : A₁ → A₁ → Type r₁}
  {R₂ : A₂ → A₂ → Type r₂} →
  (A₁↔A₂ : A₁ ↔[ k ] A₂) →
  (∀ x y →
     ∥ R₁ x y ∥ ⇔
     ∥ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y) ∥) →
  A₁ / R₁ ↔[ k ] A₂ / R₂
_/-cong-∥∥_ {k} {R₁} {R₂} A₁↔A₂′ R₁⇔R₂ =
  from-bijection (record
    { surjection = from-isomorphism A₁↔A₂ /-cong-∥∥-↠ λ x y →
        ∥ R₁ x y ∥                                                  ↝⟨ R₁⇔R₂ x y ⟩
        ∥ R₂ (to-implication A₁↔A₂′ x) (to-implication A₁↔A₂′ y) ∥  ↝⟨ ≡⇒↝ _ $ cong₂ (λ f g → ∥ R₂ (f x) (g y) ∥)
                                                                                     (to-implication∘from-isomorphism k bijection)
                                                                                     (to-implication∘from-isomorphism k bijection) ⟩□
        ∥ R₂ (to x) (to y) ∥                                        □
    ; left-inverse-of = elim-prop λ where
        .[]ʳ x →
          [ from (to x) ]  ≡⟨ cong [_] $ left-inverse-of x ⟩∎
          [ x ]            ∎
        .is-propositionʳ _ → /-is-set
    })
  where
  A₁↔A₂ = from-isomorphism A₁↔A₂′

  open _↔_ A₁↔A₂

_/-cong_ :
  {A₁ : Type a₁} {A₂ : Type a₂}
  {R₁ : A₁ → A₁ → Type r₁}
  {R₂ : A₂ → A₂ → Type r₂} →
  (A₁↔A₂ : A₁ ↔[ k ] A₂) →
  (∀ x y →
     R₁ x y ⇔ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y)) →
  A₁ / R₁ ↔[ k ] A₂ / R₂
_/-cong_ A₁↔A₂ R₁⇔R₂ =
  A₁↔A₂ /-cong-∥∥ λ x y → TruncP.∥∥-cong-⇔ (R₁⇔R₂ x y)

-- Quotienting by the propositional truncation of a relation is
-- equivalent to quotienting by the relation itself.

/-∥∥≃/ : A / (λ x y → ∥ R x y ∥) ≃ A / R
/-∥∥≃/ {R} = F.id /-cong-∥∥ λ x y →
  ∥ ∥ R x y ∥ ∥  ↔⟨ TruncP.flatten ⟩□
  ∥ R x y ∥      □

-- If the relation is a propositional equivalence relation, then it is
-- equivalent to equality under [_] (assuming propositional
-- extensionality).
--
-- The basic structure of this proof is that of Proposition 2 in
-- "Quotienting the Delay Monad by Weak Bisimilarity" by Chapman,
-- Uustalu and Veltri.

related≃[equal] :
  {R : A → A → Type r} →
  Propositional-extensionality r →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  ∀ {x y} → R x y ≃ _≡_ {A = A / R} [ x ] [ y ]
related≃[equal] {A} {r} {R} prop-ext R-equiv R-prop {x} {y} =
  _↠_.from (Eq.≃↠⇔ R-prop /-is-set)
    (record
      { to   = []-respects-relation
      ; from = λ [x]≡[y] →
                              $⟨ reflexive ⟩
          proj₁ (R′ x [ x ])  ↝⟨ ≡⇒→ (cong (proj₁ ∘ R′ x) [x]≡[y]) ⟩
          proj₁ (R′ x [ y ])  ↝⟨ id ⟩□
          R x y               □
      })
  where
  open Is-equivalence-relation R-equiv

  lemma : ∀ {x y z} → R y z → (R x y , R-prop) ≡ (R x z , R-prop)
  lemma {x} {y} {z} =
    R y z                                ↝⟨ (λ r → record
                                               { to   = flip transitive r
                                               ; from = flip transitive (symmetric r)
                                               }) ⟩
    R x y ⇔ R x z                        ↔⟨ ⇔↔≡″ ext prop-ext ⟩□
    (R x y , R-prop) ≡ (R x z , R-prop)  □

  R′ : A → A / R → Proposition r
  R′ x = rec λ where
    .[]ʳ y                 → R x y , R-prop
    .[]-respects-relationʳ → lemma
    .is-setʳ               → Is-set-∃-Is-proposition ext prop-ext

-- A variant of related≃[equal].

∥related∥≃[equal] :
  {R : A → A → Type r} →
  Propositional-extensionality r →
  Is-equivalence-relation R →
  ∀ {x y} → ∥ R x y ∥ ≃ _≡_ {A = A / R} [ x ] [ y ]
∥related∥≃[equal] {A} {R} prop-ext R-equiv {x} {y} =
  ∥ R x y ∥                                    ↝⟨ related≃[equal]
                                                    prop-ext
                                                    (TruncP.∥∥-preserves-Is-equivalence-relation R-equiv)
                                                    TruncP.truncation-is-proposition ⟩
  _≡_ {A = A / λ x y → ∥ R x y ∥} [ x ] [ y ]  ↝⟨ Eq.≃-≡ (inverse /-∥∥≃/) ⟩□
  _≡_ {A = A / R} [ x ] [ y ]                  □

-- Quotienting with equality (for a set) amounts to the same thing as
-- not quotienting at all.

/≡↔ : Is-set A → A / _≡_ ↔ A
/≡↔ A-set = record
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
      .is-propositionʳ _ → /-is-set
  }

-- Quotienting with a trivial relation amounts to the same thing as
-- using the propositional truncation.

/trivial↔∥∥ : (∀ x y → R x y) → A / R ↔ ∥ A ∥
/trivial↔∥∥ {A} {R} trivial = record
  { surjection = record
    { logical-equivalence = record
      { from = TruncP.rec /-prop [_]
      ; to   = rec-prop λ where
          .[]ʳ             → ∣_∣
          .is-propositionʳ → TruncP.truncation-is-proposition
      }
    ; right-inverse-of = TruncP.elim
        _
        (λ _ → ⇒≡ 1 TruncP.truncation-is-proposition)
        (λ _ → refl _)
    }
  ; left-inverse-of = elim-prop λ where
      .[]ʳ _             → refl _
      .is-propositionʳ _ → /-is-set
  }
  where
  /-prop : Is-proposition (A / R)
  /-prop = elim-prop λ where
    .[]ʳ x → elim-prop λ where
      .[]ʳ y             → []-respects-relation (trivial x y)
      .is-propositionʳ _ → /-is-set
    .is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      /-is-set

-- The previous property gives us an alternative to
-- constant-function≃∥inhabited∥⇒inhabited.

constant-function↔∥inhabited∥⇒inhabited :
  Is-set B →
  (∃ λ (f : A → B) → Constant f) ↔ (∥ A ∥ → B)
constant-function↔∥inhabited∥⇒inhabited {B} {A} B-set =
  (∃ λ (f : A → B) → Constant f)  ↝⟨ record
                                       { surjection = record
                                         { logical-equivalence = record
                                           { to   = λ { (f , c) → rec λ where
                                                        .[]ʳ                     → f
                                                        .[]-respects-relationʳ _ → c _ _
                                                        .is-setʳ                 → B-set }
                                           ; from = λ f → (f ∘ [_])
                                                        , (λ _ _ → cong f ([]-respects-relation _))
                                           }
                                         ; right-inverse-of = λ f → ⟨ext⟩ $ elim λ where
                                             .[]ʳ _                   → refl _
                                             .[]-respects-relationʳ _ → B-set _ _
                                             .is-setʳ _               → mono₁ 2 B-set
                                         }
                                       ; left-inverse-of = λ _ → Σ-≡,≡→≡
                                           (refl _)
                                           ((Π-closure ext 1 λ _ →
                                             Π-closure ext 1 λ _ →
                                             B-set) _ _)
                                       } ⟩
  (A / (λ _ _ → ⊤) → B)           ↝⟨ →-cong₁ ext (/trivial↔∥∥ _) ⟩□
  (∥ A ∥ → B)                     □

private

  -- The two directions of the proposition above compute in the
  -- "right" way. Note that (at the time of writing) an analogue of
  -- the second property below fails to hold definitionally for
  -- constant-function≃∥inhabited∥⇒inhabited.

  to-constant-function↔∥inhabited∥⇒inhabited :
    (B-set : Is-set B) →
    _↔_.to (constant-function↔∥inhabited∥⇒inhabited B-set) f ∣ x ∣ ≡
    proj₁ f x
  to-constant-function↔∥inhabited∥⇒inhabited _ = refl _

  from-constant-function↔∥inhabited∥⇒inhabited :
    (B-set : Is-set B) →
    proj₁ (_↔_.from (constant-function↔∥inhabited∥⇒inhabited B-set) f)
          x ≡
    f ∣ x ∣
  from-constant-function↔∥inhabited∥⇒inhabited _ = refl _

-- The quotient type ⊤ / R is equivalent to ⊤.

⊤/≃ : ⊤ / R ≃ ⊤
⊤/≃ = Eq.↔→≃
  _
  [_]
  refl
  (elim-prop λ where
     .is-propositionʳ _ → /-is-set
     .[]ʳ _             → refl _)

-- If R is a propositional equivalence relation that is pointwise
-- stable, then equality is very stable for A / R (assuming
-- propositional extensionality).

Very-stable-≡-/ :
  {R : A → A → Type r} →
  Propositional-extensionality r →
  Is-equivalence-relation R →
  (∀ x y → Is-proposition (R x y)) →
  (∀ x y → Stable (R x y)) →
  Very-stable-≡ (A / R)
Very-stable-≡-/ {A} {R} prop-ext equiv prop s =
  elim-prop λ where
    .[]ʳ x → elim-prop λ where
       .[]ʳ y →                       $⟨ s _ _ ⟩
         Stable (R x y)               ↝⟨ flip E.Stable-proposition→Very-stable (prop _ _) ⟩
         Very-stable (R x y)          ↝⟨ E.Very-stable-cong _ (related≃[equal] prop-ext equiv (prop _ _)) ⟩□
         Very-stable ([ x ] ≡ [ y ])  □
       .is-propositionʳ _ → E.Very-stable-propositional ext
    .is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      E.Very-stable-propositional ext

private

  -- An alternative definition of the quotients from
  -- Quotient.Families-of-equivalence-classes.

  infix 5 _/′_

  _/′_ : (A : Type a) → (A → A → Type a) → Type (lsuc a)
  _/′_ {a} A R = ∃ λ (P : A → Type a) → ∥ (∃ λ x → R x ≡ P) ∥

  /↔/′ : A Quotient./ R ↔ A /′ R
  /↔/′ {A} {R} =
    A Quotient./ R                                            ↔⟨⟩
    (∃ λ (P : A → Type _) → Trunc.∥ (∃ λ x → R x ≡ P) ∥ 1 _)  ↝⟨ (∃-cong λ _ → inverse $ TruncP.∥∥↔∥∥ lzero) ⟩
    (∃ λ (P : A → Type _) → ∥ (∃ λ x → R x ≡ P) ∥)            ↔⟨⟩
    A /′ R                                                    □

  [_]′ : A → A /′ R
  [_]′ = _↔_.to /↔/′ ∘ Quotient.[_]

  rec′ :
    {A : Type a} {R : A → A → Type a} →
    (∀ {x} → R x x) →
    (B : Type a) →
    Is-set B →
    (f : A → B) →
    (∀ {x y} → R x y → f x ≡ f y) →
    A /′ R → B
  rec′ refl B B-set f R⇒≡ =
    Quotient.rec ext refl B B-set f R⇒≡ ∘
    _↔_.from /↔/′

  elim-Prop′ :
    {A : Type a} {R : A → A → Type a} →
    Quotient.Strong-equivalence-with surjection R →
    (B : A /′ R → Type (lsuc a)) →
    (∀ x → Is-proposition (B [ x ]′)) →
    (f : ∀ x → B [ x ]′) →
    ∀ x → B x
  elim-Prop′ strong-equivalence B B-prop f x =
    subst B (_↔_.right-inverse-of /↔/′ _) $
      Quotient.elim-Prop
        ext
        strong-equivalence
        (B ∘ _↔_.to /↔/′)
        B-prop
        f
        (_↔_.from /↔/′ x)

-- If the relation is a propositional equivalence relation of a
-- certain size, then the quotients defined above are isomorphic to
-- families of equivalence relations, defined in a certain way
-- (assuming univalence).

/↔ :
  {A : Type a} {R : A → A → Type a} →
  Univalence a →
  Univalence lzero →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  A / R ↔ ∃ λ (P : A → Type a) → ∥ (∃ λ x → R x ≡ P) ∥
/↔ {a} {A} {R} univ univ₀ R-equiv R-prop = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  R-is-strong-equivalence : Quotient.Strong-equivalence R
  R-is-strong-equivalence =
    Quotient.propositional-equivalence⇒strong-equivalence
      ext univ R-equiv (λ _ _ → R-prop)

  to : A / R → A /′ R
  to = rec λ where
    .[]ʳ                           → [_]′
    .[]-respects-relationʳ {x} {y} →
      R x y                            ↝⟨ _≃_.to (Quotient.related↝[equal] ext R-is-strong-equivalence) ⟩
      Quotient.[ x ] ≡ Quotient.[ y ]  ↝⟨ cong (_↔_.to /↔/′) ⟩□
      [ x ]′ ≡ [ y ]′                  □
    .is-setʳ →                 $⟨ (λ {_ _} → Quotient.quotient's-h-level-is-1-+-relation's-h-level
                                               ext univ univ₀ 1 (λ _ _ → R-prop)) ⟩
      Is-set (A Quotient./ R)  ↝⟨ H.respects-surjection (_↔_.surjection /↔/′) 2 ⟩□
      Is-set (A /′ R)          □

  from : A /′ R → A / R
  from = rec′
    (Is-equivalence-relation.reflexive R-equiv)
    _
    /-is-set
    [_]
    []-respects-relation

  to∘from : ∀ x → to (from x) ≡ x
  to∘from = elim-Prop′
    (Quotient.strong-equivalence⇒strong-equivalence-with
       R-is-strong-equivalence)
    _
    (λ x →                                         $⟨ (λ {_ _} → Quotient.quotient's-h-level-is-1-+-relation's-h-level
                                                                   ext univ univ₀ 1 λ _ _ → R-prop) ⟩
       Is-set (A Quotient./ R)                     ↝⟨ H.respects-surjection (_↔_.surjection /↔/′) 2 ⟩
       Is-set (A /′ R)                             ↝⟨ +⇒≡ {n = 1} ⟩□
       Is-proposition (to (from [ x ]′) ≡ [ x ]′)  □)
    (λ _ → refl _)

  from∘to : ∀ x → from (to x) ≡ x
  from∘to = elim-prop λ where
    .[]ʳ _             → refl _
    .is-propositionʳ _ → /-is-set

-- If the relation is a propositional equivalence relation of a
-- certain size, then the definition of quotients given in
-- Quotient.Families-of-equivalence-classes is isomorphic to the one
-- given here (assuming univalence).

/↔/ :
  {A : Type a} {R : A → A → Type a} →
  Univalence a →
  Univalence lzero →
  Is-equivalence-relation R →
  (R-prop : ∀ {x y} → Is-proposition (R x y)) →
  A Quotient./ R ↔ A / R
/↔/ {a} {A} {R} univ univ₀ R-equiv R-prop =
  A Quotient./ R                                                   ↔⟨⟩
  (∃ λ (P : A → Type a) → Trunc.∥ (∃ λ x → R x ≡ P) ∥ 1 (lsuc a))  ↝⟨ (∃-cong λ _ → inverse $ TruncP.∥∥↔∥∥ lzero) ⟩
  (∃ λ (P : A → Type a) →       ∥ (∃ λ x → R x ≡ P) ∥)             ↝⟨ inverse $ /↔ univ univ₀ R-equiv R-prop ⟩□
  A / R                                                            □

------------------------------------------------------------------------
-- Various type formers commute with quotients

-- _⊎_ commutes with quotients.

⊎/-comm : (A₁ ⊎ A₂) / (R₁ ⊎ᴾ R₂) ↔ A₁ / R₁ ⊎ A₂ / R₂
⊎/-comm = record
  { surjection = record
    { logical-equivalence = record
      { to = rec λ where
          .[]ʳ     → ⊎-map [_] [_]
          .is-setʳ → ⊎-closure 0 /-is-set /-is-set

          .[]-respects-relationʳ {x = inj₁ _} {y = inj₁ _} →
            cong inj₁ ∘ []-respects-relation
          .[]-respects-relationʳ {x = inj₂ _} {y = inj₂ _} →
            cong inj₂ ∘ []-respects-relation

      ; from = Prelude.[ rec (λ where
                           .[]ʳ                   → [_] ∘ inj₁
                           .[]-respects-relationʳ → []-respects-relation
                           .is-setʳ               → /-is-set)
                       , rec (λ where
                           .[]ʳ                   → [_] ∘ inj₂
                           .[]-respects-relationʳ → []-respects-relation
                           .is-setʳ               → /-is-set)
                       ]
      }
    ; right-inverse-of =
        Prelude.[ elim-prop (λ where
                    .[]ʳ _             → refl _
                    .is-propositionʳ _ → ⊎-closure 0 /-is-set /-is-set)
                , elim-prop (λ where
                    .[]ʳ _             → refl _
                    .is-propositionʳ _ → ⊎-closure 0 /-is-set /-is-set)
                ]
    }
  ; left-inverse-of = elim-prop λ where
      .[]ʳ               → Prelude.[ (λ _ → refl _) , (λ _ → refl _) ]
      .is-propositionʳ _ → /-is-set
  }

-- Maybe commutes with quotients.
--
-- Chapman, Uustalu and Veltri mention a similar result in
-- "Quotienting the Delay Monad by Weak Bisimilarity".

Maybe/-comm : Maybe A / Maybeᴾ R ↔ Maybe (A / R)
Maybe/-comm {A} {R} =
  Maybe A / Maybeᴾ R   ↝⟨ ⊎/-comm ⟩
  ⊤ / Trivial ⊎ A / R  ↝⟨ /trivial↔∥∥ _ ⊎-cong F.id ⟩
  ∥ ⊤ ∥ ⊎ A / R        ↝⟨ TruncP.∥∥↔ (mono₁ 0 ⊤-contractible) ⊎-cong F.id ⟩□
  Maybe (A / R)        □

-- A simplification lemma for Maybe/-comm.

Maybe/-comm-[] : _↔_.to Maybe/-comm ∘ [_] ≡ ⊎-map id ([_] {R = R})
Maybe/-comm-[] =
  _↔_.to Maybe/-comm ∘ [_]                 ≡⟨⟩
  ⊎-map _ id ∘ ⊎-map _ id ∘ ⊎-map [_] [_]  ≡⟨ cong (_∘ ⊎-map [_] [_]) ⊎-map-∘ ⟩
  ⊎-map _ id ∘ ⊎-map [_] [_]               ≡⟨ ⊎-map-∘ ⟩∎
  ⊎-map id [_]                             ∎
  where
  ⊎-map-∘ : ∀ {a₁ b₁ c₁} {A₁ : Type a₁} {B₁ : Type b₁} {C₁ : Type c₁}
              {a₂ b₂ c₂} {A₂ : Type a₂} {B₂ : Type b₂} {C₂ : Type c₂}
              {f₁ : B₁ → C₁} {g₁ : A₁ → B₁}
              {f₂ : B₂ → C₂} {g₂ : A₂ → B₂} →
            ⊎-map f₁ f₂ ∘ ⊎-map g₁ g₂ ≡ ⊎-map (f₁ ∘ g₁) (f₂ ∘ g₂)
  ⊎-map-∘ = ⟨ext⟩ Prelude.[ (λ _ → refl _) , (λ _ → refl _) ]

-- Cartesian products commute with quotients, assuming that the two
-- binary relations involved in the statement are reflexive.

×/-comm :
  (∀ {x} → R₁ x x) →
  (∀ {x} → R₂ x x) →
  (A₁ × A₂) / (R₁ ×ᴾ R₂) ≃ (A₁ / R₁ × A₂ / R₂)
×/-comm {R₁} {R₂} R₁-refl R₂-refl = Eq.↔→≃
  (rec λ where
     .is-setʳ → ×-closure 2 /-is-set /-is-set

     .[]ʳ → Σ-map [_] [_]

     .[]-respects-relationʳ {x = x₁ , x₂} {y = y₁ , y₂} →
       R₁ x₁ y₁ × R₂ x₂ y₂                    ↝⟨ Σ-map []-respects-relation
                                                       []-respects-relation ⟩
       [ x₁ ] ≡ [ y₁ ] × [ x₂ ] ≡ [ y₂ ]      ↝⟨ uncurry (cong₂ _,_) ⟩□
       ([ x₁ ] , [ x₂ ]) ≡ ([ y₁ ] , [ y₂ ])  □)
  (uncurry $ rec λ where
     .is-setʳ →
       Π-closure ext 2 λ _ →
       /-is-set
     .[]ʳ x → (x ,_) /-map λ y₁ y₂ →
       R₂ y₁ y₂           ↝⟨ R₁-refl ,_ ⟩□
       R₁ x x × R₂ y₁ y₂  □
     .[]-respects-relationʳ {x = x₁} {y = x₂} R₁x₁x₂ →
       ⟨ext⟩ $ elim-prop λ where
         .is-propositionʳ _ →
           /-is-set
         .[]ʳ y →
           [ (x₁ , y) ]  ≡⟨ []-respects-relation (R₁x₁x₂ , R₂-refl) ⟩∎
           [ (x₂ , y) ]  ∎)
  (uncurry $ elim-prop λ where
     .is-propositionʳ _ →
       Π-closure ext 1 λ _ →
       ×-closure 2 /-is-set /-is-set
     .[]ʳ _ → elim-prop λ where
       .is-propositionʳ _ →
         ×-closure 2 /-is-set /-is-set
       .[]ʳ _ →
         refl _)
  (elim-prop λ where
     .is-propositionʳ _ → /-is-set
     .[]ʳ _             → refl _)

-- The sigma type former commutes (kind of) with quotients, assuming
-- that the second projections come from propositional types.

Σ/-comm :
  {P : A / R → Type p} →
  (∀ {x} → Is-proposition (P x)) →
  Σ (A / R) P ↔ Σ A (P ∘ [_]) / (R on proj₁)
Σ/-comm {A} {R} {P} P-prop = record
  { surjection = record
    { logical-equivalence = record
      { to =
          uncurry $
          elim λ where
            .[]ʳ → curry [_]
            .[]-respects-relationʳ {x} {y} r → ⟨ext⟩ λ P[y] →
              subst (λ x → P x → Σ A (P ∘ [_]) / (R on proj₁))
                    ([]-respects-relation r)
                    (curry [_] x) P[y]                               ≡⟨ subst-→-domain P {f = curry [_] _} ([]-respects-relation r) ⟩

              [ (x , subst P (sym $ []-respects-relation r) P[y]) ]  ≡⟨ []-respects-relation r ⟩∎

              [ (y , P[y]) ]                                         ∎
            .is-setʳ _ →
              Π-closure ext 2 λ _ →
              /-is-set
      ; from = rec λ where
          .[]ʳ     → Σ-map [_] id
          .is-setʳ → Σ-closure 2 /-is-set (λ _ → mono₁ 1 P-prop)

          .[]-respects-relationʳ {x = (x₁ , x₂)} {y = (y₁ , y₂)} →
            R x₁ y₁                        ↝⟨ []-respects-relation ⟩
            [ x₁ ] ≡ [ y₁ ]                ↔⟨ ignore-propositional-component P-prop ⟩
            ([ x₁ ] , x₂) ≡ ([ y₁ ] , y₂)  □
      }
    ; right-inverse-of = elim-prop λ where
        .[]ʳ _             → refl _
        .is-propositionʳ _ → /-is-set
    }
  ; left-inverse-of = uncurry $ elim-prop λ where
      .[]ʳ _ _           → refl _
      .is-propositionʳ _ →
        Π-closure ext 1 λ _ →
        Σ-closure 2 /-is-set (λ _ → mono₁ 1 P-prop)
  }

-- Erased commutes with quotients if certain conditions hold.

Erased/-comm :
  {@0 A : Type a} {@0 R : A → A → Type r} →
  @0 Is-set A →
  @0 (∀ {x y} → R x y → x ≡ y) →
  Erased A / Erasedᴾ R ≃ Erased (A / R)
Erased/-comm {A} {R} set R→≡ = Eq.↔→≃
  (rec λ where
     .is-setʳ                         → E.H-level-Erased 2 /-is-set
     .[]ʳ                             → E.map [_]
     .[]-respects-relationʳ E.[ Rxy ] →
       E.[]-cong E.[ []-respects-relation Rxy ])
  (λ (E.[ x ]) → [ E.[ from′ x ] ])
  (λ (E.[ x ]) →
     E.[]-cong
       E.[ flip (elim-prop {P = λ x → [ from′ x ] ≡ x}) x (λ @0 where
             .is-propositionʳ _ → /-is-set
             .[]ʳ _             → refl _)
         ])
  (elim-prop λ where
     .is-propositionʳ _ → /-is-set
     .[]ʳ _             → refl _)
  where
  @0 from′ : A / R → A
  from′ = rec λ @0 where
    .is-setʳ               → set
    .[]ʳ                   → id
    .[]-respects-relationʳ → R→≡

-- The type former λ X → ℕ → X commutes with quotients, assuming that
-- the quotient relation is a propositional equivalence relation, and
-- also assuming countable choice and propositional extensionality.
--
-- This result is very similar to Proposition 5 in "Quotienting the
-- Delay Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

-- The forward component of the isomorphism. This component can be
-- defined without any extra assumptions.

ℕ→/-comm-to : (ℕ → A) / (ℕ →ᴾ R) → (ℕ → A / R)
ℕ→/-comm-to = rec λ where
  .[]ʳ f n                 → [ f n ]
  .[]-respects-relationʳ r → ⟨ext⟩ ([]-respects-relation ∘ r)
  .is-setʳ                 →
    Π-closure ext 2 λ _ →
    /-is-set

-- The isomorphism.

ℕ→/-comm :
  {A : Type a} {R : A → A → Type r} →
  Axiom-of-countable-choice (a ⊔ r) →
  Propositional-extensionality r →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  (ℕ → A) / (ℕ →ᴾ R) ↔ (ℕ → A / R)
ℕ→/-comm {A} {R} cc prop-ext R-equiv R-prop = record
  { surjection = record
    { logical-equivalence = record
      { to   = ℕ→/-comm-to
      ; from = from unit
      }
    ; right-inverse-of = to∘from unit
    }
  ; left-inverse-of = from∘to unit
  }
  where
  [_]→ : (ℕ → A) → (ℕ → A / R)
  [ f ]→ n = [ f n ]

  -- A module that is introduced to ensure that []→-surjective is not
  -- in the same abstract block as the abstract definitions below.

  module Dummy where

    abstract

      []→-surjective : Surjective [_]→
      []→-surjective f =                    $⟨ []-surjective ⟩
        Surjective [_]                      ↝⟨ (λ surj → surj ∘ f) ⦂ (_ → _) ⟩
        (∀ n → ∥ (∃ λ x → [ x ] ≡ f n) ∥)   ↔⟨ TruncP.countable-choice-bijection cc ⟩
        ∥ (∀ n → ∃ λ x → [ x ] ≡ f n) ∥     ↔⟨ TruncP.∥∥-cong ΠΣ-comm ⟩
        ∥ (∃ λ g → ∀ n → [ g n ] ≡ f n) ∥   ↔⟨⟩
        ∥ (∃ λ g → ∀ n → [ g ]→ n ≡ f n) ∥  ↔⟨ TruncP.∥∥-cong (∃-cong λ _ → Eq.extensionality-isomorphism ext) ⟩□
        ∥ (∃ λ g → [ g ]→ ≡ f) ∥            □

  open Dummy

  from₁ : ∀ f → [_]→ ⁻¹ f → ℕ→/-comm-to ⁻¹ f
  from₁ f (g , [g]→≡f) =
      [ g ]
    , (ℕ→/-comm-to [ g ]  ≡⟨⟩
       [ g ]→             ≡⟨ [g]→≡f ⟩∎
       f                  ∎)

  from₁-constant : ∀ f → Constant (from₁ f)
  from₁-constant f (g₁ , [g₁]→≡f) (g₂ , [g₂]→≡f) =
                                             $⟨ (λ n → cong (_$ n) (
        [ g₁ ]→                                    ≡⟨ [g₁]→≡f ⟩
        f                                          ≡⟨ sym [g₂]→≡f ⟩∎
        [ g₂ ]→                                    ∎)) ⟩

    (∀ n → [ g₁ ]→ n ≡ [ g₂ ]→ n)            ↔⟨⟩

    (∀ n → [ g₁ n ] ≡ [ g₂ n ])              ↔⟨ ∀-cong ext (λ _ → inverse $ related≃[equal] prop-ext R-equiv R-prop) ⟩

    (∀ n → R (g₁ n) (g₂ n))                  ↔⟨⟩

    (ℕ →ᴾ R) g₁ g₂                           ↝⟨ []-respects-relation ⟩

    [ g₁ ] ≡ [ g₂ ]                          ↔⟨ ignore-propositional-component
                                                  (Π-closure ext 2 λ _ →
                                                   /-is-set) ⟩□
    ([ g₁ ] , [g₁]→≡f) ≡ ([ g₂ ] , [g₂]→≡f)  □

  from₂ : Unit → ∀ f → ∥ [_]→ ⁻¹ f ∥ → ℕ→/-comm-to ⁻¹ f
  from₂ unit f =
    _≃_.to (TruncP.constant-function≃∥inhabited∥⇒inhabited
              (Σ-closure 2 /-is-set λ _ →
               mono₁ 1 (Π-closure ext 2 (λ _ → /-is-set))))
           (from₁ f , from₁-constant f)

  unblock-from₂ : ∀ x f p → from₂ x f ∣ p ∣ ≡ from₁ f p
  unblock-from₂ unit _ _ = refl _

  abstract

    from₃ : Unit → (f : ℕ → A / R) → ℕ→/-comm-to ⁻¹ f
    from₃ x f = from₂ x f ([]→-surjective f)

    from : Unit → (ℕ → A / R) → (ℕ → A) / (ℕ →ᴾ R)
    from x f = proj₁ (from₃ x f)

    to∘from : ∀ x f → ℕ→/-comm-to (from x f) ≡ f
    to∘from x f = proj₂ (from₃ x f)

    from∘to : ∀ x f → from x (ℕ→/-comm-to f) ≡ f
    from∘to x = elim-prop λ where
      .[]ʳ f →
        from x (ℕ→/-comm-to [ f ])                      ≡⟨⟩
        proj₁ (from₂ x [ f ]→ ([]→-surjective [ f ]→))  ≡⟨ cong (proj₁ ∘ from₂ x [ f ]→) $ TruncP.truncation-is-proposition _ _ ⟩
        proj₁ (from₂ x [ f ]→ ∣ f , refl _ ∣)           ≡⟨ cong proj₁ $ unblock-from₂ x _ (f , refl _) ⟩
        proj₁ (from₁ [ f ]→ (f , refl _))               ≡⟨⟩
        [ f ]                                           ∎
      .is-propositionʳ _ → /-is-set

------------------------------------------------------------------------
-- Quotient-like eliminators

-- If there is a split surjection from a quotient type to some other
-- type, then one can construct a quotient-like eliminator for the
-- other type.
--
-- This kind of construction is used in "Quotienting the Delay Monad
-- by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

↠-eliminator :
  (surj : A / R ↠ B)
  (P : B → Type p)
  (p-[] : ∀ x → P (_↠_.to surj [ x ])) →
  (∀ {x y} (r : R x y) →
   subst P (cong (_↠_.to surj) ([]-respects-relation r)) (p-[] x) ≡
   p-[] y) →
  (∀ x → Is-set (P x)) →
  ∀ x → P x
↠-eliminator surj P p-[] ok P-set x =
  subst P (_↠_.right-inverse-of surj x) p′
  where
  p′ : P (_↠_.to surj (_↠_.from surj x))
  p′ = elim
    (λ where
       .[]ʳ                             → p-[]
       .[]-respects-relationʳ {x} {y} r →
         subst (P ∘ _↠_.to surj) ([]-respects-relation r) (p-[] x)       ≡⟨ subst-∘ P (_↠_.to surj) ([]-respects-relation r) ⟩
         subst P (cong (_↠_.to surj) ([]-respects-relation r)) (p-[] x)  ≡⟨ ok r ⟩∎
         p-[] y                                                          ∎
       .is-setʳ _ → P-set _)
    (_↠_.from surj x)

-- The eliminator "computes" in the "right" way for elements that
-- satisfy a certain property.

↠-eliminator-[] :
  ∀ (surj : A / R ↠ B)
  (P : B → Type p)
  (p-[] : ∀ x → P (_↠_.to surj [ x ]))
  (ok : ∀ {x y} (r : R x y) →
        subst P (cong (_↠_.to surj) ([]-respects-relation r)) (p-[] x) ≡
        p-[] y)
  (P-set : ∀ x → Is-set (P x)) x →
  _↠_.from surj (_↠_.to surj [ x ]) ≡ [ x ] →
  ↠-eliminator surj P p-[] ok P-set (_↠_.to surj [ x ]) ≡ p-[] x
↠-eliminator-[] {R} surj P p-[] ok P-set x hyp =
  subst P (_↠_.right-inverse-of surj (_↠_.to surj [ x ]))
    (elim e (_↠_.from surj (_↠_.to surj [ x ])))                        ≡⟨ cong (λ p → subst P p (elim e _)) $
                                                                           H.respects-surjection surj 2 /-is-set
                                                                             (_↠_.right-inverse-of surj (_↠_.to surj [ x ]))
                                                                             (cong (_↠_.to surj) hyp) ⟩
  subst P (cong (_↠_.to surj) hyp)
    (elim e (_↠_.from surj (_↠_.to surj [ x ])))                        ≡⟨ D.elim
                                                                             (λ {x y} p → subst P (cong (_↠_.to surj) p) (elim e x) ≡ elim e y)
                                                                             (λ y →
      subst P (cong (_↠_.to surj) (refl _)) (elim e y)                          ≡⟨ cong (λ p → subst P p (elim e _)) $ cong-refl (_↠_.to surj) ⟩
      subst P (refl _) (elim e y)                                               ≡⟨ subst-refl P _ ⟩∎
      elim e y                                                                  ∎)
                                                                             hyp ⟩
  elim e [ x ]                                                          ≡⟨⟩

  p-[] x                                                                ∎
  where
  e = _

-- If there is a bijection from a quotient type to some other type,
-- then one can also construct a quotient-like eliminator for the
-- other type.

↔-eliminator :
  (bij : A / R ↔ B)
  (P : B → Type p)
  (p-[] : ∀ x → P (_↔_.to bij [ x ])) →
  (∀ {x y} (r : R x y) →
   subst P (cong (_↔_.to bij) ([]-respects-relation r)) (p-[] x) ≡
   p-[] y) →
  (∀ x → Is-set (P x)) →
  ∀ x → P x
↔-eliminator bij = ↠-eliminator (_↔_.surjection bij)

-- This latter eliminator always "computes" in the "right" way.

↔-eliminator-[] :
  ∀ (bij : A / R ↔ B)
  (P : B → Type p)
  (p-[] : ∀ x → P (_↔_.to bij [ x ]))
  (ok : ∀ {x y} (r : R x y) →
        subst P (cong (_↔_.to bij) ([]-respects-relation r)) (p-[] x) ≡
        p-[] y)
  (P-set : ∀ x → Is-set (P x)) x →
  ↔-eliminator bij P p-[] ok P-set (_↔_.to bij [ x ]) ≡ p-[] x
↔-eliminator-[] bij P p-[] ok P-set x =
  ↠-eliminator-[] (_↔_.surjection bij) P p-[] ok P-set x
    (_↔_.left-inverse-of bij [ x ])

-- A quotient-like eliminator for functions of type ℕ → A / R, where R
-- is a propositional equivalence relation. Defined using countable
-- choice and propositional extensionality.
--
-- This eliminator is taken from Corollary 1 in "Quotienting the Delay
-- Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

ℕ→/-elim :
  {A : Type a} {R : A → A → Type r} →
  Axiom-of-countable-choice (a ⊔ r) →
  Propositional-extensionality r →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  (P : (ℕ → A / R) → Type p)
  (p-[] : ∀ f → P (λ n → [ f n ])) →
  (∀ {f g} (r : (ℕ →ᴾ R) f g) →
   subst P (cong ℕ→/-comm-to ([]-respects-relation r)) (p-[] f) ≡
   p-[] g) →
  (∀ f → Is-set (P f)) →
  ∀ f → P f
ℕ→/-elim cc prop-ext R-equiv R-prop =
  ↔-eliminator (ℕ→/-comm cc prop-ext R-equiv R-prop)

-- The eliminator "computes" in the "right" way.

ℕ→/-elim-[] :
  ∀ {A : Type a} {R : A → A → Type r}
  (cc : Axiom-of-countable-choice (a ⊔ r))
  (prop-ext : Propositional-extensionality r)
  (R-equiv : Is-equivalence-relation R)
  (R-prop : ∀ {x y} → Is-proposition (R x y))
  (P : (ℕ → A / R) → Type p)
  (p-[] : ∀ f → P (λ n → [ f n ]))
  (ok : ∀ {f g} (r : (ℕ →ᴾ R) f g) →
        subst P (cong ℕ→/-comm-to ([]-respects-relation r)) (p-[] f) ≡
        p-[] g)
  (P-set : ∀ f → Is-set (P f)) f →
  ℕ→/-elim cc prop-ext R-equiv R-prop P p-[] ok P-set (λ n → [ f n ]) ≡
  p-[] f
ℕ→/-elim-[] cc prop-ext R-equiv R-prop =
  ↔-eliminator-[] (ℕ→/-comm cc prop-ext R-equiv R-prop)
