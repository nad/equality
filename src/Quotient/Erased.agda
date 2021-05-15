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

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as Er using (Erased; [_])
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as PT
  using (∥_∥; ∣_∣; Surjective)
open import H-level.Truncation.Propositional.Erased eq as PTᴱ
  using (∥_∥ᴱ; ∣_∣; Surjectiveᴱ)
open import Quotient eq as Q using (_/_)
open import Surjection equality-with-J using (_↠_)

private
  variable
    a a₁ a₂ r r₁ r₂ : Level
    A A₁ A₂ B       : Type a
    R               : A → A → Type r
    f k x y         : A

------------------------------------------------------------------------
-- A re-export

-- This module re-exports Quotient.Erased.Basics.

open import Quotient.Erased.Basics eq public

------------------------------------------------------------------------
-- Preservation lemmas

-- Two preservation lemmas for functions.

infix 5 _/ᴱ-map-∥∥_ _/ᴱ-map_

_/ᴱ-map-∥∥_ :
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
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
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
  (A₁→A₂ : A₁ → A₂) →
  @0 (∀ x y → R₁ x y → R₂ (A₁→A₂ x) (A₁→A₂ y)) →
  A₁ /ᴱ R₁ → A₂ /ᴱ R₂
A₁→A₂ /ᴱ-map R₁→R₂ = A₁→A₂ /ᴱ-map-∥∥ λ x y → PT.∥∥-map (R₁→R₂ x y)

-- Two preservation lemmas for logical equivalences.

/ᴱ-cong-∥∥-⇔ :
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
  (A₁⇔A₂ : A₁ ⇔ A₂) →
  @0 (∀ x y → ∥ R₁ x y ∥ → ∥ R₂ (_⇔_.to   A₁⇔A₂ x) (_⇔_.to   A₁⇔A₂ y) ∥) →
  @0 (∀ x y → ∥ R₂ x y ∥ → ∥ R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y) ∥) →
  A₁ /ᴱ R₁ ⇔ A₂ /ᴱ R₂
/ᴱ-cong-∥∥-⇔ A₁⇔A₂ R₁→R₂ R₂→R₁ = record
  { to   = _⇔_.to   A₁⇔A₂ /ᴱ-map-∥∥ R₁→R₂
  ; from = _⇔_.from A₁⇔A₂ /ᴱ-map-∥∥ R₂→R₁
  }

/ᴱ-cong-⇔ :
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
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
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
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
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
  (A₁↠A₂ : A₁ ↠ A₂) →
  @0 (∀ x y → R₁ x y ⇔ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y)) →
  A₁ /ᴱ R₁ ↠ A₂ /ᴱ R₂
A₁↠A₂ /ᴱ-cong-↠ R₁⇔R₂ =
  A₁↠A₂ /ᴱ-cong-∥∥-↠ λ x y → PT.∥∥-cong-⇔ (R₁⇔R₂ x y)

-- Two preservation lemmas for isomorphisms.

infix 5 _/ᴱ-cong-∥∥_ _/ᴱ-cong_

_/ᴱ-cong-∥∥_ :
  {A₁ : Type a₁} {A₂ : Type a₂}
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
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
  {A₁ : Type a₁} {A₂ : Type a₂}
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
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
  {R : A → A → Type r} →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  R x y ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
related≃[equal] {A = A} {r = r} {x = x} {y = y} {R = R}
                R-equiv R-prop =
  R x y                             ↝⟨ Q.related≃[equal] R-equiv R-prop ⟩
  _≡_ {A = A /  R} Q.[ x ] Q.[ y ]  ↝⟨ Eq.≃-≡ Q./ᴱ≃/ ⟩□
  _≡_ {A = A /ᴱ R}   [ x ]   [ y ]  □

-- A variant of related≃[equal].

@0 ∥related∥≃[equal] :
  Is-equivalence-relation R →
  ∥ R x y ∥ ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
∥related∥≃[equal] {A = A} {R = R} {x = x} {y = y} R-equiv =
  ∥ R x y ∥                         ↝⟨ Q.∥related∥≃[equal] R-equiv ⟩
  _≡_ {A = A /  R} Q.[ x ] Q.[ y ]  ↝⟨ Eq.≃-≡ Q./ᴱ≃/ ⟩□
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
          .PTᴱ.truncation-is-propositionʳ → elim-prop λ @0 where
            .is-propositionʳ _ →
              Π-closure ext 1 λ _ →
              /ᴱ-is-set
            .[]ʳ x → elim-prop λ @0 where
              .is-propositionʳ _ → /ᴱ-is-set
              .[]ʳ y             → []-respects-relation (trivial x y)
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
