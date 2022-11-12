------------------------------------------------------------------------
-- A variant of set quotients with erased higher constructors
------------------------------------------------------------------------

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

module Quotient.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq
import Equality.Path.Isomorphisms.Univalence eq as U
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence.Erased equality-with-J as EEq
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as Er using (Erased; Erasedᴾ; [_])
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as PT using (∥_∥; ∣_∣)
open import H-level.Truncation.Propositional.Erased eq as PTᴱ
  using (∥_∥ᴱ; ∣_∣; Surjectiveᴱ)
import List equality-with-J as L
open import Quotient eq as Q using (_/_)
open import Sum equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

private
  variable
    a a₁ a₂ ℓ p r r₁ r₂ r₃ : Level
    A A₁ A₂ A₃ B           : Type a
    P                      : A → Type p
    R                      : A → A → Type r
    f k x y                : A

------------------------------------------------------------------------
-- A re-export

-- This module re-exports Quotient.Erased.Basics.

open import Quotient.Erased.Basics eq public

------------------------------------------------------------------------
-- Unary preservation lemmas

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
-- Binary preservation lemmas

-- Two preservation lemmas for functions.

/ᴱ-zip-∥∥ :
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
  {@0 R₃ : A₃ → A₃ → Type r₃} →
  (f : A₁ → A₂ → A₃) →
  @0 (∀ {x} → ∥ R₁ x x ∥) →
  @0 (∀ {x} → ∥ R₂ x x ∥) →
  @0 (∀ {u v x y} → ∥ R₁ u v ∥ → ∥ R₂ x y ∥ → ∥ R₃ (f u x) (f v y) ∥) →
  A₁ /ᴱ R₁ → A₂ /ᴱ R₂ → A₃ /ᴱ R₃
/ᴱ-zip-∥∥ {R₁ = R₁} {R₂ = R₂} {R₃ = R₃} f r₁ r₂ r₃ = rec λ where
  .is-setʳ →
    Π-closure ext 2 λ _ →
    /ᴱ-is-set
  .[]ʳ x →
    f x
      /ᴱ-map-∥∥
    (λ y₁ y₂ →
       ∥ R₂ y₁ y₂ ∥              →⟨ (λ hyp → r₃ r₁ hyp) ⟩□
       ∥ R₃ (f x y₁) (f x y₂) ∥  □)
  .[]-respects-relationʳ {x = x₁} {y = x₂} x₁R₁x₂ →
    ⟨ext⟩ $ elim-prop λ @0 where
      .is-propositionʳ _ →
        /ᴱ-is-set
      .[]ʳ y →
                                  $⟨ x₁R₁x₂ ⟩
        R₁ x₁ x₂                  →⟨ ∣_∣ ⟩
        ∥ R₁ x₁ x₂ ∥              →⟨ (λ hyp → r₃ hyp r₂) ⟩
        ∥ R₃ (f x₁ y) (f x₂ y) ∥  →⟨ PT.rec /ᴱ-is-set []-respects-relation ⟩□
        [ f x₁ y ] ≡ [ f x₂ y ]   □

/ᴱ-zip :
  {@0 R₁ : A₁ → A₁ → Type r₁}
  {@0 R₂ : A₂ → A₂ → Type r₂} →
  {@0 R₃ : A₃ → A₃ → Type r₃} →
  (f : A₁ → A₂ → A₃) →
  @0 (∀ {x} → R₁ x x) →
  @0 (∀ {x} → R₂ x x) →
  @0 (∀ {u v x y} → R₁ u v → R₂ x y → R₃ (f u x) (f v y)) →
  A₁ /ᴱ R₁ → A₂ /ᴱ R₂ → A₃ /ᴱ R₃
/ᴱ-zip f r₁ r₂ r₃ = /ᴱ-zip-∥∥ f ∣ r₁ ∣ ∣ r₂ ∣ (PT.∥∥-zip r₃)

------------------------------------------------------------------------
-- Some properties

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

-- If R is an equivalence relation, then A /ᴱ R is weakly effective
-- (where this is expressed using ∥_∥ᴱ).
--
-- This proof is based on that of Proposition 2 in "Quotienting the
-- Delay Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

weakly-effective :
  {R : A → A → Type r} →
  @0 Is-equivalence-relation R →
  ∥ R x x ∥ᴱ →
  _≡_ {A = A /ᴱ R} [ x ] [ y ] → ∥ R x y ∥ᴱ
weakly-effective
  {A = A} {r = r} {x = x} {y = y} {R = R} eq ∥Rxx∥ᴱ [x]≡[y] =
                     $⟨ ∥Rxx∥ᴱ ⟩
  R′ x [ x ] .proj₁  ↝⟨ ≡⇒→ (cong (λ y → R′ x y .proj₁) [x]≡[y]) ⟩
  R′ x [ y ] .proj₁  ↔⟨⟩
  ∥ R x y ∥ᴱ         □
  where
  R′ : A → A /ᴱ R → ∃ λ (P : Type r) → Erased (Is-proposition P)
  R′ x = rec λ where
    .[]ʳ y → ∥ R x y ∥ᴱ , [ PTᴱ.truncation-is-proposition ]

    .is-setʳ →                                               $⟨ (λ {_ _} → Is-set-∃-Is-proposition ext U.prop-ext) ⟩
      Is-set (Proposition r)                                 ↝⟨ H-level-cong _ 2
                                                                  (∃-cong λ _ → inverse $ Er.Erased↔ .Er.erased)
                                                                  ⦂ (_ → _) ⟩□
      Is-set (∃ λ (P : Type r) → Erased (Is-proposition P))  □

    .[]-respects-relationʳ {x = y} {y = z} →
      R y z                                        ↝⟨ (λ r → record
                                                         { to   = flip (eq .Is-equivalence-relation.transitive) r
                                                         ; from = flip (eq .Is-equivalence-relation.transitive)
                                                                    (eq .Is-equivalence-relation.symmetric r)
                                                         }) ⟩
      R x y ⇔ R x z                                ↝⟨ EEq._≃ᴱ_.logical-equivalence ∘ PTᴱ.∥∥ᴱ-cong-⇔ ⟩
      ∥ R x y ∥ᴱ ⇔ ∥ R x z ∥ᴱ                      ↔⟨ ⇔↔≡″ ext U.prop-ext ⟩
      (∥ R x y ∥ᴱ , _) ≡ (∥ R x z ∥ᴱ , _)          ↝⟨ cong (Σ-map id Er.[_]→) ⟩□
      (∥ R x y ∥ᴱ , [ _ ]) ≡ (∥ R x z ∥ᴱ , [ _ ])  □

-- If R is an equivalence relation, and R is propositional (for x
-- and y), then A /ᴱ R is effective (for x and y).

effective :
  @0 Is-equivalence-relation R →
  @0 Is-proposition (R x y) →
  R x x →
  _≡_ {A = A /ᴱ R} [ x ] [ y ] → R x y
effective {R = R} {x = x} {y = y} eq prop Rxx =
  [ x ] ≡ [ y ]  ↝⟨ weakly-effective eq ∣ Rxx ∣ ⟩
  ∥ R x y ∥ᴱ     ↔⟨ PTᴱ.∥∥ᴱ↔ prop ⟩□
  R x y          □

-- If R is an equivalence relation, and R is propositional (for x
-- and y), then R x y is equivalent to equality of x and y under [_]
-- (in erased contexts).

@0 related≃[equal] :
  Is-equivalence-relation R →
  Is-proposition (R x y) →
  R x y ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
related≃[equal] eq prop =
  Eq.⇔→≃
    prop
    /ᴱ-is-set
    []-respects-relation
    (effective eq prop (eq .Is-equivalence-relation.reflexive))

-- If R is an equivalence relation, then ∥ R x y ∥ is equivalent to
-- equality of x and y under [_] (in erased contexts).

@0 ∥related∥≃[equal] :
  Is-equivalence-relation R →
  ∥ R x y ∥ ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
∥related∥≃[equal] {R = R} {x = x} {y = y} eq =
  ∥ R x y ∥      ↝⟨ inverse PT.∥∥ᴱ≃∥∥ ⟩
  ∥ R x y ∥ᴱ     ↝⟨ Eq.⇔→≃
                      PTᴱ.truncation-is-proposition
                      /ᴱ-is-set
                      (PTᴱ.rec λ @0 where
                         .PTᴱ.truncation-is-propositionʳ → /ᴱ-is-set
                         .PTᴱ.∣∣ʳ                        →
                           []-respects-relation)
                      (weakly-effective eq ∣ eq .Is-equivalence-relation.reflexive ∣) ⟩□
  [ x ] ≡ [ y ]  □

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

------------------------------------------------------------------------
-- Various type formers commute with quotients

-- The quotient type ⊤ /ᴱ R is equivalent to ⊤.

⊤/ᴱ : ⊤ /ᴱ R ≃ ⊤
⊤/ᴱ = Eq.↔→≃
  _
  [_]
  refl
  (elim-prop λ where
     .is-propositionʳ _ → /ᴱ-is-set
     .[]ʳ _             → refl _)

-- The quotient type ⊥ {ℓ = ℓ} /ᴱ R is equivalent to ⊥ {ℓ = ℓ}.

⊥/ᴱ : ⊥ {ℓ = ℓ} /ᴱ R ≃ ⊥ {ℓ = ℓ}
⊥/ᴱ = Eq.↔→≃
  (rec-prop λ where
     .[]ʳ ()
     .is-propositionʳ ())
  (λ ())
  (λ ())
  (elim-prop λ where
     .[]ʳ ()
     .is-propositionʳ ())

-- _⊎_ commutes with quotients.

⊎/ᴱ :
  {@0 R₁ : A₁ → A₁ → Type r} {@0 R₂ : A₂ → A₂ → Type r} →
  (A₁ ⊎ A₂) /ᴱ (R₁ ⊎ᴾ R₂) ≃ (A₁ /ᴱ R₁ ⊎ A₂ /ᴱ R₂)
⊎/ᴱ = Eq.↔→≃
  (rec λ where
     .[]ʳ → ⊎-map [_] [_]

     .is-setʳ → ⊎-closure 0 /ᴱ-is-set /ᴱ-is-set

     .[]-respects-relationʳ {x = inj₁ _} {y = inj₁ _} →
       cong inj₁ ∘ []-respects-relation
     .[]-respects-relationʳ {x = inj₂ _} {y = inj₂ _} →
       cong inj₂ ∘ []-respects-relation)
  Prelude.[ rec (λ where
              .[]ʳ x                 → [ inj₁ x ]
              .[]-respects-relationʳ → []-respects-relation
              .is-setʳ               → /ᴱ-is-set)
          , rec (λ where
              .[]ʳ x                 → [ inj₂ x ]
              .[]-respects-relationʳ → []-respects-relation
              .is-setʳ               → /ᴱ-is-set)
          ]
  Prelude.[ elim-prop (λ where
              .[]ʳ _             → refl _
              .is-propositionʳ _ → ⊎-closure 0 /ᴱ-is-set /ᴱ-is-set)
          , elim-prop (λ where
              .[]ʳ _             → refl _
              .is-propositionʳ _ → ⊎-closure 0 /ᴱ-is-set /ᴱ-is-set)
          ]
  (elim-prop λ where
     .[]ʳ               → Prelude.[ (λ _ → refl _) , (λ _ → refl _) ]
     .is-propositionʳ _ → /ᴱ-is-set)

-- Maybe commutes with quotients.
--
-- Chapman, Uustalu and Veltri mention a similar result in
-- "Quotienting the Delay Monad by Weak Bisimilarity".

Maybe/ᴱ :
  {@0 R : A → A → Type r} →
  Maybe A /ᴱ Maybeᴾ R ≃ Maybe (A /ᴱ R)
Maybe/ᴱ {A = A} {R = R} =
  Maybe A /ᴱ Maybeᴾ R    ↝⟨ ⊎/ᴱ ⟩
  ⊤ /ᴱ Trivial ⊎ A /ᴱ R  ↔⟨ ⊤/ᴱ ⊎-cong F.id ⟩
  ⊤ ⊎ A /ᴱ R             ↔⟨⟩
  Maybe (A /ᴱ R)         □

-- A simplification lemma for Maybe/-comm.

Maybe/ᴱ-[] :
  {@0 R : A → A → Type r} →
  _≃_.to (Maybe/ᴱ {R = R}) ∘ [_] ≡ ⊎-map id ([_] {R = R})
Maybe/ᴱ-[] = ⟨ext⟩ λ x →
  _≃_.to Maybe/ᴱ [ x ]          ≡⟨⟩
  ⊎-map _ id (⊎-map [_] [_] x)  ≡⟨ sym $ ⊎-map-∘ x ⟩∎
  ⊎-map id [_] x                ∎

-- Cartesian products commute with quotients, assuming that the two
-- binary relations involved in the statement are reflexive.

×/ᴱ :
  {@0 R₁ : A₁ → A₁ → Type r₁} {@0 R₂ : A₂ → A₂ → Type r₂} →
  @0 (∀ {x} → R₁ x x) →
  @0 (∀ {x} → R₂ x x) →
  (A₁ × A₂) /ᴱ (R₁ ×ᴾ R₂) ≃ (A₁ /ᴱ R₁ × A₂ /ᴱ R₂)
×/ᴱ {R₁ = R₁} {R₂ = R₂} R₁-refl R₂-refl = Eq.↔→≃
  (rec λ where
     .is-setʳ → ×-closure 2 /ᴱ-is-set /ᴱ-is-set

     .[]ʳ → Σ-map [_] [_]

     .[]-respects-relationʳ {x = x₁ , x₂} {y = y₁ , y₂} →
       R₁ x₁ y₁ × R₂ x₂ y₂                    ↝⟨ Σ-map []-respects-relation
                                                       []-respects-relation ⟩
       [ x₁ ] ≡ [ y₁ ] × [ x₂ ] ≡ [ y₂ ]      ↝⟨ uncurry (cong₂ _,_) ⟩□
       ([ x₁ ] , [ x₂ ]) ≡ ([ y₁ ] , [ y₂ ])  □)
  (uncurry $ rec λ where
     .is-setʳ →
       Π-closure ext 2 λ _ →
       /ᴱ-is-set
     .[]ʳ x → (x ,_) /ᴱ-map λ y₁ y₂ →
       R₂ y₁ y₂           ↝⟨ R₁-refl ,_ ⟩□
       R₁ x x × R₂ y₁ y₂  □
     .[]-respects-relationʳ {x = x₁} {y = x₂} R₁x₁x₂ →
       ⟨ext⟩ $ elim-prop λ @0 where
         .is-propositionʳ _ →
           /ᴱ-is-set
         .[]ʳ y →
           [ (x₁ , y) ]  ≡⟨ []-respects-relation (R₁x₁x₂ , R₂-refl) ⟩∎
           [ (x₂ , y) ]  ∎)
  (uncurry $ elim-prop λ where
     .is-propositionʳ _ →
       Π-closure ext 1 λ _ →
       ×-closure 2 /ᴱ-is-set /ᴱ-is-set
     .[]ʳ _ → elim-prop λ where
       .is-propositionʳ _ →
         ×-closure 2 /ᴱ-is-set /ᴱ-is-set
       .[]ʳ _ →
         refl _)
  (elim-prop λ where
     .is-propositionʳ _ → /ᴱ-is-set
     .[]ʳ _             → refl _)

-- The sigma type former commutes (kind of) with quotients, assuming
-- that the second projections come from propositional types.

Σ/ᴱ :
  @0 (∀ {x} → Is-proposition (P x)) →
  Σ (A /ᴱ R) P ≃ Σ A (P ∘ [_]) /ᴱ (R on proj₁)
Σ/ᴱ {A = A} {R = R} {P = P} prop = Eq.↔→≃
  (uncurry $ elim λ where
     .is-setʳ _ →
       Π-closure ext 2 λ _ →
       /ᴱ-is-set

     .[]ʳ → curry [_]

     .[]-respects-relationʳ {x = x} {y = y} r → ⟨ext⟩ λ P[y] →
       subst (λ x → P x → Σ A (P ∘ [_]) /ᴱ (R on proj₁))
             ([]-respects-relation r)
             (curry [_] x) P[y]                               ≡⟨ subst-→-domain P {f = curry [_] x} ([]-respects-relation r) ⟩

       [ (x , subst P (sym $ []-respects-relation r) P[y]) ]  ≡⟨ []-respects-relation r ⟩∎

       [ (y , P[y]) ]                                         ∎)
  (rec λ where
     .is-setʳ → Σ-closure 2 /ᴱ-is-set (λ _ → mono₁ 1 prop)

     .[]ʳ → Σ-map [_] id

     .[]-respects-relationʳ {x = (x₁ , x₂)} {y = (y₁ , y₂)} →
       R x₁ y₁                        ↝⟨ []-respects-relation ⟩
       [ x₁ ] ≡ [ y₁ ]                ↔⟨ ignore-propositional-component prop ⟩
       ([ x₁ ] , x₂) ≡ ([ y₁ ] , y₂)  □)
  (elim-prop λ where
     .[]ʳ _             → refl _
     .is-propositionʳ _ → /ᴱ-is-set)
  (uncurry $ elim-prop λ where
     .[]ʳ _ _           → refl _
     .is-propositionʳ _ →
       Π-closure ext 1 λ _ →
       Σ-closure 2 /ᴱ-is-set (λ _ → mono₁ 1 prop))

-- Erased commutes with quotients if certain conditions hold.

Erased/ᴱ :
  {@0 A : Type a} {@0 R : A → A → Type r} →
  @0 Is-set A →
  @0 (∀ {x y} → R x y → x ≡ y) →
  Erased A /ᴱ Erasedᴾ R ≃ Erased (A /ᴱ R)
Erased/ᴱ {A = A} {R = R} set R→≡ = Eq.↔→≃
  (rec λ where
     .is-setʳ                       → Er.H-level-Erased 2 /ᴱ-is-set
     .[]ʳ                           → Er.map [_]
     .[]-respects-relationʳ [ Rxy ] →
       Er.[]-cong [ []-respects-relation Rxy ])
  (λ ([ x ]) → [ [ from′ x ] ])
  (λ ([ x ]) →
     Er.[]-cong
       [ flip (elim-prop {P = λ x → [ from′ x ] ≡ x}) x (λ @0 where
           .is-propositionʳ _ → /ᴱ-is-set
           .[]ʳ _             → refl _)
       ])
  (elim-prop λ where
     .is-propositionʳ _ → /ᴱ-is-set
     .[]ʳ _             → refl _)
  where
  @0 from′ : A /ᴱ R → A
  from′ = rec λ @0 where
    .is-setʳ               → set
    .[]ʳ                   → id
    .[]-respects-relationʳ → R→≡

-- List commutes with quotients in a certain sense, given a certain
-- assumption.

List/ᴱ :
  @0 (∀ {x} → R x x) →
  List A /ᴱ Listᴾ R ≃ List (A /ᴱ R)
List/ᴱ {A = A} {R = R} r = Eq.↔→≃ to from to-from from-to
  where
  @0 to-lemma :
    ∀ xs ys →
    Listᴾ R xs ys →
    _≡_ {A = List (A /ᴱ R)} (L.map [_] xs) (L.map [_] ys)
  to-lemma []       []       _        = []  ∎
  to-lemma (x ∷ xs) (y ∷ ys) (r , rs) =
    [ x ] ∷ L.map [_] xs  ≡⟨ cong₂ _∷_ ([]-respects-relation r) (to-lemma xs ys rs) ⟩∎
    [ y ] ∷ L.map [_] ys  ∎

  to : List A /ᴱ Listᴾ R → List (A /ᴱ R)
  to = rec λ where
    .[]ʳ xs                → L.map [_] xs
    .[]-respects-relationʳ → to-lemma _ _
    .is-setʳ               → L.H-level-List 0 /ᴱ-is-set

  cons : A /ᴱ R → List A /ᴱ Listᴾ R → List A /ᴱ Listᴾ R
  cons = /ᴱ-zip _∷_ r (Listᴾ-preserves-reflexivity r) _,_

  from : List (A /ᴱ R) → List A /ᴱ Listᴾ R
  from []       = [ [] ]
  from (x ∷ xs) = cons x (from xs)

  to-cons-[] : ∀ x xs → to (cons [ x ] xs) ≡ [ x ] ∷ to xs
  to-cons-[] x = elim-prop λ where
    .is-propositionʳ _ →
      L.H-level-List 0 /ᴱ-is-set
    .[]ʳ _ → refl _

  to-from : (xs : List (A /ᴱ R)) → to (from xs) ≡ xs
  to-from []       = refl _
  to-from (x ∷ xs) =
    flip (elim-prop {P = λ x → to (from (x ∷ xs)) ≡ x ∷ xs}) x λ where
      .is-propositionʳ _ →
        L.H-level-List 0 /ᴱ-is-set
      .[]ʳ x →
        to (cons [ x ] (from xs))  ≡⟨ to-cons-[] _ (from xs) ⟩
        [ x ] ∷ to (from xs)       ≡⟨ cong (_ ∷_) $ to-from xs ⟩∎
        [ x ] ∷ xs                 ∎

  from-map-[] : ∀ xs → from (L.map [_] xs) ≡ [ xs ]
  from-map-[] []       = refl _
  from-map-[] (x ∷ xs) =
    cons [ x ] (from (L.map [_] xs))  ≡⟨ cong (cons [ x ]) $ from-map-[] xs ⟩
    cons [ x ] [ xs ]                 ≡⟨⟩
    [ x ∷ xs ]                        ∎

  from-to : (xs : List A /ᴱ Listᴾ R) → from (to xs) ≡ xs
  from-to = elim-prop λ where
    .is-propositionʳ _ → /ᴱ-is-set
    .[]ʳ               → from-map-[]
