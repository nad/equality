------------------------------------------------------------------------
-- A variant of the set quotients from Quotient
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly following the HoTT book.
--
-- Unlike the HoTT book, but following the cubical library (in which
-- set quotients were implemented by Zesen Qian and Anders Mörtberg),
-- the quotienting relations are not always required to be
-- propositional. Furthermore, unlike the code in the cubical library,
-- the higher constructors take arguments stating that the quotienting
-- relation is propositional.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining quotients use path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Quotient.Higher-constructors-if-propositional
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

private
  open module D = P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence-relation equality-with-J
open import Function-universe equality-with-J as F hiding (_∘_; id)
open import H-level equality-with-J as H
import H-level P.equality-with-J as PH
open import H-level.Closure equality-with-J
import H-level.Truncation.Church equality-with-J as Trunc
open import H-level.Truncation.Propositional eq as TruncP
  using (∥_∥; ∣_∣; Surjective; Axiom-of-countable-choice)
open import Preimage equality-with-J using (_⁻¹_)
import Quotient eq as Quotient
import Quotient.Families-of-equivalence-classes equality-with-J as QF
open import Sum equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

private
  variable
    a a₁ a₂ b p          : Level
    k                    : Isomorphism-kind
    A A₁ A₂ B            : Set a
    P                    : A → Set p
    e f prop r r₁ r₂ x y : A
    R R₁ R₂              : A → A → Set r

------------------------------------------------------------------------
-- Quotients

-- The quotient type constructor.

infix 5 _/_

data _/_ (A : Set a) (R : A → A → Set r) : Set (a ⊔ r) where
  [_]                   : A → A / R
  []-respects-relationᴾ : (∀ x y → Is-proposition (R x y)) →
                          R x y → [ x ] P.≡ [ y ]
  /-is-setᴾ             : (∀ x y → Is-proposition (R x y)) →
                          P.Is-set (A / R)

-- [_] respects the quotient relation if the relation is pointwise
-- propositional.

[]-respects-relation :
  (∀ x y → Is-proposition (R x y)) →
  R x y → _≡_ {A = A / R} [ x ] [ y ]
[]-respects-relation prop = _↔_.from ≡↔≡ ∘ []-respects-relationᴾ prop

-- If R is pointwise propositional, then A / R is a set.

/-is-set : (∀ x y → Is-proposition (R x y)) → Is-set (A / R)
/-is-set = _↔_.from (H-level↔H-level 2) ∘ /-is-setᴾ

------------------------------------------------------------------------
-- Eliminators

-- An eliminator, expressed using paths.

record Elimᴾ′ {A : Set a} {R : A → A → Set r} (P : A / R → Set p) :
              Set (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    []-respects-relationʳ :
      (prop : ∀ x y → Is-proposition (R x y)) →
      (r : R x y) →
      P.[ (λ i → P ([]-respects-relationᴾ prop r i)) ] []ʳ x ≡ []ʳ y

    is-setʳ :
      (prop : ∀ x y → Is-proposition (R x y))
      {eq₁ eq₂ : x P.≡ y} {p : P x} {q : P y}
      (eq₃ : P.[ (λ i → P (eq₁ i)) ] p ≡ q)
      (eq₄ : P.[ (λ i → P (eq₂ i)) ] p ≡ q) →
      P.[ (λ i → P.[ (λ j → P (/-is-setᴾ prop eq₁ eq₂ i j)) ] p ≡ q) ]
        eq₃ ≡ eq₄

open Elimᴾ′ public

elimᴾ′ : Elimᴾ′ P → (x : A / R) → P x
elimᴾ′ {A = A} {R = R} {P = P} e = helper
  where
  module E = Elimᴾ′ e

  helper : (x : A / R) → P x
  helper [ x ] = E.[]ʳ x

  helper ([]-respects-relationᴾ prop r i) =
    E.[]-respects-relationʳ prop r i

  helper (/-is-setᴾ prop p q i j)         =
    E.is-setʳ prop (λ i → helper (p i)) (λ i → helper (q i)) i j

-- A possibly more useful eliminator, expressed using paths.

record Elimᴾ {A : Set a} {R : A → A → Set r} (P : A / R → Set p) :
             Set (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    []-respects-relationʳ :
      (prop : ∀ x y → Is-proposition (R x y)) →
      (r : R x y) →
      P.[ (λ i → P ([]-respects-relationᴾ prop r i)) ] []ʳ x ≡ []ʳ y

    is-setʳ :
      (∀ x y → Is-proposition (R x y)) →
      ∀ x → P.Is-set (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : A / R) → P x
elimᴾ e = elimᴾ′ λ where
    .[]ʳ                   → E.[]ʳ
    .[]-respects-relationʳ → E.[]-respects-relationʳ
    .is-setʳ prop          → P.heterogeneous-UIP (E.is-setʳ prop) _
  where
  module E = Elimᴾ e

private

  -- One can define elimᴾ′ using elimᴾ.

  elimᴾ′₂ : Elimᴾ′ P → (x : A / R) → P x
  elimᴾ′₂ {P = P} e = elimᴾ λ where
      .[]ʳ                        → E.[]ʳ
      .[]-respects-relationʳ      → E.[]-respects-relationʳ
      .is-setʳ prop x {y} {z} p q →                                $⟨ E.is-setʳ prop p q ⟩
        P.[ (λ i →
               P.[ (λ j → P (/-is-setᴾ prop P.refl P.refl i j)) ]
                 y ≡ z) ]
          p ≡ q                                                    ↝⟨ P.subst (λ eq → P.[ (λ i → P.[ (λ j → P (eq i j)) ] y ≡ z) ] p ≡ q)
                                                                              (PH.mono₁ 2 (/-is-setᴾ prop) _ _) ⟩
        P.[ (λ _ → P.[ (λ _ → P x) ] y ≡ z) ] p ≡ q                ↔⟨⟩

        p P.≡ q                                                    □
    where
    module E = Elimᴾ′ e

-- A non-dependent eliminator, expressed using paths.

record Recᴾ {A : Set a} (R : A → A → Set r) (B : Set b) :
            Set (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ                   : A → B
    []-respects-relationʳ : (∀ x y → Is-proposition (R x y)) →
                            (r : R x y) → []ʳ x P.≡ []ʳ y
    is-setʳ               : (∀ x y → Is-proposition (R x y)) →
                            P.Is-set B

open Recᴾ public

recᴾ : Recᴾ R B → A / R → B
recᴾ r = elimᴾ λ where
    .[]ʳ                   → R.[]ʳ
    .[]-respects-relationʳ → R.[]-respects-relationʳ
    .is-setʳ prop _        → R.is-setʳ prop
  where
  module R = Recᴾ r

-- An eliminator.

record Elim {A : Set a} {R : A → A → Set r} (P : A / R → Set p) :
            Set (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ : ∀ x → P [ x ]

    []-respects-relationʳ :
      (prop : ∀ x y → Is-proposition (R x y)) →
      (r : R x y) →
      subst P ([]-respects-relation prop r) ([]ʳ x) ≡ []ʳ y

    is-setʳ : (∀ x y → Is-proposition (R x y)) → ∀ x → Is-set (P x)

open Elim public

elim : Elim P → (x : A / R) → P x
elim {P = P} e = elimᴾ λ where
    .[]ʳ → E.[]ʳ

    .[]-respects-relationʳ prop r →
      subst≡→[]≡ (E.[]-respects-relationʳ prop r)

    .is-setʳ prop → _↔_.to (H-level↔H-level 2) ∘ E.is-setʳ prop
  where
  module E = Elim e

-- A computation rule.

elim-[]-respects-relation :
  dcong (elim e) ([]-respects-relation prop r) ≡
  e .[]-respects-relationʳ prop r
elim-[]-respects-relation {e = e} {prop = prop} =
  e .is-setʳ prop _ _ _

-- A non-dependent eliminator.

record Rec {A : Set a} (R : A → A → Set r) (B : Set b) :
           Set (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ                   : A → B
    []-respects-relationʳ : (∀ x y → Is-proposition (R x y)) →
                            (r : R x y) → []ʳ x ≡ []ʳ y
    is-setʳ               : (∀ x y → Is-proposition (R x y)) →
                            Is-set B

open Rec public

rec : Rec R B → A / R → B
rec r = recᴾ λ where
    .[]ʳ → R.[]ʳ

    .[]-respects-relationʳ prop →
      _↔_.to ≡↔≡ ∘ R.[]-respects-relationʳ prop

    .is-setʳ → _↔_.to (H-level↔H-level 2) ∘ R.is-setʳ
  where
  module R = Rec r

-- A computation rule.

rec-[]-respects-relation :
  cong (rec {R = R} {B = B} r₁)
       ([]-respects-relation {x = x} {y = y} prop r₂) ≡
  r₁ .[]-respects-relationʳ prop r₂
rec-[]-respects-relation {r₁ = r₁} {prop = prop} =
  r₁ .is-setʳ prop _ _

-- A variant of elim that can be used if the motive composed with [_]
-- is a family of propositions (assuming that the quotienting relation
-- is a family of propositions).
--
-- I took the idea for this eliminator from Nicolai Kraus.

record Elim-prop
         {A : Set a} {R : A → A → Set r} (P : A / R → Set p) :
         Set (a ⊔ r ⊔ p) where
  no-eta-equality
  field
    []ʳ             : ∀ x → P [ x ]
    is-propositionʳ : (∀ x y → Is-proposition (R x y)) →
                      ∀ x → Is-proposition (P [ x ])

open Elim-prop public

elim-prop : Elim-prop P → (x : A / R) → P x
elim-prop e = elim λ where
    .[]ʳ                          → E.[]ʳ
    .[]-respects-relationʳ prop _ → E.is-propositionʳ prop _ _ _
    .is-setʳ prop                 → elim λ where
      .[]ʳ                       → mono₁ 1 ∘ E.is-propositionʳ prop
      .[]-respects-relationʳ _ _ → H-level-propositional ext 2 _ _
      .is-setʳ _ _               → mono₁ 1 (H-level-propositional ext 2)
  where
  module E = Elim-prop e

-- A variant of rec that can be used if the motive is a proposition
-- (assuming that the quotienting relation is a family of
-- propositions).

record Rec-prop {A : Set a} (R : A → A → Set r) (B : Set b) :
                Set (a ⊔ r ⊔ b) where
  no-eta-equality
  field
    []ʳ             : A → B
    is-propositionʳ : (∀ x y → Is-proposition (R x y)) →
                      Is-proposition B

open Rec-prop public

rec-prop : Rec-prop R B → A / R → B
rec-prop r = elim-prop λ where
    .[]ʳ                    → R.[]ʳ
    .is-propositionʳ prop _ → R.is-propositionʳ prop
  where
  module R = Rec-prop r

------------------------------------------------------------------------
-- Some properties

-- [_] is surjective.

[]-surjective : Surjective ([_] {R = R})
[]-surjective = elim-prop λ where
  .[]ʳ x               → ∣ x , refl _ ∣
  .is-propositionʳ _ _ → TruncP.truncation-is-proposition

-- If the relation is a propositional equivalence relation, then it is
-- equivalent to equality under [_].
--
-- The basic structure of this proof is that of Proposition 2 in
-- "Quotienting the Delay Monad by Weak Bisimilarity" by Chapman,
-- Uustalu and Veltri.

related≃[equal] :
  {R : A → A → Set r} →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  ∀ {x y} → R x y ≃ _≡_ {A = A / R} [ x ] [ y ]
related≃[equal] {A = A} {r = r} {R = R}
                R-equiv R-prop {x} {y} =
  _↠_.from (Eq.≃↠⇔ R-prop (/-is-set λ _ _ → R-prop))
    (record
       { to   = []-respects-relation λ _ _ → R-prop
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
    .[]ʳ y                   → R x y , R-prop
    .[]-respects-relationʳ _ → lemma
    .is-setʳ _               → Is-set-∃-Is-proposition ext prop-ext

-- Quotienting with equality amounts to the same thing as not
-- quotienting at all.

/≡↔ : A / _≡_ ↔ A
/≡↔ = record
  { surjection = record
    { logical-equivalence = record
      { from = [_]
      ; to   = rec λ where
          .[]ʳ                     → id
          .[]-respects-relationʳ _ → id
          .is-setʳ prop            → prop _ _
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = elim λ where
      .[]ʳ _ → refl _

      .is-setʳ prop _ → mono₁ 2 (/-is-set prop)

      .[]-respects-relationʳ prop _ →
        /-is-set prop _ _
  }

-- Quotienting with a trivial, pointwise propositional relation
-- amounts to the same thing as using the propositional truncation
-- operator.

/trivial↔∥∥ :
  (∀ x y → R x y) →
  (∀ {x y} → Is-proposition (R x y)) →
  A / R ↔ ∥ A ∥
/trivial↔∥∥ {A = A} {R = R} trivial prop = record
  { surjection = record
    { logical-equivalence = record
      { from = TruncP.rec /-prop [_]
      ; to   = rec-prop λ where
          .[]ʳ               → ∣_∣
          .is-propositionʳ _ → TruncP.truncation-is-proposition
      }
    ; right-inverse-of = TruncP.elim
        _
        (λ _ → ⇒≡ 1 TruncP.truncation-is-proposition)
        (λ _ → refl _)
    }
  ; left-inverse-of = elim-prop λ where
      .[]ʳ _                  → refl _
      .is-propositionʳ prop _ → /-is-set prop
  }
  where
  /-prop : Is-proposition (A / R)
  /-prop = elim-prop λ where
    .[]ʳ x → elim-prop λ where
      .[]ʳ y → []-respects-relation (λ _ _ → prop) (trivial x y)

      .is-propositionʳ prop _ → /-is-set prop

    .is-propositionʳ prop _ →
      Π-closure ext 1 λ _ →
      /-is-set prop

-- The previous property gives us an alternative to
-- constant-function≃∥inhabited∥⇒inhabited.

constant-function↔∥inhabited∥⇒inhabited :
  Is-set B →
  (∃ λ (f : A → B) → Constant f) ↔ (∥ A ∥ → B)
constant-function↔∥inhabited∥⇒inhabited {B = B} {A = A} B-set =
  (∃ λ (f : A → B) → Constant f)  ↝⟨ record
                                       { surjection = record
                                         { logical-equivalence = record
                                           { to   = λ { (f , c) → rec λ where
                                                        .[]ʳ                       → f
                                                        .[]-respects-relationʳ _ _ → c _ _
                                                        .is-setʳ _                 → B-set }
                                           ; from = λ f → (f ∘ [_])
                                                        , (λ _ _ → cong f
                                                                     ([]-respects-relation
                                                                        (λ _ _ → mono₁ 0 ⊤-contractible)
                                                                        _))
                                           }
                                         ; right-inverse-of = λ f → ⟨ext⟩ $ elim λ where
                                             .[]ʳ _                     → refl _
                                             .[]-respects-relationʳ _ _ → B-set _ _
                                             .is-setʳ _ _               → mono₁ 2 B-set
                                         }
                                       ; left-inverse-of = λ _ → Σ-≡,≡→≡
                                           (refl _)
                                           ((Π-closure ext 1 λ _ →
                                             Π-closure ext 1 λ _ →
                                             B-set) _ _)
                                       } ⟩
  (A / (λ _ _ → ⊤) → B)           ↝⟨ →-cong₁ ext (/trivial↔∥∥ _ (mono₁ 0 ⊤-contractible)) ⟩□
  (∥ A ∥ → B)                     □

-- The two directions of the proposition above compute in the
-- "right" way. Note that (at the time of writing) an analogue of
-- the second property below fails to hold definitionally for
-- constant-function≃∥inhabited∥⇒inhabited.

_ :
  {B-set : Is-set B} →
  _↔_.to (constant-function↔∥inhabited∥⇒inhabited B-set) f ∣ x ∣ ≡
  proj₁ f x
_ = refl _

_ :
  {B-set : Is-set B} →
  proj₁ (_↔_.from (constant-function↔∥inhabited∥⇒inhabited B-set) f)
        x ≡
  f ∣ x ∣
_ = refl _

------------------------------------------------------------------------
-- Preservation lemmas

-- Two preservation lemmas for functions.

/-map-∥∥ :
  ((∀ x y → Is-proposition (R₁ x y)) →
   (∀ x y → Is-proposition (R₂ x y))) →
  (A₁→A₂ : A₁ → A₂) →
  (∀ x y → ∥ R₁ x y ∥ → ∥ R₂ (A₁→A₂ x) (A₁→A₂ y) ∥) →
  A₁ / R₁ → A₂ / R₂
/-map-∥∥ {R₁ = R₁} {R₂ = R₂} p A₁→A₂ R₁→R₂ = rec λ where
  .[]ʳ → [_] ∘ A₁→A₂

  .is-setʳ → /-is-set ∘ p

  .[]-respects-relationʳ {x = x} {y = y} prop →
     R₁ x y                      ↝⟨ ∣_∣ ⟩
     ∥ R₁ x y ∥                  ↝⟨ R₁→R₂ _ _ ⟩
     ∥ R₂ (A₁→A₂ x) (A₁→A₂ y) ∥  ↝⟨ TruncP.rec (/-is-set (p prop)) ([]-respects-relation (p prop)) ⟩□
     [ A₁→A₂ x ] ≡ [ A₁→A₂ y ]   □

/-map :
  ((∀ x y → Is-proposition (R₁ x y)) →
   (∀ x y → Is-proposition (R₂ x y))) →
  (A₁→A₂ : A₁ → A₂) →
  (∀ x y → R₁ x y → R₂ (A₁→A₂ x) (A₁→A₂ y)) →
  A₁ / R₁ → A₂ / R₂
/-map p A₁→A₂ R₁→R₂ =
  /-map-∥∥ p A₁→A₂ (λ x y → TruncP.∥∥-map (R₁→R₂ x y))

-- Two preservation lemmas for logical equivalences.

/-cong-∥∥-⇔ :
  ((∀ x y → Is-proposition (R₁ x y)) ⇔
   (∀ x y → Is-proposition (R₂ x y))) →
  (A₁⇔A₂ : A₁ ⇔ A₂) →
  (∀ x y → ∥ R₁ x y ∥ → ∥ R₂ (_⇔_.to   A₁⇔A₂ x) (_⇔_.to   A₁⇔A₂ y) ∥) →
  (∀ x y → ∥ R₂ x y ∥ → ∥ R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y) ∥) →
  A₁ / R₁ ⇔ A₂ / R₂
/-cong-∥∥-⇔ prop A₁⇔A₂ R₁→R₂ R₂→R₁ = record
  { to   = /-map-∥∥ (_⇔_.to   prop) (_⇔_.to   A₁⇔A₂) R₁→R₂
  ; from = /-map-∥∥ (_⇔_.from prop) (_⇔_.from A₁⇔A₂) R₂→R₁
  }

/-cong-⇔ :
  ((∀ x y → Is-proposition (R₁ x y)) ⇔
   (∀ x y → Is-proposition (R₂ x y))) →
  (A₁⇔A₂ : A₁ ⇔ A₂) →
  (∀ x y → R₁ x y → R₂ (_⇔_.to   A₁⇔A₂ x) (_⇔_.to   A₁⇔A₂ y)) →
  (∀ x y → R₂ x y → R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y)) →
  A₁ / R₁ ⇔ A₂ / R₂
/-cong-⇔ prop A₁⇔A₂ R₁→R₂ R₂→R₁ =
  /-cong-∥∥-⇔
    prop
    A₁⇔A₂
    (λ x y → TruncP.∥∥-map (R₁→R₂ x y))
    (λ x y → TruncP.∥∥-map (R₂→R₁ x y))

-- Two preservation lemmas for split surjections.

/-cong-∥∥-↠ :
  ((∀ x y → Is-proposition (R₁ x y)) ⇔
   (∀ x y → Is-proposition (R₂ x y))) →
  (A₁↠A₂ : A₁ ↠ A₂) →
  (∀ x y → ∥ R₁ x y ∥ ⇔ ∥ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y) ∥) →
  A₁ / R₁ ↠ A₂ / R₂
/-cong-∥∥-↠ {R₁ = R₁} {R₂ = R₂} prop A₁↠A₂ R₁⇔R₂ = record
  { logical-equivalence = /-cong-∥∥-⇔
      prop
      (_↠_.logical-equivalence A₁↠A₂)
      (λ x y → _⇔_.to (R₁⇔R₂ x y))
      (λ x y → ∥ R₂ x y                         ∥  ↝⟨ ≡⇒↝ _ (sym $ cong₂ (λ x y → ∥ R₂ x y ∥) (right-inverse-of x) (right-inverse-of y)) ⟩
               ∥ R₂ (to (from x)) (to (from y)) ∥  ↝⟨ _⇔_.from (R₁⇔R₂ _ _) ⟩□
               ∥ R₁ (from x) (from y)           ∥  □)
  ; right-inverse-of = elim λ where
      .[]ʳ x →
        [ to (from x) ]  ≡⟨ cong [_] $ right-inverse-of x ⟩∎
        [ x ]            ∎

      .[]-respects-relationʳ prop _ → /-is-set prop _ _

      .is-setʳ prop _ → mono₁ 1 (/-is-set prop)
  }
  where
  open _↠_ A₁↠A₂

/-cong-↠ :
  ((∀ x y → Is-proposition (R₁ x y)) ⇔
   (∀ x y → Is-proposition (R₂ x y))) →
  (A₁↠A₂ : A₁ ↠ A₂) →
  (∀ x y → R₁ x y ⇔ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y)) →
  A₁ / R₁ ↠ A₂ / R₂
/-cong-↠ prop A₁↠A₂ R₁⇔R₂ =
  /-cong-∥∥-↠
    prop
    A₁↠A₂
    (λ x y → TruncP.∥∥-cong-⇔ (R₁⇔R₂ x y))

private

  -- A preservation lemma for equivalences.

  /-cong-∥∥-≃ :
    ((∀ x y → Is-proposition (R₁ x y)) ⇔
     (∀ x y → Is-proposition (R₂ x y))) →
    (A₁≃A₂ : A₁ ≃ A₂) →
    (∀ x y →
       ∥ R₁ x y ∥ ⇔
       ∥ R₂ (to-implication A₁≃A₂ x) (to-implication A₁≃A₂ y) ∥) →
    A₁ / R₁ ≃ A₂ / R₂
  /-cong-∥∥-≃ {R₁ = R₁} {R₂ = R₂} prop A₁≃A₂ R₁⇔R₂ = Eq.↔⇒≃ (record
    { surjection = /-cong-∥∥-↠
        prop
        (_≃_.surjection A₁≃A₂)
        (λ x y →
           ∥ R₁ x y           ∥  ↝⟨ R₁⇔R₂ x y ⟩□
           ∥ R₂ (to x) (to y) ∥  □)
    ; left-inverse-of = elim λ where
        .[]ʳ x →
          [ from (to x) ]  ≡⟨ cong [_] $ left-inverse-of x ⟩∎
          [ x ]            ∎

        .[]-respects-relationʳ prop _ → /-is-set prop _ _

        .is-setʳ prop _ → mono₁ 1 (/-is-set prop)
    })
    where
    open _≃_ A₁≃A₂

-- Two preservation lemmas for isomorphisms.

/-cong-∥∥-↔ :
  {A₁ : Set a₁} {R₁ : A₁ → A₁ → Set r₁}
  {A₂ : Set a₂} {R₂ : A₂ → A₂ → Set r₂} →
  ((∀ x y → Is-proposition (R₁ x y)) ⇔
   (∀ x y → Is-proposition (R₂ x y))) →
  (A₁↔A₂ : A₁ ↔[ k ] A₂) →
  (∀ x y →
     ∥ R₁ x y ∥ ⇔
     ∥ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y) ∥) →
  A₁ / R₁ ↔[ k ] A₂ / R₂
/-cong-∥∥-↔ {k = k} {R₁ = R₁} {R₂ = R₂} prop A₁↔A₂ R₁⇔R₂ =
  from-isomorphism $
  /-cong-∥∥-≃
    prop
    A₁≃A₂
    (λ x y →
       ∥ R₁ x y ∥                                                ↝⟨ R₁⇔R₂ x y ⟩
       ∥ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y) ∥  ↝⟨ ≡⇒↝ _ $ cong₂ (λ f g → ∥ R₂ (f x) (g y) ∥)
                                                                              (to-implication∘from-isomorphism k equivalence)
                                                                              (to-implication∘from-isomorphism k equivalence) ⟩□
       ∥ R₂ (_≃_.to A₁≃A₂ x) (_≃_.to A₁≃A₂ y) ∥                  □)
  where
  A₁≃A₂ = from-isomorphism A₁↔A₂

/-cong-↔ :
  {A₁ : Set a₁} {R₁ : A₁ → A₁ → Set r₁}
  {A₂ : Set a₂} {R₂ : A₂ → A₂ → Set r₂} →
  ((∀ x y → Is-proposition (R₁ x y)) ⇔
   (∀ x y → Is-proposition (R₂ x y))) →
  (A₁↔A₂ : A₁ ↔[ k ] A₂) →
  (∀ x y →
     R₁ x y ⇔ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y)) →
  A₁ / R₁ ↔[ k ] A₂ / R₂
/-cong-↔ prop A₁↔A₂ R₁⇔R₂ =
  /-cong-∥∥-↔
    prop
    A₁↔A₂
    (λ x y → TruncP.∥∥-cong-⇔ (R₁⇔R₂ x y))

------------------------------------------------------------------------
-- The quotients defined here can be related to the ones defined in
-- Quotient

-- If the quotient relation is propositional, then the definition of
-- quotients given in Quotient is equivalent to the one given here.

/≃/ :
  (∀ {x y} → Is-proposition (R x y)) →
  A / R ≃ A Quotient./ R
/≃/ R-prop = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to = rec (λ where
          .[]ʳ → Quotient.[_]

          .[]-respects-relationʳ _ → Quotient.[]-respects-relation

          .is-setʳ _ → Quotient./-is-set)
      ; from = Quotient.rec λ where
          .Quotient.Rec.[]ʳ → [_]

          .Quotient.Rec.[]-respects-relationʳ →
            []-respects-relation λ _ _ → R-prop

          .Quotient.Rec.is-setʳ → /-is-set λ _ _ → R-prop
      }
    ; right-inverse-of = Quotient.elim-prop λ where
        .Quotient.Elim-prop.[]ʳ _ → refl _

        .Quotient.Elim-prop.is-propositionʳ _ → Quotient./-is-set
    }
  ; left-inverse-of = elim-prop λ where
        .Elim-prop.[]ʳ _ → refl _

        .Elim-prop.is-propositionʳ prop _ → /-is-set prop
  })

------------------------------------------------------------------------
-- The quotients defined here can be related to the ones defined in
-- QF.Families-of-equivalence-classes

private

  -- An alternative definition of the quotients from
  -- QF.Families-of-equivalence-classes.

  infix 5 _/′_

  _/′_ : (A : Set a) → (A → A → Set a) → Set (lsuc a)
  _/′_ {a = a} A R = ∃ λ (P : A → Set a) → ∥ (∃ λ x → R x ≡ P) ∥

  /↔/′ : A QF./ R ↔ A /′ R
  /↔/′ {A = A} {R = R} =
    A QF./ R                                                 ↔⟨⟩
    (∃ λ (P : A → Set _) → Trunc.∥ (∃ λ x → R x ≡ P) ∥ 1 _)  ↝⟨ (∃-cong λ _ → inverse $ TruncP.∥∥↔∥∥ lzero) ⟩
    (∃ λ (P : A → Set _) → ∥ (∃ λ x → R x ≡ P) ∥)            ↔⟨⟩
    A /′ R                                                   □

  [_]′ : A → A /′ R
  [_]′ = _↔_.to /↔/′ ∘ QF.[_]

  rec′ :
    {A : Set a} {R : A → A → Set a} →
    (∀ {x} → R x x) →
    (B : Set a) →
    Is-set B →
    (f : A → B) →
    (∀ {x y} → R x y → f x ≡ f y) →
    A /′ R → B
  rec′ refl B B-set f R⇒≡ =
    QF.rec ext refl B B-set f R⇒≡ ∘
    _↔_.from /↔/′

  elim-Prop′ :
    {A : Set a} {R : A → A → Set a} →
    QF.Strong-equivalence-with surjection R →
    (B : A /′ R → Set (lsuc a)) →
    (∀ x → Is-proposition (B [ x ]′)) →
    (f : ∀ x → B [ x ]′) →
    ∀ x → B x
  elim-Prop′ strong-equivalence B B-prop f x =
    subst B (_↔_.right-inverse-of /↔/′ _) $
      QF.elim-Prop
        ext
        strong-equivalence
        (B ∘ _↔_.to /↔/′)
        B-prop
        f
        (_↔_.from /↔/′ x)

-- If the relation is a propositional equivalence relation of a
-- certain size, then the quotients defined above are isomorphic to
-- families of equivalence relations, defined in a certain way.

/↔ :
  {A : Set a} {R : A → A → Set a} →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  A / R ↔ ∃ λ (P : A → Set a) → ∥ (∃ λ x → R x ≡ P) ∥
/↔ {a = a} {A = A} {R} R-equiv R-prop = record
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
  R-is-strong-equivalence : QF.Strong-equivalence R
  R-is-strong-equivalence =
    QF.propositional-equivalence⇒strong-equivalence
      ext univ R-equiv (λ _ _ → R-prop)

  to : A / R → A /′ R
  to = rec λ where
    .[]ʳ → [_]′

    .[]-respects-relationʳ {x = x} {y = y} _ →
      R x y                ↝⟨ _≃_.to (QF.related↝[equal] ext R-is-strong-equivalence) ⟩
      QF.[ x ] ≡ QF.[ y ]  ↝⟨ cong (_↔_.to /↔/′) ⟩□
      [ x ]′ ≡ [ y ]′      □

    .is-setʳ prop →      $⟨ (λ {_ _} → QF.quotient's-h-level-is-1-+-relation's-h-level
                                         ext univ univ 1 (λ _ _ → R-prop)) ⟩
      Is-set (A QF./ R)  ↝⟨ H.respects-surjection (_↔_.surjection /↔/′) 2 ⟩□
      Is-set (A /′ R)    □

  from : A /′ R → A / R
  from = rec′
    (Is-equivalence-relation.reflexive R-equiv)
    _
    (/-is-set λ _ _ → R-prop)
    [_]
    ([]-respects-relation λ _ _ → R-prop)

  to∘from : ∀ x → to (from x) ≡ x
  to∘from = elim-Prop′
    (QF.strong-equivalence⇒strong-equivalence-with
       R-is-strong-equivalence)
    _
    (λ x →                                         $⟨ (λ {_ _} → QF.quotient's-h-level-is-1-+-relation's-h-level
                                                                   ext univ univ 1 λ _ _ → R-prop) ⟩
       Is-set (A QF./ R)                           ↝⟨ H.respects-surjection (_↔_.surjection /↔/′) 2 ⟩
       Is-set (A /′ R)                             ↝⟨ +⇒≡ {n = 1} ⟩□
       Is-proposition (to (from [ x ]′) ≡ [ x ]′)  □)
    (λ _ → refl _)

  from∘to : ∀ x → from (to x) ≡ x
  from∘to = elim-prop λ where
    .[]ʳ _                  → refl _
    .is-propositionʳ prop _ → /-is-set prop

-- If the relation is a propositional equivalence relation of a
-- certain size, then the definition of quotients given in
-- QF.Families-of-equivalence-classes is isomorphic to the one given
-- here.

/↔/ : {A : Set a} {R : A → A → Set a} →
      Is-equivalence-relation R →
      (R-prop : ∀ {x y} → Is-proposition (R x y)) →
      A QF./ R ↔ A / R
/↔/ {a = a} {A = A} {R} R-equiv R-prop =
  A QF./ R                                                        ↔⟨⟩
  (∃ λ (P : A → Set a) → Trunc.∥ (∃ λ x → R x ≡ P) ∥ 1 (lsuc a))  ↝⟨ (∃-cong λ _ → inverse $ TruncP.∥∥↔∥∥ lzero) ⟩
  (∃ λ (P : A → Set a) →       ∥ (∃ λ x → R x ≡ P) ∥)             ↝⟨ inverse $ /↔ R-equiv R-prop ⟩□
  A / R                                                           □

------------------------------------------------------------------------
-- Various type formers commute with quotients

-- _⊎_ commutes with quotients if the relations are pointwise
-- propositional.

⊎/-comm :
  (∀ {x y} → Is-proposition (R₁ x y)) →
  (∀ {x y} → Is-proposition (R₂ x y)) →
  (A₁ ⊎ A₂) / (R₁ ⊎ᴾ R₂) ↔ A₁ / R₁ ⊎ A₂ / R₂
⊎/-comm R₁-prop R₂-prop = record
  { surjection = record
    { logical-equivalence = record
      { to = rec λ where
          .[]ʳ       → ⊎-map [_] [_]
          .is-setʳ _ → ⊎-closure 0 is-set₁ is-set₂

          .[]-respects-relationʳ {x = inj₁ _} {y = inj₁ _} _ →
            cong inj₁ ∘ []-respects-relation λ _ _ → R₁-prop
          .[]-respects-relationʳ {x = inj₂ _} {y = inj₂ _} _ →
            cong inj₂ ∘ []-respects-relation λ _ _ → R₂-prop

      ; from =
          Prelude.[
            rec (λ where
              .[]ʳ                     → [_] ∘ inj₁
              .[]-respects-relationʳ _ → []-respects-relation R₁₂-prop
              .is-setʳ _               → is-set₁₂)
          , rec (λ where
              .[]ʳ                     → [_] ∘ inj₂
              .[]-respects-relationʳ _ → []-respects-relation R₁₂-prop
              .is-setʳ _               → is-set₁₂)
          ]
      }
    ; right-inverse-of =
        Prelude.[ elim-prop (λ where
                    .[]ʳ _               → refl _
                    .is-propositionʳ _ _ → ⊎-closure 0 is-set₁ is-set₂)
                , elim-prop (λ where
                    .[]ʳ _               → refl _
                    .is-propositionʳ _ _ → ⊎-closure 0 is-set₁ is-set₂)
                ]
    }
  ; left-inverse-of = elim-prop λ where
      .[]ʳ                 → Prelude.[ (λ _ → refl _) , (λ _ → refl _) ]
      .is-propositionʳ _ _ → is-set₁₂
  }
  where
  R₁₂-prop = λ x y → ⊎ᴾ-preserves-Is-proposition
                       R₁-prop R₂-prop {x = x} {y = y}
  is-set₁  = /-is-set λ _ _ → R₁-prop
  is-set₂  = /-is-set λ _ _ → R₂-prop
  is-set₁₂ = /-is-set R₁₂-prop

-- Maybe commutes with quotients if the relation is pointwise
-- propositional.
--
-- Chapman, Uustalu and Veltri mention a similar result in
-- "Quotienting the Delay Monad by Weak Bisimilarity".

Maybe/-comm :
  (∀ {x y} → Is-proposition (R x y)) →
  Maybe A / Maybeᴾ R ↔ Maybe (A / R)
Maybe/-comm {A = A} {R = R} R-prop =
  Maybe A / Maybeᴾ R   ↝⟨ ⊎/-comm (↑-closure 1 (mono₁ 0 ⊤-contractible)) R-prop ⟩
  ⊤ / Trivial ⊎ A / R  ↝⟨ /trivial↔∥∥ _ (↑-closure 1 (mono₁ 0 ⊤-contractible)) ⊎-cong F.id ⟩
  ∥ ⊤ ∥ ⊎ A / R        ↝⟨ TruncP.∥∥↔ (mono₁ 0 ⊤-contractible) ⊎-cong F.id ⟩□
  Maybe (A / R)        □

-- A simplification lemma for Maybe/-comm.

Maybe/-comm-[] :
  {R : A → A → Set r}
  {R-prop : ∀ {x y} → Is-proposition (R x y)} →
  _↔_.to (Maybe/-comm {R = R} R-prop) ∘ [_] ≡ ⊎-map id [_]
Maybe/-comm-[] {R-prop = R-prop} =
  _↔_.to (Maybe/-comm R-prop) ∘ [_]        ≡⟨⟩
  ⊎-map _ id ∘ ⊎-map _ id ∘ ⊎-map [_] [_]  ≡⟨ cong (_∘ ⊎-map [_] [_]) $ sym $ ⟨ext⟩ ⊎-map-∘ ⟩
  ⊎-map _ id ∘ ⊎-map [_] [_]               ≡⟨ sym $ ⟨ext⟩ ⊎-map-∘ ⟩∎
  ⊎-map id [_]                             ∎

-- The sigma type former commutes (kind of) with quotients, assuming
-- that certain families are propositional.

Σ/-comm :
  {P : A / R → Set p} →
  (∀ {x} → Is-proposition (P x)) →
  (∀ {x y} → Is-proposition (R x y)) →
  Σ (A / R) P ↔ Σ A (P ∘ [_]) / (R on proj₁)
Σ/-comm {A = A} {R = R} {P = P} P-prop R-prop = record
  { surjection = record
    { logical-equivalence = record
      { to =
          uncurry $
          elim λ where
            .[]ʳ → curry [_]
            .[]-respects-relationʳ {x = x} {y = y} prop r → ⟨ext⟩ λ P[y] →
              subst (λ x → P x → Σ A (P ∘ [_]) / (R on proj₁))
                    ([]-respects-relation prop r)
                    (curry [_] x) P[y]                                    ≡⟨ subst-→-domain P {f = curry [_] _} ([]-respects-relation prop r) ⟩

              [ (x , subst P (sym $ []-respects-relation prop r) P[y]) ]  ≡⟨ []-respects-relation (λ _ _ → prop _ _) r ⟩∎

              [ (y , P[y]) ]                                              ∎
            .is-setʳ prop _ →
              Π-closure ext 2 λ _ →
              /-is-set λ _ _ → prop _ _
      ; from = rec λ where
          .[]ʳ       → Σ-map [_] id
          .is-setʳ _ →
            Σ-closure 2 (/-is-set λ _ _ → R-prop) (λ _ → mono₁ 1 P-prop)

          .[]-respects-relationʳ {x = (x₁ , x₂)} {y = (y₁ , y₂)} _ →
            R x₁ y₁                        ↝⟨ []-respects-relation (λ _ _ → R-prop) ⟩
            [ x₁ ] ≡ [ y₁ ]                ↔⟨ ignore-propositional-component P-prop ⟩
            ([ x₁ ] , x₂) ≡ ([ y₁ ] , y₂)  □
      }
    ; right-inverse-of = elim-prop λ where
        .[]ʳ _                  → refl _
        .is-propositionʳ prop _ → /-is-set prop
    }
  ; left-inverse-of = uncurry $ elim-prop λ where
      .[]ʳ _ _                → refl _
      .is-propositionʳ prop _ →
        Π-closure ext 1 λ _ →
        Σ-closure 2 (/-is-set prop) (λ _ → mono₁ 1 P-prop)
  }

-- The type former λ X → ℕ → X commutes with quotients, assuming that
-- the quotient relation is a propositional equivalence relation, and
-- also assuming countable choice.
--
-- This result is very similar to Proposition 5 in "Quotienting the
-- Delay Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

-- The forward component of the isomorphism. This component can be
-- defined without any extra assumptions.

ℕ→/-comm-to : (ℕ → A) / (ℕ →ᴾ R) → (ℕ → A / R)
ℕ→/-comm-to {A = A} = rec λ where
    .[]ʳ f n → [ f n ]

    .[]-respects-relationʳ prop r →
      ⟨ext⟩ ([]-respects-relation (prop⇒prop prop) ∘ r)

    .is-setʳ prop →
      Π-closure ext 2 λ _ →
      /-is-set (prop⇒prop prop)
  where
  prop⇒prop :
    ((f g : ℕ → A) → Is-proposition ((ℕ →ᴾ R) f g)) →
    ((x y : A) → Is-proposition (R x y))
  prop⇒prop prop x y p q =
    cong (_$ 0) $ prop (λ _ → x) (λ _ → y) (λ _ → p) (λ _ → q)

-- The isomorphism.

ℕ→/-comm :
  {A : Set a} {R : A → A → Set r} →
  Axiom-of-countable-choice (a ⊔ r) →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  (ℕ → A) / (ℕ →ᴾ R) ↔ (ℕ → A / R)
ℕ→/-comm {A = A} {R} cc R-equiv R-prop = record
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

    (∀ n → [ g₁ n ] ≡ [ g₂ n ])              ↔⟨ ∀-cong ext (λ _ → inverse $ related≃[equal] R-equiv R-prop) ⟩

    (∀ n → R (g₁ n) (g₂ n))                  ↔⟨⟩

    (ℕ →ᴾ R) g₁ g₂                           ↝⟨ []-respects-relation (λ _ _ → →ᴾ-preserves-Is-proposition R ext R-prop) ⟩

    [ g₁ ] ≡ [ g₂ ]                          ↔⟨ ignore-propositional-component
                                                  (Π-closure ext 2 λ _ →
                                                   /-is-set λ _ _ → R-prop) ⟩□
    ([ g₁ ] , [g₁]→≡f) ≡ ([ g₂ ] , [g₂]→≡f)  □

  from₂ : Unit → ∀ f → ∥ [_]→ ⁻¹ f ∥ → ℕ→/-comm-to ⁻¹ f
  from₂ unit f =
    _≃_.to
      (TruncP.constant-function≃∥inhabited∥⇒inhabited
         (Σ-closure 2
            (/-is-set λ _ _ →
               →ᴾ-preserves-Is-proposition R ext R-prop) λ _ →
            mono₁ 1 (Π-closure ext 2 (λ _ → /-is-set λ _ _ → R-prop))))
      (from₁ f , from₁-constant f)

  unblock-from₂ : ∀ x f p → from₂ x f ∣ p ∣ ≡ from₁ f p
  unblock-from₂ unit _ _ = refl _

  abstract

    from₃ : Unit → ∀ f → ℕ→/-comm-to ⁻¹ f
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
      .is-propositionʳ prop _ → /-is-set prop

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
  (P : B → Set p)
  (p-[] : ∀ x → P (_↠_.to surj [ x ])) →
  ((prop : ∀ x y → Is-proposition (R x y)) →
   ∀ {x y} (r : R x y) →
   subst P (cong (_↠_.to surj) ([]-respects-relation prop r)) (p-[] x) ≡
   p-[] y) →
  ((∀ x y → Is-proposition (R x y)) → ∀ x → Is-set (P x)) →
  ∀ x → P x
↠-eliminator surj P p-[] ok P-set x =
  subst P (_↠_.right-inverse-of surj x) p′
  where
  p′ : P (_↠_.to surj (_↠_.from surj x))
  p′ = elim
    (λ where
       .[]ʳ → p-[]

       .[]-respects-relationʳ {x = x} {y = y} prop r →
         subst (P ∘ _↠_.to surj) ([]-respects-relation prop r) (p-[] x)  ≡⟨ subst-∘ P (_↠_.to surj) ([]-respects-relation prop r) ⟩

         subst P (cong (_↠_.to surj) ([]-respects-relation prop r))
           (p-[] x)                                                      ≡⟨ ok prop r ⟩∎

         p-[] y                                                          ∎

       .is-setʳ prop _ → P-set prop _)

    (_↠_.from surj x)

-- The eliminator "computes" in the "right" way for elements that
-- satisfy a certain property, assuming that the quotient relation is
-- pointwise propositional.

↠-eliminator-[] :
  ∀ (surj : A / R ↠ B)
  (P : B → Set p)
  (p-[] : ∀ x → P (_↠_.to surj [ x ]))
  (ok :
     (prop : ∀ x y → Is-proposition (R x y)) →
     ∀ {x y} (r : R x y) →
     subst P (cong (_↠_.to surj) ([]-respects-relation prop r))
       (p-[] x) ≡
     p-[] y)
  (P-set : (∀ x y → Is-proposition (R x y)) → ∀ x → Is-set (P x))
  x →
  (∀ {x y} → Is-proposition (R x y)) →
  _↠_.from surj (_↠_.to surj [ x ]) ≡ [ x ] →
  ↠-eliminator surj P p-[] ok P-set (_↠_.to surj [ x ]) ≡ p-[] x
↠-eliminator-[] {R = R} surj P p-[] ok P-set x R-prop hyp =
  subst P (_↠_.right-inverse-of surj (_↠_.to surj [ x ]))
    (elim e′ (_↠_.from surj (_↠_.to surj [ x ])))          ≡⟨ cong (λ p → subst P p (elim e′ _)) $
                                                              H.respects-surjection surj 2 (/-is-set λ _ _ → R-prop)
                                                                (_↠_.right-inverse-of surj (_↠_.to surj [ x ]))
                                                                (cong (_↠_.to surj) hyp) ⟩
  subst P (cong (_↠_.to surj) hyp)
    (elim e′ (_↠_.from surj (_↠_.to surj [ x ])))          ≡⟨ D.elim
                                                                (λ {x y} p → subst P (cong (_↠_.to surj) p) (elim e′ x) ≡ elim e′ y)
                                                                (λ y →
      subst P (cong (_↠_.to surj) (refl _)) (elim e′ y)            ≡⟨ cong (λ p → subst P p (elim e′ _)) $ cong-refl (_↠_.to surj) ⟩
      subst P (refl _) (elim e′ y)                                 ≡⟨ subst-refl P _ ⟩∎
      elim e′ y                                                    ∎)
                                                                hyp ⟩
  elim e′ [ x ]                                            ≡⟨⟩

  p-[] x                                                   ∎
  where
  e′ = _

-- If there is a bijection from a quotient type to some other type,
-- then one can also construct a quotient-like eliminator for the
-- other type.

↔-eliminator :
  (bij : A / R ↔ B)
  (P : B → Set p)
  (p-[] : ∀ x → P (_↔_.to bij [ x ])) →
  ((prop : ∀ x y → Is-proposition (R x y)) →
   ∀ {x y} (r : R x y) →
   subst P (cong (_↔_.to bij) ([]-respects-relation prop r)) (p-[] x) ≡
   p-[] y) →
  ((∀ x y → Is-proposition (R x y)) → ∀ x → Is-set (P x)) →
  ∀ x → P x
↔-eliminator bij = ↠-eliminator (_↔_.surjection bij)

-- This latter eliminator always "computes" in the "right" way,
-- assuming that the quotient relation is pointwise propositional.

↔-eliminator-[] :
  ∀ (bij : A / R ↔ B)
  (P : B → Set p)
  (p-[] : ∀ x → P (_↔_.to bij [ x ]))
  (ok :
     (prop : ∀ x y → Is-proposition (R x y)) →
     ∀ {x y} (r : R x y) →
     subst P (cong (_↔_.to bij) ([]-respects-relation prop r))
       (p-[] x) ≡
     p-[] y)
  (P-set : (∀ x y → Is-proposition (R x y)) → ∀ x → Is-set (P x)) x →
  (∀ {x y} → Is-proposition (R x y)) →
  ↔-eliminator bij P p-[] ok P-set (_↔_.to bij [ x ]) ≡ p-[] x
↔-eliminator-[] bij P p-[] ok P-set x R-prop =
  ↠-eliminator-[] (_↔_.surjection bij) P p-[] ok P-set x
    R-prop
    (_↔_.left-inverse-of bij [ x ])

-- A quotient-like eliminator for functions of type ℕ → A / R, where R
-- is a propositional equivalence relation. Defined using countable
-- choice.
--
-- This eliminator is taken from Corollary 1 in "Quotienting the Delay
-- Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

ℕ→/-elim :
  {A : Set a} {R : A → A → Set r} →
  Axiom-of-countable-choice (a ⊔ r) →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  (P : (ℕ → A / R) → Set p)
  (p-[] : ∀ f → P (λ n → [ f n ])) →
  ((prop : ∀ f g → Is-proposition ((ℕ →ᴾ R) f g)) →
   ∀ {f g} (r : (ℕ →ᴾ R) f g) →
   subst P (cong ℕ→/-comm-to ([]-respects-relation prop r)) (p-[] f) ≡
   p-[] g) →
  (∀ f → Is-set (P f)) →
  ∀ f → P f
ℕ→/-elim cc R-equiv R-prop P p-[] ok P-set =
  ↔-eliminator
    (ℕ→/-comm cc R-equiv R-prop)
    P p-[] ok (λ _ → P-set)

-- The eliminator "computes" in the "right" way.

ℕ→/-elim-[] :
  ∀ {A : Set a} {R : A → A → Set r}
  (cc : Axiom-of-countable-choice (a ⊔ r))
  (R-equiv : Is-equivalence-relation R)
  (R-prop : ∀ {x y} → Is-proposition (R x y))
  (P : (ℕ → A / R) → Set p)
  (p-[] : ∀ f → P (λ n → [ f n ]))
  (ok :
     (prop : ∀ f g → Is-proposition ((ℕ →ᴾ R) f g)) →
     ∀ {f g} (r : (ℕ →ᴾ R) f g) →
     subst P (cong ℕ→/-comm-to ([]-respects-relation prop r)) (p-[] f) ≡
     p-[] g)
  (P-set : ∀ f → Is-set (P f)) f →
  ℕ→/-elim cc R-equiv R-prop P p-[] ok P-set (λ n → [ f n ]) ≡
  p-[] f
ℕ→/-elim-[] {R = R} cc R-equiv R-prop P p-[] ok P-set f =
  ↔-eliminator-[]
    (ℕ→/-comm cc R-equiv R-prop)
    P p-[] ok (λ _ → P-set) f
    (→ᴾ-preserves-Is-proposition R ext R-prop)
