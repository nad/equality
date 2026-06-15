------------------------------------------------------------------------
-- An axiomatised variant of set quotients with erased higher
-- constructors
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- Partly following the HoTT book, but adapted for erasure.
--
-- Unlike the HoTT book, but following the cubical library (in which
-- set quotients were implemented by Zesen Qian and Anders Mörtberg),
-- the quotienting relations are not (always) required to be
-- propositional.

open import Equality

module Quotient.Erased.Axiomatised
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude as P

open import Equality.Decidable-UIP eq
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Equivalence-relation eq
open import Erased.Level-1 eq as Er
  using
    (Erased; Erasedᴾ; []-cong-axiomatisation;
     Dec-Erased; Decidable-erased-equality)
  renaming ([_] to [_]ᴱ)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional.Erased.Axiomatised eq
import List eq as L
open import Sum eq
open import Surjection eq using (_↠_; Split-surjective)
open import Univalence-axiom eq

private
  module @0 BC {a} =
    Er.[]-cong₁ (Er.erased-instance-of-[]-cong-axiomatisation {a = a})

private variable
  a a₁ a₂ a₃ b ℓ p r₁ r₂ r₃ : Level
  A A₁ A₂ A₃ B C            : Type _
  P                         : A → Type _
  @0 Q R R₁ R₂              : A → A → Type _
  e k r x y                 : A

-- An axiomatisation of quotients with erased higher constructors.

record Quotientᴱ : Typeω where
  field
    -- The quotient type constructor.
    _/ᴱ_ : (A : Type a) → @0 (A → A → Type r) → Type (a ⊔ r)

    -- The "constructors".
    [_]                     : A → A /ᴱ R
    @0 []-respects-relation : R x y → _≡_ {A = A /ᴱ R} [ x ] [ y ]
    @0 /ᴱ-is-set            : Is-set (A /ᴱ R)

    -- An eliminator.
    eliminator :
      {P : A /ᴱ R → Type p}
      (f : ∀ x → P [ x ]) →
      @0 (∀ {x y} (r : R x y) →
          subst P ([]-respects-relation r) (f x) ≡ f y) →
      @0 (∀ x → Is-set (P x)) →
      (x : A /ᴱ R) → P x

    -- A computation rule for the eliminator.
    eliminator-[] :
      {P : A /ᴱ R → Type p} {f : ∀ x → P [ x ]}
      {@0 p :
         ∀ {x y} (r : R x y) →
         subst P ([]-respects-relation r) (f x) ≡ f y}
      {@0 s : ∀ x → Is-set (P x)} →
      eliminator f p s [ x ] ≡ f x

  ----------------------------------------------------------------------
  -- Eliminators

  -- An eliminator expressed using a record type.

  record Elim {A : Type a} {@0 R : A → A → Type r}
              (P : A /ᴱ R → Type p) : Type (a ⊔ r ⊔ p) where
    no-eta-equality
    field
      []ʳ : ∀ x → P [ x ]

      @0 []-respects-relationʳ :
        (r : R x y) →
        subst P ([]-respects-relation r) ([]ʳ x) ≡ []ʳ y

      @0 is-setʳ : ∀ x → Is-set (P x)

  open Elim public

  opaque

    elim : Elim P → (x : A /ᴱ R) → P x
    elim e = eliminator E.[]ʳ E.[]-respects-relationʳ E.is-setʳ
      where
      module E = Elim e

    elim-[] : elim {R = R} e [ x ] ≡ e .[]ʳ x
    elim-[] = eliminator-[]

  -- A non-dependent eliminator expressed using a record type.

  record Rec {A : Type a} (@0 R : A → A → Type r) (B : Type b) :
             Type (a ⊔ r ⊔ b) where
    no-eta-equality
    field
      []ʳ                      : A → B
      @0 []-respects-relationʳ : (r : R x y) → []ʳ x ≡ []ʳ y
      @0 is-setʳ               : Is-set B

  open Rec public

  opaque
    unfolding elim

    rec : Rec R B → A /ᴱ R → B
    rec r = elim λ where
        .[]ʳ →
          R.[]ʳ
        .[]-respects-relationʳ →
          trans (subst-const _) ∘ R.[]-respects-relationʳ
        .is-setʳ _ →
          R.is-setʳ
      where
      module R = Rec r

    rec-[] : rec {R = R} r [ x ] ≡ r .[]ʳ x
    rec-[] = eliminator-[]

  -- A variant of elim that can be used if the motive is a family of
  -- propositions.

  record Elim-prop
           {A : Type a} {@0 R : A → A → Type r}
           (P : A /ᴱ R → Type p) : Type (a ⊔ r ⊔ lsuc p) where
    no-eta-equality
    field
      []ʳ                : ∀ x → P [ x ]
      @0 is-propositionʳ : ∀ x → Is-proposition (P x)

  open Elim-prop public

  opaque
    unfolding elim

    elim-prop : Elim-prop P → (x : A /ᴱ R) → P x
    elim-prop e = elim λ where
        .[]ʳ                     → E.[]ʳ
        .[]-respects-relationʳ _ → E.is-propositionʳ _ _ _
        .is-setʳ _               → mono₁ 1 (E.is-propositionʳ _)
      where
      module E = Elim-prop e

    elim-prop-[] : elim-prop {R = R} e [ x ] ≡ e .[]ʳ x
    elim-prop-[] = eliminator-[]

  -- A variant of rec that can be used if the motive is a proposition.

  record Rec-prop (A : Type a) (B : Type b) : Type (a ⊔ b) where
    no-eta-equality
    field
      []ʳ                : A → B
      @0 is-propositionʳ : Is-proposition B

  open Rec-prop public

  opaque
    unfolding elim-prop

    rec-prop : Rec-prop A B → A /ᴱ R → B
    rec-prop r = elim-prop λ where
        .[]ʳ               → R.[]ʳ
        .is-propositionʳ _ → R.is-propositionʳ
      where
      module R = Rec-prop r

    rec-prop-[] : rec-prop {R = R} r [ x ] ≡ r .[]ʳ x
    rec-prop-[] = eliminator-[]

  ----------------------------------------------------------------------
  -- Some binary eliminators

  opaque

    -- A binary variant of elim.

    elim₂ :
      (P : A /ᴱ Q → B /ᴱ R → Type p) →
      @0 (∀ x y → Is-set (P x y)) →
      @0 (∀ {x} → Q x x) →
      @0 (∀ {y} → R y y) →
      (f : ∀ x y → P [ x ] [ y ]) →
      @0 (∀ {x₁ x₂ y₁ y₂} (x₁Qx₂ : Q x₁ x₂) (y₁Ry₂ : R y₁ y₂) →
          subst (uncurry P)
            (cong₂ _,_ ([]-respects-relation x₁Qx₂)
               ([]-respects-relation y₁Ry₂))
            (f x₁ y₁) ≡
          f x₂ y₂) →
      ∀ x y → P x y
    elim₂ {A} {Q} {B} P set Q-rfl R-rfl f resp x =
      let g : (y : B) (x : A /ᴱ Q) → P x [ y ]
          g y = elim λ where
            .[]ʳ →
              flip f y
            .[]-respects-relationʳ {x = x₁} {y = x₂} r →
              subst (flip P [ y ]) ([]-respects-relation r) (f x₁ y)  ≡⟨ subst-∘ _ _ _ ⟩

              subst (uncurry P)
                (cong (_, _) ([]-respects-relation r)) (f x₁ y)       ≡⟨ cong (flip (subst (uncurry P)) _) $
                                                                         (×-closure 2 /ᴱ-is-set /ᴱ-is-set) _ _ ⟩
              subst (uncurry P)
                (cong₂ _,_ ([]-respects-relation r)
                   ([]-respects-relation R-rfl))
                (f x₁ y)                                              ≡⟨ resp _ _ ⟩

              f x₂ y                                                  ∎
            .is-setʳ _ →
              set _ _
      in
      elim λ where
        .is-setʳ _                                 → set _ _
        .[]ʳ                                       → flip g x
        .[]-respects-relationʳ {x = y₁} {y = y₂} r →
          let Q = λ x →
                subst (P x) ([]-respects-relation r) (g y₁ x) ≡
                g y₂ x
          in
          flip (elim-prop {P = Q}) x λ @0 where
            .is-propositionʳ _ → set _ _
            .[]ʳ x             →
              subst (P [ x ]) ([]-respects-relation r) (g y₁ [ x ])     ≡⟨ cong (subst _ _) elim-[] ⟩

              subst (P [ x ]) ([]-respects-relation r) (f x y₁)         ≡⟨ subst-∘ _ _ _ ⟩

              subst (uncurry P) (cong (_ ,_) ([]-respects-relation r))
                (f x y₁)                                                ≡⟨ cong (flip (subst _) _) $
                                                                           (×-closure 2 /ᴱ-is-set /ᴱ-is-set) _ _ ⟩
              subst (uncurry P)
                (cong₂ _,_ ([]-respects-relation Q-rfl)
                   ([]-respects-relation r))
                (f x y₁)                                                ≡⟨ resp _ _ ⟩

              f x y₂                                                    ≡⟨ sym elim-[] ⟩∎

              g y₂ [ x ]                                                ∎

  opaque
    unfolding elim₂

    -- A computation rule for elim₂.

    elim₂-[] :
      {P : A /ᴱ Q → B /ᴱ R → Type p}
      {@0 set : ∀ x y → Is-set (P x y)}
      {@0 Q-rfl : ∀ {x} → Q x x}
      {@0 R-rfl : ∀ {x} → R x x}
      {f : ∀ x y → P [ x ] [ y ]}
      {@0 resp :
            ∀ {x₁ x₂ y₁ y₂} (x₁Qx₂ : Q x₁ x₂) (y₁Ry₂ : R y₁ y₂) →
            subst (uncurry P)
              (cong₂ _,_ ([]-respects-relation x₁Qx₂)
                 ([]-respects-relation y₁Ry₂))
              (f x₁ y₁) ≡
            f x₂ y₂} →
      elim₂ P set Q-rfl R-rfl f resp [ x ] [ y ] ≡ f x y
    elim₂-[] = trans elim-[] elim-[]

  opaque

    -- A binary variant of rec.

    rec₂ :
      @0 Is-set C →
      @0 (∀ {x} → Q x x) →
      @0 (∀ {x} → R x x) →
      (f : A → B → C) →
      @0 (∀ {x₁ x₂ y₁ y₂} → Q x₁ x₂ → R y₁ y₂ → f x₁ y₁ ≡ f x₂ y₂) →
      A /ᴱ Q → B /ᴱ R → C
    rec₂ set Q-rfl R-rfl f resp =
      elim₂ _ (λ _ _ → set) Q-rfl R-rfl f
        (λ r₁ r₂ → trans (subst-const _) (resp r₁ r₂))

  opaque
    unfolding rec₂

    -- A computation rule for rec₂.

    rec₂-[] :
      {@0 set : Is-set C}
      {@0 Q-rfl : ∀ {x} → Q x x}
      {@0 R-rfl : ∀ {x} → R x x}
      {f : A → B → C}
      {@0 resp :
            ∀ {x₁ x₂ y₁ y₂} → Q x₁ x₂ → R y₁ y₂ → f x₁ y₁ ≡ f x₂ y₂} →
      rec₂ set Q-rfl R-rfl f resp [ x ] [ y ] ≡ f x y
    rec₂-[] = elim₂-[]

  opaque

    -- A binary variant of elim-prop.

    elim-prop₂ :
      (P : A /ᴱ Q → B /ᴱ R → Type p) →
      @0 (∀ x y → Is-proposition (P x y)) →
      (∀ x y → P [ x ] [ y ]) →
      ∀ x y → P x y
    elim-prop₂ {A} {Q} {B} P prop f x =
      let g : (y : B) (x : A /ᴱ Q) → P x [ y ]
          g y = elim-prop λ where
            .[]ʳ               → flip f y
            .is-propositionʳ _ → prop _ _
      in
      elim-prop λ where
        .[]ʳ               → flip g x
        .is-propositionʳ _ → prop _ _

  opaque
    unfolding elim-prop₂

    -- A computation rule for elim-prop₂.

    elim-prop₂-[] :
      {P : A /ᴱ Q → B /ᴱ R → Type p}
      {@0 prop : ∀ x y → Is-proposition (P x y)}
      {f : ∀ x y → P [ x ] [ y ]} →
      elim-prop₂ P prop f [ x ] [ y ] ≡ f x y
    elim-prop₂-[] = trans elim-prop-[] elim-prop-[]

  opaque

    -- A binary variant of rec-prop.

    rec-prop₂ :
      @0 Is-proposition C →
      (A → B → C) →
      A /ᴱ Q → B /ᴱ R → C
    rec-prop₂ prop = elim-prop₂ _ (λ _ _ → prop)

  opaque
    unfolding rec-prop₂

    -- A computation rule for rec-prop₂.

    rec-prop₂-[] :
      {@0 prop : Is-proposition C} {f : A → B → C} →
      rec-prop₂ {Q = Q} {R = R} prop f [ x ] [ y ] ≡ f x y
    rec-prop₂-[] = elim-prop₂-[]

  ----------------------------------------------------------------------
  -- Propositional truncation

  opaque

    -- A propositional truncation operator defined as a quotient with
    -- a trivial relation.

    truncation : Truncationᴱ
    truncation .Truncationᴱ.∥_∥ᴱ =
      _/ᴱ (λ _ _ → ⊤)
    truncation .Truncationᴱ.∣_∣ =
      [_]
    truncation .Truncationᴱ.truncation-is-proposition =
      elim-prop₂ _ (λ _ _ → /ᴱ-is-set) (λ _ _ → []-respects-relation _)
    truncation .Truncationᴱ.eliminator f p =
      eliminator f (λ _ → p _ _ _) (mono₁ 1 ∘ p)
    truncation .Truncationᴱ.eliminator-∣∣ =
      eliminator-[]

  private
    module T = Truncationᴱ truncation

  ----------------------------------------------------------------------
  -- Effectiveness

  -- The property of being effective.
  --
  -- This definition is based on those in Martin Hofmann's PhD thesis
  -- and the HoTT book, but adapted for erasure.

  Effective : {A : Type a} → (A → A → Type r) → Type (a ⊔ r)
  Effective {A} R =
    ∀ {x y} →
    @0 Is-equivalence-relation R →
    @0 Is-proposition (R x y) →
    R x x →
    _≡_ {A = A /ᴱ R} [ x ] [ y ] → R x y

  -- See also below.

  ----------------------------------------------------------------------
  -- Some properties that are stated or implemented using
  -- propositional truncation

  module Truncation (Tr : Truncationᴱ) where

    private
      open module Tr = Truncationᴱ Tr using (∥_∥ᴱ; ∣_∣; Surjectiveᴱ)

    --------------------------------------------------------------------
    -- Preservation lemmas

    -- Preservation lemmas that are expressed using a propositional
    -- truncation operator.

    opaque

      -- A unary preservation lemma for functions.

      infix 5 _/ᴱ-map-∥∥ᴱ_

      _/ᴱ-map-∥∥ᴱ_ :
        (A₁→A₂ : A₁ → A₂) →
        @0 (∀ x y → ∥ R₁ x y ∥ᴱ → ∥ R₂ (A₁→A₂ x) (A₁→A₂ y) ∥ᴱ) →
        A₁ /ᴱ R₁ → A₂ /ᴱ R₂
      _/ᴱ-map-∥∥ᴱ_ {R₁} {R₂} A₁→A₂ R₁→R₂ = rec λ where
          .[]ʳ                           → [_] ∘ A₁→A₂
          .is-setʳ                       → /ᴱ-is-set
          .[]-respects-relationʳ {x} {y} →
             R₁ x y                       →⟨ ∣_∣ ⟩
             ∥ R₁ x y ∥ᴱ                  →⟨ R₁→R₂ _ _ ⟩
             ∥ R₂ (A₁→A₂ x) (A₁→A₂ y) ∥ᴱ  →⟨ (Tr.rec λ @0 where
                                                .Tr.∣∣ʳ                        → []-respects-relation
                                                .Tr.truncation-is-propositionʳ → /ᴱ-is-set) ⟩□
             [ A₁→A₂ x ] ≡ [ A₁→A₂ y ]    □

    opaque
      unfolding _/ᴱ-map-∥∥ᴱ_

      -- A binary preservation lemma for functions.

      /ᴱ-zip-∥∥ᴱ :
        {A₁ : Type a₁} {A₂ : Type a₂} {A₃ : Type a₃}
        {@0 R₁ : A₁ → A₁ → Type r₁}
        {@0 R₂ : A₂ → A₂ → Type r₂} →
        {@0 R₃ : A₃ → A₃ → Type r₃} →
        @0 Extensionality (a₂ ⊔ r₂) (a₃ ⊔ r₃) →
        (f : A₁ → A₂ → A₃) →
        @0 (∀ {x} → ∥ R₁ x x ∥ᴱ) →
        @0 (∀ {x} → ∥ R₂ x x ∥ᴱ) →
        @0 (∀ {u v x y} →
            ∥ R₁ u v ∥ᴱ → ∥ R₂ x y ∥ᴱ → ∥ R₃ (f u x) (f v y) ∥ᴱ) →
        A₁ /ᴱ R₁ → A₂ /ᴱ R₂ → A₃ /ᴱ R₃
      /ᴱ-zip-∥∥ᴱ {R₁} {R₂} {R₃} ext f r₁ r₂ r₃ = rec λ where
        .is-setʳ →
          Π-closure ext 2 λ _ →
          /ᴱ-is-set
        .[]ʳ x →
          f x
            /ᴱ-map-∥∥ᴱ
          (λ y₁ y₂ →
             ∥ R₂ y₁ y₂ ∥ᴱ              →⟨ (λ hyp → r₃ r₁ hyp) ⟩□
             ∥ R₃ (f x y₁) (f x y₂) ∥ᴱ  □)
        .[]-respects-relationʳ {x = x₁} {y = x₂} x₁R₁x₂ →
          apply-ext ext $ elim-prop λ @0 where
            .is-propositionʳ _ →
              /ᴱ-is-set
            .[]ʳ y →
                                                                     $⟨ x₁R₁x₂ ⟩
              R₁ x₁ x₂                                               →⟨ ∣_∣ ⟩
              ∥ R₁ x₁ x₂ ∥ᴱ                                          →⟨ (λ hyp → r₃ hyp r₂) ⟩
              ∥ R₃ (f x₁ y) (f x₂ y) ∥ᴱ                              →⟨ (Tr.rec λ where
                                                                           .Tr.∣∣ʳ                        → []-respects-relation
                                                                           .Tr.truncation-is-propositionʳ → /ᴱ-is-set) ⟩
              [ f x₁ y ] ≡ [ f x₂ y ]                                →⟨ ≡⇒↝ _ $ sym $ cong₂ _≡_ rec-[] rec-[] ⟩□
              (f x₁ /ᴱ-map-∥∥ᴱ _) [ y ] ≡ (f x₂ /ᴱ-map-∥∥ᴱ _) [ y ]  □

    opaque
      unfolding _/ᴱ-map-∥∥ᴱ_

      -- A unary preservation lemma for logical equivalences.

      /ᴱ-cong-∥∥ᴱ-⇔ :
        (A₁⇔A₂ : A₁ ⇔ A₂) →
        @0 (∀ x y →
            ∥ R₁ x y ∥ᴱ → ∥ R₂ (_⇔_.to A₁⇔A₂ x) (_⇔_.to A₁⇔A₂ y) ∥ᴱ) →
        @0 (∀ x y →
            ∥ R₂ x y ∥ᴱ →
            ∥ R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y) ∥ᴱ) →
        A₁ /ᴱ R₁ ⇔ A₂ /ᴱ R₂
      /ᴱ-cong-∥∥ᴱ-⇔ A₁⇔A₂ R₁→R₂ R₂→R₁ = record
        { to   = _⇔_.to   A₁⇔A₂ /ᴱ-map-∥∥ᴱ R₁→R₂
        ; from = _⇔_.from A₁⇔A₂ /ᴱ-map-∥∥ᴱ R₂→R₁
        }

    opaque
      unfolding /ᴱ-cong-∥∥ᴱ-⇔

      -- A unary preservation lemma for split surjections.

      infix 5 _/ᴱ-cong-∥∥ᴱ-↠_

      _/ᴱ-cong-∥∥ᴱ-↠_ :
        (A₁↠A₂ : A₁ ↠ A₂) →
        @0 (∀ x y →
            ∥ R₁ x y ∥ᴱ ⇔ ∥ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y) ∥ᴱ) →
        A₁ /ᴱ R₁ ↠ A₂ /ᴱ R₂
      _/ᴱ-cong-∥∥ᴱ-↠_ {R₁} {R₂} A₁↠A₂ R₁⇔R₂ = record
        { logical-equivalence =
            /ᴱ-cong-∥∥ᴱ-⇔
              (_↠_.logical-equivalence A₁↠A₂)
              (λ x y → _⇔_.to (R₁⇔R₂ x y))
              (λ x y → ∥ R₂ x y ∥ᴱ                          →⟨ ≡⇒↝ _ (sym $ cong₂ (λ x y → ∥ R₂ x y ∥ᴱ) (right-inverse-of x) (right-inverse-of y)) ⟩
                       ∥ R₂ (to (from x)) (to (from y)) ∥ᴱ  →⟨ _⇔_.from (R₁⇔R₂ _ _) ⟩□
                       ∥ R₁ (from x) (from y) ∥ᴱ            □)
        ; right-inverse-of = elim-prop λ where
            .[]ʳ x →
              (to /ᴱ-map-∥∥ᴱ _) ((from /ᴱ-map-∥∥ᴱ _) [ x ])  ≡⟨ trans (cong (rec _) rec-[]) rec-[] ⟩
              [ to (from x) ]                                ≡⟨ cong [_] $ right-inverse-of x ⟩∎
              [ x ]                                          ∎
            .is-propositionʳ _ → /ᴱ-is-set
        }
        where
        open _↠_ A₁↠A₂

    opaque
      unfolding _/ᴱ-cong-∥∥ᴱ-↠_

      -- A unary preservation lemma for isomorphisms.

      infix 5 _/ᴱ-cong-∥∥ᴱ_

      _/ᴱ-cong-∥∥ᴱ_ :
        {A₁ : Type a₁} {A₂ : Type a₂}
        {@0 R₁ : A₁ → A₁ → Type r₁}
        {@0 R₂ : A₂ → A₂ → Type r₂} →
        (A₁↔A₂ : A₁ ↔[ k ] A₂) →
        @0 (∀ x y →
            ∥ R₁ x y ∥ᴱ ⇔
            ∥ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y) ∥ᴱ) →
        A₁ /ᴱ R₁ ↔[ k ] A₂ /ᴱ R₂
      _/ᴱ-cong-∥∥ᴱ_ {k} {R₁} {R₂} A₁↔A₂ R₁⇔R₂ =
        let A₁≃A₂ = from-isomorphism A₁↔A₂

            open _≃_ A₁≃A₂
        in
        from-bijection (record
          { surjection = from-isomorphism A₁≃A₂ /ᴱ-cong-∥∥ᴱ-↠ λ x y →
              ∥ R₁ x y ∥ᴱ                                                ↝⟨ R₁⇔R₂ x y ⟩
              ∥ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y) ∥ᴱ  ↝⟨ ≡⇒↝ _ $
                                                                            cong₂ (λ f g → ∥ R₂ (f x) (g y) ∥ᴱ)
                                                                              (to-implication∘from-isomorphism k equivalence)
                                                                              (to-implication∘from-isomorphism k equivalence) ⟩□
              ∥ R₂ (to x) (to y) ∥ᴱ                                      □
          ; left-inverse-of = elim-prop λ where
              .[]ʳ x →
                (from /ᴱ-map-∥∥ᴱ _) ((to /ᴱ-map-∥∥ᴱ _) [ x ])  ≡⟨ trans (cong (rec _) rec-[]) rec-[] ⟩
                [ from (to x) ]                                ≡⟨ cong [_] $ left-inverse-of x ⟩∎
                [ x ]                                          ∎
              .is-propositionʳ _ → /ᴱ-is-set
          })

    --------------------------------------------------------------------
    -- Effectiveness

    -- The property of being weakly effective.
    --
    -- This definition is based on one in "Quotienting the Delay Monad
    -- by Weak Bisimilarity" by Chapman, Uustalu and Veltri, but
    -- adapted for erasure.

    Weakly-effective : {A : Type a} → (A → A → Type r) → Type (a ⊔ r)
    Weakly-effective {A} R =
      ∀ {x y} →
      @0 Is-equivalence-relation R →
      ∥ R x x ∥ᴱ →
      _≡_ {A = A /ᴱ R} [ x ] [ y ] → ∥ R x y ∥ᴱ

    opaque

      -- If R is weakly effective, then the relation is effective.

      Weakly-effective→Effective :
        {R : A → A → Type r} →
        Weakly-effective R → Effective R
      Weakly-effective→Effective {R} eff {x} {y} eq prop Rxx =
        [ x ] ≡ [ y ]  →⟨ eff eq ∣ Rxx ∣ ⟩
        ∥ R x y ∥ᴱ     ↔⟨ Tr.∥∥ᴱ≃ prop ⟩□
        R x y          □

    opaque

      -- If R is effective and propositional, then the relation is
      -- weakly effective.

      Effective→Weakly-effective :
        {R : A → A → Type r} →
        @0 (∀ {x y} → Is-proposition (R x y)) →
        Effective R → Weakly-effective R
      Effective→Weakly-effective {R} prop eff {x} {y} eq Rxx =
        [ x ] ≡ [ y ]  →⟨ eff eq prop (_≃_.to (Tr.∥∥ᴱ≃ prop) Rxx) ⟩
        R x y          ↔⟨ inverse (Tr.∥∥ᴱ≃ prop) ⟩□
        ∥ R x y ∥ᴱ     □

    opaque

      -- If R is an effective equivalence relation that is a
      -- proposition for x and y, then R x y is equivalent to equality
      -- of x and y under [_] (in erased contexts).

      @0 ≃[]≡[] :
        Effective R →
        Is-equivalence-relation R →
        Is-proposition (R x y) →
        R x y ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
      ≃[]≡[] eff eq prop =
        Eq.⇔→≃ prop /ᴱ-is-set []-respects-relation
          (eff eq prop (eq .Is-equivalence-relation.reflexive))

    opaque

      -- If R is a weakly effective equivalence relation, then R x y
      -- is equivalent to equality of x and y under [_] (in erased
      -- contexts).

      @0 ∥∥ᴱ≃[]≡[] :
        Weakly-effective R →
        Is-equivalence-relation R →
        ∥ R x y ∥ᴱ ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
      ∥∥ᴱ≃[]≡[] eff eq =
        Eq.⇔→≃
          Tr.truncation-is-proposition
          /ᴱ-is-set
          (Tr.rec λ @0 where
             .Tr.truncation-is-propositionʳ → /ᴱ-is-set
             .Tr.∣∣ʳ                        → []-respects-relation)
          (eff eq ∣ eq .Is-equivalence-relation.reflexive ∣)

    -- In the presence of erased propositional extensionality and
    -- erased function extensionality every (non-erased) relation is
    -- weakly effective and effective.

    module Propositional-extensionality
      (@0 ext      : Extensionality (lsuc r) (lsuc r))
      (@0 prop-ext : Propositional-extensionality r)
      where

      opaque

        -- Every non-erased relation is weakly effective.
        --
        -- This proof is based on that of Proposition 2 in
        -- "Quotienting the Delay Monad by Weak Bisimilarity" by
        -- Chapman, Uustalu and Veltri.

        weakly-effective :
          {R : A → A → Type r} →
          Weakly-effective R
        weakly-effective {A} {R} {x} {y} eq ∥Rxx∥ᴱ [x]≡[y] =
                             $⟨ ∥Rxx∥ᴱ ⟩
          ∥ R x x ∥ᴱ         ↔⟨ ≡⇒↝ equivalence (cong proj₁ (sym rec-[])) ⟩
          R′ x [ x ] .proj₁  →⟨ ≡⇒→ (cong (λ y → R′ x y .proj₁) [x]≡[y]) ⟩
          R′ x [ y ] .proj₁  ↔⟨ ≡⇒↝ equivalence (cong proj₁ rec-[]) ⟩□
          ∥ R x y ∥ᴱ         □
          where
          R′ : A → A /ᴱ R → ∃ λ (P : Type r) → Erased (Is-proposition P)
          R′ x = rec λ where
            .[]ʳ y → ∥ R x y ∥ᴱ , Er.[ Tr.truncation-is-proposition ]

            .is-setʳ →
              Er.Is-set-∃-Erased-Is-proposition ext prop-ext

            .[]-respects-relationʳ {x = y} {y = z} →
              R y z                                              ↝⟨ (λ r → record
                                                                       { to   = flip (eq .Is-equivalence-relation.transitive) r
                                                                       ; from = flip (eq .Is-equivalence-relation.transitive)
                                                                                  (eq .Is-equivalence-relation.symmetric r)
                                                                       }) ⟩
              R x y ⇔ R x z                                      ↝⟨ EEq._≃ᴱ_.logical-equivalence ∘ Tr.∥∥ᴱ-cong-⇔ ⟩
              ∥ R x y ∥ᴱ ⇔ ∥ R x z ∥ᴱ                            ↔⟨ ⇔↔≡″ ext prop-ext ⟩
              (∥ R x y ∥ᴱ , _) ≡ (∥ R x z ∥ᴱ , _)                ↝⟨ cong (Σ-map id Er.[_]→) ⟩□
              (∥ R x y ∥ᴱ , Er.[ _ ]) ≡ (∥ R x z ∥ᴱ , Er.[ _ ])  □

      opaque

        -- Every non-erased relation is effective.

        effective :
          {R : A → A → Type r} →
          Effective R
        effective = Weakly-effective→Effective weakly-effective

    -- One can prove that the quotient type is effective given certain
    -- assumptions that do not include function extensionality or
    -- propositional extensionality.

    module Idempotent
      (@0 A-set : Is-set A)
      (f        : A → A)
      (@0 idem  : ∀ x → f (f x) ≡ f x)
      (@0 R≃    : ∀ {x y} → R x y ≃ (f x ≡ f y))
      where

      opaque

        -- The relation R is an equivalence relation (in erased
        -- contexts).

        @0 is-equivalence-relation : Is-equivalence-relation R
        is-equivalence-relation = record
          { reflexive  = _≃_.from R≃ (refl _)
          ; symmetric  = _≃_.from R≃ ∘ sym ∘ _≃_.to R≃
          ; transitive =
              curry $
              _≃_.from R≃ ∘ uncurry trans ∘ Σ-map (_≃_.to R≃) (_≃_.to R≃)
          }

      opaque

        -- The relation R is propositional (in erased contexts).

        @0 is-proposition : Is-proposition (R x y)
        is-proposition = H-level-cong _ 1 (inverse R≃) A-set

      opaque

        -- A certain type is equivalent (with erased proofs) to A /ᴱ R.

        ∃-Erased-≡-≃ᴱ/ᴱ :
          (∃ λ x → Erased (f x ≡ x)) ≃ᴱ A /ᴱ R
        ∃-Erased-≡-≃ᴱ/ᴱ =
          let g = rec λ where
               .[]ʳ x → f x , [ idem x ]ᴱ
               .[]-respects-relationʳ r →
                 Σ-≡,≡→≡ (_≃_.to R≃ r)
                   (BC.H-level-Erased 1 A-set _ _)
               .is-setʳ →
                 Σ-closure 2 A-set λ _ →
                 BC.H-level-Erased 2 (mono₁ 1 A-set)
          in
          EEq.↔→≃ᴱ ([_] ∘ proj₁) g
            (elim-prop λ @0 where
               .[]ʳ x →
                 [ proj₁ (g [ x ]) ]  ≡⟨ cong ([_] ∘ proj₁) rec-[] ⟩
                 [ f x ]              ≡⟨ []-respects-relation (_≃_.from R≃ (idem x)) ⟩∎
                 [ x ]                ∎
               .is-propositionʳ _ → /ᴱ-is-set)
            (λ (x , eq) →
               Σ-≡,≡→≡
                 (proj₁ (g [ x ])  ≡⟨ cong proj₁ rec-[] ⟩
                  f x              ≡⟨ eq .Er.erased ⟩∎
                  x                ∎)
                 (BC.H-level-Erased 1 A-set _ _))

      opaque
        unfolding ∃-Erased-≡-≃ᴱ/ᴱ

        -- A computation rule.

        from-∃-Erased-≡-≃ᴱ/ᴱ-[] :
          _≃ᴱ_.from ∃-Erased-≡-≃ᴱ/ᴱ [ x ] ≡ (f x , [ idem x ]ᴱ)
        from-∃-Erased-≡-≃ᴱ/ᴱ-[] = rec-[]

      opaque

        -- The relation R is weakly effective (in erased contexts).

        @0 weakly-effective : Weakly-effective R
        weakly-effective {x} {y} _ _ =
          [ x ] ≡ [ y ]                              ↔⟨ inverse (Eq.≃-≡ (EEq.≃ᴱ→≃ (inverse ∃-Erased-≡-≃ᴱ/ᴱ))) ⟩

          _≃ᴱ_.from ∃-Erased-≡-≃ᴱ/ᴱ [ x ] ≡
          _≃ᴱ_.from ∃-Erased-≡-≃ᴱ/ᴱ [ y ]            →⟨ ≡⇒↝ _ (cong₂ _≡_ from-∃-Erased-≡-≃ᴱ/ᴱ-[] from-∃-Erased-≡-≃ᴱ/ᴱ-[]) ⟩

          (f x , [ idem x ]ᴱ) ≡ (f y , [ idem y ]ᴱ)  ↔⟨ inverse (ignore-propositional-component (BC.H-level-Erased 1 A-set)) ⟩

          f x ≡ f y                                  ↔⟨ inverse R≃ ⟩

          R x y                                      →⟨ ∣_∣ ⟩

          ∥ R x y ∥ᴱ                                 □

      opaque

        -- The relation R is effective (in erased contexts).

        @0 effective : Effective R
        effective = Weakly-effective→Effective weakly-effective

      opaque

        -- R x y is equivalent to equality of x and y under [_] (in
        -- erased contexts).

        @0 ≃[]≡[]′ : R x y ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
        ≃[]≡[]′ =
          ≃[]≡[] effective is-equivalence-relation is-proposition

    -- A special case of the module above.

    module Split-surjection
      (@0 A-set : Is-set A)
      (@0 B-set : Is-set B)
      (f        : A → B)
      (g        : B → A)
      (@0 f-g   : ∀ x → f (g x) ≡ x)
      where

      open Idempotent
             {R = λ x y → f x ≡ f y}
             A-set
             (g ∘ f)
             (λ x →
                g (f (g (f x)))  ≡⟨ cong g (f-g (f x)) ⟩∎
                g (f x)          ∎)
             (λ {x y} →
                Eq.⇔→≃ B-set A-set
                  (cong g)
                  (λ eq →
                     f x          ≡⟨ sym (f-g (f x)) ⟩
                     f (g (f x))  ≡⟨ cong f eq ⟩
                     f (g (f y))  ≡⟨ f-g (f y) ⟩∎
                     f y          ∎))
        public

      opaque
        unfolding _/ᴱ-cong-∥∥ᴱ_

        -- A variant of ≃[]≡[]′.

        @0 ≃[]≡[]″ :
          (∀ {x y} → R x y ≃ (f x ≡ f y)) →
          R x y ≃ _≡_ {A = A /ᴱ R} [ x ] [ y ]
        ≃[]≡[]″ {R} {x} {y} R≃ =
          R x y                                         ↝⟨ R≃ ⟩
          f x ≡ f y                                     ↝⟨ ≃[]≡[]′ ⟩
          _≡_ {A = A /ᴱ λ x y → f x ≡ f y} [ x ] [ y ]  ↝⟨ inverse (Eq.≃-≡ equiv) ⟩
          _≃_.to equiv [ x ] ≡ _≃_.to equiv [ y ]       ↝⟨ ≡⇒↝ _ (cong₂ _≡_ rec-[] rec-[]) ⟩□
          _≡_ {A = A /ᴱ R} [ x ] [ y ]                  □
          where
          equiv : (A /ᴱ λ x y → f x ≡ f y) ≃ A /ᴱ R
          equiv =
            F.id /ᴱ-cong-∥∥ᴱ λ _ _ →
              Tr.∥∥ᴱ-cong (_≃_.logical-equivalence (inverse R≃))

    --------------------------------------------------------------------
    -- Decidable erased equality

    opaque

      -- If R is a weakly effective equivalence relation and it is
      -- decidable (with erased proofs) whether R holds, then erased
      -- equality is decidable for A /ᴱ R (assuming erased function
      -- extensionality).

      decidable-erased-equality′ :
        {A : Type a} {@0 R : A → A → Type r} →
        @0 Extensionality (a ⊔ r) lzero →
        @0 Weakly-effective R →
        @0 Is-equivalence-relation R →
        (∀ x y → Dec-Erased (R x y)) →
        Decidable-erased-equality (A /ᴱ R)
      decidable-erased-equality′ ext eff equiv dec =
        elim-prop₂ _
          (λ _ _ → BC.Is-proposition-Dec-Erased ext /ᴱ-is-set)
          (λ x y →
             Tr.Dec-Erased-map-∥∥ᴱ
               (_≃_.logical-equivalence (∥∥ᴱ≃[]≡[] eff equiv))
               (dec x y))

    opaque

      -- If R is an effective, propositional equivalence relation and
      -- it is decidable (with erased proofs) whether R holds, then
      -- erased equality is decidable for A /ᴱ R (assuming erased
      -- function extensionality).

      decidable-erased-equality :
        {A : Type a} {@0 R : A → A → Type r} →
        @0 Extensionality (a ⊔ r) lzero →
        @0 Effective R →
        @0 Is-equivalence-relation R →
        @0 (∀ {x y} → Is-proposition (R x y)) →
        (∀ x y → Dec-Erased (R x y)) →
        Decidable-erased-equality (A /ᴱ R)
      decidable-erased-equality ext eff equiv prop dec =
        decidable-erased-equality′ ext
          (Effective→Weakly-effective prop eff) equiv dec

    --------------------------------------------------------------------
    -- Other properties

    opaque

      -- [_] is surjective with erased proofs.

      Surjectiveᴱ-[] : Surjectiveᴱ ([_] {R = R})
      Surjectiveᴱ-[] = elim-prop λ where
        .[]ʳ x             → ∣ x , Er.[ refl _ ] ∣
        .is-propositionʳ _ → Tr.truncation-is-proposition

    opaque

      -- Quotienting by the propositional truncation of a relation is
      -- equivalent to quotienting by the relation itself.

      /ᴱ-∥∥ᴱ≃/ᴱ : A /ᴱ (λ x y → ∥ R x y ∥ᴱ) ≃ A /ᴱ R
      /ᴱ-∥∥ᴱ≃/ᴱ {R} = F.id /ᴱ-cong-∥∥ᴱ λ x y →
        ∥ ∥ R x y ∥ᴱ ∥ᴱ  ↔⟨ Tr.flatten ⟩□
        ∥ R x y ∥ᴱ       □

    opaque

      -- Quotienting with a trivial relation amounts to the same thing
      -- as using the propositional truncation operator.

      /ᴱtrivial≃∥∥ᴱ :
        {A : Type a} {@0 R : A → A → Type r} →
        @0 (∀ x y → R x y) →
        A /ᴱ R ≃ ∥ A ∥ᴱ
      /ᴱtrivial≃∥∥ᴱ trivial =
        Eq.↔→≃
          (rec-prop λ where
             .[]ʳ             → ∣_∣
             .is-propositionʳ → Tr.truncation-is-proposition)
          (Tr.rec λ where
             .Tr.∣∣ʳ                        → [_]
             .Tr.truncation-is-propositionʳ →
               elim-prop₂ _ (λ _ _ → /ᴱ-is-set)
                 λ x y → []-respects-relation (trivial x y))
          (Tr.elim λ where
             .Tr.∣∣ʳ _ →
               trans (cong (rec-prop _) Tr.rec-∣∣) rec-prop-[]
             .Tr.truncation-is-propositionʳ _ →
               ⇒≡ 1 Tr.truncation-is-proposition)
          (elim-prop λ where
             .[]ʳ _ →
               trans (cong (Tr.rec _) rec-prop-[]) Tr.rec-∣∣
             .is-propositionʳ _ →
               /ᴱ-is-set)

    --------------------------------------------------------------------
    -- A property related to ∥_∥ᴱ, proved using _/ᴱ_

    opaque

      -- Having a constant function (with an erased proof of
      -- constancy) into a set is equivalent to having a function from
      -- a propositionally truncated type into the set.
      --
      -- The statement of this result is adapted from that of
      -- Proposition 2.2 in "The General Universal Property of the
      -- Propositional Truncation" by Kraus.
      --
      -- This proof can be compared to
      -- Truncationᴱ.Σ→Erased-Constant≃ᴱ∥∥ᴱ→.

      Σ→Erased-Constant≃ᴱ∥∥ᴱ→ :
        {A : Type a} {B : Type b} →
        @0 Extensionality a (a ⊔ b) →
        @0 Is-set B →
        (∃ λ (f : A → B) → Erased (Constant f)) ≃ᴱ (∥ A ∥ᴱ → B)
      Σ→Erased-Constant≃ᴱ∥∥ᴱ→ {a} {b} {A} {B} ext B-set =
        (∃ λ (f : A → B) → Erased (Constant f))  ↝⟨ lemma ⟩
        (A /ᴱ (λ _ _ → ⊤) → B)                   ↝⟨ →-cong₁ Er.[ extᵃᵇ ] (/ᴱtrivial≃∥∥ᴱ _) ⟩□
        (∥ A ∥ᴱ → B)                             □
        where
        @0 extᵃᵇ : Extensionality a b
        extᵃᵇ = lower-extensionality lzero a ext

        lemma :
          (∃ λ (f : A → B) → Erased (Constant f)) ≃ᴱ
          (A /ᴱ (λ _ _ → ⊤) → B)
        lemma =
          EEq.↔→≃ᴱ
            (λ (f , Er.[ c ]) → rec λ where
               .[]ʳ                     → f
               .[]-respects-relationʳ _ → c _ _
               .is-setʳ                 → B-set)
            (λ f →
               f ∘ [_] ,
               Er.[ (λ _ _ → cong f ([]-respects-relation _)) ])
            (λ f → apply-ext extᵃᵇ $ elim λ where
               .[]ʳ _                   → rec-[]
               .[]-respects-relationʳ _ → B-set _ _
               .is-setʳ _               → mono₁ 2 B-set)
            (λ _ →
               Σ-≡,≡→≡
                 (apply-ext extᵃᵇ (λ _ → rec-[]))
                 (BC.H-level-Erased 1
                    (Π-closure ext   1 λ _ →
                     Π-closure extᵃᵇ 1 λ _ →
                     B-set)
                    _ _))

    opaque
      unfolding Σ→Erased-Constant≃ᴱ∥∥ᴱ→ /ᴱtrivial≃∥∥ᴱ

      -- The left-to-right direction of Σ→Erased-Constant≃ᴱ∥∥ᴱ→
      -- computes in the "right" way.

      to-Σ→Erased-Constant≃ᴱ∥∥ᴱ→ :
        {A : Type a} {B : Type b}
        {@0 ext : Extensionality a (a ⊔ b)} {@0 B-set : Is-set B}
        {f : ∃ λ (f : A → B) → Erased (Constant f)} {x : A} →
        _≃ᴱ_.to (Σ→Erased-Constant≃ᴱ∥∥ᴱ→ ext B-set) f ∣ x ∣ ≡ f .proj₁ x
      to-Σ→Erased-Constant≃ᴱ∥∥ᴱ→ =
        trans (cong (rec _) Tr.rec-∣∣) rec-[]

    opaque
      unfolding Σ→Erased-Constant≃ᴱ∥∥ᴱ→ /ᴱtrivial≃∥∥ᴱ

      -- The right-to-left direction of Σ→Erased-Constant≃ᴱ∥∥ᴱ→
      -- computes in the "right" way.

      from-Σ→Erased-Constant≃ᴱ∥∥ᴱ→ :
        {A : Type a} {B : Type b}
        {@0 ext : Extensionality a (a ⊔ b)} {@0 B-set : Is-set B}
        {f : ∥ A ∥ᴱ → B} {x : A} →
        _≃ᴱ_.from (Σ→Erased-Constant≃ᴱ∥∥ᴱ→ ext B-set) f .proj₁ x ≡
        f ∣ x ∣
      from-Σ→Erased-Constant≃ᴱ∥∥ᴱ→ {f} =
        cong f rec-prop-[]

  -- The module Truncation can be instantiated with the truncation
  -- operator defined above.

  module Truncation-/ᴱ = Truncation truncation

  -- Some results that do not refer to the truncation operator are
  -- re-exported.

  open Truncation-/ᴱ public
    using (≃[]≡[]; decidable-erased-equality)

  open Truncation-/ᴱ.Propositional-extensionality public
    using (effective)

  ----------------------------------------------------------------------
  -- Preservation lemmas

  -- See also the module Truncation above.

  opaque
    unfolding Truncation-/ᴱ._/ᴱ-map-∥∥ᴱ_

    -- A unary preservation lemma for functions.

    infix 5 _/ᴱ-map_

    _/ᴱ-map_ :
      (A₁→A₂ : A₁ → A₂) →
      @0 (∀ x y → R₁ x y → R₂ (A₁→A₂ x) (A₁→A₂ y)) →
      A₁ /ᴱ R₁ → A₂ /ᴱ R₂
    _/ᴱ-map_ {R₁} {R₂} A₁→A₂ R₁→R₂ =
      Truncation-/ᴱ._/ᴱ-map-∥∥ᴱ_ A₁→A₂ (λ x y → T.∥∥ᴱ-map (R₁→R₂ x y))

  opaque
    unfolding _/ᴱ-map_

    -- A binary preservation lemma for functions.

    /ᴱ-zip :
      {A₁ : Type a₁} {A₂ : Type a₂} {A₃ : Type a₃}
      {@0 R₁ : A₁ → A₁ → Type r₁}
      {@0 R₂ : A₂ → A₂ → Type r₂} →
      {@0 R₃ : A₃ → A₃ → Type r₃} →
      (f : A₁ → A₂ → A₃) →
      @0 (∀ {x} → R₁ x x) →
      @0 (∀ {x} → R₂ x x) →
      @0 (∀ {u v x y} → R₁ u v → R₂ x y → R₃ (f u x) (f v y)) →
      A₁ /ᴱ R₁ → A₂ /ᴱ R₂ → A₃ /ᴱ R₃
    /ᴱ-zip f r₁ r₂ r₃ =
      rec₂ /ᴱ-is-set r₁ r₂ (λ x y → [ f x y ])
        (λ x y → []-respects-relation (r₃ x y))

  opaque
    unfolding Truncation-/ᴱ./ᴱ-cong-∥∥ᴱ-⇔

    -- A unary preservation lemma for logical equivalences.

    /ᴱ-cong-⇔ :
      (A₁⇔A₂ : A₁ ⇔ A₂) →
      @0 (∀ x y → R₁ x y → R₂ (_⇔_.to   A₁⇔A₂ x) (_⇔_.to   A₁⇔A₂ y)) →
      @0 (∀ x y → R₂ x y → R₁ (_⇔_.from A₁⇔A₂ x) (_⇔_.from A₁⇔A₂ y)) →
      A₁ /ᴱ R₁ ⇔ A₂ /ᴱ R₂
    /ᴱ-cong-⇔ A₁⇔A₂ R₁→R₂ R₂→R₁ =
      Truncation-/ᴱ./ᴱ-cong-∥∥ᴱ-⇔ A₁⇔A₂ (λ x y → T.∥∥ᴱ-map (R₁→R₂ x y))
        (λ x y → T.∥∥ᴱ-map (R₂→R₁ x y))

  opaque
    unfolding Truncation-/ᴱ._/ᴱ-cong-∥∥ᴱ-↠_

    -- Two preservation lemmas for split surjections.

    infix 5 _/ᴱ-cong-↠_

    _/ᴱ-cong-↠_ :
      (A₁↠A₂ : A₁ ↠ A₂) →
      @0 (∀ x y → R₁ x y ⇔ R₂ (_↠_.to A₁↠A₂ x) (_↠_.to A₁↠A₂ y)) →
      A₁ /ᴱ R₁ ↠ A₂ /ᴱ R₂
    A₁↠A₂ /ᴱ-cong-↠ R₁⇔R₂ =
      A₁↠A₂ Truncation-/ᴱ./ᴱ-cong-∥∥ᴱ-↠
        (λ x y → _≃ᴱ_.logical-equivalence (T.∥∥ᴱ-cong-⇔ (R₁⇔R₂ x y)))

  opaque
    unfolding Truncation-/ᴱ._/ᴱ-cong-∥∥ᴱ_

    -- A unary preservation lemma for isomorphisms.

    infix 5 _/ᴱ-cong_

    _/ᴱ-cong_ :
      {A₁ : Type a₁} {A₂ : Type a₂}
      {@0 R₁ : A₁ → A₁ → Type r₁}
      {@0 R₂ : A₂ → A₂ → Type r₂} →
      (A₁↔A₂ : A₁ ↔[ k ] A₂) →
      @0 (∀ x y →
          R₁ x y ⇔
          R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y)) →
      A₁ /ᴱ R₁ ↔[ k ] A₂ /ᴱ R₂
    _/ᴱ-cong_ A₁↔A₂ R₁⇔R₂ =
      A₁↔A₂ Truncation-/ᴱ./ᴱ-cong-∥∥ᴱ
        (λ x y → _≃ᴱ_.logical-equivalence (T.∥∥ᴱ-cong-⇔ (R₁⇔R₂ x y)))

  ----------------------------------------------------------------------
  -- A property

  opaque

    -- Quotienting with a relation that is contained in equality
    -- amounts to the same thing as not quotienting at all (for a
    -- set).
    --
    -- The generalisation from "equality" to "a relation that is
    -- contained in equality" is based on a suggestion from Andreas
    -- Abel.

    /ᴱ≡≃ : @0 (∀ {x y} → R x y → x ≡ y) → @0 Is-set A → A /ᴱ R ≃ A
    /ᴱ≡≃ R⊆≡ A-set =
      Eq.↔→≃
        (rec λ where
           .[]ʳ                   → id
           .[]-respects-relationʳ → R⊆≡
           .is-setʳ               → A-set)
        [_]
        (λ _ → rec-[])
        (elim-prop λ where
           .[]ʳ _             → cong [_] rec-[]
           .is-propositionʳ _ → /ᴱ-is-set)

  ------------------------------------------------------------------------
  -- Various type formers commute with quotients

  opaque

    -- The quotient type ⊤ /ᴱ R is equivalent to ⊤.

    ⊤/ᴱ : ⊤ /ᴱ R ≃ ⊤
    ⊤/ᴱ = Eq.↔→≃
      _
      [_]
      refl
      (elim-prop λ where
         .is-propositionʳ _ → /ᴱ-is-set
         .[]ʳ _             → refl _)

  opaque

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
         .is-propositionʳ → ⊥-elim {ℓ = lzero} ∘ rec-prop λ where
           .[]ʳ ()
           .is-propositionʳ → ⊥-propositional)

  opaque

    -- _⊎_ commutes with quotients.

    ⊎/ᴱ :
      {@0 R₁ : A₁ → A₁ → Type r} {@0 R₂ : A₂ → A₂ → Type r} →
      (A₁ ⊎ A₂) /ᴱ (R₁ ⊎ᴾ R₂) ≃ (A₁ /ᴱ R₁ ⊎ A₂ /ᴱ R₂)
    ⊎/ᴱ = Eq.↔→≃
      (rec λ where
         .[]ʳ →
           ⊎-map [_] [_]
         .is-setʳ →
           ⊎-closure 0 /ᴱ-is-set /ᴱ-is-set
         .[]-respects-relationʳ {x = inj₁ _} {y = inj₁ _} →
           cong inj₁ ∘ []-respects-relation
         .[]-respects-relationʳ {x = inj₂ _} {y = inj₂ _} →
           cong inj₂ ∘ []-respects-relation)
      P.[ (rec λ where
             .[]ʳ x                 → [ inj₁ x ]
             .[]-respects-relationʳ → []-respects-relation
             .is-setʳ               → /ᴱ-is-set)
        , (rec λ where
             .[]ʳ x                 → [ inj₂ x ]
             .[]-respects-relationʳ → []-respects-relation
             .is-setʳ               → /ᴱ-is-set)
        ]
      P.[ (elim-prop λ where
             .[]ʳ _             → trans (cong (rec _) rec-[]) rec-[]
             .is-propositionʳ _ → ⊎-closure 0 /ᴱ-is-set /ᴱ-is-set)
        , (elim-prop λ where
             .[]ʳ _             → trans (cong (rec _) rec-[]) rec-[]
             .is-propositionʳ _ → ⊎-closure 0 /ᴱ-is-set /ᴱ-is-set)
        ]
      (elim-prop λ where
         .[]ʳ →
           P.[ (λ _ → trans (cong P.[ _ , _ ] rec-[]) rec-[])
             , (λ _ → trans (cong P.[ _ , _ ] rec-[]) rec-[])
             ]
         .is-propositionʳ _ →
           /ᴱ-is-set)

  opaque
    unfolding ⊎/ᴱ

    -- Maybe commutes with quotients.
    --
    -- Chapman, Uustalu and Veltri mention a similar result in
    -- "Quotienting the Delay Monad by Weak Bisimilarity".

    Maybe/ᴱ : Maybe A /ᴱ Maybeᴾ R ≃ Maybe (A /ᴱ R)
    Maybe/ᴱ {A} {R} =
      Maybe A /ᴱ Maybeᴾ R    ↝⟨ ⊎/ᴱ ⟩
      ⊤ /ᴱ Trivial ⊎ A /ᴱ R  ↔⟨ ⊤/ᴱ ⊎-cong F.id ⟩
      ⊤ ⊎ A /ᴱ R             ↔⟨⟩
      Maybe (A /ᴱ R)         □

  opaque
    unfolding Maybe/ᴱ

    -- A simplification lemma for Maybe/ᴱ.

    Maybe/ᴱ-[] :
      {A : Type a} {@0 R : A → A → Type r} →
      Extensionality a (a ⊔ r) →
      _≃_.to (Maybe/ᴱ {R = R}) ∘ [_] ≡ ⊎-map id ([_] {R = R})
    Maybe/ᴱ-[] ext = apply-ext ext λ x →
      _≃_.to Maybe/ᴱ [ x ]          ≡⟨ cong P.[ _ , _ ] rec-[] ⟩
      ⊎-map _ id (⊎-map [_] [_] x)  ≡⟨ sym $ ⊎-map-∘ x ⟩∎
      ⊎-map id [_] x                ∎

  opaque
    unfolding _/ᴱ-map_

    -- Cartesian products commute with quotients, assuming that the
    -- two binary relations involved in the statement are reflexive.

    ×/ᴱ :
      {A₁ : Type a₁} {A₂ : Type a₂}
      {@0 R₁ : A₁ → A₁ → Type r₁} {@0 R₂ : A₂ → A₂ → Type r₂} →
      @0 (∀ {x} → R₁ x x) →
      @0 (∀ {x} → R₂ x x) →
      (A₁ × A₂) /ᴱ (R₁ ×ᴾ R₂) ≃ (A₁ /ᴱ R₁ × A₂ /ᴱ R₂)
    ×/ᴱ {R₁} {R₂} R₁-refl R₂-refl = Eq.↔→≃
      (rec λ where
         .is-setʳ →
           ×-closure 2 /ᴱ-is-set /ᴱ-is-set
         .[]ʳ →
           Σ-map [_] [_]
         .[]-respects-relationʳ {x = x₁ , x₂} {y = y₁ , y₂} →
           R₁ x₁ y₁ × R₂ x₂ y₂                    →⟨ Σ-map []-respects-relation []-respects-relation ⟩
           [ x₁ ] ≡ [ y₁ ] × [ x₂ ] ≡ [ y₂ ]      →⟨ uncurry (cong₂ _,_) ⟩□
           ([ x₁ ] , [ x₂ ]) ≡ ([ y₁ ] , [ y₂ ])  □)
      (uncurry $
       rec₂ /ᴱ-is-set R₁-refl R₂-refl (λ x y → [ (x , y) ])
         (λ r₁ r₂ → []-respects-relation (r₁ , r₂)))
      (uncurry $
       elim-prop₂ _ (λ _ _ → ×-closure 2 /ᴱ-is-set /ᴱ-is-set)
         (λ x y → trans (cong (rec _) rec₂-[]) rec-[]))
      (elim-prop λ where
         .is-propositionʳ _ → /ᴱ-is-set
         .[]ʳ _             →
           trans (cong (uncurry (rec₂ _ _ _ _ _)) rec-[]) rec₂-[])

  opaque

    -- The sigma type former commutes (kind of) with quotients,
    -- assuming that the second projections come from propositional
    -- types (as well as erased function extensionality).

    Σ/ᴱ :
      {A : Type a} {@0 R : A → A → Type r} {P : A /ᴱ R → Type p} →
      @0 Extensionality p (a ⊔ p ⊔ r) →
      @0 (∀ {x} → Is-proposition (P x)) →
      Σ (A /ᴱ R) P ≃ Σ A (P ∘ [_]) /ᴱ (R on proj₁)
    Σ/ᴱ {A} {R} {P} ext prop = Eq.↔→≃
      (uncurry $ elim λ where
         .is-setʳ _ →
           Π-closure ext 2 λ _ →
           /ᴱ-is-set
         .[]ʳ →
           curry [_]
         .[]-respects-relationʳ {x} {y} r → apply-ext ext λ P[y] →
           subst (λ x → P x → Σ A (P ∘ [_]) /ᴱ (R on proj₁))
             ([]-respects-relation r) (curry [_] x) P[y]          ≡⟨ subst-→-domain _ _ ⟩

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
         .[]ʳ _ →
           trans (cong (uncurry (elim _)) rec-[]) $
           cong (λ (f : _ → _) → f _) elim-[]
         .is-propositionʳ _ →
           /ᴱ-is-set)
      (uncurry $ elim-prop λ where
         .[]ʳ _ _ →
           trans (cong (λ (f : _ → _) → rec _ (f _)) elim-[]) rec-[]
         .is-propositionʳ _ →
           Π-closure ext 1 λ _ →
           Σ-closure 2 /ᴱ-is-set (λ _ → mono₁ 1 prop))

  private

    -- A lemma used below.

    to-Erased/ᴱ :
      {@0 A : Type a} {@0 R : A → A → Type r} →
      Erased A /ᴱ Erasedᴾ R → Erased (A /ᴱ R)
    to-Erased/ᴱ = rec λ where
      .is-setʳ →
        BC.H-level-Erased 2 /ᴱ-is-set
      .[]ʳ →
        Er.map [_]
      .[]-respects-relationʳ Er.[ Rxy ] →
        cong Er.[_]→ ([]-respects-relation Rxy)

  opaque

    -- Erased commutes with quotients if certain conditions hold.

    Erased/ᴱ :
      {@0 A : Type a} {@0 R : A → A → Type r} →
      []-cong-axiomatisation (a ⊔ r) →
      @0 Is-set A →
      @0 (∀ {x y} → R x y → x ≡ y) →
      Erased A /ᴱ Erasedᴾ R ≃ Erased (A /ᴱ R)
    Erased/ᴱ {r} {A} {R} ax set R→≡ = Eq.↔→≃
      to-Erased/ᴱ
      ([_] ∘ Er.map from)
      (λ { Er.[ _ ] →
           trans rec-[] $
           Er.[]-cong₁.[]-cong ax
             Er.[ elim-prop {P = λ x → [ from x ] ≡ x}
                    (λ @0 where
                       .is-propositionʳ _ → /ᴱ-is-set
                       .[]ʳ _             → cong [_] rec-[])
                    _
                ] })
      (elim-prop λ where
         .is-propositionʳ _ →
           /ᴱ-is-set
         .[]ʳ Er.[ _ ] →
           cong [_] $
           Er.[]-cong₁.[]-cong (Er.lower-[]-cong-axiomatisation r ax)
             Er.[ trans (cong (rec _ ∘ Er.erased) rec-[]) rec-[] ])
      where
      @0 from : A /ᴱ R → A
      from = rec λ where
        .is-setʳ               → set
        .[]ʳ                   → id
        .[]-respects-relationʳ → R→≡

  opaque
    unfolding Erased/ᴱ

    -- Erased commutes with quotients, up to _≃ᴱ_, if certain
    -- conditions hold.

    Erased/ᴱ-≃ᴱ :
      {@0 A : Type a} {@0 R : A → A → Type r} →
      @0 Is-set A →
      @0 (∀ {x y} → R x y → x ≡ y) →
      Erased A /ᴱ Erasedᴾ R ≃ᴱ Erased (A /ᴱ R)
    Erased/ᴱ-≃ᴱ set R→≡ =
      EEq.[≃]→≃ᴱ
        (EEq.[proofs]
           (Erased/ᴱ Er.erased-instance-of-[]-cong-axiomatisation set
              R→≡))

  opaque
    unfolding /ᴱ-zip

    -- List commutes with quotients in a certain sense, given a
    -- certain assumption.

    List/ᴱ :
      {@0 R : A → A → Type r} →
      @0 (∀ {x} → R x x) →
      List A /ᴱ Listᴾ R ≃ List (A /ᴱ R)
    List/ᴱ {A} {R} r = Eq.↔→≃ to from to-from from-to
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
        .[]ʳ _ →
          trans (cong (rec _) rec₂-[]) $
          trans rec-[] $
          cong (_∷_ _) (sym rec-[])

      to-from : (xs : List (A /ᴱ R)) → to (from xs) ≡ xs
      to-from []       = rec-[]
      to-from (x ∷ xs) =
        flip (elim-prop {P = λ x → to (from (x ∷ xs)) ≡ x ∷ xs}) x
          λ where
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
        cons [ x ] [ xs ]                 ≡⟨ rec₂-[] ⟩∎
        [ x ∷ xs ]                        ∎

      from-to : (xs : List A /ᴱ Listᴾ R) → from (to xs) ≡ xs
      from-to = elim-prop λ where
        .is-propositionʳ _ → /ᴱ-is-set
        .[]ʳ _             → trans (cong from rec-[]) (from-map-[] _)
