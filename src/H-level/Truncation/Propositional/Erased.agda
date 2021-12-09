------------------------------------------------------------------------
-- A variant of the propositional truncation operator with an erased
-- truncation constructor
------------------------------------------------------------------------

-- Partly following the HoTT book, but adapted for erasure.

{-# OPTIONS --erased-cubical --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the propositional truncation
-- operator uses path equality, but the supplied notion of equality is
-- used for many other things.

import Equality.Path as P

module H-level.Truncation.Propositional.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude as P
open import Logical-equivalence using (_⇔_)

open import Accessibility equality-with-J as A using (Acc; Well-founded)
open import Bijection equality-with-J as Bijection using (_↔_)
import Colimit.Sequential.Very-erased eq as C
open import Embedding equality-with-J as Emb using (Is-embedding)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased equality-with-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages equality-with-J
  as ECP using (Contractibleᴱ; _⁻¹ᴱ_)
open import Equivalence.Path-split equality-with-J as PS
  using (Is-∞-extendable-along-[_])
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as Er
  using (Erased; [_]; erased; Very-stableᴱ-≡; Erased-singleton)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹-out-^)
import H-level.Truncation.Propositional.Non-recursive.Erased eq as N
open import Modality.Basics equality-with-J
open import Monad equality-with-J
import Nat equality-with-J as Nat
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J as S
  using (_↠_; Split-surjective)

private
  variable
    a b ℓ p r         : Level
    A A₁ A₂ B B₁ B₂ C : Type a
    P Q               : A → Type p
    R                 : A → A → Type r
    f g k x y         : A

------------------------------------------------------------------------
-- The type former

-- A propositional truncation operator with an erased higher
-- constructor.

data ∥_∥ᴱ (A : Type a) : Type a where
  ∣_∣                           : A → ∥ A ∥ᴱ
  @0 truncation-is-propositionᴾ : P.Is-proposition ∥ A ∥ᴱ

-- The truncation produces propositions (in erased contexts).

@0 truncation-is-proposition : Is-proposition ∥ A ∥ᴱ
truncation-is-proposition =
  _↔_.from (H-level↔H-level 1) truncation-is-propositionᴾ

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ′ {A : Type a} (P : ∥ A ∥ᴱ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    @0 truncation-is-propositionʳ :
      (p : P x) (q : P y) →
      P.[ (λ i → P (truncation-is-propositionᴾ x y i)) ] p ≡ q

open Elimᴾ′ public

elimᴾ′ : Elimᴾ′ P → (x : ∥ A ∥ᴱ) → P x
elimᴾ′ {A = A} {P = P} e = helper
  where
  module E = Elimᴾ′ e

  helper : (x : ∥ A ∥ᴱ) → P x
  helper ∣ x ∣                              = E.∣∣ʳ x
  helper (truncation-is-propositionᴾ x y i) =
    E.truncation-is-propositionʳ (helper x) (helper y) i

-- A possibly more useful dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : ∥ A ∥ᴱ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    @0 truncation-is-propositionʳ :
      (x : ∥ A ∥ᴱ) → P.Is-proposition (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : ∥ A ∥ᴱ) → P x
elimᴾ e = elimᴾ′ λ where
    .∣∣ʳ                            → E.∣∣ʳ
    .truncation-is-propositionʳ _ _ →
      P.heterogeneous-irrelevance E.truncation-is-propositionʳ
  where
  module E = Elimᴾ e

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ                           : A → B
    @0 truncation-is-propositionʳ : P.Is-proposition B

open Recᴾ public

recᴾ : Recᴾ A B → ∥ A ∥ᴱ → B
recᴾ r = elimᴾ λ where
    .∣∣ʳ                          → R.∣∣ʳ
    .truncation-is-propositionʳ _ → R.truncation-is-propositionʳ
  where
  module R = Recᴾ r

-- A dependently typed eliminator.

record Elim {A : Type a} (P : ∥ A ∥ᴱ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    @0 truncation-is-propositionʳ :
      (x : ∥ A ∥ᴱ) → Is-proposition (P x)

open Elim public

elim : Elim P → (x : ∥ A ∥ᴱ) → P x
elim e = elimᴾ λ where
    .∣∣ʳ                        → E.∣∣ʳ
    .truncation-is-propositionʳ →
      _↔_.to (H-level↔H-level 1) ∘ E.truncation-is-propositionʳ
  where
  module E = Elim e

-- Primitive "recursion".

record Rec (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ                           : A → B
    @0 truncation-is-propositionʳ : Is-proposition B

open Rec public

rec : Rec A B → ∥ A ∥ᴱ → B
rec r = recᴾ λ where
    .∣∣ʳ                        → R.∣∣ʳ
    .truncation-is-propositionʳ →
      _↔_.to (H-level↔H-level 1) R.truncation-is-propositionʳ
  where
  module R = Rec r

------------------------------------------------------------------------
-- ∥_∥ᴱ is a modality

-- ∥_∥ᴱ and ∣_∣ form a modality, where a type A is modal if
-- Erased (Is-proposition A) holds.

∥∥ᴱ-modality : Modality ℓ
∥∥ᴱ-modality {ℓ = ℓ} = λ where
    .◯                      → ∥_∥ᴱ
    .η                      → ∣_∣
    .Is-modal A             → Erased (Is-proposition A)
    .Is-modal-propositional → λ ext →
                                Er.H-level-Erased 1
                                  (H-level-propositional ext 1)
    .Is-modal-◯             → [ truncation-is-proposition ]
    .Is-modal-respects-≃    → λ A≃B → Er.map (H-level-cong _ 1 A≃B)
    .extendable-along-η     → extendable
  where
  open Modality

  extendable :
    {A : Type ℓ} {P : ∥ A ∥ᴱ → Type ℓ} →
    (∀ x → Erased (Is-proposition (P x))) →
    Is-∞-extendable-along-[ ∣_∣ ] P
  extendable {A = A} {P = P} =
    (∀ x → Erased (Is-proposition (P x)))                  →⟨ (λ prop →
                                                                 _≃_.is-equivalence $
                                                                 Eq.↔→≃
                                                                   _
                                                                   (λ f → elim λ where
                                                                      .∣∣ʳ                          → f
                                                                      .truncation-is-propositionʳ _ → prop _ .erased)
                                                                   refl
                                                                   (λ f → ⟨ext⟩ $ elim λ where
                                                                      .∣∣ʳ _                        → refl _
                                                                      .truncation-is-propositionʳ _ → ⇒≡ 1 $ prop _ .erased)) ⟩
    Is-equivalence (λ (f : (x : ∥ A ∥ᴱ) → P x) → f ∘ ∣_∣)  ↔⟨ inverse $ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩□
    Is-∞-extendable-along-[ ∣_∣ ] P                        □

-- The modality is empty-modal.

∥∥ᴱ-empty-modal : Empty-modal (∥∥ᴱ-modality {ℓ = ℓ})
∥∥ᴱ-empty-modal = [ ⊥-propositional ]

-- The modality is not very modal.

¬-∥∥ᴱ-very-modal : ¬ Very-modal (∥∥ᴱ-modality {ℓ = ℓ})
¬-∥∥ᴱ-very-modal {ℓ = ℓ} =
  Very-modal (∥∥ᴱ-modality {ℓ = ℓ})                ↔⟨⟩
  ({A : Type ℓ} → ∥ Erased (Is-proposition A) ∥ᴱ)  →⟨ (λ hyp → hyp) ⟩
  ∥ Erased (Is-proposition (↑ ℓ Bool)) ∥ᴱ          →⟨ ◯-map (Er.map (⊥-elim ∘ ¬-Bool-propositional ∘ H-level-cong _ 1 Bijection.↑↔)) ⟩
  ∥ Erased ⊥ ∥ᴱ                                    →⟨ ◯-map (_↔_.to Er.Erased-⊥↔⊥) ⟩
  ∥ ⊥ ∥ᴱ                                           →⟨ ⊥-elim ∘ Is-modal→Stable ∥∥ᴱ-empty-modal ⟩□
  ⊥                                                □
  where
  open Modality (∥∥ᴱ-modality {ℓ = ℓ})

-- The modality is not accessibility-modal.

¬-∥∥ᴱ-accessibility-modal :
  ¬ Modality.Accessibility-modal (∥∥ᴱ-modality {ℓ = ℓ})
¬-∥∥ᴱ-accessibility-modal {ℓ = ℓ} acc =
  Er.Very-stable→Stable 0 Er.Very-stable-⊥
    [                          $⟨ A.Well-founded-ℕ ⟩
      Well-founded Nat._<_     →⟨ (λ wf → A.Well-founded-↑ _ (A.Well-founded-on wf)) ⟩
      Well-founded _<_         →⟨ (λ wf → elim λ where
                                     .∣∣ʳ n →
                                       acc .proj₁ (wf n)
                                     .truncation-is-propositionʳ _ →
                                       A.Acc-propositional ext) ⟩
      Well-founded _[ _<_ ]◯_  →⟨ A.<→¬-Well-founded cyclic ⟩□
      ⊥                        □
    ]
  where
  open Modality (∥∥ᴱ-modality {ℓ = ℓ})

  _<_ : ↑ ℓ ℕ → ↑ ℓ ℕ → Type ℓ
  lift m < lift n = ↑ ℓ (m Nat.< n)

  @0 cyclic : ∣ lift 0 ∣ [ _<_ ]◯ ∣ lift 0 ∣
  cyclic =
    ∣ lift 0
    , lift 1
    , truncation-is-proposition _ _
    , truncation-is-proposition _ _
    , lift (from-⊎ (1 Nat.≤? 1))
    ∣

-- The modality is accessibility-modal for propositional types and
-- relations.

Is-proposition→∥∥ᴱ-accessibility-modal :
  {@0 A : Type ℓ} {@0 _<_ : A → A → Type ℓ} →
  @0 Is-proposition A →
  @0 (∀ x y → Is-proposition (x < y)) →
  Modality.Accessibility-modal-for ∥∥ᴱ-modality _<_
Is-proposition→∥∥ᴱ-accessibility-modal {ℓ = ℓ} p₁ p₂ =
  Accessibility-modal-for-erasure-stable
    [ (
        (λ acc →
           Is-modal→Acc→Acc-[]◯-η
             [ p₁ ]
             (rec λ where
                .∣∣ʳ                        → id
                .truncation-is-propositionʳ → p₂ _ _)
             acc)
      , (rec λ where
           .∣∣ʳ                        → id
           .truncation-is-propositionʳ → A.Acc-propositional ext)
      )
    ]
  where
  open Modality (∥∥ᴱ-modality {ℓ = ℓ})

-- If the modality is accessibility-modal for all relations for a
-- type A, then all values of type A are not not equal.

∥∥ᴱ-accessibility-modal→¬¬≡ :
  {x y : A} →
  ({_<_ : A → A → Type ℓ} →
   Modality.Accessibility-modal-for ∥∥ᴱ-modality _<_) →
  ¬ ¬ x ≡ y
∥∥ᴱ-accessibility-modal→¬¬≡
  {ℓ = ℓ} {A = A} {x = x} {y = y} acc x≢y =
                         $⟨ (A.acc λ _ x≡y → ⊥-elim $ x≢y x≡y) ⟩
  Acc _<_ x              →⟨ Acc-[]◯-η acc ⟩
  Acc _[ _<_ ]◯_ ∣ x ∣   →⟨ (λ acc →
                               A.Acc-map
                                 (λ _ → ∣ y , y
                                        , truncation-is-proposition _ _
                                        , truncation-is-proposition _ _
                                        , refl _
                                        ∣)
                                 acc) ⟩
  Acc (λ _ _ → ⊤) ∣ x ∣  →⟨ A.<→¬-Acc _ ⟩□
  ⊥                      □
  where
  open Modality (∥∥ᴱ-modality {ℓ = ℓ})

  _<_ : A → A → Type ℓ
  _ < z = z ≡ y

------------------------------------------------------------------------
-- Conversion functions

-- ∥_∥ᴱ is pointwise equivalent to N.∥_∥ᴱ.

∥∥ᴱ≃∥∥ᴱ : ∥ A ∥ᴱ ≃ N.∥ A ∥ᴱ
∥∥ᴱ≃∥∥ᴱ = Eq.↔→≃
  (rec λ where
     .∣∣ʳ                        → N.∣_∣
     .truncation-is-propositionʳ → N.∥∥ᴱ-proposition)
  (N.elim λ where
     .N.∣∣ʳ               → ∣_∣
     .N.is-propositionʳ _ → truncation-is-proposition)
  (N.elim λ where
     .N.∣∣ʳ _             → refl _
     .N.is-propositionʳ _ → mono₁ 1 N.∥∥ᴱ-proposition)
  (elim λ where
     .∣∣ʳ _                        → refl _
     .truncation-is-propositionʳ _ → mono₁ 1 truncation-is-proposition)

------------------------------------------------------------------------
-- Some preservation lemmas and related results

-- A map function.

∥∥ᴱ-map : (A → B) → ∥ A ∥ᴱ → ∥ B ∥ᴱ
∥∥ᴱ-map f = rec λ where
  .∣∣ʳ                        → ∣_∣ ∘ f
  .truncation-is-propositionʳ → truncation-is-proposition

mutual

  -- If A and B are logically equivalent, then there is an equivalence
  -- with erased proofs between ∥ A ∥ᴱ and ∥ B ∥ᴱ.

  ∥∥ᴱ-cong-⇔ : A ⇔ B → ∥ A ∥ᴱ ≃ᴱ ∥ B ∥ᴱ
  ∥∥ᴱ-cong-⇔ A⇔B = ∥∥ᴱ-cong-⇔′ (∣_∣ ∘ _⇔_.to A⇔B) (∣_∣ ∘ _⇔_.from A⇔B)

  -- A variant of the previous result.

  ∥∥ᴱ-cong-⇔′ : (A → ∥ B ∥ᴱ) → (B → ∥ A ∥ᴱ) → ∥ A ∥ᴱ ≃ᴱ ∥ B ∥ᴱ
  ∥∥ᴱ-cong-⇔′ A→∥B∥ B→∥A∥ = EEq.⇔→≃ᴱ
    truncation-is-proposition
    truncation-is-proposition
    (rec λ where
       .∣∣ʳ                        → A→∥B∥
       .truncation-is-propositionʳ → truncation-is-proposition)
    (rec λ where
       .∣∣ʳ                        → B→∥A∥
       .truncation-is-propositionʳ → truncation-is-proposition)

-- If there is a split surjection from A to B, then there is a split
-- surjection from ∥ A ∥ᴱ to ∥ B ∥ᴱ.

∥∥ᴱ-cong-↠ : A ↠ B → ∥ A ∥ᴱ ↠ ∥ B ∥ᴱ
∥∥ᴱ-cong-↠ A↠B = record
  { logical-equivalence = record
    { to   = ∥∥ᴱ-map (_↠_.to   A↠B)
    ; from = ∥∥ᴱ-map (_↠_.from A↠B)
    }
  ; right-inverse-of = elim λ where
      .∣∣ʳ x →
        ∣ _↠_.to A↠B (_↠_.from A↠B x) ∣  ≡⟨ cong ∣_∣ (_↠_.right-inverse-of A↠B x) ⟩∎
        ∣ x ∣                            ∎
      .truncation-is-propositionʳ _ →
        mono₁ 1 truncation-is-proposition
  }

private

  ∥∥ᴱ-cong-↔ : A ↔ B → ∥ A ∥ᴱ ↔ ∥ B ∥ᴱ
  ∥∥ᴱ-cong-↔ A↔B = record
    { surjection      = ∥∥ᴱ-cong-↠ (_↔_.surjection A↔B)
    ; left-inverse-of = elim λ where
        .∣∣ʳ x →
          ∣ _↔_.from A↔B (_↔_.to A↔B x) ∣  ≡⟨ cong ∣_∣ (_↔_.left-inverse-of A↔B x) ⟩∎
          ∣ x ∣                            ∎
        .truncation-is-propositionʳ _ →
          mono₁ 1 truncation-is-proposition
    }

-- The truncation operator preserves "symmetric" functions.

∥∥ᴱ-cong : A ↝[ ⌊ k ⌋-sym ] B → ∥ A ∥ᴱ ↝[ ⌊ k ⌋-sym ] ∥ B ∥ᴱ
∥∥ᴱ-cong {k = logical-equivalence} = _≃ᴱ_.logical-equivalence ∘
                                     ∥∥ᴱ-cong-⇔
∥∥ᴱ-cong {k = bijection}           = ∥∥ᴱ-cong-↔
∥∥ᴱ-cong {k = equivalence}         = from-isomorphism ∘ ∥∥ᴱ-cong-↔ ∘
                                     from-isomorphism
∥∥ᴱ-cong {k = equivalenceᴱ}        = ∥∥ᴱ-cong-⇔ ∘
                                     _≃ᴱ_.logical-equivalence

------------------------------------------------------------------------
-- Some bijections/erased equivalences

-- If the underlying type is a proposition, then truncations of the
-- type are isomorphic to the type itself.

∥∥ᴱ↔ : @0 Is-proposition A → ∥ A ∥ᴱ ↔ A
∥∥ᴱ↔ A-prop = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec λ where
          .∣∣ʳ                        → id
          .truncation-is-propositionʳ → A-prop
      ; from = ∣_∣
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = elim λ where
      .∣∣ʳ _                        → refl _
      .truncation-is-propositionʳ _ → mono₁ 1 truncation-is-proposition
  }

-- If A is merely inhabited, then the truncation of A is equivalent
-- (with erased proofs) to the unit type.

inhabited⇒∥∥ᴱ≃ᴱ⊤ : ∥ A ∥ᴱ → ∥ A ∥ᴱ ≃ᴱ ⊤
inhabited⇒∥∥ᴱ≃ᴱ⊤ ∥a∥ =
  EEq.inhabited→Is-proposition→≃ᴱ⊤ ∥a∥ truncation-is-proposition

-- If A is not inhabited, then the propositional truncation of A is
-- isomorphic to the empty type.

not-inhabited⇒∥∥ᴱ↔⊥ : ¬ A → ∥ A ∥ᴱ ↔ ⊥ {ℓ = ℓ}
not-inhabited⇒∥∥ᴱ↔⊥ {A = A} =
  ¬ A         ↝⟨ (λ ¬a → rec λ where
                           .∣∣ʳ                        → ¬a
                           .truncation-is-propositionʳ → ⊥-propositional) ⟩
  ¬ ∥ A ∥ᴱ    ↝⟨ inverse ∘ Bijection.⊥↔uninhabited ⟩□
  ∥ A ∥ᴱ ↔ ⊥  □

-- The negation of the truncation of A is isomorphic to the negation
-- of A.

¬∥∥ᴱ↔¬ : ¬ ∥ A ∥ᴱ ↔ ¬ A
¬∥∥ᴱ↔¬ {A = A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → f ∘ ∣_∣
      ; from = λ ¬A → rec λ where
                        .∣∣ʳ                        → ¬A
                        .truncation-is-propositionʳ → ⊥-propositional
      }
    ; right-inverse-of = λ _ → ¬-propositional ext _ _
    }
  ; left-inverse-of = λ _ → ¬-propositional ext _ _
  }

-- A form of idempotence for binary sums.

idempotent : ∥ A ⊎ A ∥ᴱ ≃ᴱ ∥ A ∥ᴱ
idempotent = ∥∥ᴱ-cong-⇔ (record { to = P.[ id , id ]; from = inj₁ })

------------------------------------------------------------------------
-- The universal property, and some related results

mutual

  -- The propositional truncation operator's universal property.
  --
  -- See also Quotient.Erased.Σ→Erased-Constant≃∥∥ᴱ→.

  universal-property :
    @0 Is-proposition B →
    (∥ A ∥ᴱ → B) ≃ (A → B)
  universal-property B-prop = universal-property-Π (λ _ → B-prop)

  -- A generalisation of the universal property.

  universal-property-Π :
    @0 (∀ x → Is-proposition (P x)) →
    ((x : ∥ A ∥ᴱ) → P x) ≃ ((x : A) → P ∣ x ∣)
  universal-property-Π {A = A} {P = P} P-prop =
    ((x : ∥ A ∥ᴱ) → P x)      ↝⟨ Eq.↔⇒≃ (record
                                   { surjection = record
                                     { logical-equivalence = record
                                       { to   = λ f → ∣ f ∘ ∣_∣ ∣
                                       ; from = rec λ where
                                           .∣∣ʳ f → elim λ where
                                             .∣∣ʳ                        → f
                                             .truncation-is-propositionʳ → P-prop
                                           .truncation-is-propositionʳ →
                                             Π-closure ext 1 λ _ → P-prop _
                                       }
                                     ; right-inverse-of = elim λ where
                                         .∣∣ʳ _                        → refl _
                                         .truncation-is-propositionʳ _ →
                                           mono₁ 1 truncation-is-proposition
                                     }
                                   ; left-inverse-of = λ f → ⟨ext⟩ $ elim λ where
                                       .∣∣ʳ _                        → refl _
                                       .truncation-is-propositionʳ _ →
                                         mono₁ 1 (P-prop _)
                                   }) ⟩
    ∥ ((x : A) → P ∣ x ∣) ∥ᴱ  ↔⟨ ∥∥ᴱ↔ (Π-closure ext 1 λ _ → P-prop _) ⟩□
    ((x : A) → P ∣ x ∣)       □

-- The universal property computes in the "right" way.

_ :
  (@0 B-prop : Is-proposition B)
  (f : ∥ A ∥ᴱ → B) →
  _≃_.to (universal-property B-prop) f ≡ f ∘ ∣_∣
_ = λ _ _ → refl _

_ :
  (@0 B-prop : Is-proposition B)
  (f : A → B) (x : A) →
  _≃_.from (universal-property B-prop) f ∣ x ∣ ≡ f x
_ = λ _ _ _ → refl _

-- Functions from ∥ A ∥ᴱ can be expressed as functions from A along
-- with some erased data.

∥∥ᴱ→≃ :
  (∥ A ∥ᴱ → B)
    ≃
  (∃ λ (f : A → B) →
     Erased (∃ λ (g : ∀ n → ∥ A ∥¹-out-^ (suc n) → B) →
               (∀ x → g zero O.∣ x ∣ ≡ f x) ×
               (∀ n x → g (suc n) O.∣ x ∣ ≡ g n x)))
∥∥ᴱ→≃ {A = A} {B = B} =
  (∥ A ∥ᴱ → B)                                           ↝⟨ →-cong ext ∥∥ᴱ≃∥∥ᴱ F.id ⟩

  (N.∥ A ∥ᴱ → B)                                         ↝⟨ C.universal-property ⟩□

  (∃ λ (f : A → B) →
     Erased (∃ λ (g : ∀ n → ∥ A ∥¹-out-^ (suc n) → B) →
               (∀ x → g zero O.∣ x ∣ ≡ f x) ×
               (∀ n x → g (suc n) O.∣ x ∣ ≡ g n x)))     □

-- A function of type (x : ∥ A ∥ᴱ) → P x, along with an erased proof
-- showing that the function is equal to some erased function, is
-- equivalent to a function of type (x : A) → P ∣ x ∣, along with an
-- erased equality proof.

Σ-Π-∥∥ᴱ-Erased-≡-≃ :
  {@0 g : (x : ∥ A ∥ᴱ) → P x} →
  (∃ λ (f : (x : ∥ A ∥ᴱ) → P x) → Erased (f ≡ g)) ≃
  (∃ λ (f : (x : A) → P ∣ x ∣) → Erased (f ≡ g ∘ ∣_∣))
Σ-Π-∥∥ᴱ-Erased-≡-≃ {A = A} {P = P} {g = g} =
  (∃ λ (f : (x : ∥ A ∥ᴱ) → P x) → Erased (f ≡ g))       ↝⟨ (Σ-cong lemma λ _ → Er.Erased-cong (inverse $ Eq.≃-≡ lemma)) ⟩

  (∃ λ (f : (x : N.∥ A ∥ᴱ) → P (_≃_.from ∥∥ᴱ≃∥∥ᴱ x)) →
     Erased (f ≡ g ∘ _≃_.from ∥∥ᴱ≃∥∥ᴱ))                 ↝⟨ N.Σ-Π-∥∥ᴱ-Erased-≡-≃ ⟩□

  (∃ λ (f : (x : A) → P ∣ x ∣) → Erased (f ≡ g ∘ ∣_∣))  □
  where
  lemma = Π-cong-contra ext (inverse ∥∥ᴱ≃∥∥ᴱ) λ _ → Eq.id

------------------------------------------------------------------------
-- Some results based on "Generalizations of Hedberg's Theorem" by
-- Kraus, Escardó, Coquand and Altenkirch

-- Types with constant endofunctions are "h-stable" (meaning that
-- "mere inhabitance" implies inhabitance).

constant-endofunction⇒h-stable :
  {f : A → A} → @0 Constant f → ∥ A ∥ᴱ → A
constant-endofunction⇒h-stable {A = A} {f = f} c =
  ∥ A ∥ᴱ                            ↝⟨ (rec λ where
                                          .∣∣ʳ x → f x , [ c (f x) x ]
                                          .truncation-is-propositionʳ → prop) ⟩
  (∃ λ (x : A) → Erased (f x ≡ x))  ↝⟨ proj₁ ⟩□
  A                                 □
  where
  @0 prop : _
  prop =                                       $⟨ fixpoint-lemma f c ⟩
    Is-proposition (∃ λ x → f x ≡ x)           ↝⟨ H-level-cong _ 1 (∃-cong λ _ → inverse $ Er.erased Er.Erased↔) ⦂ (_ → _) ⟩□
    Is-proposition (∃ λ x → Erased (f x ≡ x))  □

-- Having a constant endofunction is logically equivalent to being
-- h-stable.

constant-endofunction⇔h-stable :
  (∃ λ (f : A → A) → Erased (Constant f)) ⇔ (∥ A ∥ᴱ → A)
constant-endofunction⇔h-stable = record
  { to   = λ (_ , [ c ]) → constant-endofunction⇒h-stable c
  ; from = λ f → f ∘ ∣_∣
         , [ (λ x y →
                f ∣ x ∣  ≡⟨ cong f $ truncation-is-proposition _ _ ⟩∎
                f ∣ y ∣  ∎)
           ]
  }

------------------------------------------------------------------------
-- Some results related to _×_

-- The cartesian product of the truncation of A and A is equivalent
-- (with erased "proofs") to A.

∥∥ᴱ×≃ᴱ : (∥ A ∥ᴱ × A) ≃ᴱ A
∥∥ᴱ×≃ᴱ = EEq.↔→≃ᴱ
  proj₂
  (λ x → ∣ x ∣ , x)
  refl
  (λ _ → cong (_, _) (truncation-is-proposition _ _))

-- The application _≃ᴱ_.right-inverse-of ∥∥ᴱ×≃ᴱ x computes in a
-- certain way.

_ : _≃ᴱ_.right-inverse-of ∥∥ᴱ×≃ᴱ x ≡ refl _
_ = refl _

-- ∥_∥ᴱ commutes with _×_.

∥∥ᴱ×∥∥ᴱ↔∥×∥ᴱ : (∥ A ∥ᴱ × ∥ B ∥ᴱ) ↔ ∥ A × B ∥ᴱ
∥∥ᴱ×∥∥ᴱ↔∥×∥ᴱ = record
  { surjection = record
    { logical-equivalence = record
      { from = λ p → ∥∥ᴱ-map proj₁ p , ∥∥ᴱ-map proj₂ p
      ; to   = uncurry $ rec λ where
                 .∣∣ʳ x → rec λ where
                   .∣∣ʳ y                      → ∣ x , y ∣
                   .truncation-is-propositionʳ →
                     truncation-is-proposition
                 .truncation-is-propositionʳ →
                   Π-closure ext 1 λ _ →
                   truncation-is-proposition
      }
    ; right-inverse-of = elim λ where
        .∣∣ʳ _                        → refl _
        .truncation-is-propositionʳ _ →
          mono₁ 1 truncation-is-proposition
    }
  ; left-inverse-of = uncurry $ elim λ where
      .∣∣ʳ _ → elim λ where
        .∣∣ʳ _ → refl _
        .truncation-is-propositionʳ _ →
          mono₁ 1 $
          ×-closure 1 truncation-is-proposition
                      truncation-is-proposition
      .truncation-is-propositionʳ _ →
        Π-closure ext 1 λ _ →
        mono₁ 1 $
        ×-closure 1 truncation-is-proposition
                    truncation-is-proposition
  }

------------------------------------------------------------------------
-- Some results related to h-levels

-- Variants of proj₁-closure.

private

  H-level-×₁-lemma :
    (A → ∥ B ∥ᴱ) →
    ∀ n → H-level (suc n) (A × B) → H-level (suc n) A
  H-level-×₁-lemma inhabited n h =
    [inhabited⇒+]⇒+ n λ a →
    flip rec (inhabited a) λ where
      .∣∣ʳ b →
        proj₁-closure (λ _ → b) (suc n) h
      .truncation-is-propositionʳ →
        H-level-propositional ext (suc n)

H-level-×₁ :
  (A → ∥ B ∥ᴱ) →
  ∀ n → H-level n (A × B) → H-level n A
H-level-×₁ inhabited zero h =
  propositional⇒inhabited⇒contractible
    (H-level-×₁-lemma inhabited 0 (mono₁ 0 h))
    (proj₁ (proj₁ h))
H-level-×₁ inhabited (suc n) =
  H-level-×₁-lemma inhabited n

H-level-×₂ :
  (B → ∥ A ∥ᴱ) →
  ∀ n → H-level n (A × B) → H-level n B
H-level-×₂ {B = B} {A = A} inhabited n =
  H-level n (A × B)  ↝⟨ H-level.respects-surjection (from-bijection ×-comm) n ⟩
  H-level n (B × A)  ↝⟨ H-level-×₁ inhabited n ⟩□
  H-level n B        □

------------------------------------------------------------------------
-- Flattening

-- A generalised flattening lemma.

flatten′ :
  (F : (Type ℓ → Type ℓ) → Type f)
  (map : ∀ {G H} → (∀ {A} → G A → H A) → F G → F H)
  (f : F ∥_∥ᴱ → ∥ F id ∥ᴱ) →
  (∀ x → f (map ∣_∣ x) ≡ ∣ x ∣) →
  (∀ x → ∥∥ᴱ-map (map ∣_∣) (f x) ≡ ∣ x ∣) →
  ∥ F ∥_∥ᴱ ∥ᴱ ↔ ∥ F id ∥ᴱ
flatten′ _ map f f-map map-f = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec λ where
                 .∣∣ʳ                        → f
                 .truncation-is-propositionʳ → truncation-is-proposition
      ; from = ∥∥ᴱ-map (map ∣_∣)
      }
    ; right-inverse-of = elim λ where
        .∣∣ʳ                          → f-map
        .truncation-is-propositionʳ _ →
          mono₁ 1 truncation-is-proposition
    }
  ; left-inverse-of = elim λ where
      .∣∣ʳ                          → map-f
      .truncation-is-propositionʳ _ →
        mono₁ 1 truncation-is-proposition
  }

-- Nested truncations can be flattened.

flatten : ∥ ∥ A ∥ᴱ ∥ᴱ ↔ ∥ A ∥ᴱ
flatten {A = A} = flatten′
  (λ F → F A)
  (λ f → f)
  id
  (λ _ → refl _)
  (elim λ where
     .∣∣ʳ _                        → refl _
     .truncation-is-propositionʳ _ → mono₁ 1 truncation-is-proposition)

private

  -- Another flattening lemma, given as an example of how flatten′ can
  -- be used.

  ∥∃∥∥ᴱ∥ᴱ↔∥∃∥ᴱ : ∥ ∃ (∥_∥ᴱ ∘ P) ∥ᴱ ↔ ∥ ∃ P ∥ᴱ
  ∥∃∥∥ᴱ∥ᴱ↔∥∃∥ᴱ {P = P} = flatten′
    (λ F → ∃ (F ∘ P))
    (λ f → Σ-map id f)
    (uncurry λ x → ∥∥ᴱ-map (x ,_))
    (λ _ → refl _)
    (uncurry λ _ → elim λ where
       .∣∣ʳ _ → refl _
       .truncation-is-propositionʳ _ →
         mono₁ 1 truncation-is-proposition)

-- A variant of flatten′ with _≃ᴱ_ instead of _↔_.

flatten-≃ᴱ :
  (F : (Type ℓ → Type ℓ) → Type f)
  (map : ∀ {G H} → (∀ {A} → G A → H A) → F G → F H)
  (f : F ∥_∥ᴱ → ∥ F id ∥ᴱ) →
  @0 (∀ x → f (map ∣_∣ x) ≡ ∣ x ∣) →
  @0 (∀ x → ∥∥ᴱ-map (map ∣_∣) (f x) ≡ ∣ x ∣) →
  ∥ F ∥_∥ᴱ ∥ᴱ ≃ᴱ ∥ F id ∥ᴱ
flatten-≃ᴱ _ map f f-map map-f = EEq.↔→≃ᴱ
  (rec λ where
     .∣∣ʳ                        → f
     .truncation-is-propositionʳ → truncation-is-proposition)
  (∥∥ᴱ-map (map ∣_∣))
  (elim λ @0 where
     .∣∣ʳ                          → f-map
     .truncation-is-propositionʳ _ →
       mono₁ 1 truncation-is-proposition)
  (elim λ @0 where
     .∣∣ʳ                          → map-f
     .truncation-is-propositionʳ _ →
       mono₁ 1 truncation-is-proposition)

------------------------------------------------------------------------
-- The propositional truncation operator is a monad

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∥ A ∥ᴱ → (A → ∥ B ∥ᴱ) → ∥ B ∥ᴱ
x >>=′ f = _↔_.to flatten (∥∥ᴱ-map f x)

-- The universe-polymorphic variant of bind is associative.

>>=′-associative :
  (x : ∥ A ∥ᴱ) →
  x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
>>=′-associative = elim λ where
  .∣∣ʳ _                        → refl _
  .truncation-is-propositionʳ _ → ⇒≡ 1 truncation-is-proposition

instance

  -- The propositional truncation operator is a monad.

  raw-monad : Raw-monad (∥_∥ᴱ {a = a})
  Raw-monad.return raw-monad = ∣_∣
  Raw-monad._>>=_  raw-monad = _>>=′_

  monad : Monad (∥_∥ᴱ {a = a})
  Monad.raw-monad monad           = raw-monad
  Monad.left-identity monad _ _   = refl _
  Monad.associativity monad x _ _ = >>=′-associative x
  Monad.right-identity monad      = elim λ where
    .∣∣ʳ                        _ → refl _
    .truncation-is-propositionʳ _ → ⇒≡ 1 truncation-is-proposition

------------------------------------------------------------------------
-- Surjectivity

-- A variant of surjectivity with "erased proofs".

Surjectiveᴱ :
  {A : Type a} {B : Type b} →
  (A → B) → Type (a ⊔ b)
Surjectiveᴱ f = ∀ y → ∥ f ⁻¹ᴱ y ∥ᴱ

-- The property Surjectiveᴱ f is a proposition (in erased contexts).

@0 Surjectiveᴱ-propositional : Is-proposition (Surjectiveᴱ f)
Surjectiveᴱ-propositional =
  Π-closure ext 1 λ _ →
  truncation-is-proposition

-- The function ∣_∣ is surjective (with erased proofs).

∣∣-surjective : Surjectiveᴱ (∣_∣ {A = A})
∣∣-surjective = elim λ where
  .∣∣ʳ x                        → ∣ x , [ refl _ ] ∣
  .truncation-is-propositionʳ _ → truncation-is-proposition

-- Split surjective functions are surjective (with erased proofs).

Split-surjective→Surjectiveᴱ :
  Split-surjective f → Surjectiveᴱ f
Split-surjective→Surjectiveᴱ s = λ y → ∣ ECP.⁻¹→⁻¹ᴱ (s y) ∣

-- Being both surjective (with erased proofs) and an embedding
-- (completely erased) is equivalent to being an equivalence (with
-- erased proofs).
--
-- This result, without erasure, is Corollary 4.6.4 from the first
-- edition of the HoTT book.

Surjectiveᴱ×Erased-Is-embedding≃ᴱIs-equivalenceᴱ :
  (Surjectiveᴱ f × Erased (Is-embedding f)) ≃ᴱ Is-equivalenceᴱ f
Surjectiveᴱ×Erased-Is-embedding≃ᴱIs-equivalenceᴱ {f = f} = EEq.⇔→≃ᴱ
  (×-closure 1
     Surjectiveᴱ-propositional
     (Er.H-level-Erased 1
        (Emb.Is-embedding-propositional ext)))
  (EEq.Is-equivalenceᴱ-propositional ext f)
  (λ (is-surj , is-emb) →
     _⇔_.from EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP $ λ y →
                              $⟨ is-surj y ⟩
     ∥ f ⁻¹ᴱ y ∥ᴱ             ↝⟨ (rec λ where
                                    .∣∣ʳ p → ECP.inhabited→Is-proposition→Contractibleᴱ p
                                               (H-level-cong _ 1
                                                  ECP.⁻¹≃⁻¹ᴱ
                                                  (Emb.embedding→⁻¹-propositional (Er.erased is-emb) _))
                                    .truncation-is-propositionʳ →
                                      ECP.Contractibleᴱ-propositional ext) ⟩□
     Contractibleᴱ (f ⁻¹ᴱ y)  □)
  (λ is-eq@(inv , [ r-inv , _ ]) →
       (λ y →           $⟨ inv y , [ r-inv y ] ⟩
          f ⁻¹ᴱ y       ↝⟨ ∣_∣ ⟩
          ∥ f ⁻¹ᴱ y ∥ᴱ  □)

     ,                            ($⟨ is-eq ⟩
       Is-equivalenceᴱ f           ↝⟨ Er.[_]→ ⟩
       Erased (Is-equivalenceᴱ f)  ↝⟨ Er.map EEq.Is-equivalenceᴱ→Is-equivalence ⟩
       Erased (Is-equivalence f)   ↝⟨ Er.map Emb.Is-equivalence→Is-embedding ⟩□
       Erased (Is-embedding f)     □))

------------------------------------------------------------------------
-- Another lemma

-- The function λ R x y → ∥ R x y ∥ᴱ preserves Is-equivalence-relation.

∥∥ᴱ-preserves-Is-equivalence-relation :
  Is-equivalence-relation R →
  Is-equivalence-relation (λ x y → ∥ R x y ∥ᴱ)
∥∥ᴱ-preserves-Is-equivalence-relation R-equiv = record
  { reflexive  = ∣ reflexive ∣
  ; symmetric  = symmetric ⟨$⟩_
  ; transitive = λ p q → transitive ⟨$⟩ p ⊛ q
  }
  where
  open Is-equivalence-relation R-equiv

------------------------------------------------------------------------
-- Definitions related to truncated binary sums

-- Truncated binary sums.

infixr 1 _∥⊎∥ᴱ_

_∥⊎∥ᴱ_ : Type a → Type b → Type (a ⊔ b)
A ∥⊎∥ᴱ B = ∥ A ⊎ B ∥ᴱ

-- Introduction rules.

∣inj₁∣ : A → A ∥⊎∥ᴱ B
∣inj₁∣ = ∣_∣ ∘ inj₁

∣inj₂∣ : B → A ∥⊎∥ᴱ B
∣inj₂∣ = ∣_∣ ∘ inj₂

-- In erased contexts _∥⊎∥ᴱ_ is pointwise propositional.

@0 ∥⊎∥ᴱ-propositional : Is-proposition (A ∥⊎∥ᴱ B)
∥⊎∥ᴱ-propositional = truncation-is-proposition

-- The _∥⊎∥ᴱ_ operator preserves "symmetric" functions.

infixr 1 _∥⊎∥ᴱ-cong_

_∥⊎∥ᴱ-cong_ :
  A₁ ↝[ ⌊ k ⌋-sym ] A₂ → B₁ ↝[ ⌊ k ⌋-sym ] B₂ →
  (A₁ ∥⊎∥ᴱ B₁) ↝[ ⌊ k ⌋-sym ] (A₂ ∥⊎∥ᴱ B₂)
A₁↝A₂ ∥⊎∥ᴱ-cong B₁↝B₂ = ∥∥ᴱ-cong (A₁↝A₂ ⊎-cong B₁↝B₂)

-- _∥⊎∥ᴱ_ is commutative.

∥⊎∥ᴱ-comm : A ∥⊎∥ᴱ B ↔ B ∥⊎∥ᴱ A
∥⊎∥ᴱ-comm = ∥∥ᴱ-cong ⊎-comm

-- If one truncates the types to the left or right of _∥⊎∥ᴱ_, then one
-- ends up with an isomorphic type.

truncate-left-∥⊎∥ᴱ : A ∥⊎∥ᴱ B ↔ ∥ A ∥ᴱ ∥⊎∥ᴱ B
truncate-left-∥⊎∥ᴱ =
  inverse $
  flatten′
    (λ F → F _ ⊎ _)
    (λ f → ⊎-map f id)
    P.[ ∥∥ᴱ-map inj₁ , ∣inj₂∣ ]
    P.[ (λ _ → refl _) , (λ _ → refl _) ]
    P.[ (elim λ where
           .∣∣ʳ _ → refl _
           .truncation-is-propositionʳ _ →
             mono₁ 1 ∥⊎∥ᴱ-propositional)
      , (λ _ → refl _)
      ]

truncate-right-∥⊎∥ᴱ : A ∥⊎∥ᴱ B ↔ A ∥⊎∥ᴱ ∥ B ∥ᴱ
truncate-right-∥⊎∥ᴱ {A = A} {B = B} =
  A ∥⊎∥ᴱ B       ↝⟨ ∥⊎∥ᴱ-comm ⟩
  B ∥⊎∥ᴱ A       ↝⟨ truncate-left-∥⊎∥ᴱ ⟩
  ∥ B ∥ᴱ ∥⊎∥ᴱ A  ↝⟨ ∥⊎∥ᴱ-comm ⟩□
  A ∥⊎∥ᴱ ∥ B ∥ᴱ  □

-- _∥⊎∥ᴱ_ is associative.

∥⊎∥ᴱ-assoc : A ∥⊎∥ᴱ (B ∥⊎∥ᴱ C) ↔ (A ∥⊎∥ᴱ B) ∥⊎∥ᴱ C
∥⊎∥ᴱ-assoc {A = A} {B = B} {C = C} =
  ∥ A ⊎ ∥ B ⊎ C ∥ᴱ ∥ᴱ  ↝⟨ inverse truncate-right-∥⊎∥ᴱ ⟩
  ∥ A ⊎ B ⊎ C ∥ᴱ       ↝⟨ ∥∥ᴱ-cong ⊎-assoc ⟩
  ∥ (A ⊎ B) ⊎ C ∥ᴱ     ↝⟨ truncate-left-∥⊎∥ᴱ ⟩□
  ∥ ∥ A ⊎ B ∥ᴱ ⊎ C ∥ᴱ  □

-- ⊥ is a left and right identity of _∥⊎∥ᴱ_ if the other argument is a
-- proposition.

∥⊎∥ᴱ-left-identity : @0 Is-proposition A → ⊥ {ℓ = ℓ} ∥⊎∥ᴱ A ↔ A
∥⊎∥ᴱ-left-identity {A = A} A-prop =
  ∥ ⊥ ⊎ A ∥ᴱ  ↝⟨ ∥∥ᴱ-cong ⊎-left-identity ⟩
  ∥ A ∥ᴱ      ↝⟨ ∥∥ᴱ↔ A-prop ⟩□
  A          □

∥⊎∥ᴱ-right-identity : @0 Is-proposition A → A ∥⊎∥ᴱ ⊥ {ℓ = ℓ} ↔ A
∥⊎∥ᴱ-right-identity {A = A} A-prop =
  A ∥⊎∥ᴱ ⊥  ↔⟨ ∥⊎∥ᴱ-comm ⟩
  ⊥ ∥⊎∥ᴱ A  ↔⟨ ∥⊎∥ᴱ-left-identity A-prop ⟩□
  A         □

-- _∥⊎∥ᴱ_ is idempotent for propositions (up to equivalences with
-- erased proofs).

∥⊎∥ᴱ-idempotent : @0 Is-proposition A → (A ∥⊎∥ᴱ A) ≃ᴱ A
∥⊎∥ᴱ-idempotent {A = A} A-prop =
  ∥ A ⊎ A ∥ᴱ  ↝⟨ idempotent ⟩
  ∥ A ∥ᴱ      ↔⟨ ∥∥ᴱ↔ A-prop ⟩□
  A           □

-- Sometimes a truncated binary sum is equivalent (with erased proofs)
-- to one of its summands.

drop-left-∥⊎∥ᴱ :
  @0 Is-proposition B → (A → B) → (A ∥⊎∥ᴱ B) ≃ᴱ B
drop-left-∥⊎∥ᴱ B-prop A→B = EEq.⇔→≃ᴱ
  ∥⊎∥ᴱ-propositional
  B-prop
  (rec λ where
     .∣∣ʳ → P.[ A→B , id ]
     .truncation-is-propositionʳ → B-prop)
  ∣inj₂∣

drop-right-∥⊎∥ᴱ :
  @0 Is-proposition A → (B → A) → (A ∥⊎∥ᴱ B) ≃ᴱ A
drop-right-∥⊎∥ᴱ {A = A} {B = B} A-prop B→A =
  A ∥⊎∥ᴱ B  ↔⟨ ∥⊎∥ᴱ-comm ⟩
  B ∥⊎∥ᴱ A  ↝⟨ drop-left-∥⊎∥ᴱ A-prop B→A ⟩□
  A        □

-- Sometimes a truncated binary sum is isomorphic to one of its
-- summands.

drop-⊥-right-∥⊎∥ᴱ :
  @0 Is-proposition A → ¬ B → A ∥⊎∥ᴱ B ↔ A
drop-⊥-right-∥⊎∥ᴱ A-prop ¬B = record
  { surjection = record
    { logical-equivalence = record
      { to = rec λ where
          .∣∣ʳ → P.[ id , ⊥-elim ∘ ¬B ]
          .truncation-is-propositionʳ → A-prop
      ; from = ∣inj₁∣
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = elim λ where
      .∣∣ʳ → P.[ (λ _ → refl _) , ⊥-elim ∘ ¬B ]
      .truncation-is-propositionʳ _ →
        mono₁ 1 ∥⊎∥ᴱ-propositional
  }

drop-⊥-left-∥⊎∥ᴱ :
  @0 Is-proposition B → ¬ A → A ∥⊎∥ᴱ B ↔ B
drop-⊥-left-∥⊎∥ᴱ B-prop ¬A = record
  { surjection = record
    { logical-equivalence = record
      { to = rec λ where
          .∣∣ʳ → P.[ ⊥-elim ∘ ¬A , id ]
          .truncation-is-propositionʳ → B-prop
      ; from = ∣inj₂∣
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = elim λ where
      .∣∣ʳ → P.[ ⊥-elim ∘ ¬A , (λ _ → refl _) ]
      .truncation-is-propositionʳ _ →
        mono₁ 1 ∥⊎∥ᴱ-propositional
  }

-- A type of functions from a truncated binary sum to a family of
-- propositions can be expressed as a binary product of function
-- types.

Π∥⊎∥ᴱ↔Π×Π :
  @0 (∀ x → Is-proposition (P x)) →
  ((x : A ∥⊎∥ᴱ B) → P x)
    ↔
  ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))
Π∥⊎∥ᴱ↔Π×Π {A = A} {B = B} {P = P} P-prop =
  ((x : A ∥⊎∥ᴱ B) → P x)                               ↔⟨ universal-property-Π P-prop ⟩
  ((x : A ⊎ B) → P ∣ x ∣)                              ↝⟨ Π⊎↔Π×Π ext ⟩□
  ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))  □

-- Two distributivity laws for Σ and _∥⊎∥ᴱ_.

Σ-∥⊎∥ᴱ-distrib-left :
  @0 Is-proposition A →
  Σ A (λ x → P x ∥⊎∥ᴱ Q x) ↔ Σ A P ∥⊎∥ᴱ Σ A Q
Σ-∥⊎∥ᴱ-distrib-left {P = P} {Q = Q} A-prop =
  (∃ λ x → ∥ P x ⊎ Q x ∥ᴱ)       ↝⟨ inverse $ ∥∥ᴱ↔ (Σ-closure 1 A-prop λ _ → ∥⊎∥ᴱ-propositional) ⟩
  ∥ (∃ λ x → ∥ P x ⊎ Q x ∥ᴱ) ∥ᴱ  ↝⟨ flatten′
                                      (λ F → (∃ λ x → F (P x ⊎ Q x)))
                                      (λ f → Σ-map id f)
                                      (uncurry λ x → ∥∥ᴱ-map (x ,_))
                                      (λ _ → refl _)
                                      (uncurry λ _ → elim λ where
                                         .∣∣ʳ _ → refl _
                                         .truncation-is-propositionʳ _ →
                                           mono₁ 1 truncation-is-proposition) ⟩
  ∥ (∃ λ x → P x ⊎ Q x) ∥ᴱ       ↝⟨ ∥∥ᴱ-cong ∃-⊎-distrib-left ⟩□
  ∥ ∃ P ⊎ ∃ Q ∥ᴱ                 □

Σ-∥⊎∥ᴱ-distrib-right :
  @0 (∀ x → Is-proposition (P x)) →
  Σ (A ∥⊎∥ᴱ B) P ↔ Σ A (P ∘ ∣inj₁∣) ∥⊎∥ᴱ Σ B (P ∘ ∣inj₂∣)
Σ-∥⊎∥ᴱ-distrib-right {A = A} {B = B} {P = P} P-prop = record
  { surjection = record
    { logical-equivalence = record
      { to = uncurry $ elim λ where
          .∣∣ʳ → curry (∣_∣ ∘ _↔_.to ∃-⊎-distrib-right)
          .truncation-is-propositionʳ _ →
            Π-closure ext 1 λ _ →
            ∥⊎∥ᴱ-propositional
      ; from = rec λ where
          .∣∣ʳ → Σ-map ∣_∣ id ∘ _↔_.from ∃-⊎-distrib-right
          .truncation-is-propositionʳ → prop
      }
    ; right-inverse-of = elim λ where
      .∣∣ʳ → P.[ (λ _ → refl _) , (λ _ → refl _) ]
      .truncation-is-propositionʳ _ →
        mono₁ 1 ∥⊎∥ᴱ-propositional
    }
  ; left-inverse-of = uncurry $ elim λ where
      .∣∣ʳ → P.[ (λ _ _ → refl _) , (λ _ _ → refl _) ]
      .truncation-is-propositionʳ _ →
        Π-closure ext 1 λ _ →
        mono₁ 1 prop
  }
  where
  @0 prop : _
  prop = Σ-closure 1 ∥⊎∥ᴱ-propositional P-prop

-- A variant of one of De Morgan's laws.

¬∥⊎∥ᴱ¬↔¬× :
  Dec (¬ A) → Dec (¬ B) →
  (¬ A ∥⊎∥ᴱ ¬ B) ≃ᴱ (¬ (A × B))
¬∥⊎∥ᴱ¬↔¬× {A = A} {B = B} dec-¬A dec-¬B = EEq.⇔→≃ᴱ
  ∥⊎∥ᴱ-propositional
  (¬-propositional ext)
  (rec λ where
     .∣∣ʳ → ¬⊎¬→×¬
     .truncation-is-propositionʳ → ¬-propositional ext)
  (∣_∣ ∘ _↠_.from (¬⊎¬↠¬× ext dec-¬A dec-¬B))

------------------------------------------------------------------------
-- Code related to Erased-singleton

-- A corollary of erased-singleton-with-erased-center-propositional.

↠→↠Erased-singleton :
  {@0 y : B}
  (A↠B : A ↠ B) →
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ᴱ ↠ Erased-singleton y
↠→↠Erased-singleton {A = A} {y = y} A↠B =
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ᴱ  ↝⟨ ∥∥ᴱ-cong-↠ (S.Σ-cong A↠B λ _ → F.id) ⟩
  ∥ Erased-singleton y ∥ᴱ                         ↔⟨ ∥∥ᴱ↔
                                                       (Er.erased-singleton-with-erased-center-propositional $
                                                        Er.Very-stable→Very-stableᴱ 1 $
                                                        Er.Very-stable→Very-stable-≡ 0 $
                                                        erased Er.Erased-Very-stable) ⟩□
  Erased-singleton y                              □

-- Another corollary of
-- erased-singleton-with-erased-center-propositional.

↠→≃ᴱErased-singleton :
  {@0 y : B}
  (A↠B : A ↠ B) →
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ᴱ ≃ᴱ Erased-singleton y
↠→≃ᴱErased-singleton {A = A} {y = y} A↠B =
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ᴱ  ↝⟨ ∥∥ᴱ-cong-⇔ (S.Σ-cong-⇔ A↠B λ _ → F.id) ⟩
  ∥ Erased-singleton y ∥ᴱ                         ↔⟨ ∥∥ᴱ↔
                                                       (Er.erased-singleton-with-erased-center-propositional $
                                                        Er.Very-stable→Very-stableᴱ 1 $
                                                        Er.Very-stable→Very-stable-≡ 0 $
                                                        erased Er.Erased-Very-stable) ⟩□
  Erased-singleton y                              □

-- A corollary of Σ-Erased-Erased-singleton↔ and ↠→≃ᴱErased-singleton.

Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ :
  (A↠B : A ↠ B) →
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥ᴱ) ≃ᴱ
  B
Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ {A = A} {B = B} A↠B =
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥ᴱ)  ↝⟨ (∃-cong λ _ → ↠→≃ᴱErased-singleton A↠B) ⟩

  (∃ λ (x : Erased B) → Erased-singleton (erased x))         ↔⟨ Er.Σ-Erased-Erased-singleton↔ ⟩□

  B                                                          □

-- In an erased context the left-to-right direction of
-- Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ returns the erased first component.

@0 to-Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ≡ :
  ∀ (A↠B : A ↠ B) x →
  _≃ᴱ_.to (Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ A↠B) x ≡ erased (proj₁ x)
to-Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ≡ A↠B ([ x ] , y) =
  _≃ᴱ_.to (Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ A↠B) ([ x ] , y)  ≡⟨⟩
  proj₁ (_≃ᴱ_.to (↠→≃ᴱErased-singleton A↠B) y)         ≡⟨ erased (proj₂ (_≃ᴱ_.to (↠→≃ᴱErased-singleton A↠B) y)) ⟩∎
  x                                                    ∎
