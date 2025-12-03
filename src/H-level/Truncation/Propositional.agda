------------------------------------------------------------------------
-- Propositional truncation
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe #-}

-- Partly following the HoTT book.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the propositional truncation uses
-- path equality, but the supplied notion of equality is used for many
-- other things.

import Equality.Path as P

module H-level.Truncation.Propositional
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Dec
open import Prelude
open import Logical-equivalence using (_⇔_)

open import Accessibility equality-with-J as A using (Acc)
open import Bijection equality-with-J as Bijection using (_↔_)
open import Embedding equality-with-J as Embedding hiding (id; _∘_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Path-split equality-with-J as PS
  using (Is-∞-extendable-along-[_]; _-Null_)
open import Equivalence.Erased equality-with-J using (_≃ᴱ_)
open import Equivalence.Erased.Contractible-preimages equality-with-J
  as ECP using (_⁻¹ᴱ_)
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as E
  using (Erased; erased; Dec-Erased; Very-stableᴱ-≡; Erased-singleton)
import Erased.Stability equality-with-J as ES
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
import H-level.Truncation.Church equality-with-J as Trunc
open import H-level.Truncation.Propositional.Erased eq as TE
  using (∥_∥ᴱ; Surjectiveᴱ)
open import Injection equality-with-J using (_↣_)
open import Modality.Basics equality-with-J
open import Monad equality-with-J
import Nat equality-with-J as Nat
open import Preimage equality-with-J as Preimage using (_⁻¹_)
open import Surjection equality-with-J as Surjection
  using (_↠_; Split-surjective)

private
  variable
    a b c d p r ℓ ℓ′    : Level
    A A₁ A₂ B B₁ B₂ C D : Type a
    P Q                 : A → Type p
    R                   : A → A → Type r
    A↠B f k s x y       : A

------------------------------------------------------------------------
-- The type constructor and some eliminators

-- Propositional truncation.

data ∥_∥ (A : Type a) : Type a where
  ∣_∣                        : A → ∥ A ∥
  truncation-is-propositionᴾ : P.Is-proposition ∥ A ∥

-- The truncation produces propositions.

truncation-is-proposition : Is-proposition ∥ A ∥
truncation-is-proposition =
  _↔_.from (H-level↔H-level 1) truncation-is-propositionᴾ

-- A dependent eliminator, expressed using paths.

record Elimᴾ′ {A : Type a} (P : ∥ A ∥ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    truncation-is-propositionʳ :
      (p : P x) (q : P y) →
      P.[ (λ i → P (truncation-is-propositionᴾ x y i)) ] p ≡ q

open Elimᴾ′ public

elimᴾ′ : Elimᴾ′ P → (x : ∥ A ∥) → P x
elimᴾ′ {A} {P} e = helper
  where
  module E′ = Elimᴾ′ e

  helper : (x : ∥ A ∥) → P x
  helper ∣ x ∣                              = E′.∣∣ʳ x
  helper (truncation-is-propositionᴾ x y i) =
    E′.truncation-is-propositionʳ (helper x) (helper y) i

-- A possibly more useful dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : ∥ A ∥ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    truncation-is-propositionʳ :
      (x : ∥ A ∥) → P.Is-proposition (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : ∥ A ∥) → P x
elimᴾ e = elimᴾ′ e′
  where
  module E′ = Elimᴾ e

  e′ : Elimᴾ′ _
  e′ .∣∣ʳ                            = E′.∣∣ʳ
  e′ .truncation-is-propositionʳ _ _ =
    P.heterogeneous-irrelevance E′.truncation-is-propositionʳ

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ                        : A → B
    truncation-is-propositionʳ : P.Is-proposition B

open Recᴾ public

recᴾ : Recᴾ A B → ∥ A ∥ → B
recᴾ r = elimᴾ e
  where
  module R = Recᴾ r

  e : Elimᴾ _
  e .∣∣ʳ                          = R.∣∣ʳ
  e .truncation-is-propositionʳ _ = R.truncation-is-propositionʳ

-- A dependently typed eliminator.

record Elim′ {A : Type a} (P : ∥ A ∥ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    truncation-is-propositionʳ :
      (x : ∥ A ∥) → Is-proposition (P x)

open Elim′ public

elim′ : Elim′ P → (x : ∥ A ∥) → P x
elim′ e = elimᴾ e′
  where
  module E′ = Elim′ e

  e′ : Elimᴾ _
  e′ .∣∣ʳ                        = E′.∣∣ʳ
  e′ .truncation-is-propositionʳ =
    _↔_.to (H-level↔H-level 1) ∘ E′.truncation-is-propositionʳ

elim :
  (P : ∥ A ∥ → Type p) →
  (∀ x → Is-proposition (P x)) →
  ((x : A) → P ∣ x ∣) →
  (x : ∥ A ∥) → P x
elim _ p f = elim′ λ where
  .∣∣ʳ                        → f
  .truncation-is-propositionʳ → p

-- Primitive "recursion".

record Rec′ (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ                        : A → B
    truncation-is-propositionʳ : Is-proposition B

open Rec′ public

rec′ : Rec′ A B → ∥ A ∥ → B
rec′ r = recᴾ r′
  where
  module R = Rec′ r

  r′ : Recᴾ _ _
  r′ .∣∣ʳ                        = R.∣∣ʳ
  r′ .truncation-is-propositionʳ =
    _↔_.to (H-level↔H-level 1) R.truncation-is-propositionʳ

rec : Is-proposition B → (A → B) → ∥ A ∥ → B
rec p f = rec′ λ where
  .∣∣ʳ                        → f
  .truncation-is-propositionʳ → p

------------------------------------------------------------------------
-- A lemma

-- A map function.

∥∥-map : (A → B) → ∥ A ∥ → ∥ B ∥
∥∥-map f = rec truncation-is-proposition (∣_∣ ∘ f)

------------------------------------------------------------------------
-- The axiom of choice, and the axiom of countable choice

-- The axiom of choice, in one of the alternative forms given in the
-- HoTT book (§3.8).

Axiom-of-choice : (a b : Level) → Type (lsuc (a ⊔ b))
Axiom-of-choice a b =
  {A : Type a} {B : A → Type b} →
  Is-set A → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

-- The axiom of choice can be turned into a bijection.

choice-bijection :
  {A : Type a} {B : A → Type b} →
  Axiom-of-choice a b → Is-set A →
  (∀ x → ∥ B x ∥) ↔ ∥ (∀ x → B x) ∥
choice-bijection choice A-set = record
  { surjection = record
    { logical-equivalence = record
      { to   = choice A-set
      ; from = λ f x → ∥∥-map (_$ x) f
      }
    ; right-inverse-of = λ _ → truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ →
      (Π-closure ext 1 λ _ →
       truncation-is-proposition) _ _
  }

-- The axiom of countable choice, stated in a corresponding way.

Axiom-of-countable-choice : (b : Level) → Type (lsuc b)
Axiom-of-countable-choice b =
  {B : ℕ → Type b} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

-- The axiom of countable choice can be turned into a bijection.

countable-choice-bijection :
  {B : ℕ → Type b} →
  Axiom-of-countable-choice b →
  (∀ x → ∥ B x ∥) ↔ ∥ (∀ x → B x) ∥
countable-choice-bijection cc = record
  { surjection = record
    { logical-equivalence = record
      { to   = cc
      ; from = λ f x → ∥∥-map (_$ x) f
      }
    ; right-inverse-of = λ _ → truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ →
      (Π-closure ext 1 λ _ →
       truncation-is-proposition) _ _
  }

------------------------------------------------------------------------
-- Propositional truncation is an accessible modality

-- Propositional truncation is a modality.
--
-- This proof is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

∥∥-modality : Modality ℓ
∥∥-modality {ℓ} = λ where
    .◯            → ∥_∥
    .η            → ∣_∣
    .modality-for → λ where
      .Modal               → Is-proposition
      .Modal-propositional → λ ext → H-level-propositional ext 1
      .Modal-◯             → truncation-is-proposition
      .Modal-respects-≃    → H-level-cong _ 1
      .extendable-along-η  → extendable
  where
  open Modality
  open Modality-for

  extendable :
    {A : Type ℓ} {P : ∥ A ∥ → Type ℓ} →
    (∀ x → Is-proposition (P x)) →
    Is-∞-extendable-along-[ ∣_∣ ] P
  extendable {A} {P} =
    (∀ x → Is-proposition (P x))                          →⟨ (λ prop →
                                                                _≃_.is-equivalence $
                                                                Eq.↔→≃
                                                                  _
                                                                  (elim _ prop)
                                                                  refl
                                                                  (λ f → ⟨ext⟩ $
                                                                     elim
                                                                       _
                                                                       (⇒≡ 1 ∘ prop)
                                                                       (λ _ → refl _))) ⟩
    Is-equivalence (λ (f : (x : ∥ A ∥) → P x) → f ∘ ∣_∣)  ↔⟨ inverse $ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩□
    Is-∞-extendable-along-[ ∣_∣ ] P                       □

-- The propositional truncation modality is accessible.
--
-- This proof is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

∥∥-accessible : Accessible (∥∥-modality {ℓ = ℓ})
∥∥-accessible {ℓ} =
    ↑ ℓ ⊤
  , (λ _ → ↑ ℓ Bool)
  , (λ A →
       Is-proposition A                                 ↝⟨ record { from = from; to = to } ⟩
       (λ (_ : ↑ ℓ ⊤) → ↑ ℓ Bool) -Null A               ↔⟨ inverse $ PS.Π-Is-∞-extendable-along≃Null ext ⟩□
       (↑ ℓ ⊤ → Is-∞-extendable-along-[ _ ] (λ _ → A))  □)

  where
  to : Is-proposition A → (λ (_ : ↑ ℓ ⊤) → ↑ ℓ Bool) -Null A
  to prop _ =
    _≃_.is-equivalence $
    Eq.⇔→≃
      prop
      (Π-closure ext 1 λ _ → prop)
      _
      (_$ lift true)

  from : (λ (_ : ↑ ℓ ⊤) → ↑ ℓ Bool) -Null A → Is-proposition A
  from {A} null x y =
    x                                           ≡⟨⟩
    case true ⦂ Bool of if_then x else y        ≡⟨ cong (_$ true) $ sym $ EB→.right-inverse-of _ ⟩
    EB→.to (EB→.from (if_then x else y)) true   ≡⟨⟩
    EB→.from (if_then x else y)                 ≡⟨⟩
    EB→.to (EB→.from (if_then x else y)) false  ≡⟨ cong (_$ false) $ EB→.right-inverse-of _ ⟩
    case false ⦂ Bool of if_then x else y       ≡⟨⟩
    y                                           ∎
    where
    ≃Bool→ : A ≃ (Bool → A)
    ≃Bool→ =
      A               ↝⟨ Eq.⟨ _ , null _ ⟩ ⟩
      (↑ ℓ Bool → A)  ↝⟨ Eq.↔→≃ (_∘ lift) (_∘ lower) refl refl ⟩□
      (Bool → A)      □

    module EB→ = _≃_ ≃Bool→

-- The propositional truncation modality is empty-modal.

∥∥-empty-modal : Empty-modal (∥∥-modality {ℓ = ℓ})
∥∥-empty-modal = ⊥-propositional

-- The modality is not left exact.
--
-- This result is mentioned by Rijke, Shulman and Spitters in
-- "Modalities in Homotopy Type Theory".

¬-∥∥-left-exact : ¬ Left-exact (∥_∥ {a = a})
¬-∥∥-left-exact {a} =
  Empty-modal→Is-proposition-◯→¬-Left-exact
    ∥∥-empty-modal truncation-is-proposition
  where
  open Modality (∥∥-modality {ℓ = a})

-- The modality is not very modal.

¬-∥∥-very-modal : ¬ Very-modal (∥∥-modality {ℓ = ℓ})
¬-∥∥-very-modal {ℓ} =
  Very-modal (∥∥-modality {ℓ = ℓ})       ↔⟨⟩
  ({A : Type ℓ} → ∥ Is-proposition A ∥)  →⟨ (λ hyp → hyp) ⟩
  ∥ Is-proposition (↑ ℓ Bool) ∥          →⟨ ◯-map (⊥-elim ∘ ¬-Bool-propositional ∘ H-level-cong _ 1 Bijection.↑↔) ⟩
  ∥ ⊥ ∥                                  →⟨ ⊥-elim ∘ Modal→Stable ∥∥-empty-modal ⟩□
  ⊥                                      □
  where
  open Modality (∥∥-modality {ℓ = ℓ})

-- The modality is W-modal.

∥∥-W-modal : W-modal (∥∥-modality {ℓ = ℓ})
∥∥-W-modal = W-closure ext 0

-- The modality is not accessibility-modal.

¬-∥∥-accessibility-modal :
  ¬ Modality.Accessibility-modal (∥∥-modality {ℓ = ℓ})
¬-∥∥-accessibility-modal {ℓ} =
  Is-proposition-◯→¬-Accessibility-modal
    truncation-is-proposition
  where
  open Modality (∥∥-modality {ℓ = ℓ})

-- The modality is accessibility-modal for propositional types and
-- relations.

Is-proposition→∥∥-accessibility-modal :
  {A : Type ℓ} {_<_ : A → A → Type ℓ} →
  Is-proposition A →
  (∀ x y → Is-proposition (x < y)) →
  Modality.Accessibility-modal-for ∥∥-modality _<_
Is-proposition→∥∥-accessibility-modal {ℓ} p₁ p₂ =
    (λ acc →
       Modal→Acc→Acc-[]◯-η
         p₁
         (rec′ λ where
            .∣∣ʳ                        → id
            .truncation-is-propositionʳ → p₂ _ _)
         acc)
  , (rec′ λ where
       .∣∣ʳ                        → id
       .truncation-is-propositionʳ → A.Acc-propositional ext)
  where
  open Modality (∥∥-modality {ℓ = ℓ})

-- If the modality is accessibility-modal for all relations for a
-- type A, then all values of type A are not not equal.

∥∥-accessibility-modal→¬¬≡ :
  {x y : A} →
  ({_<_ : A → A → Type ℓ} →
   Modality.Accessibility-modal-for ∥∥-modality _<_) →
  ¬ ¬ x ≡ y
∥∥-accessibility-modal→¬¬≡ {ℓ} {A} {x} {y} acc x≢y =
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
  open Modality (∥∥-modality {ℓ = ℓ})

  _<_ : A → A → Type ℓ
  _ < z = z ≡ y

-- The modality commutes with Σ.

∥∥-commutes-with-Σ : Modality.Commutes-with-Σ (∥∥-modality {ℓ = ℓ})
∥∥-commutes-with-Σ = Modality.commutes-with-Σ ∥∥-modality ext

-- If the axiom of choice holds, then the modality has choice for
-- families over sets.

∥∥-has-choice-for-sets :
  {A : Type ℓ} →
  Axiom-of-choice ℓ ℓ →
  Is-set A →
  Modality.Has-choice-for (∥∥-modality {ℓ = ℓ}) A
∥∥-has-choice-for-sets choice set =
  _≃_.from (Has-choice-for≃Is-equivalence-◯Π→Π◯ ext) $
  _≃_.is-equivalence $
  Eq.with-other-function
    (from-bijection $ inverse $ choice-bijection choice set)
    _
    (λ _ → (Π-closure ext 1 λ _ →
            truncation-is-proposition)
             _ _)
  where
  open Modality ∥∥-modality

-- If the axiom of countable choice holds, then the modality has
-- choice for families over ℕ (lifted).

∥∥-has-choice-for-ℕ :
  Axiom-of-countable-choice ℓ →
  Modality.Has-choice-for (∥∥-modality {ℓ = ℓ}) (↑ ℓ ℕ)
∥∥-has-choice-for-ℕ choice =
  _≃_.from (Has-choice-for≃Is-equivalence-◯Π→Π◯ ext) λ {P = P} →
  _≃_.is-equivalence $
  Eq.with-other-function
    (∥ ((n : ↑ _ ℕ) → P n) ∥     ↝⟨ (◯-cong-≃ $ Π-cong ext Bijection.↑↔ λ _ → F.id) ⟩
     ∥ ((n : ℕ) → P (lift n)) ∥  ↔⟨ inverse $ countable-choice-bijection choice ⟩
     ((n : ℕ) → ∥ P (lift n) ∥)  ↝⟨ (Π-cong ext (inverse Bijection.↑↔) λ _ → F.id) ⟩□
     ((n : ↑ _ ℕ) → ∥ P n ∥)     □)
    _
    (λ _ → (Π-closure ext 1 λ _ →
            truncation-is-proposition)
             _ _)
  where
  open Modality ∥∥-modality

------------------------------------------------------------------------
-- Various lemmas

-- The propositional truncation defined here is isomorphic to the one
-- defined in H-level.Truncation.Church.

∥∥↔∥∥ :
  ∀ ℓ {a} {A : Type a} →
  ∥ A ∥ ↔ Trunc.∥ A ∥ 1 (a ⊔ ℓ)
∥∥↔∥∥ ℓ = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec (Trunc.truncation-has-correct-h-level 1 ext)
                   Trunc.∣_∣₁
      ; from = lower {ℓ = ℓ} ∘
               Trunc.rec 1
                         (↑-closure 1 truncation-is-proposition)
                         (lift ∘ ∣_∣)
      }
    ; right-inverse-of = λ _ →
        Trunc.truncation-has-correct-h-level 1 ext _ _
    }
  ; left-inverse-of = λ _ → truncation-is-proposition _ _
  }

-- If A is merely inhabited (with erased proofs), then A is merely
-- inhabited.

∥∥ᴱ→∥∥ : ∥ A ∥ᴱ → ∥ A ∥
∥∥ᴱ→∥∥ = TE.rec λ where
  .TE.∣∣ʳ                        → ∣_∣
  .TE.truncation-is-propositionʳ → truncation-is-proposition

-- In an erased context the propositional truncation operator defined
-- in H-level.Truncation.Propositional.Erased is equivalent to the one
-- defined here.

@0 ∥∥ᴱ≃∥∥ : ∥ A ∥ᴱ ≃ ∥ A ∥
∥∥ᴱ≃∥∥ = Eq.⇔→≃
  TE.truncation-is-proposition
  truncation-is-proposition
  ∥∥ᴱ→∥∥
  (rec TE.truncation-is-proposition TE.∣_∣)

-- One can convert from Dec ∥ A ∥ᴱ to Dec-Erased ∥ A ∥.

Dec-∥∥ᴱ→Dec-Erased-∥∥ : Dec ∥ A ∥ᴱ → Dec-Erased ∥ A ∥
Dec-∥∥ᴱ→Dec-Erased-∥∥ =
  E.Dec→Dec-Erased ∘ Dec-map₀ ∥∥ᴱ→∥∥ (_≃_.from ∥∥ᴱ≃∥∥)

mutual

  -- If A and B are logically equivalent, then functions of any kind can
  -- be constructed from ∥ A ∥ to ∥ B ∥.

  ∥∥-cong-⇔ : ∀ {k} → A ⇔ B → ∥ A ∥ ↝[ k ] ∥ B ∥
  ∥∥-cong-⇔ A⇔B = ∥∥-cong-⇔′ (∣_∣ ∘ _⇔_.to A⇔B) (∣_∣ ∘ _⇔_.from A⇔B)

  -- A variant of the previous result.

  ∥∥-cong-⇔′ : ∀ {k} → (A → ∥ B ∥) → (B → ∥ A ∥) → ∥ A ∥ ↝[ k ] ∥ B ∥
  ∥∥-cong-⇔′ A→∥B∥ B→∥A∥ =
    from-equivalence $
    Eq.⇔→≃
      truncation-is-proposition
      truncation-is-proposition
      (rec truncation-is-proposition A→∥B∥)
      (rec truncation-is-proposition B→∥A∥)

-- The truncation operator preserves all kinds of functions.

private

  ∥∥-cong-↣ : A ↣ B → ∥ A ∥ ↣ ∥ B ∥
  ∥∥-cong-↣ f = record
    { to        = ∥∥-map (_↣_.to f)
    ; injective = λ _ → truncation-is-proposition _ _
    }

∥∥-cong : A ↝[ k ] B → ∥ A ∥ ↝[ k ] ∥ B ∥
∥∥-cong {k = implication}         = ∥∥-map
∥∥-cong {k = logical-equivalence} = ∥∥-cong-⇔
∥∥-cong {k = surjection}          = ∥∥-cong-⇔ ∘ _↠_.logical-equivalence
∥∥-cong {k = bijection}           = ∥∥-cong-⇔ ∘ from-isomorphism
∥∥-cong {k = equivalence}         = ∥∥-cong-⇔ ∘ from-isomorphism
∥∥-cong {k = equivalenceᴱ}        = ∥∥-cong-⇔ ∘ _≃ᴱ_.logical-equivalence
∥∥-cong {k = injection}           = ∥∥-cong-↣
∥∥-cong {k = embedding}           =
  _↔_.to (↣↔Embedding ext
            (mono₁ 1 truncation-is-proposition)
            (mono₁ 1 truncation-is-proposition)) ∘
  ∥∥-cong-↣ ∘ Embedding.injection

-- A form of idempotence for binary sums.

idempotent : ∥ A ⊎ A ∥ ↔ ∥ A ∥
idempotent = ∥∥-cong-⇔ (record { to = [ id , id ]; from = inj₁ })

-- A generalised flattening lemma.

flatten′ :
  (F : (Type ℓ → Type ℓ) → Type f) →
  (∀ {G H} → (∀ {A} → G A → H A) → F G → F H) →
  (F ∥_∥ → ∥ F id ∥) →
  ∥ F ∥_∥ ∥ ↔ ∥ F id ∥
flatten′ _ map f = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec truncation-is-proposition f
      ; from = ∥∥-map (map ∣_∣)
      }
    ; right-inverse-of = λ _ → truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ → truncation-is-proposition _ _
  }

-- Nested truncations can be flattened.

flatten : ∥ ∥ A ∥ ∥ ↔ ∥ A ∥
flatten {A} = flatten′ (λ F → F A) (λ f → f) id

private

  -- Another flattening lemma, given as an example of how flatten′ can
  -- be used.

  ∥∃∥∥∥↔∥∃∥ : {B : A → Type b} →
              ∥ ∃ (∥_∥ ∘ B) ∥ ↔ ∥ ∃ B ∥
  ∥∃∥∥∥↔∥∃∥ {B} =
    flatten′ (λ F → ∃ (F ∘ B))
             (λ f → Σ-map id f)
             (uncurry λ x → ∥∥-map (x ,_))

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∥ A ∥ → (A → ∥ B ∥) → ∥ B ∥
x >>=′ f = _↔_.to flatten (∥∥-map f x)

-- The universe-polymorphic variant of bind is associative.

>>=′-associative :
  (x : ∥ A ∥) {f : A → ∥ B ∥} {g : B → ∥ C ∥} →
  x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
>>=′-associative x {f} {g} = elim
  (λ x → x >>=′ (λ x₁ → f x₁ >>=′ g) ≡ x >>=′ f >>=′ g)
  (λ _ → ⇒≡ 1 truncation-is-proposition)
  (λ _ → refl _)
  x

instance

  -- The propositional truncation operator is a monad.

  raw-monad : ∀ {ℓ} → Raw-monad (∥_∥ {a = ℓ})
  Raw-monad.return raw-monad = ∣_∣
  Raw-monad._>>=_  raw-monad = _>>=′_

  monad : ∀ {ℓ} → Monad (∥_∥ {a = ℓ})
  Monad.raw-monad monad           = raw-monad
  Monad.left-identity monad x f   = refl _
  Monad.associativity monad x _ _ = >>=′-associative x
  Monad.right-identity monad      = elim
    _
    (λ _ → ⇒≡ 1 truncation-is-proposition)
    (λ _ → refl _)

-- Surjectivity.

Surjective :
  {A : Type a} {B : Type b} →
  (A → B) → Type (a ⊔ b)
Surjective f = ∀ b → ∥ f ⁻¹ b ∥

-- The property Surjective f is a proposition.

Surjective-propositional : {f : A → B} → Is-proposition (Surjective f)
Surjective-propositional =
  Π-closure ext 1 λ _ →
  truncation-is-proposition

-- In an erased context surjectivity with erased proofs is equivalent
-- to surjectivity.
--
-- It appears to me as if neither direction of this equivalence can be
-- established if the erasure annotation is removed.

@0 Surjectiveᴱ≃Surjective : Surjectiveᴱ f ≃ Surjective f
Surjectiveᴱ≃Surjective {f} =
  (∀ y → ∥ f ⁻¹ᴱ y ∥ᴱ)  ↝⟨ (∀-cong ext λ _ → ∥∥ᴱ≃∥∥) ⟩
  (∀ y → ∥ f ⁻¹ᴱ y ∥)   ↝⟨ (∀-cong ext λ _ → ∥∥-cong (inverse ECP.⁻¹≃⁻¹ᴱ)) ⟩□
  (∀ y → ∥ f ⁻¹  y ∥)   □

-- The function ∣_∣ is surjective.

∣∣-surjective : Surjective (∣_∣ {A = A})
∣∣-surjective = elim
  _
  (λ _ → truncation-is-proposition)
  (λ x → ∣ x , refl _ ∣)

-- Split surjective functions are surjective.

Split-surjective→Surjective :
  {f : A → B} → Split-surjective f → Surjective f
Split-surjective→Surjective s = λ b → ∣ s b ∣

-- Being both surjective and an embedding is equivalent to being an
-- equivalence.
--
-- This is Corollary 4.6.4 from the first edition of the HoTT book
-- (the proof is perhaps not quite identical).

surjective×embedding≃equivalence :
  {f : A → B} →
  (Surjective f × Is-embedding f) ≃ Is-equivalence f
surjective×embedding≃equivalence {f} =
  (Surjective f × Is-embedding f)          ↔⟨ ∀-cong ext (λ _ → ∥∥↔∥∥ lzero) ×-cong F.id ⟩
  (Trunc.Surjective _ f × Is-embedding f)  ↝⟨ Trunc.surjective×embedding≃equivalence lzero ext ⟩□
  Is-equivalence f                         □

-- If the underlying type is a proposition, then truncations of the
-- type are isomorphic to the type itself.

∥∥↔ : Is-proposition A → ∥ A ∥ ↔ A
∥∥↔ A-prop = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec A-prop id
      ; from = ∣_∣
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → truncation-is-proposition _ _
  }

-- A type is a proposition if it is equivalent to the propositional
-- truncation of some type.

≃∥∥→Is-proposition : A ≃ ∥ B ∥ → Is-proposition A
≃∥∥→Is-proposition A≃∥B∥ a₁ a₂ =     $⟨ truncation-is-proposition _ _ ⟩
  _≃_.to A≃∥B∥ a₁ ≡ _≃_.to A≃∥B∥ a₂  ↝⟨ Eq.≃-≡ A≃∥B∥ ⟩□
  a₁ ≡ a₂                            □

-- A simple isomorphism involving propositional truncation.

∥∥×↔ : ∥ A ∥ × A ↔ A
∥∥×↔ =
  drop-⊤-left-× λ a →
  _⇔_.to contractible⇔↔⊤ $
    propositional⇒inhabited⇒contractible
      truncation-is-proposition
      ∣ a ∣

-- A variant of ∥∥×↔, introduced to ensure that the right-inverse-of
-- proof is, by definition, simple.

∥∥×≃ : (∥ A ∥ × A) ≃ A
∥∥×≃ = Eq.↔→≃
  proj₂
  (λ x → ∣ x ∣ , x)
  refl
  (λ _ → cong (_, _) (truncation-is-proposition _ _))

_ : _≃_.right-inverse-of ∥∥×≃ x ≡ refl _
_ = refl _

-- A variant of ∥∥×≃.

Erased-∥∥×≃ : (Erased ∥ A ∥ × A) ≃ A
Erased-∥∥×≃ = Eq.↔→≃
  proj₂
  (λ x → E.[ ∣ x ∣ ] , x)
  refl
  (λ { (E.[ _ ] , x) →
       cong (_, x) (E.[]-cong E.[ truncation-is-proposition _ _ ]) })

_ : _≃_.right-inverse-of Erased-∥∥×≃ x ≡ refl _
_ = refl _

-- ∥_∥ commutes with _×_.

∥∥×∥∥↔∥×∥ : (∥ A ∥ × ∥ B ∥) ↔ ∥ A × B ∥
∥∥×∥∥↔∥×∥ = record
  { surjection = record
    { logical-equivalence = record
      { from = λ p → ∥∥-map proj₁ p , ∥∥-map proj₂ p
      ; to   = λ { (x , y) →
                   rec truncation-is-proposition
                       (λ x → rec truncation-is-proposition
                                  (λ y → ∣ x , y ∣)
                                  y)
                       x }
      }
    ; right-inverse-of = λ _ → truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ →
      ×-closure 1 truncation-is-proposition
                  truncation-is-proposition
        _ _
  }

-- A zip function.

∥∥-zip : (A → B → C) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
∥∥-zip {A} {B} {C} f = curry
  (∥ A ∥ × ∥ B ∥  ↔⟨ ∥∥×∥∥↔∥×∥ ⟩
   ∥ A × B ∥      →⟨ ∥∥-map (uncurry f) ⟩□
   ∥ C ∥          □)

-- Variants of proj₁-closure.

private

  H-level-×₁-lemma :
    (A → ∥ B ∥) →
    ∀ n → H-level (suc n) (A × B) → H-level (suc n) A
  H-level-×₁-lemma inhabited n h =
    [inhabited⇒+]⇒+ n λ a →
    rec (H-level-propositional ext (suc n))
        (λ b → proj₁-closure (λ _ → b) (suc n) h)
        (inhabited a)

H-level-×₁ :
  (A → ∥ B ∥) →
  ∀ n → H-level n (A × B) → H-level n A
H-level-×₁ inhabited zero h =
  propositional⇒inhabited⇒contractible
    (H-level-×₁-lemma inhabited 0 (mono₁ 0 h))
    (proj₁ (proj₁ h))
H-level-×₁ inhabited (suc n) =
  H-level-×₁-lemma inhabited n

H-level-×₂ :
  (B → ∥ A ∥) →
  ∀ n → H-level n (A × B) → H-level n B
H-level-×₂ {B} {A} inhabited n =
  H-level n (A × B)  ↝⟨ H-level.respects-surjection (from-bijection ×-comm) n ⟩
  H-level n (B × A)  ↝⟨ H-level-×₁ inhabited n ⟩□
  H-level n B        □

-- If A is merely inhabited, then the truncation of A is isomorphic to
-- the unit type.

inhabited⇒∥∥↔⊤ : ∥ A ∥ → ∥ A ∥ ↔ ⊤
inhabited⇒∥∥↔⊤ ∥a∥ =
  _⇔_.to contractible⇔↔⊤ $
    propositional⇒inhabited⇒contractible
      truncation-is-proposition
      ∥a∥

-- If A is not inhabited, then the propositional truncation of A is
-- isomorphic to the empty type.

not-inhabited⇒∥∥↔⊥ : ¬ A → ∥ A ∥ ↔ ⊥ {ℓ = ℓ}
not-inhabited⇒∥∥↔⊥ {A} =
  ¬ A        ↝⟨ (λ ¬a ∥a∥ → rec ⊥-propositional ¬a ∥a∥) ⟩
  ¬ ∥ A ∥    ↝⟨ inverse ∘ Bijection.⊥↔uninhabited ⟩□
  ∥ A ∥ ↔ ⊥  □

-- The negation of the truncation of A is isomorphic to the negation
-- of A.

¬∥∥↔¬ : ¬ ∥ A ∥ ↔ ¬ A
¬∥∥↔¬ {A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → f ∘ ∣_∣
      ; from = rec ⊥-propositional
      }
    ; right-inverse-of = λ _ → ¬-propositional ext _ _
    }
  ; left-inverse-of = λ _ → ¬-propositional ext _ _
  }

-- The function λ R x y → ∥ R x y ∥ preserves Is-equivalence-relation.

∥∥-preserves-Is-equivalence-relation :
  Is-equivalence-relation R →
  Is-equivalence-relation (λ x y → ∥ R x y ∥)
∥∥-preserves-Is-equivalence-relation R-equiv = record
  { reflexive  = ∣ reflexive ∣
  ; symmetric  = symmetric ⟨$⟩_
  ; transitive = λ p q → transitive ⟨$⟩ p ⊛ q
  }
  where
  open Is-equivalence-relation R-equiv

mutual

  -- The propositional truncation's universal property.

  universal-property :
    Is-proposition B →
    (∥ A ∥ → B) ≃ (A → B)
  universal-property B-prop = universal-property-Π (λ _ → B-prop)

  -- A generalisation of the universal property.

  universal-property-Π :
    (∀ x → Is-proposition (P x)) →
    ((x : ∥ A ∥) → P x) ≃ ((x : A) → P ∣ x ∣)
  universal-property-Π {A} {P} P-prop =
    ((x : ∥ A ∥) → P x)      ↝⟨ Eq.⇔→≃ prop truncation-is-proposition
                                  (λ f → ∣ f ∘ ∣_∣ ∣) (rec prop (elim _ P-prop)) ⟩
    ∥ ((x : A) → P ∣ x ∣) ∥  ↔⟨ ∥∥↔ (Π-closure ext 1 λ _ → P-prop _) ⟩□
    ((x : A) → P ∣ x ∣)      □
    where
    prop = Π-closure ext 1 λ _ → P-prop _

private

  -- The universal property computes in the right way.

  _ :
    (B-prop : Is-proposition B)
    (f : ∥ A ∥ → B) →
    _≃_.to (universal-property B-prop) f ≡ f ∘ ∣_∣
  _ = λ _ _ → refl _

  _ :
    (B-prop : Is-proposition B)
    (f : A → B) (x : A) →
    _≃_.from (universal-property B-prop) f ∣ x ∣ ≡ f x
  _ = λ _ _ _ → refl _

-- If there is a function f : A → ∥ B ∥, then f is an equivalence if
-- and only if the second projection from A × B is an equivalence.

equivalence-to-∥∥≃proj₂-equivalence :
  (f : A → ∥ B ∥) →
  Is-equivalence f ≃ Is-equivalence (proj₂ ⦂ (A × B → B))
equivalence-to-∥∥≃proj₂-equivalence {A} {B} f = Eq.⇔→≃
  (Is-equivalence-propositional ext)
  (Is-equivalence-propositional ext)
  (λ eq → _≃_.is-equivalence
            (A × B      ↝⟨ (×-cong₁ λ _ → Eq.⟨ _ , eq ⟩) ⟩
             ∥ B ∥ × B  ↝⟨ ∥∥×≃ ⟩□
             B          □))
  from
  where
  from : Is-equivalence proj₂ → Is-equivalence f
  from eq = _≃_.is-equivalence $ Eq.⇔→≃
    A-prop
    truncation-is-proposition
    _
    (rec A-prop (proj₁ ∘ _≃_.from Eq.⟨ _ , eq ⟩))
    where
    A-prop₁ : B → Is-proposition A
    A-prop₁ b a₁ a₂ =                  $⟨ refl _ ⟩
      b ≡ b                            ↔⟨⟩
      proj₂ (a₁ , b) ≡ proj₂ (a₂ , b)  ↔⟨ Eq.≃-≡ Eq.⟨ _ , eq ⟩ ⟩
      (a₁ , b) ≡ (a₂ , b)              ↝⟨ cong proj₁ ⟩□
      a₁ ≡ a₂                          □

    A-prop : Is-proposition A
    A-prop = [inhabited⇒+]⇒+ 0
      (A                 ↝⟨ f ⟩
       ∥ B ∥             ↝⟨ rec (H-level-propositional ext 1) A-prop₁ ⟩□
       Is-proposition A  □)

-- There is an equivalence between "A is equivalent to ∥ B ∥" and
-- "there is a function from A to ∥ B ∥ and the second projection is
-- an equivalence from A × B to B".

≃∥∥≃→∥∥×proj₂-equivalence :
  (A ≃ ∥ B ∥) ≃ ((A → ∥ B ∥) × Is-equivalence (proj₂ ⦂ (A × B → B)))
≃∥∥≃→∥∥×proj₂-equivalence {A} {B} =
  A ≃ ∥ B ∥                                           ↔⟨ Eq.≃-as-Σ ⟩
  (∃ λ (f : A → ∥ B ∥) → Is-equivalence f)            ↝⟨ ∃-cong equivalence-to-∥∥≃proj₂-equivalence ⟩□
  (A → ∥ B ∥) × Is-equivalence (proj₂ ⦂ (A × B → B))  □

-- The following three results come from "Generalizations of Hedberg's
-- Theorem" by Kraus, Escardó, Coquand and Altenkirch.

-- Types with constant endofunctions are "h-stable" (meaning that
-- "mere inhabitance" implies inhabitance).

constant-endofunction⇒h-stable : {f : A → A} → Constant f → ∥ A ∥ → A
constant-endofunction⇒h-stable {A} {f} c =
  ∥ A ∥                    ↝⟨ rec (fixpoint-lemma f c) (λ x → f x , c (f x) x) ⟩
  (∃ λ (x : A) → f x ≡ x)  ↝⟨ proj₁ ⟩□
  A                        □

-- Having a constant endofunction is logically equivalent to being
-- h-stable.

constant-endofunction⇔h-stable :
  (∃ λ (f : A → A) → Constant f) ⇔ (∥ A ∥ → A)
constant-endofunction⇔h-stable = record
  { to = λ { (_ , c) → constant-endofunction⇒h-stable c }
  ; from = λ f → f ∘ ∣_∣ , λ x y →

      f ∣ x ∣  ≡⟨ cong f $ truncation-is-proposition _ _ ⟩∎
      f ∣ y ∣  ∎
  }

-- A type is a set if and only if it is "h-separated" (which means
-- that all its equality types are h-stable).

Is-set⇔h-separated :
  Is-set A ⇔ ((x y : A) → ∥ x ≡ y ∥ → x ≡ y)
Is-set⇔h-separated {A} = record
  { to   = λ A-set _ _ → rec A-set id
  ; from =
      ((x y : A) → ∥ x ≡ y ∥ → x ≡ y)                     ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                              _⇔_.from constant-endofunction⇔h-stable) ⟩
      ((x y : A) → ∃ λ (f : x ≡ y → x ≡ y) → Constant f)  ↝⟨ constant⇒set ⟩□
      Is-set A                                            □
  }

-- If A is decided, then ∥ A ∥ is decided.

Dec→Dec-∥∥ : Dec A → Dec ∥ A ∥
Dec→Dec-∥∥ (yes a) = yes ∣ a ∣
Dec→Dec-∥∥ (no ¬A) = no (_↔_.from ¬∥∥↔¬ ¬A)

-- If A is decided (with erased proofs), then ∥ A ∥ is decided (with
-- erased proofs).

Dec-Erased→Dec-Erased-∥∥ : Dec-Erased A → Dec-Erased ∥ A ∥
Dec-Erased→Dec-Erased-∥∥ {A} =
  Dec-Erased A        →⟨ E.Dec-Erased↔Dec-Erased _ ⟩
  Dec (Erased A)      →⟨ Dec→Dec-∥∥ ⟩
  Dec ∥ Erased A ∥    →⟨ Dec-map₀
                           (rec′ λ where
                              .Rec′.∣∣ʳ →
                                E.map ∣_∣
                              .Rec′.truncation-is-propositionʳ →
                                E.H-level-Erased 1 truncation-is-proposition)
                           (λ (E.[ x ]) → ∥∥-map E.[_]→ x) ⟩
  Dec (Erased ∥ A ∥)  →⟨ _⇔_.from (E.Dec-Erased↔Dec-Erased _) ⟩□
  Dec-Erased ∥ A ∥    □

-- If a binary relation can be decided, then the propositional
-- truncation of the relation can also be decided.

ΠΠ-Dec→ΠΠ-Dec-∥∥ :
  {P : A → B → Type p} →
  ((x : A) (y : B) → Dec (P x y)) →
  ((x : A) (y : B) → Dec ∥ P x y ∥)
ΠΠ-Dec→ΠΠ-Dec-∥∥ dec =
  λ x y → Dec→Dec-∥∥ (dec x y)

-- A variant of ΠΠ-Dec→ΠΠ-Dec-∥∥ for Dec-Erased.

ΠΠ-Dec-Erased→ΠΠ-Dec-Erased-∥∥ :
  {P : A → B → Type p} →
  ((x : A) (y : B) → Dec-Erased (P x y)) →
  ((x : A) (y : B) → Dec-Erased ∥ P x y ∥)
ΠΠ-Dec-Erased→ΠΠ-Dec-Erased-∥∥ dec =
  λ x y → Dec-Erased→Dec-Erased-∥∥ (dec x y)

-- If A is decided, then one can convert between ∥ A ∥ and A.

Dec→∥∥⇔ :
  Dec A → ∥ A ∥ ⇔ A
Dec→∥∥⇔ _       ._⇔_.from = ∣_∣
Dec→∥∥⇔ (yes a) ._⇔_.to   = λ _ → a
Dec→∥∥⇔ (no ¬A) ._⇔_.to   = ⊥-elim ∘ rec ⊥-propositional ¬A

-- If A is decided, then one can convert between Erased ∥ A ∥ and A.

Dec→Erased-∥∥⇔ : Dec A → Erased ∥ A ∥ ⇔ A
Dec→Erased-∥∥⇔ {A} dec =
  Erased ∥ A ∥  ↝⟨ record { to = E.Dec→Stable (Dec→Dec-∥∥ dec); from = E.[_]→ } ⟩
  ∥ A ∥         ↝⟨ Dec→∥∥⇔ dec ⟩□
  A             □

-- If A is decided, then one can convert between ∥ Erased A ∥ and A.

Dec→∥Erased∥⇔ : Dec A → ∥ Erased A ∥ ⇔ A
Dec→∥Erased∥⇔ {A} dec =
  ∥ Erased A ∥  ↝⟨ Dec→∥∥⇔ (E.Dec-Erased↔Dec-Erased _ (E.Dec→Dec-Erased dec)) ⟩
  Erased A      ↝⟨ record { to = E.Dec→Stable dec; from = E.[_]→ } ⟩□
  A             □

-- Variants of the following two lemmas were communicated to me by
-- Nicolai Kraus. They are closely related to Lemma 2.1 in his paper
-- "The General Universal Property of the Propositional Truncation".

-- A variant of ∥∥×≃.

drop-∥∥ :
  {B : A → Type b} →
  (A → ∥ C ∥) →
  (∥ C ∥ → ∀ x → B x) ≃ (∀ x → B x)
drop-∥∥ {C} {B} inh =
  Eq.with-other-inverse
    ((∥ C ∥ → ∀ a → B a)  ↔⟨ Π-comm ⟩
     (∀ a → ∥ C ∥ → B a)  ↝⟨ (∀-cong ext λ a → drop-⊤-left-Π ext (inhabited⇒∥∥↔⊤ (inh a))) ⟩□
     (∀ a → B a)          □)
    (λ f _ → f)
    (λ f → ⟨ext⟩ λ _ → ⟨ext⟩ λ a →
       _    ≡⟨ subst-const _ ⟩∎
       f a  ∎)

-- Another variant of ∥∥×≃.

push-∥∥ :
  {B : A → Type b} {C : (∀ x → B x) → Type c} →
  (A → ∥ D ∥) →
  (∥ D ∥ → ∃ λ (f : ∀ x → B x) → C f) ≃
  (∃ λ (f : ∀ x → B x) → ∥ D ∥ → C f)
push-∥∥ {D} {B} {C} inh =
  (∥ D ∥ → ∃ λ (f : ∀ c → B c) → C f)            ↔⟨ ΠΣ-comm ⟩
  (∃ λ (f : ∥ D ∥ → ∀ c → B c) → ∀ b → C (f b))  ↝⟨ (Σ-cong-contra (inverse $ drop-∥∥ inh) λ _ → F.id) ⟩□
  (∃ λ (f : ∀ c → B c) → ∥ D ∥ → C f)            □

-- Having a coherently constant function into a groupoid is equivalent
-- to having a function from a propositionally truncated type into the
-- groupoid. This result is Proposition 2.3 in "The General Universal
-- Property of the Propositional Truncation" by Kraus.

Coherently-constant :
  {A : Type a} {B : Type b} →
  (A → B) → Type (a ⊔ b)
Coherently-constant f =
  ∃ λ (c : Constant f) →
  ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃

coherently-constant-function≃∥inhabited∥⇒inhabited :
  {A : Type a} {B : Type b} →
  H-level 3 B →
  (∃ λ (f : A → B) → Coherently-constant f) ≃ (∥ A ∥ → B)
coherently-constant-function≃∥inhabited∥⇒inhabited
  {a} {b} {A} {B} B-groupoid =

  (∃ λ (f : A → B) → Coherently-constant f)  ↝⟨ Trunc.coherently-constant-function≃∥inhabited∥⇒inhabited lzero ext B-groupoid ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)                ↝⟨ →-cong₁ ext (inverse $ ∥∥↔∥∥ (a ⊔ b)) ⟩□
  (∥ A ∥ → B)                                □

private

  -- One direction of the proposition above computes in the right way.

  to-coherently-constant-function≃∥inhabited∥⇒inhabited :
    (h : H-level 3 B)
    (f : ∃ λ (f : A → B) → Coherently-constant f) (x : A) →
    _≃_.to (coherently-constant-function≃∥inhabited∥⇒inhabited h)
      f ∣ x ∣ ≡
    proj₁ f x
  to-coherently-constant-function≃∥inhabited∥⇒inhabited _ _ _ = refl _

-- Having a constant function into a set is equivalent to having a
-- function from a propositionally truncated type into the set. The
-- statement of this result is that of Proposition 2.2 in "The General
-- Universal Property of the Propositional Truncation" by Kraus, but
-- it uses a different proof: as observed by Kraus this result follows
-- from Proposition 2.3.

constant-function≃∥inhabited∥⇒inhabited :
  {A : Type a} {B : Type b} →
  Is-set B →
  (∃ λ (f : A → B) → Constant f) ≃ (∥ A ∥ → B)
constant-function≃∥inhabited∥⇒inhabited {a} {b} {A} {B} B-set =
  (∃ λ (f : A → B) → Constant f)  ↝⟨ Trunc.constant-function≃∥inhabited∥⇒inhabited lzero ext B-set ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)     ↝⟨ →-cong₁ ext (inverse $ ∥∥↔∥∥ (a ⊔ b)) ⟩□
  (∥ A ∥ → B)                     □

private

  -- One direction of the proposition above computes in the right way.

  to-constant-function≃∥inhabited∥⇒inhabited :
    (B-set : Is-set B)
    (f : ∃ λ (f : A → B) → Constant f) (x : A) →
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited B-set) f ∣ x ∣ ≡
    proj₁ f x
  to-constant-function≃∥inhabited∥⇒inhabited _ _ _ = refl _

------------------------------------------------------------------------
-- Definitions related to truncated binary sums

-- Truncated binary sums.

infixr 1 _∥⊎∥_

_∥⊎∥_ : Type a → Type b → Type (a ⊔ b)
A ∥⊎∥ B = ∥ A ⊎ B ∥

-- Introduction rules.

∣inj₁∣ : A → A ∥⊎∥ B
∣inj₁∣ = ∣_∣ ∘ inj₁

∣inj₂∣ : B → A ∥⊎∥ B
∣inj₂∣ = ∣_∣ ∘ inj₂

-- _∥⊎∥_ is pointwise propositional.

∥⊎∥-propositional : Is-proposition (A ∥⊎∥ B)
∥⊎∥-propositional = truncation-is-proposition

-- _∥⊎∥_ preserves all kinds of functions.

infixr 1 _∥⊎∥-cong_

_∥⊎∥-cong_ : A₁ ↝[ k ] A₂ → B₁ ↝[ k ] B₂ → A₁ ∥⊎∥ B₁ ↝[ k ] A₂ ∥⊎∥ B₂
A₁↝A₂ ∥⊎∥-cong B₁↝B₂ = ∥∥-cong (A₁↝A₂ ⊎-cong B₁↝B₂)

-- _∥⊎∥_ is commutative.

∥⊎∥-comm : A ∥⊎∥ B ↔ B ∥⊎∥ A
∥⊎∥-comm = ∥∥-cong ⊎-comm

-- If one truncates the types to the left or right of _∥⊎∥_, then one
-- ends up with an isomorphic type.

truncate-left-∥⊎∥ : A ∥⊎∥ B ↔ ∥ A ∥ ∥⊎∥ B
truncate-left-∥⊎∥ =
  inverse $ flatten′ (λ F → F _ ⊎ _) (λ f → ⊎-map f id) [ ∥∥-map inj₁ , ∣inj₂∣ ]

truncate-right-∥⊎∥ : A ∥⊎∥ B ↔ A ∥⊎∥ ∥ B ∥
truncate-right-∥⊎∥ {A} {B} =
  A ∥⊎∥ B      ↝⟨ ∥⊎∥-comm ⟩
  B ∥⊎∥ A      ↝⟨ truncate-left-∥⊎∥ ⟩
  ∥ B ∥ ∥⊎∥ A  ↝⟨ ∥⊎∥-comm ⟩□
  A ∥⊎∥ ∥ B ∥  □

-- _∥⊎∥_ is associative.

∥⊎∥-assoc : A ∥⊎∥ (B ∥⊎∥ C) ↔ (A ∥⊎∥ B) ∥⊎∥ C
∥⊎∥-assoc {A} {B} {C} =
  ∥ A ⊎ ∥ B ⊎ C ∥ ∥  ↝⟨ inverse truncate-right-∥⊎∥ ⟩
  ∥ A ⊎ B ⊎ C ∥      ↝⟨ ∥∥-cong ⊎-assoc ⟩
  ∥ (A ⊎ B) ⊎ C ∥    ↝⟨ truncate-left-∥⊎∥ ⟩□
  ∥ ∥ A ⊎ B ∥ ⊎ C ∥  □

-- ⊥ is a left and right identity of _∥⊎∥_ if the other argument is a
-- proposition.

∥⊎∥-left-identity : Is-proposition A → ⊥ {ℓ = ℓ} ∥⊎∥ A ↔ A
∥⊎∥-left-identity {A} A-prop =
  ∥ ⊥ ⊎ A ∥  ↝⟨ ∥∥-cong ⊎-left-identity ⟩
  ∥ A ∥      ↝⟨ ∥∥↔ A-prop ⟩□
  A          □

∥⊎∥-right-identity : Is-proposition A → A ∥⊎∥ ⊥ {ℓ = ℓ} ↔ A
∥⊎∥-right-identity {A} A-prop =
  A ∥⊎∥ ⊥  ↔⟨ ∥⊎∥-comm ⟩
  ⊥ ∥⊎∥ A  ↔⟨ ∥⊎∥-left-identity A-prop ⟩□
  A        □

-- _∥⊎∥_ is idempotent for propositions.

∥⊎∥-idempotent : Is-proposition A → A ∥⊎∥ A ↔ A
∥⊎∥-idempotent {A} A-prop =
  ∥ A ⊎ A ∥  ↝⟨ idempotent ⟩
  ∥ A ∥      ↝⟨ ∥∥↔ A-prop ⟩□
  A          □

-- Sometimes a truncated binary sum is isomorphic to one of its
-- summands.

drop-left-∥⊎∥ :
  Is-proposition B → (A → B) → A ∥⊎∥ B ↔ B
drop-left-∥⊎∥ B-prop A→B =
  _≃_.bijection $
  Eq.⇔→≃ ∥⊎∥-propositional B-prop
    (rec B-prop [ to-implication A→B , id ]) ∣inj₂∣

drop-right-∥⊎∥ :
  Is-proposition A → (B → A) → A ∥⊎∥ B ↔ A
drop-right-∥⊎∥ {A} {B} A-prop B→A =
  A ∥⊎∥ B  ↝⟨ ∥⊎∥-comm ⟩
  B ∥⊎∥ A  ↝⟨ drop-left-∥⊎∥ A-prop B→A ⟩□
  A        □

drop-⊥-right-∥⊎∥ :
  Is-proposition A → ¬ B → A ∥⊎∥ B ↔ A
drop-⊥-right-∥⊎∥ A-prop ¬B =
  drop-right-∥⊎∥ A-prop (⊥-elim ∘ ¬B)

drop-⊥-left-∥⊎∥ :
  Is-proposition B → ¬ A → A ∥⊎∥ B ↔ B
drop-⊥-left-∥⊎∥ B-prop ¬A =
  drop-left-∥⊎∥ B-prop (⊥-elim ∘ ¬A)

-- A type of functions from a truncated binary sum to a family of
-- propositions can be expressed as a binary product of function
-- types.

Π∥⊎∥↔Π×Π :
  (∀ x → Is-proposition (P x)) →
  ((x : A ∥⊎∥ B) → P x)
    ↔
  ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))
Π∥⊎∥↔Π×Π {A} {B} {P} P-prop =
  ((x : A ∥⊎∥ B) → P x)                                ↔⟨ universal-property-Π P-prop ⟩
  ((x : A ⊎ B) → P ∣ x ∣)                              ↝⟨ Π⊎↔Π×Π ext ⟩□
  ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))  □

-- Two distributivity laws for Σ and _∥⊎∥_.

Σ-∥⊎∥-distrib-left :
  Is-proposition A →
  Σ A (λ x → P x ∥⊎∥ Q x) ↔ Σ A P ∥⊎∥ Σ A Q
Σ-∥⊎∥-distrib-left {P} {Q} A-prop =
  (∃ λ x → ∥ P x ⊎ Q x ∥)      ↝⟨ inverse $ ∥∥↔ (Σ-closure 1 A-prop λ _ → ∥⊎∥-propositional) ⟩
  ∥ (∃ λ x → ∥ P x ⊎ Q x ∥) ∥  ↝⟨ flatten′ (λ F → (∃ λ x → F (P x ⊎ Q x))) (λ f → Σ-map id f) (uncurry λ x → ∥∥-map (x ,_)) ⟩
  ∥ (∃ λ x → P x ⊎ Q x) ∥      ↝⟨ ∥∥-cong ∃-⊎-distrib-left ⟩□
  ∥ ∃ P ⊎ ∃ Q ∥                □

Σ-∥⊎∥-distrib-right :
  (∀ x → Is-proposition (P x)) →
  Σ (A ∥⊎∥ B) P ↔ Σ A (P ∘ ∣inj₁∣) ∥⊎∥ Σ B (P ∘ ∣inj₂∣)
Σ-∥⊎∥-distrib-right {A} {B} {P} P-prop =
  _≃_.bijection $
  Eq.⇔→≃ prop₂ prop₁
    (uncurry $
     elim _ (λ _ → Π-closure ext 1 λ _ → prop₁) λ where
       (inj₁ x) y → ∣ inj₁ (x , y) ∣
       (inj₂ x) y → ∣ inj₂ (x , y) ∣)
    (rec prop₂ [ Σ-map ∣inj₁∣ id , Σ-map ∣inj₂∣ id ])
  where
  prop₁ = ∥⊎∥-propositional
  prop₂ = Σ-closure 1 ∥⊎∥-propositional P-prop

-- A variant of one of De Morgan's laws.

¬∥⊎∥¬↔¬× :
  Dec (¬ A) → Dec (¬ B) →
  ¬ A ∥⊎∥ ¬ B ↔ ¬ (A × B)
¬∥⊎∥¬↔¬× {A} {B} dec-¬A dec-¬B = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec (¬-propositional ext) ¬⊎¬→×¬
      ; from = ∣_∣ ∘ _↠_.from (¬⊎¬↠¬× ext dec-¬A dec-¬B)
      }
    ; right-inverse-of = λ _ → ¬-propositional ext _ _
    }
  ; left-inverse-of = λ _ → ∥⊎∥-propositional _ _
  }

-- If ∥ A ∥ is decided, then A ∥⊎∥ B is equivalent to A ∥⊎∥ ¬ A × B.

∥⊎∥≃∥⊎∥¬× :
  Dec ∥ A ∥ →
  (A ∥⊎∥ B) ≃ (A ∥⊎∥ ¬ A × B)
∥⊎∥≃∥⊎∥¬× (yes ∥A∥) = Eq.⇔→≃
  ∥⊎∥-propositional
  ∥⊎∥-propositional
  (const (∥∥-map inj₁ ∥A∥))
  (id ∥⊎∥-cong proj₂)
∥⊎∥≃∥⊎∥¬× (no ¬∥A∥) = Eq.⇔→≃
  ∥⊎∥-propositional
  ∥⊎∥-propositional
  (id ∥⊎∥-cong (¬∥A∥ ∘ ∣_∣) ,_)
  (id ∥⊎∥-cong proj₂)

-- If ∥ B ∥ is decided, then A ∥⊎∥ B is equivalent to ¬ B × A ∥⊎∥ B.

∥⊎∥≃¬×∥⊎∥ :
  Dec ∥ B ∥ →
  (A ∥⊎∥ B) ≃ (¬ B × A ∥⊎∥ B)
∥⊎∥≃¬×∥⊎∥ {B} {A} dec-∥B∥ =
  A ∥⊎∥ B        ↔⟨ ∥⊎∥-comm ⟩
  B ∥⊎∥ A        ↝⟨ ∥⊎∥≃∥⊎∥¬× dec-∥B∥ ⟩
  B ∥⊎∥ ¬ B × A  ↔⟨ ∥⊎∥-comm ⟩□
  ¬ B × A ∥⊎∥ B  □

------------------------------------------------------------------------
-- Code related to Erased-singleton

-- A corollary of erased-singleton-with-erased-center-propositional.

↠→↔Erased-singleton :
  {@0 y : B}
  (A↠B : A ↠ B) →
  Very-stableᴱ-≡ B →
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ ↔ Erased-singleton y
↠→↔Erased-singleton {A} {y} A↠B s =
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥  ↝⟨ ∥∥-cong-⇔ (Surjection.Σ-cong-⇔ A↠B λ _ → F.id) ⟩
  ∥ Erased-singleton y ∥                         ↝⟨ ∥∥↔ (E.erased-singleton-with-erased-center-propositional s) ⟩□
  Erased-singleton y                             □

mutual

  -- The right-to-left direction of the previous lemma does not depend
  -- on the assumption of stability.

  ↠→Erased-singleton→ :
    {@0 y : B}
    (A↠B : A ↠ B) →
    Erased-singleton y →
    ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥
  ↠→Erased-singleton→ = _  -- Agda can infer the definition.

  _ : _↔_.from (↠→↔Erased-singleton A↠B s) x ≡
      ↠→Erased-singleton→ A↠B x
  _ = refl _

-- A corollary of Σ-Erased-Erased-singleton↔ and ↠→↔Erased-singleton.

Σ-Erased-∥-Σ-Erased-≡-∥↔ :
  (A↠B : A ↠ B) →
  Very-stableᴱ-≡ B →
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥) ↔
  B
Σ-Erased-∥-Σ-Erased-≡-∥↔ {A} {B} A↠B s =
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥)  ↝⟨ (∃-cong λ _ → ↠→↔Erased-singleton A↠B s) ⟩

  (∃ λ (x : Erased B) → Erased-singleton (erased x))        ↝⟨ E.Σ-Erased-Erased-singleton↔ ⟩□

  B                                                         □

mutual

  -- Again the right-to-left direction of the previous lemma does not
  -- depend on the assumption of stability.

  →Σ-Erased-∥-Σ-Erased-≡-∥ :
    (A↠B : A ↠ B) →
    B →
    ∃ λ (x : Erased B) →
      ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥
  →Σ-Erased-∥-Σ-Erased-≡-∥ = _  -- Agda can infer the definition.

  _ : _↔_.from (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) x ≡
      →Σ-Erased-∥-Σ-Erased-≡-∥ A↠B x
  _ = refl _

-- In an erased context the left-to-right direction of
-- Σ-Erased-∥-Σ-Erased-≡-∥↔ returns the erased first component.

@0 to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ :
  ∀ (A↠B : A ↠ B) (s : Very-stableᴱ-≡ B) x →
  _↔_.to (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) x ≡ erased (proj₁ x)
to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ A↠B s (E.[ x ] , y) =
  _↔_.to (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) (E.[ x ] , y)  ≡⟨⟩
  proj₁ (_↔_.to (↠→↔Erased-singleton A↠B s) y)           ≡⟨ erased (proj₂ (_↔_.to (↠→↔Erased-singleton A↠B s) y)) ⟩∎
  x                                                      ∎

------------------------------------------------------------------------
-- Some properties that hold for Erased do not hold for every
-- accessible modality

-- It is not the case that, for all types A, ∥ Is-proposition A ∥
-- holds.
--
-- Compare with Erased.Stability.Erased-Very-stable.

¬∥Is-proposition∥ : ¬ ({A : Type a} → ∥ Is-proposition A ∥)
¬∥Is-proposition∥ {a} =
  ({A : Type a} → ∥ Is-proposition A ∥)  →⟨ (λ hyp → hyp) ⟩
  ∥ Is-proposition (↑ a Bool) ∥          →⟨ ∥∥-map (H-level-cong _ 1 Bijection.↑↔) ⟩
  ∥ Is-proposition Bool ∥                →⟨ ∥∥-map ¬-Bool-propositional ⟩
  ∥ ⊥ ∥                                  ↔⟨ ∥∥↔ ⊥-propositional ⟩□
  ⊥                                      □

-- It is not the case that, for all types A and B and functions
-- f : A → B, "f is ∥∥-connected" implies ∥ Is-equivalence f ∥.

¬[∥∥-connected→∥Is-equivalence∥] :
  ¬ ({A : Type a} {B : Type b} {f : A → B} →
     (∀ y → Contractible ∥ f ⁻¹ y ∥) → ∥ Is-equivalence f ∥)
¬[∥∥-connected→∥Is-equivalence∥] hyp =
                                                                   $⟨ (λ _ → ∣ lift true , refl _ ∣) ⟩

  ((y : ↑ _ ⊤) → ∥ (const (lift tt) ⦂ (↑ _ Bool → ↑ _ ⊤)) ⁻¹ y ∥)  →⟨ (∀-cong _ λ _ →
                                                                       propositional⇒inhabited⇒contractible truncation-is-proposition) ⟩
  ((y : ↑ _ ⊤) →
   Contractible ∥ (const (lift tt) ⦂ (↑ _ Bool → ↑ _ ⊤)) ⁻¹ y ∥)   →⟨ hyp ⟩

  ∥ Is-equivalence (const (lift tt) ⦂ (↑ _ Bool → ↑ _ ⊤)) ∥        ↔⟨ ∥∥↔ (Is-equivalence-propositional ext) ⟩

  Is-equivalence (const (lift tt) ⦂ (↑ _ Bool → ↑ _ ⊤))            →⟨ Eq.⟨ _ ,_⟩ ⟩

  ↑ _ Bool ≃ ↑ _ ⊤                                                 →⟨ (λ eq → Eq.↔⇒≃ Bijection.↑↔ F.∘ eq F.∘ Eq.↔⇒≃ (inverse Bijection.↑↔)) ⟩

  Bool ≃ ⊤                                                         →⟨ (λ eq → H-level-cong _ 1 (inverse eq) (mono₁ 0 ⊤-contractible)) ⟩

  Is-proposition Bool                                              →⟨ ¬-Bool-propositional ⟩□

  ⊥                                                                □

-- It is not the case that, for all types A and B and functions
-- f : A → B, "f is ∥∥-connected" is equivalent to
-- ∥ Is-equivalence f ∥.
--
-- Compare with
-- Erased.Level-1.[]-cong₂-⊔.Erased-connected↔Erased-Is-equivalence.

¬[∥∥-connected≃∥Is-equivalence∥] :
  ¬ ({A : Type a} {B : Type b} {f : A → B} →
     (∀ y → Contractible ∥ f ⁻¹ y ∥) ≃ ∥ Is-equivalence f ∥)
¬[∥∥-connected≃∥Is-equivalence∥] hyp =
  ¬[∥∥-connected→∥Is-equivalence∥] (_≃_.to hyp)

-- If (x : A) → ∥ P x ∥ implies ∥ ((x : A) → P x) ∥ for all types A
-- and type families P over A, then the axiom of choice holds.

[Π∥∥→∥Π∥]→Axiom-of-choice :
  ({A : Type a} {P : A → Type p} →
   ((x : A) → ∥ P x ∥) → ∥ ((x : A) → P x) ∥) →
  Axiom-of-choice a p
[Π∥∥→∥Π∥]→Axiom-of-choice hyp = λ _ → hyp

-- If ∥ ((x : A) → P x) ∥ is isomorphic to (x : A) → ∥ P x ∥ for all
-- types A and type families P over A, then the axiom of choice holds.
--
-- Compare with Erased.Level-1.Erased-Π↔Π.

[∥Π∥↔Π∥∥]→Axiom-of-choice :
  ({A : Type a} {P : A → Type p} →
   ∥ ((x : A) → P x) ∥ ↔ ((x : A) → ∥ P x ∥)) →
  Axiom-of-choice a p
[∥Π∥↔Π∥∥]→Axiom-of-choice hyp =
  [Π∥∥→∥Π∥]→Axiom-of-choice (_↔_.from hyp)

-- If ∥ A ∥ → ∥ B ∥ implies ∥ (A → B) ∥ for all types A and B in the
-- same universe, then ∥ (∥ A ∥ → A) ∥ holds for every type A in this
-- universe. This is a variant of the axiom of choice of which Kraus
-- et al. state that "We expect that this makes it possible to show
-- that, in MLTT with weak propositional truncation, [a logically
-- equivalent variant of the axiom] is not derivable" (see "Notions of
-- Anonymous Existence in Martin-Löf Type Theory").

[[∥∥→∥∥]→∥→∥]→Axiom-of-choice :
  ({A B : Type a} → (∥ A ∥ → ∥ B ∥) → ∥ (A → B) ∥) →
  ({A : Type a} → ∥ (∥ A ∥ → A) ∥)
[[∥∥→∥∥]→∥→∥]→Axiom-of-choice hyp {A} =
                       $⟨ rec truncation-is-proposition id ⟩
  (∥ ∥ A ∥ ∥ → ∥ A ∥)  →⟨ hyp ⟩□
  ∥ (∥ A ∥ → A) ∥      □

-- If ∥ (A → B) ∥ is isomorphic to ∥ A ∥ → ∥ B ∥ for all types A and B
-- in the same universe, then ∥ (∥ A ∥ → A) ∥ holds for every type A
-- in this universe. This is a variant of the axiom of choice of which
-- Kraus et al. state that "We expect that this makes it possible to
-- show that, in MLTT with weak propositional truncation, [a logically
-- equivalent variant of the axiom] is not derivable" (see "Notions of
-- Anonymous Existence in Martin-Löf Type Theory").
--
-- Compare with Erased.Level-1.Erased-Π↔Π-Erased.

[∥→∥↔[∥∥→∥∥]]→Axiom-of-choice :
  ({A B : Type a} → ∥ (A → B) ∥ ↔ (∥ A ∥ → ∥ B ∥)) →
  ({A : Type a} → ∥ (∥ A ∥ → A) ∥)
[∥→∥↔[∥∥→∥∥]]→Axiom-of-choice hyp =
  [[∥∥→∥∥]→∥→∥]→Axiom-of-choice (_↔_.from hyp)

-- It is not the case that, for every type A, if A is Is-proposition,
-- then A is (λ (A : Type a) → Is-proposition A)-null.

¬[Is-proposition→Is-proposition-Null] :
  ¬ ({A : Type a} →
     Is-proposition A → (λ (A : Type a) → Is-proposition A) -Null A)
¬[Is-proposition→Is-proposition-Null] hyp =                     $⟨ ⊥-propositional ⟩
  Is-proposition ⊥                                              →⟨ hyp ⟩
  (∀ A → Is-equivalence (const ⦂ (⊥ → Is-proposition A → ⊥)))   →⟨ _$ _ ⟩
  Is-equivalence (const ⦂ (⊥ → Is-proposition (↑ _ Bool) → ⊥))  →⟨ Eq.⟨ _ ,_⟩ ⟩
  ⊥ ≃ (Is-proposition (↑ _ Bool) → ⊥)                           →⟨ →-cong ext
                                                                     (Eq.↔⇒≃ $ inverse $
                                                                      Bijection.⊥↔uninhabited (¬-Bool-propositional ∘ ↑⁻¹-closure 1))
                                                                     Eq.id F.∘_ ⟩
  ⊥ ≃ (⊥₀ → ⊥)                                                  →⟨ Π⊥↔⊤ ext F.∘_ ⟩
  ⊥ ≃ ⊤                                                         →⟨ (λ eq → ⊥-elim $ _≃_.from eq _) ⟩□
  ⊥                                                             □

-- It is not the case that, for every type A, there is an equivalence
-- between "A is Is-proposition" and
-- (λ (A : Type a) → Is-proposition A) -Null A.
--
-- Compare with Erased.Stability.Very-stable≃Very-stable-Null.

¬[Is-proposition≃Is-proposition-Null] :
  ¬ ({A : Type a} →
     Is-proposition A ≃ (λ (A : Type a) → Is-proposition A) -Null A)
¬[Is-proposition≃Is-proposition-Null] hyp =
  ¬[Is-proposition→Is-proposition-Null] (_≃_.to hyp)

-- It is not the case that, for every type A : Type a and proof of
-- Extensionality a a, there is an equivalence between "A is
-- Is-proposition" and (λ (A : Type a) → Is-proposition A) -Null A.
--
-- Compare with Erased.Stability.Very-stable≃Very-stable-Null.

¬[Is-proposition≃Is-proposition-Null]′ :
  ¬ ({A : Type a} →
     Extensionality a a →
     Is-proposition A ≃ (λ (A : Type a) → Is-proposition A) -Null A)
¬[Is-proposition≃Is-proposition-Null]′ hyp =
  ¬[Is-proposition≃Is-proposition-Null] (hyp ext)
