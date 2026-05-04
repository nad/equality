------------------------------------------------------------------------
-- An axiomatised variant of the propositional truncation operator
-- with an erased truncation constructor
------------------------------------------------------------------------

-- Partly following the HoTT book, but adapted for erasure.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module H-level.Truncation.Propositional.Erased.Axiomatised
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq hiding (elim)

open import Prelude as P
open import Logical-equivalence using (_⇔_)

open import Accessibility eq as A using (Acc)
open import Bijection eq as Bijection using (_↔_)
open import Embedding eq as Emb using (Is-embedding)
open import Equality.Decidable-UIP eq
open import Equivalence eq as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased eq as EEq
  using (_≃ᴱ_; _≃ᴱ′_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (Contractibleᴱ; _⁻¹ᴱ_)
open import Equivalence.Path-split eq
  using (Is-∞-extendable-along-[_])
open import Equivalence-relation eq
open import Erased.Level-1 eq as E₁
  using (Erased; [_]; erased)
import Erased.Level-2 eq as E₂
open import Erased.Stability eq as ES using (Erased-singleton)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Modality.Basics eq
open import Monad eq
open import Surjection eq as S
  using (_↠_; Split-surjective)

private variable
  a b ℓ p           : Level
  A A₁ A₂ B B₁ B₂ C : Type _
  P Q               : A → Type _
  R                 : A → A → Type _
  e f g k r x       : A

-- An axiomatisation of propositional truncation with an erased
-- "higher constructor".

record Truncationᴱ : Typeω where
  field
    -- The truncation operator and its "constructors".
    ∥_∥ᴱ                         : Type a → Type a
    ∣_∣                          : A → ∥ A ∥ᴱ
    @0 truncation-is-proposition : Is-proposition ∥ A ∥ᴱ

    -- An eliminator.
    eliminator :
      ((x : A) → P ∣ x ∣) →
      @0 ((x : ∥ A ∥ᴱ) → Is-proposition (P x)) →
      (x : ∥ A ∥ᴱ) → P x

    -- A computation rule for the eliminator.
    eliminator-∣∣ :
      {@0 p : (x : ∥ A ∥ᴱ) → Is-proposition (P x)} →
      eliminator f p ∣ x ∣ ≡ f x

  ----------------------------------------------------------------------
  -- Eliminators

  -- An eliminator expressed using a record type.

  record Elim {A : Type a} (P : ∥ A ∥ᴱ → Type p) : Type (a ⊔ p) where
    no-eta-equality
    field
      ∣∣ʳ                           : (x : A) → P ∣ x ∣
      @0 truncation-is-propositionʳ :
        (x : ∥ A ∥ᴱ) → Is-proposition (P x)

  open Elim public

  opaque

    elim : {P : ∥ A ∥ᴱ → Type p} → Elim P → (x : ∥ A ∥ᴱ) → P x
    elim e = eliminator E.∣∣ʳ E.truncation-is-propositionʳ
      where
      module E = Elim e

    elim-∣∣ : elim e ∣ x ∣ ≡ Elim.∣∣ʳ e x
    elim-∣∣ = eliminator-∣∣

  -- Primitive "recursion".

  record Rec (A : Type a) (B : Type b) : Type (a ⊔ b) where
    no-eta-equality
    field
      ∣∣ʳ                           : A → B
      @0 truncation-is-propositionʳ : Is-proposition B

  open Rec public

  opaque
    unfolding elim

    rec : Rec A B → ∥ A ∥ᴱ → B
    rec r = elim λ where
        .∣∣ʳ                          → R.∣∣ʳ
        .truncation-is-propositionʳ _ → R.truncation-is-propositionʳ
      where
      module R = Rec r

    rec-∣∣ : rec r ∣ x ∣ ≡ Rec.∣∣ʳ r x
    rec-∣∣ = eliminator-∣∣

  ----------------------------------------------------------------------
  -- ∥_∥ᴱ is a modality

  opaque

    -- ∥_∥ᴱ and ∣_∣ form a modality, where a type A is modal if
    -- Erased (Is-proposition A) holds.

    ∥∥ᴱ-modality : Modality ℓ
    ∥∥ᴱ-modality {ℓ} = λ where
        .◯            → ∥_∥ᴱ
        .η            → ∣_∣
        .modality-for → λ where
          .Modal A                 → Erased (Is-proposition A)
          .Modal-propositional ext →
            E₁.[]-cong₁.H-level-Erased
              (E₁.Extensionality→[]-cong-axiomatisation ext)
              1 (H-level-propositional ext 1)
          .Modal-◯              → [ truncation-is-proposition ]
          .Modal-respects-≃     → λ A≃B → E₁.map (H-level-cong _ 1 A≃B)
          .extendable-along-η p → extendable (erased ∘ p)
      where
      open Modality
      open Modality-for

      extendable :
        {A : Type ℓ} {P : ∥ A ∥ᴱ → Type ℓ} →
        @0 (∀ x → Is-proposition (P x)) →
        Is-∞-extendable-along-[ ∣_∣ ] P
      extendable _    zero    = _
      extendable prop (suc n) =
        (λ f →
           (elim λ where
              .∣∣ʳ                        → f
              .truncation-is-propositionʳ → prop) ,
           (λ _ → elim-∣∣)) ,
        (λ _ _ → extendable (λ x → mono₁ 1 (prop x)) n)

  opaque
    unfolding ∥∥ᴱ-modality

    -- The modality is empty-modal.

    ∥∥ᴱ-empty-modal : Empty-modal (∥∥ᴱ-modality {ℓ = ℓ})
    ∥∥ᴱ-empty-modal = [ ⊥-propositional ]

  opaque
    unfolding ∥∥ᴱ-modality

    -- The modality is not left exact.

    ¬-∥∥ᴱ-left-exact : ¬ Left-exact (∥_∥ᴱ {a = a})
    ¬-∥∥ᴱ-left-exact {a} =
      ES.Stable-¬
        [ Empty-modal→Is-proposition-◯→¬-Left-exact
            ∥∥ᴱ-empty-modal truncation-is-proposition
        ]
      where
      open Modality (∥∥ᴱ-modality {ℓ = a})

  opaque
    unfolding ∥∥ᴱ-modality

    -- The modality is not very modal.

    ¬-∥∥ᴱ-very-modal : ¬ Very-modal (∥∥ᴱ-modality {ℓ = ℓ})
    ¬-∥∥ᴱ-very-modal {ℓ} =
      Very-modal (∥∥ᴱ-modality {ℓ = ℓ})                ↔⟨⟩
      ({A : Type ℓ} → ∥ Erased (Is-proposition A) ∥ᴱ)  →⟨ (λ hyp → hyp) ⟩
      ∥ Erased (Is-proposition (↑ ℓ Bool)) ∥ᴱ          →⟨ ◯-map (E₁.map (⊥-elim ∘ ¬-Bool-propositional ∘ H-level-cong _ 1 Bijection.↑↔)) ⟩
      ∥ Erased ⊥ ∥ᴱ                                    →⟨ ◯-map (_↔_.to E₁.Erased-⊥↔⊥) ⟩
      ∥ ⊥ ∥ᴱ                                           →⟨ ⊥-elim ∘ Modal→Stable ∥∥ᴱ-empty-modal ⟩□
      ⊥                                                □
      where
      open Modality (∥∥ᴱ-modality {ℓ = ℓ})

  opaque
    unfolding ∥∥ᴱ-modality

    -- The modality is W-modal (assuming erased function
    -- extensionality).

    ∥∥ᴱ-W-modal :
      @0 Extensionality ℓ ℓ →
      W-modal (∥∥ᴱ-modality {ℓ = ℓ})
    ∥∥ᴱ-W-modal ext [ p ] = [ W-closure ext 0 p ]

  opaque
    unfolding ∥∥ᴱ-modality

    -- The modality is not accessibility-modal.

    ¬-∥∥ᴱ-accessibility-modal :
      ¬ Modality.Accessibility-modal (∥∥ᴱ-modality {ℓ = ℓ})
    ¬-∥∥ᴱ-accessibility-modal {ℓ} acc =
      ES.Very-stable→Stable 0 ES.Very-stable-⊥
        [ Is-proposition-◯→¬-Accessibility-modal
            truncation-is-proposition acc
        ]
      where
      open Modality (∥∥ᴱ-modality {ℓ = ℓ})

  opaque
    unfolding ∥∥ᴱ-modality

    -- The modality is accessibility-modal for propositional types and
    -- relations (assuming erased function extensionality).

    Is-proposition→∥∥ᴱ-accessibility-modal :
      {A : Type ℓ} {_<_ : A → A → Type ℓ} →
      @0 Extensionality ℓ ℓ →
      @0 Is-proposition A →
      @0 (∀ x y → Is-proposition (x < y)) →
      Modality.Accessibility-modal-for ∥∥ᴱ-modality _<_
    Is-proposition→∥∥ᴱ-accessibility-modal {ℓ} ext p₁ p₂ =
        (λ acc →
           Modal→Acc→Acc-[]◯-η
             [ p₁ ]
             (rec λ where
                .∣∣ʳ                        → id
                .truncation-is-propositionʳ → p₂ _ _)
             acc)
      , (rec λ where
           .∣∣ʳ                        → id
           .truncation-is-propositionʳ → A.Acc-propositional ext)
      where
      open Modality (∥∥ᴱ-modality {ℓ = ℓ})

  opaque
    unfolding ∥∥ᴱ-modality

    -- If the modality is accessibility-modal for all relations for a
    -- type A, then all values of type A are not not equal.

    ∥∥ᴱ-accessibility-modal→¬¬≡ :
      {x y : A} →
      ({_<_ : A → A → Type ℓ} →
       Modality.Accessibility-modal-for ∥∥ᴱ-modality _<_) →
      ¬ ¬ x ≡ y
    ∥∥ᴱ-accessibility-modal→¬¬≡ {ℓ} {A} {x} {y} acc x≢y =
      ES.Very-stable→Stable₀ ES.Very-stable-⊥
        [                        $⟨ (A.acc λ _ x≡y → ⊥-elim $ x≢y x≡y) ⟩
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
        ]
      where
      open Modality (∥∥ᴱ-modality {ℓ = ℓ})

      _<_ : A → A → Type ℓ
      _ < z = z ≡ y

  opaque
    unfolding ∥∥ᴱ-modality Modality.◯-rec

    -- ∥_∥ᴱ commutes with Σ (assuming erased function extensionality).

    ∥∥ᴱ-commutes-with-Σ :
      @0 Extensionality ℓ ℓ →
      Modality.Commutes-with-Σ (∥∥ᴱ-modality {ℓ = ℓ})
    ∥∥ᴱ-commutes-with-Σ ext {A} {P} =
      _≃_.is-equivalence $
      Eq.↔→≃ to (uncurry (elim e′))
        (uncurry $
         elim λ where
           .∣∣ʳ x → elim λ where
             .∣∣ʳ y →
               to (elim e′ ∣ x ∣ ∣ y ∣)  ≡⟨ cong to $ trans (cong (_$ ∣ y ∣) elim-∣∣) rec-∣∣ ⟩
               to ∣ x , y ∣              ≡⟨ elim-∣∣ ⟩∎
               ∣ x ∣ , ∣ y ∣             ∎
             .truncation-is-propositionʳ _ →
               mono₁ 1 $
               Σ-closure 1 truncation-is-proposition λ _ →
               truncation-is-proposition
           .truncation-is-propositionʳ _ →
             Π-closure ext 1 λ _ →
             mono₁ 1 $
             Σ-closure 1 truncation-is-proposition λ _ →
             truncation-is-proposition)
        (elim λ where
           .∣∣ʳ (x , y) →
             uncurry (elim e′) (to ∣ x , y ∣)  ≡⟨ cong (uncurry (elim e′)) elim-∣∣ ⟩
             elim e′ ∣ x ∣ ∣ y ∣               ≡⟨ trans (cong (_$ ∣ y ∣) elim-∣∣) rec-∣∣ ⟩
             ∣ x , y ∣                         ∎
           .truncation-is-propositionʳ _ →
             mono₁ 1 truncation-is-proposition)
      where
      to : ∥ (∃ λ x → P ∣ x ∣) ∥ᴱ → ∃ λ (x : ∥ A ∥ᴱ) → ∥ P x ∥ᴱ
      to = Modality.◯Ση≃Σ◯◯ ∥∥ᴱ-modality _

      r′ : ∀ x → Rec (P ∣ x ∣) ∥ (∃ λ x → P ∣ x ∣) ∥ᴱ
      r′ x .∣∣ʳ y                      = ∣ x , y ∣
      r′ _ .truncation-is-propositionʳ = truncation-is-proposition

      e′ : Elim (λ x → (y : ∥ P x ∥ᴱ) → ∥ (∃ λ x → P ∣ x ∣) ∥ᴱ)
      e′ .∣∣ʳ x                        = rec (r′ x)
      e′ .truncation-is-propositionʳ _ =
        Π-closure ext 1 λ _ → truncation-is-proposition

  ----------------------------------------------------------------------
  -- Some preservation lemmas and related results

  opaque
    unfolding rec

    -- A map function.

    ∥∥ᴱ-map : (A → B) → ∥ A ∥ᴱ → ∥ B ∥ᴱ
    ∥∥ᴱ-map f = rec λ where
      .∣∣ʳ                        → ∣_∣ ∘ f
      .truncation-is-propositionʳ → truncation-is-proposition

  opaque
    unfolding ∥∥ᴱ-map

    -- A "computation" rule.

    ∥∥ᴱ-map-∣∣ : ∥∥ᴱ-map f ∣ x ∣ ≡ ∣ f x ∣
    ∥∥ᴱ-map-∣∣ = eliminator-∣∣

  opaque
   unfolding rec
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

  opaque
    unfolding ∥∥ᴱ-map

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
            ∥∥ᴱ-map (_↠_.to A↠B) (∥∥ᴱ-map (_↠_.from A↠B) ∣ x ∣)  ≡⟨ trans (cong (∥∥ᴱ-map _) ∥∥ᴱ-map-∣∣) ∥∥ᴱ-map-∣∣ ⟩
            ∣ _↠_.to A↠B (_↠_.from A↠B x) ∣                      ≡⟨ cong ∣_∣ (_↠_.right-inverse-of A↠B x) ⟩∎
            ∣ x ∣                                                ∎
          .truncation-is-propositionʳ _ →
            mono₁ 1 truncation-is-proposition
      }

  private opaque
    unfolding ∥∥ᴱ-cong-↠

    ∥∥ᴱ-cong-↔ : A ↔ B → ∥ A ∥ᴱ ↔ ∥ B ∥ᴱ
    ∥∥ᴱ-cong-↔ A↔B = record
      { surjection      = ∥∥ᴱ-cong-↠ (_↔_.surjection A↔B)
      ; left-inverse-of = elim λ where
          .∣∣ʳ x →
            ∥∥ᴱ-map (_↔_.from A↔B) (∥∥ᴱ-map (_↔_.to A↔B) ∣ x ∣)  ≡⟨ trans (cong (∥∥ᴱ-map _) ∥∥ᴱ-map-∣∣) ∥∥ᴱ-map-∣∣ ⟩
            ∣ _↔_.from A↔B (_↔_.to A↔B x) ∣                      ≡⟨ cong ∣_∣ (_↔_.left-inverse-of A↔B x) ⟩∎
            ∣ x ∣                                                ∎
          .truncation-is-propositionʳ _ →
            mono₁ 1 truncation-is-proposition
      }

  opaque
    unfolding ∥∥ᴱ-cong-⇔ ∥∥ᴱ-cong-↔

    -- The truncation operator preserves "symmetric function types".

    ∥∥ᴱ-cong : A ↝[ ⌊ k ⌋-sym ] B → ∥ A ∥ᴱ ↝[ ⌊ k ⌋-sym ] ∥ B ∥ᴱ
    ∥∥ᴱ-cong {k = logical-equivalence} =
      _≃ᴱ_.logical-equivalence ∘ ∥∥ᴱ-cong-⇔
    ∥∥ᴱ-cong {k = bijection} =
      ∥∥ᴱ-cong-↔
    ∥∥ᴱ-cong {k = equivalence} =
      from-isomorphism ∘ ∥∥ᴱ-cong-↔ ∘ from-isomorphism
    ∥∥ᴱ-cong {k = equivalenceᴱ} =
      ∥∥ᴱ-cong-⇔ ∘ _≃ᴱ_.logical-equivalence

  ----------------------------------------------------------------------
  -- Some (erased) equivalences

  opaque

    -- If the underlying type is a proposition, then truncations of the
    -- type are equivalent to the type itself.

    ∥∥ᴱ≃ : @0 Is-proposition A → ∥ A ∥ᴱ ≃ A
    ∥∥ᴱ≃ A-prop =
      Eq.↔→≃
        (rec λ where
           .∣∣ʳ                        → id
           .truncation-is-propositionʳ → A-prop)
        ∣_∣
        (λ _ → rec-∣∣)
        (elim λ where
           .∣∣ʳ _                        → cong ∣_∣ rec-∣∣
           .truncation-is-propositionʳ _ →
             mono₁ 1 truncation-is-proposition)

  opaque

    -- If A is merely inhabited, then the truncation of A is equivalent
    -- (with erased proofs) to the unit type.

    inhabited⇒∥∥ᴱ≃ᴱ⊤ : ∥ A ∥ᴱ → ∥ A ∥ᴱ ≃ᴱ ⊤
    inhabited⇒∥∥ᴱ≃ᴱ⊤ ∥a∥ =
      EEq.inhabited→Is-proposition→≃ᴱ⊤ ∥a∥ truncation-is-proposition

  opaque

    -- If A is not inhabited, then the propositional truncation of A
    -- is equivalent to the empty type.

    not-inhabited⇒∥∥ᴱ≃⊥ : ¬ A → ∥ A ∥ᴱ ≃ ⊥ {ℓ = ℓ}
    not-inhabited⇒∥∥ᴱ≃⊥ {A} =
      ¬ A         →⟨ (λ ¬a → rec λ where
                               .∣∣ʳ                        → ¬a
                               .truncation-is-propositionʳ → ⊥-propositional) ⟩
      ¬ ∥ A ∥ᴱ    →⟨ inverse ∘ from-isomorphism ∘ Bijection.⊥↔uninhabited ⟩□
      ∥ A ∥ᴱ ≃ ⊥  □

  opaque

    -- The negation of the truncation of A is equivalent with erased
    -- proofs to the negation of A (assuming erased function
    -- extensionality).

    ¬∥∥ᴱ≃ᴱ¬ :
      {A : Type a} →
      @0 Extensionality a lzero →
      (¬ ∥ A ∥ᴱ) ≃ᴱ (¬ A)
    ¬∥∥ᴱ≃ᴱ¬ {A} ext =
      EEq.↔→≃ᴱ
        (_∘ ∣_∣)
        (λ ¬A → rec λ where
           .∣∣ʳ                        → ¬A
           .truncation-is-propositionʳ → ⊥-propositional)
        (λ _ → ¬-propositional ext _ _)
        (λ _ → ¬-propositional ext _ _)

  -- A form of idempotence for binary sums.

  idempotent : ∥ A ⊎ A ∥ᴱ ≃ᴱ ∥ A ∥ᴱ
  idempotent = ∥∥ᴱ-cong-⇔ (record { to = P.[ id , id ]; from = inj₁ })

  ----------------------------------------------------------------------
  -- Some results related to _×_

  opaque

    -- A is equivalent (with one erased proof) to the cartesian
    -- product of the truncation of A and A.

    ≃ᴱ′∥∥ᴱ× : A ≃ᴱ′ (∥ A ∥ᴱ × A)
    ≃ᴱ′∥∥ᴱ× = EEq.↔→≃ᴱ′
      (λ x → ∣ x ∣ , x)
      proj₂
      (λ _ → cong (_, _) (truncation-is-proposition _ _))
      refl

  opaque
    unfolding ≃ᴱ′∥∥ᴱ×

    -- The cartesian product of the truncation of A and A is
    -- equivalent (with erased proofs) to A.

    ∥∥ᴱ×≃ᴱ : (∥ A ∥ᴱ × A) ≃ᴱ A
    ∥∥ᴱ×≃ᴱ = inverse (_≃ᴱ′_.equivalence-with-erased-proofs ≃ᴱ′∥∥ᴱ×)

  opaque
    unfolding ∥∥ᴱ×≃ᴱ

    -- A function used to state right-inverse-of-∥∥ᴱ×≃ᴱ.

    @0 Right-inverse-of-∥∥ᴱ×≃ᴱ : {A : Type a} → A → Type a
    Right-inverse-of-∥∥ᴱ×≃ᴱ x = _≃ᴱ_.right-inverse-of ∥∥ᴱ×≃ᴱ x ≡ refl x

    -- The application _≃ᴱ_.right-inverse-of ∥∥ᴱ×≃ᴱ x computes in a
    -- certain way.

    right-inverse-of-∥∥ᴱ×≃ᴱ : Right-inverse-of-∥∥ᴱ×≃ᴱ x
    right-inverse-of-∥∥ᴱ×≃ᴱ = refl _

  opaque

    -- ∥_∥ᴱ commutes with _×_ (assuming erased function
    -- extensionality).

    ∥∥ᴱ×∥∥ᴱ≃∥×∥ᴱ :
      {A : Type a} {B : Type b} →
      @0 Extensionality b (a ⊔ b) →
      (∥ A ∥ᴱ × ∥ B ∥ᴱ) ≃ ∥ A × B ∥ᴱ
    ∥∥ᴱ×∥∥ᴱ≃∥×∥ᴱ {A} {B} ext =
      Eq.↔→≃ (uncurry (rec r′))
        (λ p → ∥∥ᴱ-map proj₁ p , ∥∥ᴱ-map proj₂ p)
        (elim λ where
            .∣∣ʳ (_ , y) →
              trans (cong₂ (rec r′) ∥∥ᴱ-map-∣∣ ∥∥ᴱ-map-∣∣) $
              trans (cong (_$ ∣ y ∣) rec-∣∣) $
              rec-∣∣
            .truncation-is-propositionʳ _ →
              mono₁ 1 truncation-is-proposition)
        (uncurry $ elim λ where
          .∣∣ʳ _ → elim λ where
            .∣∣ʳ y →
              cong₂ _,_
                (trans
                   (cong (∥∥ᴱ-map _) $
                    trans (cong (_$ ∣ y ∣) rec-∣∣) $
                    rec-∣∣) $
                 ∥∥ᴱ-map-∣∣)
                (trans
                   (cong (∥∥ᴱ-map _) $
                    trans (cong (_$ ∣ y ∣) rec-∣∣) $
                    rec-∣∣) $
                 ∥∥ᴱ-map-∣∣)
            .truncation-is-propositionʳ _ →
              mono₁ 1 $
              ×-closure 1 truncation-is-proposition
                truncation-is-proposition
          .truncation-is-propositionʳ _ →
            Π-closure ext 1 λ _ →
            mono₁ 1 $
            ×-closure 1 truncation-is-proposition
              truncation-is-proposition)
      where
      r′ : Rec A (∥ B ∥ᴱ → ∥ A × B ∥ᴱ)
      r′ .∣∣ʳ x = rec λ where
        .∣∣ʳ y                      → ∣ x , y ∣
        .truncation-is-propositionʳ →
          truncation-is-proposition
      r′ .truncation-is-propositionʳ =
        Π-closure ext 1 λ _ →
        truncation-is-proposition

  ----------------------------------------------------------------------
  -- The universal property, and some related results

  opaque mutual

    -- The propositional truncation operator's universal property.

    universal-property :
      {A : Type a} {B : Type b} →
      Extensionality a b →
      @0 Is-proposition B →
      (∥ A ∥ᴱ → B) ≃ (A → B)
    universal-property ext B-prop = universal-property-Π ext (λ _ → B-prop)

    -- A generalisation of universal-property.

    universal-property-Π :
      {A : Type a} {P : ∥ A ∥ᴱ → Type p} →
      Extensionality a p →
      @0 (∀ x → Is-proposition (P x)) →
      ((x : ∥ A ∥ᴱ) → P x) ≃ ((x : A) → P ∣ x ∣)
    universal-property-Π {A} {P} ext P-prop =
      ((x : ∥ A ∥ᴱ) → P x)      ↝⟨ Eq.↔→≃
                                     (λ f → ∣ f ∘ ∣_∣ ∣)
                                     (rec λ where
                                        .∣∣ʳ f → elim λ where
                                          .∣∣ʳ                        → f
                                          .truncation-is-propositionʳ → P-prop
                                        .truncation-is-propositionʳ →
                                          Π-closure ext 1 λ _ → P-prop _)
                                     (elim λ where
                                        .∣∣ʳ _ →
                                          cong ∣_∣ $ apply-ext ext λ x →
                                          trans (cong (_$ ∣ x ∣) rec-∣∣)
                                            elim-∣∣
                                        .truncation-is-propositionʳ _ →
                                          mono₁ 1 truncation-is-proposition)
                                     (λ f →
                                        trans rec-∣∣ $ apply-ext ext $ elim λ where
                                        .∣∣ʳ _                        → elim-∣∣
                                        .truncation-is-propositionʳ _ →
                                          mono₁ 1 (P-prop _)) ⟩
      ∥ ((x : A) → P ∣ x ∣) ∥ᴱ  ↔⟨ ∥∥ᴱ≃ (Π-closure ext 1 λ _ → P-prop _) ⟩□
      ((x : A) → P ∣ x ∣)       □

  opaque
    unfolding universal-property ∥∥ᴱ≃

    -- Some "computation" rules.

    to-universal-property-Π :
      {A : Type a} {P : ∥ A ∥ᴱ → Type p}
      {ext : Extensionality a p}
      {@0 P-prop : ∀ x → Is-proposition (P x)}
      {f : (x : ∥ A ∥ᴱ) → P x} →
      _≃_.to (universal-property-Π ext P-prop) f ≡ f ∘ ∣_∣
    to-universal-property-Π = rec-∣∣

    from-universal-property-Π :
      {A : Type a} {P : ∥ A ∥ᴱ → Type p}
      {ext : Extensionality a p}
      {@0 P-prop : ∀ x → Is-proposition (P x)}
      {f : (x : A) → P ∣ x ∣} {x : A} →
      _≃_.from (universal-property-Π ext P-prop) f ∣ x ∣ ≡ f x
    from-universal-property-Π {x} =
      trans (cong (_$ ∣ x ∣) rec-∣∣) elim-∣∣

  opaque mutual

    -- The propositional truncation operator's universal property,
    -- expressed using _≃ᴱ_.

    universal-property-≃ᴱ :
      {A : Type a} {B : Type b} →
      @0 Extensionality a b →
      @0 Is-proposition B →
      (∥ A ∥ᴱ → B) ≃ᴱ (A → B)
    universal-property-≃ᴱ ext B-prop =
      universal-property-≃ᴱ-Π ext (λ _ → B-prop)

    -- A generalisation of universal-property-≃ᴱ.

    universal-property-≃ᴱ-Π :
      {A : Type a} {P : ∥ A ∥ᴱ → Type p} →
      @0 Extensionality a p →
      @0 (∀ x → Is-proposition (P x)) →
      ((x : ∥ A ∥ᴱ) → P x) ≃ᴱ ((x : A) → P ∣ x ∣)
    universal-property-≃ᴱ-Π {A} {P} ext P-prop =
      ((x : ∥ A ∥ᴱ) → P x)      ↝⟨ EEq.↔→≃ᴱ
                                     (λ f → ∣ f ∘ ∣_∣ ∣)
                                     (rec λ where
                                        .∣∣ʳ f → elim λ where
                                          .∣∣ʳ                        → f
                                          .truncation-is-propositionʳ → P-prop
                                        .truncation-is-propositionʳ →
                                          Π-closure ext 1 λ _ → P-prop _)
                                     (elim λ @0 where
                                        .∣∣ʳ _ →
                                          cong ∣_∣ $ apply-ext ext λ x →
                                          trans (cong (_$ ∣ x ∣) rec-∣∣)
                                            elim-∣∣
                                        .truncation-is-propositionʳ _ →
                                          mono₁ 1 truncation-is-proposition)
                                     (λ f →
                                        trans rec-∣∣ $ apply-ext ext $ elim λ where
                                        .∣∣ʳ _                        → elim-∣∣
                                        .truncation-is-propositionʳ _ →
                                          mono₁ 1 (P-prop _)) ⟩
      ∥ ((x : A) → P ∣ x ∣) ∥ᴱ  ↔⟨ ∥∥ᴱ≃ (Π-closure ext 1 λ _ → P-prop _) ⟩□
      ((x : A) → P ∣ x ∣)       □

  opaque
    unfolding universal-property-≃ᴱ-Π ∥∥ᴱ≃

    -- Some "computation" rules.

    to-universal-property-≃ᴱ-Π :
      {A : Type a} {P : ∥ A ∥ᴱ → Type p}
      {@0 ext : Extensionality a p}
      {@0 P-prop : ∀ x → Is-proposition (P x)}
      {f : (x : ∥ A ∥ᴱ) → P x} →
      _≃ᴱ_.to (universal-property-≃ᴱ-Π ext P-prop) f ≡ f ∘ ∣_∣
    to-universal-property-≃ᴱ-Π = rec-∣∣

    from-universal-property-≃ᴱ-Π :
      {A : Type a} {P : ∥ A ∥ᴱ → Type p}
      {@0 ext : Extensionality a p}
      {@0 P-prop : ∀ x → Is-proposition (P x)}
      {f : (x : A) → P ∣ x ∣} {x : A} →
      _≃ᴱ_.from (universal-property-≃ᴱ-Π ext P-prop) f ∣ x ∣ ≡ f x
    from-universal-property-≃ᴱ-Π {x} =
      trans (cong (_$ ∣ x ∣) rec-∣∣) elim-∣∣

  opaque

    -- Having a constant function (with an erased proof of constancy)
    -- into a set is equivalent (with erased proofs) to having a
    -- function from a propositionally truncated type (with erased
    -- proofs) into the set (assuming erased function extensionality).
    --
    -- This result is based on Proposition 2.2 in "The General
    -- Universal Property of the Propositional Truncation" by Kraus.

    Σ→Erased-Constant≃ᴱ∥∥ᴱ→ :
      {A : Type a} {B : Type b} →
      @0 Extensionality (a ⊔ b) (a ⊔ b) →
      @0 Is-set B →
      (∃ λ (f : A → B) → Erased (Constant f)) ≃ᴱ (∥ A ∥ᴱ → B)
    Σ→Erased-Constant≃ᴱ∥∥ᴱ→ {a} {b} {A} {B} ext B-set =
      (∃ λ (f : A → B) → Erased (Constant f))                     ↝⟨ EEq.↔→≃ᴱ
                                                                       (λ (f , [ c ]) → const f , [ (λ _ → c) ])
                                                                       (λ (f , [ c ]) →
                                                                          (λ x → f ∣ x ∣ x) ,
                                                                          [ (λ x y →
                                                                               trans (cong (flip f _) (truncation-is-proposition _ _)) $
                                                                               c ∣ y ∣ x y) ])
                                                                       (λ @0 { (f , [ _ ]) →
                                                                               Σ-≡,≡→≡
                                                                                 (apply-ext extᵃᵃᵇ λ _ →
                                                                                  apply-ext extᵃᵇ λ _ →
                                                                                  cong (flip f _) (truncation-is-proposition _ _))
                                                                                 (E₁.[]-cong₁.H-level-Erased
                                                                                    E₁.erased-instance-of-[]-cong-axiomatisation
                                                                                    1
                                                                                    (Π-closure extᵃᵃᵇ 1 λ _ →
                                                                                     Π-closure extᵃᵃᵇ 1 λ _ →
                                                                                     Π-closure extᵃᵇ 1 λ _ →
                                                                                     B-set)
                                                                                    _ _) })
                                                                       (λ @0 { (_ , [ _ ]) →
                                                                               cong (_,_ _) $
                                                                               E₁.[]-cong₁.H-level-Erased
                                                                               E₁.erased-instance-of-[]-cong-axiomatisation
                                                                               1
                                                                               (Π-closure extᵃᵃᵇ 1 λ _ →
                                                                                Π-closure extᵃᵇ 1 λ _ →
                                                                                B-set)
                                                                               _ _ }) ⟩
      (∃ λ (f : ∥ A ∥ᴱ → A → B) → Erased (∀ x → Constant (f x)))  ↝⟨ (inverse (from-isomorphism ΠΣ-comm) F.∘
                                                                      ∃-cong λ _ → E₁.Erased-Π↔Π [ extᵃᵃᵇ ]) ⟩
      (∥ A ∥ᴱ → ∃ λ (f : A → B) → Erased (Constant f))            ↝⟨ ∀-cong [ extᵃᵃᵇ ] equiv′ ⟩□
      (∥ A ∥ᴱ → B)                                                □
      where
      @0 extᵃᵇ : Extensionality a b
      extᵃᵇ = lower-extensionality b a ext

      @0 extᵃᵃᵇ : Extensionality a (a ⊔ b)
      extᵃᵃᵇ = lower-extensionality b lzero ext

      equiv : A → (∃ λ (f : A → B) → Erased (Constant f)) ≃ᴱ B
      equiv x =
        (∃ λ (f : A → B) → Erased (Constant f))                          ↝⟨ (∃-cong λ _ → inverse $ drop-⊤-right λ _ →
                                                                             ES.Erased-other-singleton≃ᴱ⊤) ⟩
        (∃ λ (f : A → B) → Erased (Constant f) ×
         ∃ λ (y : B) → Erased (f x ≡ y))                                 ↝⟨ (∃-cong λ _ → ∃-cong λ c → ∃-cong λ _ → inverse $ drop-⊤-right λ eq →
                                                                             _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ $
                                                                             ECP.Contractibleᴱ-Π extᵃᵇ λ _ →
                                                                             E₂.Erased-Contractibleᴱ≃Contractibleᴱ-Erased _
                                                                               [ ECP.inhabited→Is-proposition→Contractibleᴱ
                                                                                   (trans (c .erased _ _) (eq .erased)) B-set
                                                                               ]) ⟩
        (∃ λ (f : A → B) → Erased (Constant f) ×
         ∃ λ (y : B) → Erased (f x ≡ y) × ((x : A) → Erased (f x ≡ y)))  ↝⟨ EEq.↔→≃ᴱ (λ (f , c , y , eq , eqs) → y , f , eqs , c , eq)
                                                                              _ refl refl ⟩
        (∃ λ (y : B) → ∃ λ (f : A → B) → ((x : A) → Erased (f x ≡ y)) ×
         Erased (Constant f) × Erased (f x ≡ y))                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → drop-⊤-right λ eq →
                                                                             _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ $
                                                                             ECP.Contractibleᴱ-×
                                                                               (E₂.Erased-Contractibleᴱ≃Contractibleᴱ-Erased _
                                                                                  [ ECP.inhabited→Is-proposition→Contractibleᴱ
                                                                                      (λ x y → trans (eq x .erased) (sym (eq y .erased)))
                                                                                      (Π-closure extᵃᵃᵇ 1 λ _ →
                                                                                       Π-closure extᵃᵇ 1 λ _ →
                                                                                       B-set)
                                                                                  ])
                                                                               (E₂.Erased-Contractibleᴱ≃Contractibleᴱ-Erased _
                                                                                  [ ECP.inhabited→Is-proposition→Contractibleᴱ
                                                                                      (eq _ .erased) B-set
                                                                                  ])) ⟩

        (∃ λ (y : B) → ∃ λ (f : A → B) → (x : A) → Erased (f x ≡ y))     ↔⟨ (∃-cong λ _ → inverse ΠΣ-comm) ⟩

        (∃ λ (y : B) → A → ∃ λ (x : B) → Erased (x ≡ y))                 ↝⟨ (drop-⊤-right λ _ → _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ $
                                                                             ECP.Contractibleᴱ-Π extᵃᵇ λ _ →
                                                                             _⇔_.from EEq.Contractibleᴱ⇔≃ᴱ⊤ ES.Erased-singleton≃ᴱ⊤) ⟩□
        B                                                                □

      equiv′ : ∥ A ∥ᴱ → (∃ λ (f : A → B) → Erased (Constant f)) ≃ᴱ B
      equiv′ x =
        inverse $
        EEq.⟨ (λ y → (λ _ → y) , [ (λ _ _ → refl y) ])
            , rec
                (λ where
                   .∣∣ʳ x →
                     _⇔_.to
                       (EEq.Is-equivalenceᴱ-cong-⇔
                          λ _ →
                            cong (_,_ _ ∘ E₁.[_]→)
                            (apply-ext extᵃᵃᵇ λ _ →
                             apply-ext extᵃᵇ λ _ →
                             trans-symʳ _)) $
                     _≃ᴱ_.is-equivalence (inverse (equiv x))
                   .truncation-is-propositionʳ →
                     EEq.Is-equivalenceᴱ-propositional ext _)
                x
            ⟩

  opaque

    -- A function of type (x : ∥ A ∥ᴱ) → P x, along with an erased
    -- proof showing that the function is equal to some erased
    -- function, is equivalent (with erased proofs) to a function of
    -- type (x : A) → P ∣ x ∣, along with an erased equality proof.

    Σ-Π-∥∥ᴱ-Erased-≡-≃ᴱ :
      {A : Type a} {P : ∥ A ∥ᴱ → Type p} {@0 g : (x : ∥ A ∥ᴱ) → P x} →
      @0 Extensionality a p →
      (∃ λ (f : (x : ∥ A ∥ᴱ) → P x) → Erased (f ≡ g)) ≃ᴱ
      (∃ λ (f : (x : A) → P ∣ x ∣) → Erased (f ≡ g ∘ ∣_∣))
    Σ-Π-∥∥ᴱ-Erased-≡-≃ᴱ {a} {p} {A} {P} {g} ext =
      (∃ λ (f : (x : ∥ A ∥ᴱ) → P x) → Erased (f ≡ g))       ↝⟨ lemma₂ ⟩
      ((x : ∥ A ∥ᴱ) → ∃ λ (y : P x) → Erased (y ≡ g x))     ↝⟨ universal-property-≃ᴱ-Π ext (λ _ → lemma₁) ⟩
      ((x : A) → ∃ λ (y : P ∣ x ∣) → Erased (y ≡ g ∣ x ∣))  ↝⟨ inverse lemma₂ ⟩
      (∃ λ (f : (x : A) → P ∣ x ∣) → Erased (f ≡ g ∘ ∣_∣))  □
      where
      opaque

        @0 lemma₁ : Is-proposition (∃ λ y → Erased (y ≡ g x))
        lemma₁ =
          mono₁ 0 $
          H-level-cong _ 0
            (∃-cong λ _ → inverse (erased E₁.Erased↔))
            (singleton-contractible _)

      lemma₂ :
        {A : Type a} {P : A → Type p}
        {@0 g : (x : A) → P x} →
        (∃ λ (f : (x : A) → P x) → Erased (f ≡ g)) ≃ᴱ
        ((x : A) → ∃ λ (y : P x) → Erased (y ≡ g x))
      lemma₂ {A} {P} {g} =
        (∃ λ (f : (x : A) → P x) → Erased (f ≡ g))                ↝⟨ (∃-cong λ _ →
                                                                      E₁.Erased-cong-≃ᴱ
                                                                        (inverse $ from-isomorphism $
                                                                         Eq.extensionality-isomorphism ext)) ⟩
        (∃ λ (f : (x : A) → P x) → Erased ((x : A) → f x ≡ g x))  ↝⟨ (∃-cong λ _ → E₁.Erased-Π↔Π [ ext ]) ⟩
        (∃ λ (f : (x : A) → P x) → (x : A) → Erased (f x ≡ g x))  ↔⟨ inverse ΠΣ-comm ⟩
        ((x : A) → ∃ λ (y : P x) → Erased (y ≡ g x))              □

  ----------------------------------------------------------------------
  -- Some results based on "Generalizations of Hedberg's Theorem" by
  -- Kraus, Escardó, Coquand and Altenkirch

  opaque

    -- Types with constant endofunctions are "h-stable" (meaning that
    -- "mere inhabitance" implies inhabitance).

    constant-endofunction⇒h-stable :
      {f : A → A} → @0 Constant f → ∥ A ∥ᴱ → A
    constant-endofunction⇒h-stable {A} {f} c =
      ∥ A ∥ᴱ                            ↝⟨ (rec λ where
                                              .∣∣ʳ x                      → f x , [ c (f x) x ]
                                              .truncation-is-propositionʳ → prop) ⟩
      (∃ λ (x : A) → Erased (f x ≡ x))  ↝⟨ proj₁ ⟩□
      A                                 □
      where
      @0 prop : Is-proposition (∃ λ x → Erased (f x ≡ x))
      prop =                                       $⟨ fixpoint-lemma f c ⟩
        Is-proposition (∃ λ x → f x ≡ x)           ↝⟨ H-level-cong _ 1 (∃-cong λ _ → inverse $ E₁.erased E₁.Erased↔) ⦂ (_ → _) ⟩□
        Is-proposition (∃ λ x → Erased (f x ≡ x))  □

  opaque

    -- Having a constant endofunction is logically equivalent to being
    -- h-stable.

    constant-endofunction⇔h-stable :
      (∃ λ (f : A → A) → Erased (Constant f)) ⇔ (∥ A ∥ᴱ → A)
    constant-endofunction⇔h-stable = record
      { to   = λ (_ , [ c ]) → constant-endofunction⇒h-stable c
      ; from = λ f →
          f ∘ ∣_∣ ,
          [ (λ x y →
               f ∣ x ∣  ≡⟨ cong f $ truncation-is-proposition _ _ ⟩∎
               f ∣ y ∣  ∎)
          ]
      }

  ----------------------------------------------------------------------
  -- Some results related to h-levels

  private opaque

    -- A lemma used below.

    H-level-×₁-lemma :
      {A : Type a} →
      @0 Extensionality a a →
      (A → ∥ B ∥ᴱ) →
      ∀ n → H-level (suc n) (A × B) → H-level (suc n) A
    H-level-×₁-lemma ext inhabited n h =
      [inhabited⇒+]⇒+ n λ x →
      flip rec (inhabited x) λ where
        .∣∣ʳ y →
          proj₁-closure (λ _ → y) (suc n) h
        .truncation-is-propositionʳ →
          H-level-propositional ext (suc n)

  opaque

    -- A variant of proj₁-closure.

    H-level-×₁ :
      {A : Type a} →
      @0 Extensionality a a →
      (A → ∥ B ∥ᴱ) →
      ∀ n → H-level n (A × B) → H-level n A
    H-level-×₁ ext inhabited zero h =
      propositional⇒inhabited⇒contractible
        (H-level-×₁-lemma ext inhabited 0 (mono₁ 0 h))
        (proj₁ (proj₁ h))
    H-level-×₁ ext inhabited (suc n) =
      H-level-×₁-lemma ext inhabited n

  opaque

    -- A variant of proj₂-closure.

    H-level-×₂ :
      {B : Type b} →
      @0 Extensionality b b →
      (B → ∥ A ∥ᴱ) →
      ∀ n → H-level n (A × B) → H-level n B
    H-level-×₂ {A} {B} ext inhabited n =
      H-level n (A × B)  ↝⟨ H-level.respects-surjection (from-bijection ×-comm) n ⟩
      H-level n (B × A)  ↝⟨ H-level-×₁ ext inhabited n ⟩□
      H-level n B        □

  ----------------------------------------------------------------------
  -- Flattening

  opaque

    private

      -- A lemma used below.

      flatten-to :
        (F : (Type ℓ → Type ℓ) → Type f) →
        (F ∥_∥ᴱ → ∥ F id ∥ᴱ) →
        ∥ F ∥_∥ᴱ ∥ᴱ → ∥ F id ∥ᴱ
      flatten-to _ f =
        rec λ where
          .∣∣ʳ                        → f
          .truncation-is-propositionʳ → truncation-is-proposition

    -- A generalised flattening lemma.

    flatten-≃ :
      (F : (Type ℓ → Type ℓ) → Type f)
      (map : ∀ {G H} → (∀ {A} → G A → H A) → F G → F H)
      (f : F ∥_∥ᴱ → ∥ F id ∥ᴱ) →
      (∀ x → f (map ∣_∣ x) ≡ ∣ x ∣) →
      (∀ x → ∥∥ᴱ-map (map ∣_∣) (f x) ≡ ∣ x ∣) →
      ∥ F ∥_∥ᴱ ∥ᴱ ≃ ∥ F id ∥ᴱ
    flatten-≃ F map f f-map map-f =
      Eq.↔→≃ (flatten-to F f) (∥∥ᴱ-map (map ∣_∣))
        (elim λ where
           .∣∣ʳ _ →
             trans (cong (rec _) ∥∥ᴱ-map-∣∣) $
             trans rec-∣∣ (f-map _)
           .truncation-is-propositionʳ _ →
             mono₁ 1 truncation-is-proposition)
        (elim λ where
           .∣∣ʳ _ →
             trans (cong (∥∥ᴱ-map _) rec-∣∣) $
             map-f _
           .truncation-is-propositionʳ _ →
             mono₁ 1 truncation-is-proposition)

  opaque
    unfolding flatten-≃

    -- A variant of flatten-≃ with _≃ᴱ_ instead of _≃_.

    flatten-≃ᴱ :
      (F : (Type ℓ → Type ℓ) → Type f)
      (map : ∀ {G H} → (∀ {A} → G A → H A) → F G → F H)
      (f : F ∥_∥ᴱ → ∥ F id ∥ᴱ) →
      @0 (∀ x → f (map ∣_∣ x) ≡ ∣ x ∣) →
      @0 (∀ x → ∥∥ᴱ-map (map ∣_∣) (f x) ≡ ∣ x ∣) →
      ∥ F ∥_∥ᴱ ∥ᴱ ≃ᴱ ∥ F id ∥ᴱ
    flatten-≃ᴱ _ map f f-map map-f =
      EEq.[≃]→≃ᴱ (EEq.[proofs] (flatten-≃ _ map f f-map map-f))

  opaque
    unfolding flatten-≃ ∥∥ᴱ-map

    -- Nested truncations can be flattened.

    flatten : ∥ ∥ A ∥ᴱ ∥ᴱ ≃ ∥ A ∥ᴱ
    flatten {A} = flatten-≃
      (λ F → F A)
      (λ f → f)
      id
      (λ _ → refl _)
      (elim λ where
         .∣∣ʳ _                        → ∥∥ᴱ-map-∣∣
         .truncation-is-propositionʳ _ → mono₁ 1 truncation-is-proposition)

  private opaque

    -- Another flattening lemma, given as an example of how flatten-≃
    -- can be used.

    ∥∃∥∥ᴱ∥ᴱ≃∥∃∥ᴱ : ∥ ∃ (∥_∥ᴱ ∘ P) ∥ᴱ ≃ ∥ ∃ P ∥ᴱ
    ∥∃∥∥ᴱ∥ᴱ≃∥∃∥ᴱ {P} = flatten-≃
      (λ F → ∃ (F ∘ P))
      (λ f → Σ-map id f)
      (uncurry λ x → ∥∥ᴱ-map (x ,_))
      (λ _ → ∥∥ᴱ-map-∣∣)
      (uncurry λ _ → elim λ where
         .∣∣ʳ _ →
           trans (cong (∥∥ᴱ-map _) ∥∥ᴱ-map-∣∣) ∥∥ᴱ-map-∣∣
         .truncation-is-propositionʳ _ →
           mono₁ 1 truncation-is-proposition)

  ----------------------------------------------------------------------
  -- The propositional truncation operator is a monad

  opaque

    -- A universe-polymorphic variant of bind.

    infixl 5 _>>=′_

    _>>=′_ : ∥ A ∥ᴱ → (A → ∥ B ∥ᴱ) → ∥ B ∥ᴱ
    x >>=′ f = _≃_.to flatten (∥∥ᴱ-map f x)

  opaque
    unfolding flatten _>>=′_

    -- A "computation" rule.

    >>=′-∣∣ : ∣ x ∣ >>=′ f ≡ f x
    >>=′-∣∣ = trans (cong (_≃_.to flatten) ∥∥ᴱ-map-∣∣) eliminator-∣∣

  opaque

    -- The universe-polymorphic variant of bind is associative.

    >>=′-associative :
      (x : ∥ A ∥ᴱ) →
      x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
    >>=′-associative = elim λ where
      .∣∣ʳ _ →
        trans >>=′-∣∣ $
        cong (_>>=′ _) (sym >>=′-∣∣)
      .truncation-is-propositionʳ _ → ⇒≡ 1 truncation-is-proposition

  opaque instance

    -- The propositional truncation operator is a monad.

    raw-monad : Raw-monad (∥_∥ᴱ {a = a})
    Raw-monad.return raw-monad = ∣_∣
    Raw-monad._>>=_  raw-monad = _>>=′_

    monad : Monad (∥_∥ᴱ {a = a})
    Monad.raw-monad monad           = raw-monad
    Monad.left-identity monad _ _   = >>=′-∣∣
    Monad.associativity monad x _ _ = >>=′-associative x
    Monad.right-identity monad      = elim λ where
      .∣∣ʳ                        _ → >>=′-∣∣
      .truncation-is-propositionʳ _ → ⇒≡ 1 truncation-is-proposition

  ----------------------------------------------------------------------
  -- Surjectivity

  -- A variant of surjectivity with "erased proofs".

  Surjectiveᴱ :
    {A : Type a} {B : Type b} →
    (A → B) → Type (a ⊔ b)
  Surjectiveᴱ f = ∀ y → ∥ f ⁻¹ᴱ y ∥ᴱ

  opaque

    -- The property Surjectiveᴱ f is a proposition (in erased
    -- contexts, assuming function extensionality).

    @0 Surjectiveᴱ-propositional :
      {A : Type a} {B : Type b} {f : A → B} →
      Extensionality b (a ⊔ b) →
      Is-proposition (Surjectiveᴱ f)
    Surjectiveᴱ-propositional ext =
      Π-closure ext 1 λ _ →
      truncation-is-proposition

  opaque

    -- The function ∣_∣ is surjective (with erased proofs).

    ∣∣-surjective : Surjectiveᴱ (∣_∣ {A = A})
    ∣∣-surjective = elim λ where
      .∣∣ʳ x                        → ∣ x , [ refl _ ] ∣
      .truncation-is-propositionʳ _ → truncation-is-proposition

  opaque

    -- Split surjective functions are surjective (with erased proofs).

    Split-surjective→Surjectiveᴱ :
      Split-surjective f → Surjectiveᴱ f
    Split-surjective→Surjectiveᴱ s = λ y → ∣ ECP.⁻¹→⁻¹ᴱ (s y) ∣

  opaque

    -- Being both surjective (with erased proofs) and an embedding
    -- (completely erased) is equivalent to being an equivalence (with
    -- erased proofs), assuming erased function extensionality.
    --
    -- This result, without erasure, is Corollary 4.6.4 from the first
    -- edition of the HoTT book.

    Surjectiveᴱ×Erased-Is-embedding≃ᴱIs-equivalenceᴱ :
      {A : Type a} {B : Type b} {f : A → B} →
      @0 Extensionality (a ⊔ b) (a ⊔ b) →
      (Surjectiveᴱ f × Erased (Is-embedding f)) ≃ᴱ Is-equivalenceᴱ f
    Surjectiveᴱ×Erased-Is-embedding≃ᴱIs-equivalenceᴱ {a} {f} ext =
      EEq.⇔→≃ᴱ
        (×-closure 1
           (Surjectiveᴱ-propositional
              (lower-extensionality a lzero ext))
           (E₁.[]-cong₁.H-level-Erased
              E₁.erased-instance-of-[]-cong-axiomatisation
              1 (Emb.Is-embedding-propositional ext)))
        (EEq.Is-equivalenceᴱ-propositional ext f)
        (λ (is-surj , is-emb) →
           _⇔_.from EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP $ λ y →
                                    $⟨ is-surj y ⟩
           ∥ f ⁻¹ᴱ y ∥ᴱ             ↝⟨ (rec λ where
                                          .∣∣ʳ p → ECP.inhabited→Is-proposition→Contractibleᴱ p
                                                     (H-level-cong _ 1
                                                        ECP.⁻¹≃⁻¹ᴱ
                                                        (Emb.embedding→⁻¹-propositional (E₁.erased is-emb) _))
                                          .truncation-is-propositionʳ →
                                            ECP.Contractibleᴱ-propositional ext) ⟩□
           Contractibleᴱ (f ⁻¹ᴱ y)  □)
        (λ is-eq@(inv , [ r-inv , _ ]) →
           (λ y →           $⟨ inv y , [ r-inv y ] ⟩
              f ⁻¹ᴱ y       ↝⟨ ∣_∣ ⟩
              ∥ f ⁻¹ᴱ y ∥ᴱ  □) ,
           (                            $⟨ is-eq ⟩
            Is-equivalenceᴱ f           ↝⟨ E₁.[_]→ ⟩
            Erased (Is-equivalenceᴱ f)  ↝⟨ E₁.map EEq.Is-equivalenceᴱ→Is-equivalence ⟩
            Erased (Is-equivalence f)   ↝⟨ E₁.map Emb.Is-equivalence→Is-embedding ⟩□
            Erased (Is-embedding f)     □))

  ----------------------------------------------------------------------
  -- More lemmas

  opaque

    -- Unique choice.

    unique-choice :
      @0 ((x : A) → Is-proposition (P x)) →
      ((x : A) → ∥ P x ∥ᴱ) →
      ((x : A) → P x)
    unique-choice prop p x =
      _≃_.to (∥∥ᴱ≃ (prop x)) (p x)

  opaque

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

  ----------------------------------------------------------------------
  -- Definitions related to truncated binary sums

  -- Truncated binary sums.

  infixr 1 _∥⊎∥ᴱ_

  _∥⊎∥ᴱ_ : Type a → Type b → Type (a ⊔ b)
  A ∥⊎∥ᴱ B = ∥ A ⊎ B ∥ᴱ

  opaque

    -- An introduction rule.

    ∣inj₁∣ : A → A ∥⊎∥ᴱ B
    ∣inj₁∣ = ∣_∣ ∘ inj₁

  opaque

    -- Another introduction rule.

    ∣inj₂∣ : B → A ∥⊎∥ᴱ B
    ∣inj₂∣ = ∣_∣ ∘ inj₂

  opaque

    -- In erased contexts _∥⊎∥ᴱ_ is pointwise propositional.

    @0 ∥⊎∥ᴱ-propositional : Is-proposition (A ∥⊎∥ᴱ B)
    ∥⊎∥ᴱ-propositional = truncation-is-proposition

  opaque

    -- The _∥⊎∥ᴱ_ operator preserves functions.

    infixr 1 _∥⊎∥ᴱ-map_

    _∥⊎∥ᴱ-map_ : (A₁ → A₂) → (B₁ → B₂) → A₁ ∥⊎∥ᴱ B₁ → A₂ ∥⊎∥ᴱ B₂
    f ∥⊎∥ᴱ-map g = ∥∥ᴱ-map (f ⊎-cong g)

  opaque

    -- The _∥⊎∥ᴱ_ operator preserves "symmetric" functions.

    infixr 1 _∥⊎∥ᴱ-cong_

    _∥⊎∥ᴱ-cong_ :
      A₁ ↝[ ⌊ k ⌋-sym ] A₂ → B₁ ↝[ ⌊ k ⌋-sym ] B₂ →
      (A₁ ∥⊎∥ᴱ B₁) ↝[ ⌊ k ⌋-sym ] (A₂ ∥⊎∥ᴱ B₂)
    A₁↝A₂ ∥⊎∥ᴱ-cong B₁↝B₂ = ∥∥ᴱ-cong (A₁↝A₂ ⊎-cong B₁↝B₂)

  opaque

    -- _∥⊎∥ᴱ_ is commutative.

    ∥⊎∥ᴱ-comm : (A ∥⊎∥ᴱ B) ≃ (B ∥⊎∥ᴱ A)
    ∥⊎∥ᴱ-comm = ∥∥ᴱ-cong (from-isomorphism ⊎-comm)

  opaque
    unfolding ∣inj₂∣

    -- If one truncates the types to the left of _∥⊎∥ᴱ_, then one ends
    -- up with an equivalent type.

    truncate-left-∥⊎∥ᴱ : (A ∥⊎∥ᴱ B) ≃ (∥ A ∥ᴱ ∥⊎∥ᴱ B)
    truncate-left-∥⊎∥ᴱ =
      inverse $
      flatten-≃
        (λ F → F _ ⊎ _)
        (λ f → ⊎-map f id)
        P.[ ∥∥ᴱ-map inj₁ , ∣inj₂∣ ]
        P.[ (λ _ → ∥∥ᴱ-map-∣∣) , (λ _ → refl _) ]
        P.[ (elim λ where
               .∣∣ʳ _ →
                 trans (cong (∥∥ᴱ-map _) ∥∥ᴱ-map-∣∣) ∥∥ᴱ-map-∣∣
               .truncation-is-propositionʳ _ →
                 mono₁ 1 ∥⊎∥ᴱ-propositional)
          , (λ _ → ∥∥ᴱ-map-∣∣)
          ]

  opaque

    -- If one truncates the types to the right of _∥⊎∥ᴱ_, then one
    -- ends up with an equivalent type.

    truncate-right-∥⊎∥ᴱ : (A ∥⊎∥ᴱ B) ≃ (A ∥⊎∥ᴱ ∥ B ∥ᴱ)
    truncate-right-∥⊎∥ᴱ {A} {B} =
      A ∥⊎∥ᴱ B       ↝⟨ ∥⊎∥ᴱ-comm ⟩
      B ∥⊎∥ᴱ A       ↝⟨ truncate-left-∥⊎∥ᴱ ⟩
      ∥ B ∥ᴱ ∥⊎∥ᴱ A  ↝⟨ ∥⊎∥ᴱ-comm ⟩□
      A ∥⊎∥ᴱ ∥ B ∥ᴱ  □

  opaque

    -- _∥⊎∥ᴱ_ is associative.

    ∥⊎∥ᴱ-assoc : (A ∥⊎∥ᴱ (B ∥⊎∥ᴱ C)) ≃ ((A ∥⊎∥ᴱ B) ∥⊎∥ᴱ C)
    ∥⊎∥ᴱ-assoc {A} {B} {C} =
      ∥ A ⊎ ∥ B ⊎ C ∥ᴱ ∥ᴱ  ↝⟨ inverse truncate-right-∥⊎∥ᴱ ⟩
      ∥ A ⊎ B ⊎ C ∥ᴱ       ↔⟨ ∥∥ᴱ-cong ⊎-assoc ⟩
      ∥ (A ⊎ B) ⊎ C ∥ᴱ     ↝⟨ truncate-left-∥⊎∥ᴱ ⟩□
      ∥ ∥ A ⊎ B ∥ᴱ ⊎ C ∥ᴱ  □

  opaque

    -- ⊥ is a right identity of _∥⊎∥ᴱ_ if the left argument is a
    -- proposition.

    ∥⊎∥ᴱ-left-identity :
      @0 Is-proposition A →
      (⊥ {ℓ = ℓ} ∥⊎∥ᴱ A) ≃ A
    ∥⊎∥ᴱ-left-identity {A} A-prop =
      ∥ ⊥ ⊎ A ∥ᴱ  ↔⟨ ∥∥ᴱ-cong ⊎-left-identity ⟩
      ∥ A ∥ᴱ      ↝⟨ ∥∥ᴱ≃ A-prop ⟩□
      A           □

  opaque

    -- ⊥ is a left identity of _∥⊎∥ᴱ_ if the right argument is a
    -- proposition.

    ∥⊎∥ᴱ-right-identity :
      @0 Is-proposition A →
      (A ∥⊎∥ᴱ ⊥ {ℓ = ℓ}) ≃ A
    ∥⊎∥ᴱ-right-identity {A} A-prop =
      A ∥⊎∥ᴱ ⊥  ↔⟨ ∥⊎∥ᴱ-comm ⟩
      ⊥ ∥⊎∥ᴱ A  ↔⟨ ∥⊎∥ᴱ-left-identity A-prop ⟩□
      A         □

  opaque

    -- _∥⊎∥ᴱ_ is idempotent for propositions (up to equivalences with
    -- erased proofs).

    ∥⊎∥ᴱ-idempotent : @0 Is-proposition A → (A ∥⊎∥ᴱ A) ≃ᴱ A
    ∥⊎∥ᴱ-idempotent {A} A-prop =
      ∥ A ⊎ A ∥ᴱ  ↝⟨ idempotent ⟩
      ∥ A ∥ᴱ      ↔⟨ ∥∥ᴱ≃ A-prop ⟩□
      A           □

  opaque

    -- Sometimes a truncated binary sum is equivalent (with erased
    -- proofs) to its right summand.

    drop-left-∥⊎∥ᴱ :
      @0 Is-proposition B → (A → B) → (A ∥⊎∥ᴱ B) ≃ᴱ B
    drop-left-∥⊎∥ᴱ B-prop A→B = EEq.⇔→≃ᴱ
      ∥⊎∥ᴱ-propositional
      B-prop
      (rec λ where
         .∣∣ʳ                        → P.[ A→B , id ]
         .truncation-is-propositionʳ → B-prop)
      ∣inj₂∣

  opaque

    -- Sometimes a truncated binary sum is equivalent (with erased
    -- proofs) to its left summand.

    drop-right-∥⊎∥ᴱ :
      @0 Is-proposition A → (B → A) → (A ∥⊎∥ᴱ B) ≃ᴱ A
    drop-right-∥⊎∥ᴱ {A} {B} A-prop B→A =
      A ∥⊎∥ᴱ B  ↔⟨ ∥⊎∥ᴱ-comm ⟩
      B ∥⊎∥ᴱ A  ↝⟨ drop-left-∥⊎∥ᴱ A-prop B→A ⟩□
      A         □

  opaque
    unfolding ∣inj₁∣

    -- Sometimes a truncated binary sum is equivalent to its left
    -- summand.

    drop-⊥-right-∥⊎∥ᴱ :
      @0 Is-proposition A → ¬ B → (A ∥⊎∥ᴱ B) ≃ A
    drop-⊥-right-∥⊎∥ᴱ A-prop ¬B =
      Eq.↔→≃
        (rec λ where
           .∣∣ʳ                        → P.[ id , ⊥-elim ∘ ¬B ]
           .truncation-is-propositionʳ → A-prop)
        ∣inj₁∣
        (λ _ → rec-∣∣)
        (elim λ where
           .∣∣ʳ →
             P.[ (λ _ → cong (∣_∣ ∘ inj₁) rec-∣∣) , ⊥-elim ∘ ¬B ]
           .truncation-is-propositionʳ _ →
             mono₁ 1 ∥⊎∥ᴱ-propositional)

  opaque

    -- Sometimes a truncated binary sum is equivalent to its right
    -- summand.

    drop-⊥-left-∥⊎∥ᴱ :
      @0 Is-proposition B → ¬ A → (A ∥⊎∥ᴱ B) ≃ B
    drop-⊥-left-∥⊎∥ᴱ {B} {A} B-prop ¬A =
      A ∥⊎∥ᴱ B  ↝⟨ ∥⊎∥ᴱ-comm ⟩
      B ∥⊎∥ᴱ A  ↝⟨ drop-⊥-right-∥⊎∥ᴱ B-prop ¬A ⟩
      B         □

  opaque
    unfolding ∣inj₁∣ ∣inj₂∣

    -- A type of functions from a truncated binary sum to a family of
    -- propositions can be expressed (up to _≃ᴱ_) as a binary product
    -- of function types (assuming erased function extensionality).

    Π∥⊎∥ᴱ≃ᴱΠ×Π :
      {A : Type a} {B : Type b} {P : A ∥⊎∥ᴱ B → Type p} →
      @0 Extensionality (a ⊔ b) p →
      @0 (∀ x → Is-proposition (P x)) →
      ((x : A ∥⊎∥ᴱ B) → P x) ≃ᴱ
      (((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y)))
    Π∥⊎∥ᴱ≃ᴱΠ×Π {A} {B} {P} ext P-prop =
      ((x : A ∥⊎∥ᴱ B) → P x)                               ↝⟨ universal-property-≃ᴱ-Π ext P-prop ⟩
      ((x : A ⊎ B) → P ∣ x ∣)                              ↝⟨ Π⊎↔Π×Π [ ext ] ⟩□
      ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))  □

  opaque

    -- A distributivity law for Σ and _∥⊎∥ᴱ_.

    Σ-∥⊎∥ᴱ-distrib-left :
      @0 Is-proposition A →
      Σ A (λ x → P x ∥⊎∥ᴱ Q x) ≃ (Σ A P ∥⊎∥ᴱ Σ A Q)
    Σ-∥⊎∥ᴱ-distrib-left {P} {Q} A-prop =
      (∃ λ x → ∥ P x ⊎ Q x ∥ᴱ)       ↝⟨ inverse $ ∥∥ᴱ≃ (Σ-closure 1 A-prop λ _ → ∥⊎∥ᴱ-propositional) ⟩
      ∥ (∃ λ x → ∥ P x ⊎ Q x ∥ᴱ) ∥ᴱ  ↝⟨ flatten-≃
                                          (λ F → (∃ λ x → F (P x ⊎ Q x)))
                                          (λ f → Σ-map id f)
                                          (uncurry λ x → ∥∥ᴱ-map (x ,_))
                                          (λ _ → ∥∥ᴱ-map-∣∣)
                                          (uncurry λ _ → elim λ where
                                             .∣∣ʳ _ →
                                               trans (cong (∥∥ᴱ-map _) ∥∥ᴱ-map-∣∣) ∥∥ᴱ-map-∣∣
                                             .truncation-is-propositionʳ _ →
                                               mono₁ 1 truncation-is-proposition) ⟩
      ∥ (∃ λ x → P x ⊎ Q x) ∥ᴱ       ↔⟨ ∥∥ᴱ-cong ∃-⊎-distrib-left ⟩□
      ∥ ∃ P ⊎ ∃ Q ∥ᴱ                 □

  opaque
    unfolding ∣inj₁∣ ∣inj₂∣

    -- A distributivity law for Σ and _∥⊎∥ᴱ_.

    Σ-∥⊎∥ᴱ-distrib-right :
      {A : Type a} {B : Type b} {P : A ∥⊎∥ᴱ B → Type p} →
      @0 Extensionality p (a ⊔ b ⊔ p) →
      @0 (∀ x → Is-proposition (P x)) →
      Σ (A ∥⊎∥ᴱ B) P ≃ (Σ A (P ∘ ∣inj₁∣) ∥⊎∥ᴱ Σ B (P ∘ ∣inj₂∣))
    Σ-∥⊎∥ᴱ-distrib-right {A} {B} {P} ext P-prop =
      Eq.↔→≃
        (uncurry $ elim λ where
           .∣∣ʳ →
             curry (∣_∣ ∘ _↔_.to ∃-⊎-distrib-right)
           .truncation-is-propositionʳ _ →
             Π-closure ext 1 λ _ →
             ∥⊎∥ᴱ-propositional)
        (rec λ where
           .∣∣ʳ →
             Σ-map ∣_∣ id ∘ _↔_.from ∃-⊎-distrib-right
           .truncation-is-propositionʳ →
             prop)
        (elim λ where
           .∣∣ʳ →
             P.[ (λ (_ , y) →
                    trans (cong (uncurry (elim _)) rec-∣∣) $
                    cong (_$ y) elim-∣∣)
               , (λ (_ , y) →
                    trans (cong (uncurry (elim _)) rec-∣∣) $
                    cong (_$ y) elim-∣∣)
               ]
           .truncation-is-propositionʳ _ →
             mono₁ 1 ∥⊎∥ᴱ-propositional)
        (uncurry $ elim λ where
           .∣∣ʳ →
             P.[ (λ _ y → trans (cong (rec _ ∘ (_$ y)) elim-∣∣) rec-∣∣)
               , (λ _ y → trans (cong (rec _ ∘ (_$ y)) elim-∣∣) rec-∣∣)
               ]
           .truncation-is-propositionʳ _ →
             Π-closure ext 1 λ _ →
             mono₁ 1 prop)
      where
      @0 prop : Is-proposition (Σ (A ∥⊎∥ᴱ B) P)
      prop = Σ-closure 1 ∥⊎∥ᴱ-propositional P-prop

  opaque

    -- A variant of one of De Morgan's laws.

    ¬∥⊎∥ᴱ¬≃¬× :
      {A : Type a} {B : Type b} →
      @0 Extensionality (a ⊔ b) lzero →
      Dec (¬ A) → Dec (¬ B) →
      (¬ A ∥⊎∥ᴱ ¬ B) ≃ᴱ (¬ (A × B))
    ¬∥⊎∥ᴱ¬≃¬× {A} {B} ext dec-¬A dec-¬B = EEq.⇔→≃ᴱ
      ∥⊎∥ᴱ-propositional
      (¬-propositional ext)
      (rec λ where
         .∣∣ʳ → ¬⊎¬→×¬
         .truncation-is-propositionʳ → ¬-propositional ext)
      (∣_∣ ∘ _⇔_.from (¬⊎¬⇔¬× dec-¬A dec-¬B))

  ----------------------------------------------------------------------
  -- Code related to Erased-singleton

  opaque

    -- A corollary of
    -- erased-singleton-with-erased-center-propositional.

    ↠→↠Erased-singleton :
      {@0 y : B}
      (A↠B : A ↠ B) →
      ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ᴱ ↠ Erased-singleton y
    ↠→↠Erased-singleton {A} {y} A↠B =
      ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ᴱ  ↝⟨ ∥∥ᴱ-cong-↠ (S.Σ-cong A↠B λ _ → F.id) ⟩
      ∥ Erased-singleton y ∥ᴱ                         ↔⟨ ∥∥ᴱ≃
                                                           (erased-singleton-with-erased-center-propositional $
                                                            ES.Very-stable→Very-stableᴱ 1 $
                                                            Very-stable→Very-stable-≡ 0 $
                                                            erased ES.Erased-Very-stable) ⟩□
      Erased-singleton y                              □
      where
      open module @0 E = ES.[]-cong₁ E₁.erased-instance-of-[]-cong-axiomatisation

  opaque

    -- Another corollary of
    -- erased-singleton-with-erased-center-propositional.

    ↠→≃ᴱErased-singleton :
      {@0 y : B}
      (A↠B : A ↠ B) →
      ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ᴱ ≃ᴱ Erased-singleton y
    ↠→≃ᴱErased-singleton {A} {y} A↠B =
      ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ᴱ  ↝⟨ ∥∥ᴱ-cong-⇔ (S.Σ-cong-⇔ A↠B λ _ → F.id) ⟩
      ∥ Erased-singleton y ∥ᴱ                         ↔⟨ ∥∥ᴱ≃
                                                           (erased-singleton-with-erased-center-propositional $
                                                            ES.Very-stable→Very-stableᴱ 1 $
                                                            Very-stable→Very-stable-≡ 0 $
                                                            erased ES.Erased-Very-stable) ⟩□
      Erased-singleton y                              □
      where
      open module @0 E = ES.[]-cong₁ E₁.erased-instance-of-[]-cong-axiomatisation

  opaque

    -- A corollary of Σ-Erased-Erased-singleton↔ and
    -- ↠→≃ᴱErased-singleton.

    Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ :
      (A↠B : A ↠ B) →
      (∃ λ (x : Erased B) →
         ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥ᴱ) ≃ᴱ
      B
    Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ {A} {B} A↠B =
      (∃ λ (x : Erased B) →
         ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥ᴱ)  ↝⟨ (∃-cong λ _ → ↠→≃ᴱErased-singleton A↠B) ⟩

      (∃ λ (x : Erased B) → Erased-singleton (erased x))         ↝⟨ ES.Σ-Erased-Erased-singleton-≃ᴱ ⟩□

      B                                                          □

  opaque
    unfolding Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ

    -- In an erased context the left-to-right direction of
    -- Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ returns the erased first component.

    @0 to-Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ≡ :
      ∀ (A↠B : A ↠ B) x →
      _≃ᴱ_.to (Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ A↠B) x ≡ erased (proj₁ x)
    to-Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ≡ A↠B ([ x ] , y) =
      _≃ᴱ_.to (Σ-Erased-∥-Σ-Erased-≡-∥≃ᴱ A↠B) ([ x ] , y)  ≡⟨⟩
      proj₁ (_≃ᴱ_.to (↠→≃ᴱErased-singleton A↠B) y)         ≡⟨ erased (proj₂ (_≃ᴱ_.to (↠→≃ᴱErased-singleton A↠B) y)) ⟩∎
      x                                                    ∎
