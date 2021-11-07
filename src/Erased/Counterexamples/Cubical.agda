------------------------------------------------------------------------
-- Some properties that hold for Erased do not hold for every
-- accessible modality
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Erased.Counterexamples.Cubical
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as B using (_↔_)
open import Erased.Cubical eq using (Modality; Accessible)
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Path-split equality-with-J as PS
  using (_-Null_; Is-∞-extendable-along-[_])
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T
  using (∥_∥; ∣_∣; Axiom-of-choice)
open import Preimage equality-with-J using (_⁻¹_)

private
  variable
    a b ℓ ℓ′ p : Level
    A          : Type a

-- A type is modal with respect to the modality ∥_∥ if it is a
-- proposition.

∥∥-modal : Type ℓ → Type ℓ
∥∥-modal = Is-proposition

-- Propositional truncation is a modality.
--
-- This proof is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

∥∥-modality : Modality ℓ
∥∥-modality {ℓ = ℓ} = λ where
    .◯                      → ∥_∥
    .η                      → ∣_∣
    .Is-modal               → ∥∥-modal
    .Is-modal-propositional → λ ext → H-level-propositional ext 1
    .Is-modal-◯             → T.truncation-is-proposition
    .Is-modal-respects-≃    → H-level-cong _ 1
    .extendable-along-η     → extendable
  where
  open Modality

  extendable :
    {A : Type ℓ} {P : ∥ A ∥ → Type ℓ} →
    (∀ x → Is-proposition (P x)) →
    Is-∞-extendable-along-[ ∣_∣ ] P
  extendable {A = A} {P = P} =
    (∀ x → Is-proposition (P x))                          →⟨ (λ prop →
                                                                _≃_.is-equivalence $
                                                                Eq.↔→≃
                                                                  _
                                                                  (T.elim _ prop)
                                                                  refl
                                                                  (λ f → ⟨ext⟩ $
                                                                     T.elim
                                                                       _
                                                                       (⇒≡ 1 ∘ prop)
                                                                       (λ _ → refl _))) ⟩
    Is-equivalence (λ (f : (x : ∥ A ∥) → P x) → f ∘ ∣_∣)  ↔⟨ inverse $ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩□
    Is-∞-extendable-along-[ ∣_∣ ] P                       □

-- The propositional truncation modality is accessible.
--
-- This proof is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

∥∥-accessible : Accessible ℓ′ (∥∥-modality {ℓ = ℓ})
∥∥-accessible {ℓ′ = ℓ′} {ℓ = ℓ} =
    ↑ ℓ′ ⊤
  , (λ _ → ↑ ℓ′ Bool)
  , (λ A →
       Is-proposition A                                  ↝⟨ record { from = from; to = to } ⟩
       (λ _ → ↑ ℓ′ Bool) -Null A                         ↔⟨ inverse $ PS.Π-Is-∞-extendable-along≃Null ext ⟩□
       (↑ ℓ′ ⊤ → Is-∞-extendable-along-[ _ ] (λ _ → A))  □)

  where
  to : Is-proposition A → (λ _ → ↑ ℓ′ Bool) -Null A
  to prop _ =
    _≃_.is-equivalence $
    Eq.⇔→≃
      prop
      (Π-closure ext 1 λ _ → prop)
      _
      (_$ lift true)

  from : (λ _ → ↑ ℓ′ Bool) -Null A → Is-proposition A
  from {A = A} null x y =
    x                                      ≡⟨⟩
    case true ⦂ Bool of if_then x else y   ≡⟨ cong (_$ true) $ sym $ E.right-inverse-of _ ⟩
    E.to (E.from (if_then x else y)) true  ≡⟨⟩
    E.from (if_then x else y)              ≡⟨⟩
    E.to (E.from (if_then x else y)) false ≡⟨ cong (_$ false) $ E.right-inverse-of _ ⟩
    case false ⦂ Bool of if_then x else y  ≡⟨⟩
    y                                      ∎
    where
    ≃Bool→ : A ≃ (Bool → A)
    ≃Bool→ =
      A                ↝⟨ Eq.⟨ _ , null _ ⟩ ⟩
      (↑ ℓ′ Bool → A)  ↝⟨ Eq.↔→≃ (_∘ lift) (_∘ lower) refl refl ⟩□
      (Bool → A)       □

    module E = _≃_ ≃Bool→

-- It is not the case that, for all types A and B and functions
-- f : A → B, "f is ∥∥-connected" implies ∥ Is-equivalence f ∥.

¬[∥∥-connected→∥Is-equivalence∥] :
  ¬ ({A : Type a} {B : Type b} {f : A → B} →
     (∀ y → Contractible ∥ f ⁻¹ y ∥) → ∥ Is-equivalence f ∥)
¬[∥∥-connected→∥Is-equivalence∥] hyp =
                                                                   $⟨ (λ _ → ∣ lift true , refl _ ∣) ⟩

  ((y : ↑ _ ⊤) → ∥ (const (lift tt) ⦂ (↑ _ Bool → ↑ _ ⊤)) ⁻¹ y ∥)  →⟨ (∀-cong _ λ _ →
                                                                       propositional⇒inhabited⇒contractible T.truncation-is-proposition) ⟩
  ((y : ↑ _ ⊤) →
   Contractible ∥ (const (lift tt) ⦂ (↑ _ Bool → ↑ _ ⊤)) ⁻¹ y ∥)   →⟨ hyp ⟩

  ∥ Is-equivalence (const (lift tt) ⦂ (↑ _ Bool → ↑ _ ⊤)) ∥        ↔⟨ T.∥∥↔ (Eq.propositional ext _) ⟩

  Is-equivalence (const (lift tt) ⦂ (↑ _ Bool → ↑ _ ⊤))            →⟨ Eq.⟨ _ ,_⟩ ⟩

  ↑ _ Bool ≃ ↑ _ ⊤                                                 →⟨ (λ eq → Eq.↔⇒≃ B.↑↔ F.∘ eq F.∘ Eq.↔⇒≃ (inverse B.↑↔)) ⟩

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
[[∥∥→∥∥]→∥→∥]→Axiom-of-choice hyp {A = A} =
                       $⟨ T.rec T.truncation-is-proposition id ⟩
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

-- It is not the case that, for every type A, if A is ∥∥-modal, then A
-- is (λ (A : Type a) → ∥∥-modal A)-null.

¬[∥∥-modal→∥∥-modal-Null] :
  ¬ ({A : Type a} → ∥∥-modal A → (λ (A : Type a) → ∥∥-modal A) -Null A)
¬[∥∥-modal→∥∥-modal-Null] hyp =                                 $⟨ ⊥-propositional ⟩
  Is-proposition ⊥                                              →⟨ hyp ⟩
  (∀ A → Is-equivalence (const ⦂ (⊥ → Is-proposition A → ⊥)))   →⟨ _$ _ ⟩
  Is-equivalence (const ⦂ (⊥ → Is-proposition (↑ _ Bool) → ⊥))  →⟨ Eq.⟨ _ ,_⟩ ⟩
  ⊥ ≃ (Is-proposition (↑ _ Bool) → ⊥)                           →⟨ →-cong ext
                                                                     (Eq.↔⇒≃ $ inverse $
                                                                      B.⊥↔uninhabited (¬-Bool-propositional ∘ ↑⁻¹-closure 1))
                                                                     Eq.id F.∘_ ⟩
  ⊥ ≃ (⊥₀ → ⊥)                                                  →⟨ Π⊥↔⊤ ext F.∘_ ⟩
  ⊥ ≃ ⊤                                                         →⟨ (λ eq → ⊥-elim $ _≃_.from eq _) ⟩□
  ⊥                                                             □

-- It is not the case that, for every type A, there is an equivalence
-- between "A is ∥∥-modal" and (λ (A : Type a) → ∥∥-modal A) -Null A.
--
-- Compare with Erased.Stability.Very-stable≃Very-stable-Null.

¬[∥∥-modal≃∥∥-modal-Null] :
  ¬ ({A : Type a} → ∥∥-modal A ≃ (λ (A : Type a) → ∥∥-modal A) -Null A)
¬[∥∥-modal≃∥∥-modal-Null] hyp =
  ¬[∥∥-modal→∥∥-modal-Null] (_≃_.to hyp)

-- It is not the case that, for every type A : Type a and proof of
-- Extensionality a a, there is an equivalence between "A is ∥∥-modal"
-- and (λ (A : Type a) → ∥∥-modal A) -Null A.
--
-- Compare with Erased.Stability.Very-stable≃Very-stable-Null.

¬[∥∥-modal≃∥∥-modal-Null]′ :
  ¬ ({A : Type a} →
     Extensionality a a →
     ∥∥-modal A ≃ (λ (A : Type a) → ∥∥-modal A) -Null A)
¬[∥∥-modal≃∥∥-modal-Null]′ hyp =
  ¬[∥∥-modal≃∥∥-modal-Null] (hyp ext)
