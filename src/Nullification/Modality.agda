------------------------------------------------------------------------
-- The nullification modality
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- Based on "Modalities in Homotopy Type Theory" by Rijke, Shulman and
-- Spitters.

import Equality.Path as P

module Nullification.Modality
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Path-split equality-with-J as PS
  using (_-Null_; Is-∞-extendable-along-[_])
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level.Closure equality-with-J
open import Localisation eq hiding (ext)
open import Modality.Basics equality-with-J
open import Nullification eq
open import Univalence-axiom equality-with-J

private
  variable
    a p : Level
    A   : Type a
    P   : A → Type p

------------------------------------------------------------------------
-- The nullification modality

-- The nullification modality for a given type family.

Nullification-modality :
  {A : Type a} (P : A → Type a) →
  Modality a
Nullification-modality {a = a} P =
  Σ-closed-reflective-subuniverse.modality λ where
    .Σ-closed-reflective-subuniverse.◯ → Nullification P

    .Σ-closed-reflective-subuniverse.η → [_]

    .Σ-closed-reflective-subuniverse.Modal A → P -Null A

    .Σ-closed-reflective-subuniverse.Modal-propositional _ →
      Π-closure ext 1 λ _ →
      Eq.propositional ext _

    .Σ-closed-reflective-subuniverse.Modal-◯ {A = A} →
                                                                          $⟨ Local-Localisation ⟩
      (λ x (_ : P x) → tt) -Local Localisation {P = P} {Q = λ _ → ⊤} _ A  ↝⟨ inverse Null≃Local ⟩
      P -Null Localisation {P = P} {Q = λ _ → ⊤} _ A                      ↝⟨ PS.Null-cong ext (λ _ → F.id) (inverse Nullification≃Localisation) ⟩□
      P -Null Nullification P A                                           □

    .Σ-closed-reflective-subuniverse.Modal-respects-≃
      {A = A} {B = B} A≃B →
      P -Null A  ↔⟨ PS.Null-cong ext (λ _ → F.id) A≃B ⟩□
      P -Null B  □

    .Σ-closed-reflective-subuniverse.extendable-along-η
      {B = B} {A = A} →
      P -Null B                                                         ↔⟨ Null≃Local ⟩

      (λ x (_ : P x) → tt) -Local B                                     →⟨ Local→Is-equivalence-[] ⟩

      Is-equivalence
        (λ (f : Localisation {P = P} {Q = λ _ → ⊤} _ A → B) → f ∘ [_])  ↔⟨ Is-equivalence≃Is-equivalence-∘ʳ
                                                                             (_≃_.is-equivalence $
                                                                              →-cong ext Nullification≃Localisation F.id)
                                                                             {k = equivalence}
                                                                             ext ⟩
      Is-equivalence
        ((_∘ [_]) ∘ (_∘ _≃_.from Nullification≃Localisation))           ↔⟨⟩

      Is-equivalence (λ (f : Nullification P A → B) → f ∘ [_])          ↔⟨ inverse $ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩□

      Is-∞-extendable-along-[ [_] ] (λ (_ : Nullification P A) → B)     □

    .Σ-closed-reflective-subuniverse.Σ-closed {A = B} {P = Q} mB mQ x →
      _≃_.is-equivalence
        ((∃ λ (y : B) → Q y)                        ↝⟨ (∃-cong λ y → Eq.⟨ _ , mQ y x ⟩) ⟩
         (∃ λ (y : B) → P x → Q y)                  ↝⟨ (Σ-cong Eq.⟨ _ , mB x ⟩ λ _ → F.id) ⟩
         (∃ λ (f : P x → B) → (y : P x) → Q (f y))  ↔⟨ inverse ΠΣ-comm ⟩□
         (P x → ∃ λ (y : B) → Q y)                  □)

-- The nullification modality for P is accessible.

Nullification-accessible :
  {P : A → Type a} →
  Accessible (Nullification-modality P)
Nullification-accessible {a = a} {P = P} =
    _
  , P
  , (λ A →
       Modal A                                               ↔⟨⟩
       P -Null A                                             ↔⟨ inverse $ PS.Π-Is-∞-extendable-along≃Null ext ⟩□
       (∀ x →
          Is-∞-extendable-along-[ (λ (_ : P x) → lift tt) ]
            (λ (_ : ↑ a ⊤) → A))                             □)
  where
  open Modality (Nullification-modality P)

-- If P is pointwise propositional, then the nullification modality
-- for P is topological.

Nullification-topological :
  (∀ x → Is-proposition (P x)) →
  Topological (Nullification-modality P)
Nullification-topological prop =
  Nullification-accessible , prop

-- An alternative characterisation of "accessible".

Accessible≃≃ :
  (M : Modality a) →
  Accessible M ≃
  ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
  ∃ λ (eq : ∀ B → Modality.◯ M B ≃ Nullification P B) →
    ∀ B → _≃_.to (eq B) ∘ Modality.η M ≡ [_]
Accessible≃≃ {a = a} M =
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     (B : Type a) →
     Modal B ⇔
     ∀ x →
     Is-∞-extendable-along-[ (λ (_ : P x) → lift tt) ]
       (λ (_ : ↑ a ⊤) → B))                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                            ⇔-cong ext F.id (PS.Π-Is-∞-extendable-along≃Null ext)) ⟩
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     (B : Type a) → Modal B ⇔ P -Null B)                ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                            Modal⇔Modal≃◯≃◯ ext M (Nullification-modality _) ext) ⟩□
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
   ∃ λ (eq : ∀ B → ◯ B ≃ Nullification P B) →
     ∀ B → _≃_.to (eq B) ∘ η ≡ [_])                     □
  where
  open Modality M

-- If a modality is accessible, then it is related to nullification in
-- a certain way.

Accessible→≃Nullification :
  (M : Modality a)
  ((_ , P , _) : Accessible M) →
  ∃ λ (eq : ∀ B → Modality.◯ M B ≃ Nullification P B) →
    ∀ B → _≃_.to (eq B) ∘ Modality.η M ≡ [_]
Accessible→≃Nullification M acc =
  _≃_.to (Accessible≃≃ M) acc .proj₂ .proj₂

-- Another alternative characterisation of "accessible".

Accessible≃≡ :
  Univalence a →
  (M : Modality a) →
  Accessible M ≃
  ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
    M ≡ Nullification-modality P
Accessible≃≡ {a = a} univ M =
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     (B : Type a) →
     Modal B ⇔
     ∀ x →
     Is-∞-extendable-along-[ (λ (_ : P x) → lift tt) ]
       (λ (_ : ↑ a ⊤) → B))                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                            ⇔-cong ext F.id (PS.Π-Is-∞-extendable-along≃Null ext)) ⟩
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     (B : Type a) → Modal B ⇔ P -Null B)                ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                            Modal⇔Modal≃≡ ext univ) ⟩□
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     M ≡ Nullification-modality P)                      □
  where
  open Modality M

-- An alternative characterisation of "topological".

Topological≃≃ :
  (M : Modality a) →
  Topological M ≃
  ∃ λ ((_ , P , _) :
       ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
       ∃ λ (eq : ∀ B → Modality.◯ M B ≃ Nullification P B) →
         (∀ B → _≃_.to (eq B) ∘ Modality.η M ≡ [_])) →
    ∀ x → Is-proposition (P x)
Topological≃≃ M = Σ-cong (Accessible≃≃ M) λ _ → F.id

-- Another alternative characterisation of "topological".

Topological≃≡ :
  Univalence a →
  (M : Modality a) →
  Topological M ≃
  ∃ λ ((_ , P , _) :
       ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
         M ≡ Nullification-modality P) →
    ∀ x → Is-proposition (P x)
Topological≃≡ univ M = Σ-cong (Accessible≃≡ univ M) λ _ → F.id
