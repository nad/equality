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

open import Bijection equality-with-J as B using (_↔_)
open import Embedding equality-with-J as Emb using (Is-embedding)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.List equality-with-J
open import Equivalence.Path-split equality-with-J as PS
  using (_-Null_; Is-∞-extendable-along-[_])
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Localisation eq hiding (ext)
open import Modality.Basics equality-with-J
import Modality.Left-exact equality-with-J as Lex
open import Nullification eq
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J using (_↠_; Split-surjective)
open import Univalence-axiom equality-with-J

private
  variable
    a ℓ p   : Level
    A B C D : Type a
    P       : A → Type p
    i       : A

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
      Is-equivalence-propositional ext

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

----------------------------------------------------------------------
-- The canonical accessible extension

-- The canonical accessible extension of an accessible modality M.

Canonical-accessible-extension :
  (M : Modality a) →
  Accessible M →
  ∀ ℓ → Modality (a ⊔ ℓ)
Canonical-accessible-extension M (I , P , _) ℓ =
  Nullification-modality {A = ↑ ℓ I} (↑ ℓ ∘ P ∘ lower)

-- Some properties that hold for canonical accessible extensions.

module Canonical-accessible-extension
  (M : Modality a)
  (acc@(I , P , _) : Accessible M)
  (ℓ : Level)
  where

  private
    module M = Modality M

  open Modality (Canonical-accessible-extension M acc ℓ) public

  -- A : Type (a ⊔ ℓ) is modal exactly when it is null.

  Modal≃Null :
    {A : Type (a ⊔ ℓ)} →
    Modal A ≃ P -Null A
  Modal≃Null {A = A} =
    (↑ ℓ ∘ P ∘ lower) -Null A                                            ↔⟨⟩
    (((lift i) : ↑ ℓ I) → Is-equivalence (const ⦂ (A → ↑ ℓ (P i) → A)))  ↝⟨ (Π-cong ext B.↑↔ λ _ → F.id) ⟩
    (∀ i → Is-equivalence (const ⦂ (A → ↑ ℓ (P i) → A)))                 ↔⟨⟩
    (∀ i → Is-equivalence ((_∘ lower) ∘ const ⦂ (A → ↑ ℓ (P i) → A)))    ↝⟨ (∀-cong ext λ _ →
                                                                             Is-equivalence≃Is-equivalence-∘ˡ
                                                                               (_≃_.is-equivalence $ Eq.↔⇒≃ $ →-cong ext B.↑↔ F.id)
                                                                               ext) ⟩
    (∀ i → Is-equivalence (const ⦂ (A → P i → A)))                       ↔⟨⟩
    P -Null A                                                            □

  -- A : Type a is M-modal exactly when ↑ ℓ A is modal.

  Modal≃Modal-↑ :
    {A : Type a} →
    M.Modal A ≃ Modal (↑ ℓ A)
  Modal≃Modal-↑ {A = A} =
    M.Modal A                                               ↝⟨ M.Accessible→Modal≃Null ext acc ⟩

    P -Null A                                               ↔⟨⟩

    (∀ i → Is-equivalence (const ⦂ (A → P i → A)))          ↝⟨ (∀-cong ext λ _ → inverse $
                                                                Is-equivalence≃Is-equivalence-∘ʳ
                                                                  (_≃_.is-equivalence $ Eq.↔⇒≃ $ inverse B.↑↔)
                                                                  ext F.∘
                                                                Is-equivalence≃Is-equivalence-∘ˡ
                                                                  (_≃_.is-equivalence $ Eq.↔⇒≃ $ →-cong ext F.id B.↑↔)
                                                                  ext) ⟩
    ((i : I) →
     Is-equivalence
       ((lift ∘_) ∘ const ∘ lower ⦂
        (↑ ℓ A → P i → ↑ ℓ A)))                             ↔⟨⟩

    (∀ i → Is-equivalence (const ⦂ (↑ ℓ A → P i → ↑ ℓ A)))  ↔⟨⟩

    P -Null ↑ ℓ A                                           ↝⟨ inverse Modal≃Null ⟩□

    Modal (↑ ℓ A)                                           □

  -- There is an equivalence between ◯ (↑ ℓ A) and M.◯ A.

  ◯↑≃◯ : ◯ (↑ ℓ A) ≃ M.◯ A
  ◯↑≃◯ {A = A} =
    Nullification (↑ ℓ ∘ P ∘ lower) (↑ ℓ A)  ↝⟨ Nullification-↑-↑-≃ ⟩
    Nullification P A                        ↝⟨ inverse $ Accessible→≃Nullification M acc .proj₁ _ ⟩□
    M.◯ A                                    □

  -- Two "computation rules" for ◯↑≃◯.

  from-◯↑≃◯-η : _≃_.from (◯↑≃◯ {A = A}) ∘ M.η ≡ η ∘ lift
  from-◯↑≃◯-η =
    _≃_.from Nullification-↑-↑-≃ ∘
    _≃_.to (Accessible→≃Nullification M acc .proj₁ _) ∘ M.η  ≡⟨ cong (_≃_.from Nullification-↑-↑-≃ ∘_) $
                                                                Accessible→≃Nullification M acc .proj₂ _ ⟩

    _≃_.from Nullification-↑-↑-≃ ∘ [_]                       ≡⟨⟩

    η ∘ lift                                                 ∎

  to-◯↑≃◯-η : _≃_.to (◯↑≃◯ {A = A}) ∘ η ≡ M.η ∘ lower
  to-◯↑≃◯-η = ⟨ext⟩ λ x → _≃_.from-to ◯↑≃◯
    (_≃_.from ◯↑≃◯ (M.η (lower x))  ≡⟨ cong (_$ lower x) from-◯↑≃◯-η ⟩∎
     η x                            ∎)

  -- Modal A can be expressed in another way.

  Modal≃ :
    {A : Type (a ⊔ ℓ)} →
    Modal A ≃
    ({B C : Type a} {f : B → C} →
     Is-equivalence (M.◯-map f) →
     Is-equivalence ((_∘ f) ⦂ ((C → A) → (B → A))))
  Modal≃ {A = A} =
    Modal A                                          ↝⟨ Modal≃Null ⟩

    P -Null A                                        ↝⟨ Eq.⇔→≃
                                                          (PS.Null-propositional ext)
                                                          (implicit-Π-closure ext 1 λ _ →
                                                           implicit-Π-closure ext 1 λ _ →
                                                           implicit-Π-closure ext 1 λ _ →
                                                           Π-closure ext 1 λ _ →
                                                           Is-equivalence-propositional ext)
                                                          (λ hyp → to hyp)
                                                          from ⟩□
    ({B C : Type a} {f : B → C} →
     Is-equivalence (M.◯-map f) →
     Is-equivalence ((_∘ f) ⦂ ((C → A) → (B → A))))  □
    where
    from =
      ({B C : Type a} {f : B → C} →
       Is-equivalence (M.◯-map f) →
       Is-equivalence ((_∘ f) ⦂ ((C → A) → (B → A))))                    →⟨ (λ hyp _ → hyp equiv) ⟩

      (λ i (_ : P i) → lift tt) -Local A                                 ↔⟨⟩

      (∀ i →
       Is-equivalence (_∘ const (lift tt) ⦂ ((↑ a ⊤ → A) → (P i → A))))  →⟨ (∀-cong _ λ _ →
                                                                             Is-equivalence≃Is-equivalence-∘ʳ
                                                                               (_≃_.is-equivalence $
                                                                                →-cong ext (Eq.↔⇒≃ $ inverse B.↑↔) F.id)
                                                                               _) ⟩

      (∀ i → Is-equivalence (_∘ const tt ⦂ ((⊤ → A) → (P i → A))))       ↔⟨⟩

      (λ i (_ : P i) → tt) -Local A                                      ↔⟨ inverse Null≃Local ⟩□

      P -Null A                                                          □
      where
      equiv : {f : P i → ↑ a ⊤} → Is-equivalence (M.◯-map f)
      equiv {f = f} =                 $⟨ (λ {_} → M.Accessible→Connected ext acc) ⟩
        (∀ {i} → M.◯ -Connected P i)  →⟨ (λ hyp _ →
                                            M.Connected-Σ
                                              hyp
                                              (λ _ → M.Contractible→Connected
                                                       (H-level.⇒≡ 0 (↑-closure 0 ⊤-contractible)))) ⟩
        M.◯ -Connected-→ f            →⟨ M.Connected-→→Is-equivalence-◯-map ⟩□
        Is-equivalence (M.◯-map f)    □

    to :
      {f : B → C} →
      P -Null A →
      Is-equivalence (M.◯-map f) →
      Is-equivalence ((_∘ f) ⦂ ((C → A) → (B → A)))
    to {B = B} {C = C} {f = f} null =
      Is-equivalence (M.◯-map f)                                →⟨ Is-equivalence≃Is-equivalence-∘ˡ
                                                                     (_≃_.is-equivalence $ inverse ◯↑≃◯)
                                                                     _ ∘
                                                                   Is-equivalence≃Is-equivalence-∘ʳ
                                                                     (_≃_.is-equivalence ◯↑≃◯)
                                                                     _ ⟩

      Is-equivalence (_≃_.from ◯↑≃◯ ∘ M.◯-map f ∘ _≃_.to ◯↑≃◯)  →⟨ (Is-equivalence-cong _ $
                                                                    ◯-elim (λ _ → Separated-◯ _ _) λ x →

        _≃_.from ◯↑≃◯ (M.◯-map f (_≃_.to ◯↑≃◯ (η x)))                 ≡⟨ cong (_≃_.from ◯↑≃◯ ∘ M.◯-map f) $ ext⁻¹ to-◯↑≃◯-η _ ⟩
        _≃_.from ◯↑≃◯ (M.◯-map f (M.η (lower x)))                     ≡⟨ cong (_≃_.from ◯↑≃◯) M.◯-map-η ⟩
        _≃_.from ◯↑≃◯ (M.η (f (lower x)))                             ≡⟨ ext⁻¹ from-◯↑≃◯-η _ ⟩
        η (lift (f (lower x)))                                        ≡⟨⟩
        η (f′ x)                                                      ≡⟨ sym ◯-map-η ⟩∎
        ◯-map f′ (η x)                                                ∎) ⟩

      Is-equivalence (◯-map f′)                                 →⟨ (λ eq →
                                                                      _≃_.is-equivalence $
                                                                      →-cong ext (inverse Eq.⟨ _ , eq ⟩) F.id) ⟩

      Is-equivalence (_∘ ◯-map f′)                              →⟨ Is-equivalence≃Is-equivalence-∘ˡ
                                                                     (_≃_.is-equivalence ◯→A≃→A)
                                                                     _ ⟩

      Is-equivalence ((_∘ η) ∘ (_∘ ◯-map f′))                   ↔⟨⟩

      Is-equivalence (_∘ (◯-map f′ ∘ η))                        →⟨ (Is-equivalence-cong _ λ g → ⟨ext⟩ λ _ → cong g
                                                                    ◯-map-η) ⟩
      Is-equivalence (_∘ (η ∘ f′))                              ↔⟨⟩

      Is-equivalence ((_∘ f′) ∘ (_∘ η))                         →⟨ Is-equivalence≃Is-equivalence-∘ʳ
                                                                     (_≃_.is-equivalence $ inverse ◯→A≃→A)
                                                                     _ ⟩

      Is-equivalence ((_∘ f′) ∘ (_∘ η) ∘ _≃_.from ◯→A≃→A)       →⟨ (Is-equivalence-cong _ λ g →
                                                                    cong {y = g} (_∘ (lift ∘ f ∘ lower)) $
                                                                    _≃_.right-inverse-of ◯→A≃→A _) ⟩

      Is-equivalence (_∘ f′)                                    →⟨ Is-equivalence≃Is-equivalence-∘ˡ
                                                                     (_≃_.is-equivalence $
                                                                      →-cong ext (Eq.↔⇒≃ B.↑↔) F.id)
                                                                     _ ∘
                                                                   Is-equivalence≃Is-equivalence-∘ʳ
                                                                     (_≃_.is-equivalence $
                                                                      →-cong ext (Eq.↔⇒≃ $ inverse B.↑↔) F.id)
                                                                     _ ⟩□
      Is-equivalence (_∘ f)                                     □
      where
      f′ : ↑ ℓ B → ↑ ℓ C
      f′ = lift ∘ f ∘ lower

      ◯→A≃→A : (◯ (↑ ℓ D) → A) ≃ (↑ ℓ D → A)
      ◯→A≃→A {D = D} =                 $⟨ null ⟩
        P -Null A                      ↔⟨ inverse Modal≃Null ⟩
        (↑ ℓ ∘ P ∘ lower) -Null A      →⟨ Null→Is-equivalence-∘[] ⟩
        Is-equivalence (_∘ η)          →⟨ Eq.⟨ _ ,_⟩ ⟩□
        (◯ (↑ ℓ D) → A) ≃ (↑ ℓ D → A)  □

-- The modal types of the canonical accessible extension of an
-- accessible modality do not depend on the accessibility proof.

modal-types-do-not-depend-on-accessibility-proof :
  (M : Modality a)
  (acc₁ acc₂ : Accessible M) →
  Modality.Modal (Canonical-accessible-extension M acc₁ ℓ) A ≃
  Modality.Modal (Canonical-accessible-extension M acc₂ ℓ) A
modal-types-do-not-depend-on-accessibility-proof
  {a = a} {ℓ = ℓ} {A = A} M acc₁ acc₂ =
  Modality.Modal (Canonical-accessible-extension M acc₁ ℓ) A  ↝⟨ Canonical-accessible-extension.Modal≃ _ acc₁ _ ⟩

  ({B C : Type a} {f : B → C} →
   Is-equivalence (◯-map f) →
   Is-equivalence ((_∘ f) ⦂ ((C → A) → (B → A))))             ↝⟨ inverse $ Canonical-accessible-extension.Modal≃ _ acc₂ _ ⟩□

  Modality.Modal (Canonical-accessible-extension M acc₂ ℓ) A  □
  where
  open Modality M

------------------------------------------------------------------------
-- Left exactness

-- If M is an accessible modality for the universe level a, and
-- ∃ λ (A : Type a) → Modal A (where Modal is the modality predicate
-- of M) is modal with respect to a certain canonical accessible
-- extension of M, then M is left exact (for a certain definition of
-- "left exact").

Accessible→Modal-∃-Modal→Left-exact :
  (M : Modality a)
  (acc : Accessible M) →
  let open Modality M
      module CAE = Canonical-accessible-extension M acc (lsuc a)
  in
  CAE.Modal (∃ λ (A : Type a) → Modal A) →
  {A : Type a} {P : A → Type a} →
  ◯ -Connected A → (∀ x → Modal (P x)) →
  ∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B
Accessible→Modal-∃-Modal→Left-exact
  {a = a} M acc modal {A = A} {P = P} =                  $⟨ modal ⟩

  CAE.Modal (∃ Modal)                                    →⟨ (λ hyp c →
                                                               _≃_.is-equivalence $
                                                               Eq.with-other-function
                                                                 (
    ∃ Modal                                                       ↝⟨ inverse $ drop-⊤-left-Π ext $ _⇔_.to contractible⇔↔⊤ c ⟩
    (◯ A → ∃ Modal)                                               ↝⟨ →-cong ext (inverse CAE.◯↑≃◯) F.id ⟩
    (CAE.◯ (↑ _ A) → ∃ Modal)                                     ↝⟨ CAE.Π◯≃Πη ext (λ _ → CAE.Modal→Stable hyp) ⟩
    (↑ _ A → ∃ Modal)                                             ↝⟨ →-cong ext (from-bijection B.↑↔) F.id ⟩□
    (A → ∃ Modal)                                                 □)
                                                                 const
                                                                 (λ B →
    _≃_.to (CAE.Π◯≃Πη ext (λ _ → CAE.Modal→Stable hyp))
      ((λ x → subst (const (∃ Modal)) (proj₂ c x) B) ∘
       _≃_.to CAE.◯↑≃◯) ∘
    lift                                                            ≡⟨ (⟨ext⟩ λ _ →
                                                                        CAE.Π◯≃Πη-η ext
                                                                          (λ _ → CAE.Modal→Stable hyp)
                                                                          ((λ x → subst (const (∃ Modal)) (proj₂ c x) B) ∘ _≃_.to CAE.◯↑≃◯)) ⟩
    (λ x → subst (const (∃ Modal)) (proj₂ c x) B) ∘
    _≃_.to CAE.◯↑≃◯ ∘ [_] ∘ lift                                    ≡⟨⟩

    (λ x →
       subst (const (∃ Modal))
         (proj₂ c (_≃_.to CAE.◯↑≃◯ [ lift x ]))
         B)                                                         ≡⟨ (⟨ext⟩ λ _ → subst-const _) ⟩∎

    const B                                                         ∎)) ⟩

  (◯ -Connected A →
   Is-equivalence (const ⦂ (∃ Modal → A → ∃ Modal)))     →⟨ (λ hyp c m →
                                                               _≃_.split-surjective Eq.⟨ _ , hyp c ⟩ (λ x → P x , m x)) ⟩
  (◯ -Connected A → (m : ∀ x → Modal (P x)) →
   ∃ λ (B : ∃ Modal) → const B ≡ (λ x → (P x , m x)))    →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                             const⁻¹→) ⟩□
  (◯ -Connected A → (∀ x → Modal (P x)) →
   ∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B)           □
  where
  open Modality M
  module CAE = Canonical-accessible-extension M acc (lsuc a)

private

  -- A lemma used below.

  Is-embedding-const :
    Univalence a →
    (M : Modality a)
    ((_ , P , _) : Accessible M) →
    let open Modality M in
    ∀ i → Is-embedding (const ⦂ (∃ Modal → P i → ∃ Modal))
  Is-embedding-const univ M =
    λ acc@(_ , P , _) i Bm@(B , m-B) Cm@(C , m-C) →                  $⟨ Accessible→Connected ext acc ⟩
      ◯ -Connected P i                                               →⟨ Is-equivalence-const m-B m-C ⟩
      Is-equivalence (const ⦂ (B ≃ C → P i → B ≃ C))                 ↔⟨ Is-equivalence-const≃ ⟩□
      Is-equivalence (cong const ⦂ (Bm ≡ Cm → const Bm ≡ const Cm))  □
    where
    open Modality M

    Is-equivalence-const :
      Modal A → Modal B →
      ◯ -Connected C →
      Is-equivalence (const ⦂ (A ≃ B → C → A ≃ B))
    Is-equivalence-const m-A m-B c =
      _⇔_.to (Connected≃Modal→Is-equivalence-const ext _)
        c
        (Modal-≃ ext m-A m-B)

    Is-equivalence-const≃ :
      {Bm@(B , _) Cm@(C , _) : ∃ Modal} →
      Is-equivalence (const ⦂ (B ≃ C → A → B ≃ C)) ≃
      Is-equivalence (cong const ⦂ (Bm ≡ Cm → const Bm ≡ const Cm))
    Is-equivalence-const≃
      {A = A} {Bm = Bm@(B , m-B)} {Cm = Cm@(C , m-C)} =

      Is-equivalence (const ⦂ (B ≃ C → A → B ≃ C))           ↝⟨ Is-equivalence-cong ext lemma₃ ⟩

      Is-equivalence
        ((≡⇒≃ ∘_) ∘ const ∘ ≃⇒≡ univ ⦂ (B ≃ C → A → B ≃ C))  ↝⟨ inverse $
                                                                Is-equivalence≃Is-equivalence-∘ʳ
                                                                  (_≃_.is-equivalence $ inverse $ ≡≃≃ univ)
                                                                  ext F.∘
                                                                Is-equivalence≃Is-equivalence-∘ˡ
                                                                  (_≃_.is-equivalence $ ∀-cong ext λ _ → ≡≃≃ univ)
                                                                  ext ⟩

      Is-equivalence (const ⦂ (B ≡ C → A → B ≡ C))           ↝⟨ Is-equivalence-cong ext lemma₂ ⟩

      Is-equivalence
        ((_↔_.from lemma₁ ∘_) ∘ const ∘ _↔_.to lemma₁ ⦂
         (B ≡ C → A → B ≡ C))                                ↝⟨ inverse $
                                                                Is-equivalence≃Is-equivalence-∘ʳ
                                                                  (_≃_.is-equivalence $ Eq.↔⇒≃ lemma₁)
                                                                  ext F.∘
                                                                Is-equivalence≃Is-equivalence-∘ˡ
                                                                  (_≃_.is-equivalence $ inverse $
                                                                   ∀-cong ext λ _ → Eq.↔⇒≃ lemma₁)
                                                                  ext ⟩

      Is-equivalence (const ⦂ (Bm ≡ Cm → A → Bm ≡ Cm))       ↝⟨ (Is-equivalence-cong ext λ eq → ⟨ext⟩ λ y →
        eq                                                         ≡⟨ cong-id _ ⟩
        cong id eq                                                 ≡⟨ sym $ cong-∘ _ _ _ ⟩∎
        cong (_$ y) (cong const eq)                                ∎) ⟩

      Is-equivalence
        (ext⁻¹ ∘ cong const ⦂ (Bm ≡ Cm → A → Bm ≡ Cm))       ↝⟨ inverse {k = equivalence} $
                                                                Is-equivalence≃Is-equivalence-∘ˡ
                                                                  (_≃_.is-equivalence $ inverse $
                                                                   Eq.extensionality-isomorphism ext)
                                                                  ext ⟩□
      Is-equivalence
        (cong const ⦂ (Bm ≡ Cm → const Bm ≡ const Cm))       □
      where
      lemma₁ : B ≡ C ↔ Bm ≡ Cm
      lemma₁ =
        ignore-propositional-component (Modal-propositional ext)

      lemma₂ :
        ∀ eq → const eq ≡ _↔_.from lemma₁ ∘ const (_↔_.to lemma₁ eq)
      lemma₂ eq = ⟨ext⟩ λ _ →
        eq                                  ≡⟨ sym $ _↔_.left-inverse-of lemma₁ _ ⟩∎
        _↔_.from lemma₁ (_↔_.to lemma₁ eq)  ∎

      lemma₃ : (eq : B ≃ C) → const eq ≡ ≡⇒≃ ∘ const (≃⇒≡ univ eq)
      lemma₃ eq = ⟨ext⟩ λ _ →
        eq                 ≡⟨ sym $ _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
        ≡⇒≃ (≃⇒≡ univ eq)  ∎

-- Some definitions of "left exact" for accessible modalities are
-- logically equivalent (assuming univalence).

Accessible→Logically-equivalent-Left-exact :
  Univalence a →
  (M : Modality a)
  (acc@(_ , P , _) : Accessible M) →
  let open Modality M
      module CAE = Canonical-accessible-extension M acc (lsuc a)
  in
  Logically-equivalent
    (Left-exact ◯ ,

     (∀ i → (Q : P i → Type a) → (∀ y → Modal (Q y)) →
      ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B)) ,

     (∃ λ ((_ , P , _) : Accessible M) →
      ∀ i → (Q : P i → Type a) → (∀ y → Modal (Q y)) →
      ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B)) ,

     CAE.Modal (∃ λ (A : Type a) → Modal A))
Accessible→Logically-equivalent-Left-exact
  {a = a} univ M acc@(_ , P , _) =
    (Left-exact ◯                                       →⟨ (λ lex →
                                                              Lex.Accessible→ M
                                                                (_⇔_.to (Left-exact≃Left-exact-η-cong _) lex) ext acc) ⟩⇔
     (∀ i → (Q : P i → Type a) → (∀ y → Modal (Q y)) →
      ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B))     →⟨ (λ lex → acc , lex) ⟩⇔

     (∃ λ ((_ , P , _) : Accessible M) →
      ∀ i → (Q : P i → Type a) → (∀ y → Modal (Q y)) →
      ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B))     →⟨ uncurry step₂ ⟩⇔□)

  , (CAE.Modal acc (∃ Modal)                            →⟨ Accessible→Modal-∃-Modal→Left-exact M acc ⟩

     ({A : Type a} {P : A → Type a} →
      ◯ -Connected A → (∀ x → Modal (P x)) →
      ∃ λ (B : Type a) → Modal B × ∀ x → P x ≃ B)       ↔⟨ inverse $ Left-exact≃Connected→Modal→≃ ext univ ⟩□

     Left-exact ◯                                       □)
  where
  open Modality M
  module CAE acc = Canonical-accessible-extension M acc (lsuc a)
  step₂ :
    ((_ , P , _) : Accessible M) →
    (∀ i → (Q : P i → Type a) → (∀ y → Modal (Q y)) →
     ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B)) →
    CAE.Modal acc (∃ λ (A : Type a) → Modal A)
  step₂ acc′@(I , P , _) =
    (∀ i → (Q : P i → Type a) → (∀ y → Modal (Q y)) →
     ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B))                    →⟨ (λ hyp _ → surj hyp) ⟩

    ((i : I) → Split-surjective (const ⦂ (∃ Modal → P i → ∃ Modal)))  →⟨ (λ hyp i →
                                                                            _⇔_.to Emb.Is-embedding×Split-surjective⇔Is-equivalence
                                                                              (Is-embedding-const univ M acc′ i , hyp i)) ⟩
    ((i : I) → Is-equivalence (const ⦂ (∃ Modal → P i → ∃ Modal)))    ↔⟨⟩

    P -Null ∃ Modal                                                   ↔⟨ inverse $ CAE.Modal≃Null acc′ ⟩

    CAE.Modal acc′ (∃ Modal)                                          ↔⟨ modal-types-do-not-depend-on-accessibility-proof M acc′ acc ⟩□

    CAE.Modal acc (∃ Modal)                                           □
    where
    surj :
      (∀ i → (Q : P i → Type a) → (∀ y → Modal (Q y)) →
       ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B)) →
      Split-surjective (const ⦂ (∃ Modal → P i → ∃ Modal))
    surj {i = i} hyp Q =                           $⟨ hyp i (proj₁ ∘ Q) (proj₂ ∘ Q) ⟩
      (∃ λ B → Modal B × (∀ y → proj₁ (Q y) ≃ B))  ↝⟨ inverse $ const⁻¹≃ ext univ ⟩□
      const ⁻¹ Q                                   □

-- Some definitions of "left exact" for accessible modalities are
-- equivalent (assuming univalence).

Accessible→Equivalent-Left-exact :
  Univalence a →
  (M : Modality a)
  (acc@(_ , P , _) : Accessible M) →
  let open Modality M
      module CAE = Canonical-accessible-extension M acc (lsuc a)
  in
  Equivalent
    (Left-exact ◯ ,

     (∀ i → (Q : P i → Type a) → (∀ y → Modal (Q y)) →
      ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B)) ,

     CAE.Modal (∃ λ (A : Type a) → Modal A))
Accessible→Equivalent-Left-exact
  {a = a} univ M acc@(_ , P , _) =
    Logically-equivalent-Delete
      (inj₂ (inj₂ (inj₁ F.id)))
      (Accessible→Logically-equivalent-Left-exact
         univ M acc)
  , ( Left-exact-propositional ext
    , prop
    , CAE.Modal-propositional ext
    , _
    )
  where
  open Modality M
  module CAE = Canonical-accessible-extension M acc (lsuc a)

  prop =                                                     $⟨ (Π-closure ext 1 λ _ →
                                                                 Π-closure ext 1 λ _ →
                                                                 Emb.embedding→⁻¹-propositional
                                                                   (Is-embedding-const univ M acc _)
                                                                   _) ⟩
    Is-proposition (∀ x → (Q : P x → ∃ Modal) → const ⁻¹ Q)  →⟨ (H-level-cong _ 1 $
                                                                 ∀-cong ext λ _ →
                                                                 Eq.↔⇒≃ currying F.∘
                                                                 (Π-cong ext ΠΣ-comm λ _ → F.id) F.∘
                                                                 (∀-cong ext λ Q → const⁻¹≃ ext univ)) ⟩□
    Is-proposition
      (∀ x → (Q : P x → Type a) → (∀ y → Modal (Q y)) →
       ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B))         □

-- If P is pointwise propositional, then Nullification P is left exact
-- (assuming univalence).

Is-proposition→Left-exact-Nullification-modality :
  {P : A → Type a} →
  Univalence a →
  (∀ x → Is-proposition (P x)) →
  Left-exact (Nullification P)
Is-proposition→Left-exact-Nullification-modality
  {a = a} {P = P} univ prop =
  _⇔_.to
    (logically-equivalent
       (Accessible→Logically-equivalent-Left-exact
          univ
          (Nullification-modality P)
          Nullification-accessible)
       (inj₂ (inj₁ F.id)) (inj₁ F.id))
    lex
  where
  open Modality (Nullification-modality P)

  lex :
    ∀ x → (Q : P x → Type a) → (∀ y → Modal (Q y)) →
    ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B)
  lex x Q m =
      (∀ x → Q x)
    , Modal-Π ext m
    , (λ y →
         Q y          ↝⟨ inverse $ drop-⊤-left-Π ext $
                         _⇔_.to contractible⇔↔⊤ $
                         propositional⇒inhabited⇒contractible
                           (prop _)
                           y ⟩□
         (∀ y → Q y)  □)

-- Topological modalities are left exact (assuming univalence).

Topological→Left-exact :
  Univalence a →
  (M : Modality a) →
  let open Modality M in
  Topological M → Left-exact ◯
Topological→Left-exact {a = a} univ M =
  Topological M                                    ↔⟨ Topological≃≡ univ M ⟩

  (∃ λ ((_ , P , _) :
        ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
          M ≡ Nullification-modality P) →
     ∀ x → Is-proposition (P x))                   →⟨ (λ ((_ , _ , M≡) , prop) →
                                                         subst
                                                           (Left-exact ∘ Modality.◯)
                                                           (sym M≡)
                                                           (Is-proposition→Left-exact-Nullification-modality
                                                              univ prop)) ⟩□
  Left-exact ◯                                     □
  where
  open Modality M
