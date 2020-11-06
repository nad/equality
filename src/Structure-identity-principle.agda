------------------------------------------------------------------------
-- Aczel's structure identity principle (for 1-categories), more or
-- less as found in "Homotopy Type Theory: Univalent Foundations of
-- Mathematics" (first edition)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Structure-identity-principle
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq using (_↔_; Σ-≡,≡↔≡)
open import Category eq
open Derived-definitions-and-properties eq
open import Equality.Decidable-UIP eq
open import Equivalence eq hiding (id; _∘_; inverse; lift-equality)
open import Function-universe eq hiding (id) renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (id)

-- Standard notions of structure.

record Standard-notion-of-structure
         {c₁ c₂} ℓ₁ ℓ₂ (C : Precategory c₁ c₂) :
         Type (c₁ ⊔ c₂ ⊔ lsuc (ℓ₁ ⊔ ℓ₂)) where
  open Precategory C

  field
    P               : Obj → Type ℓ₁
    H               : ∀ {X Y} (p : P X) (q : P Y) → Hom X Y → Type ℓ₂
    H-prop          : ∀ {X Y} {p : P X} {q : P Y}
                      (f : Hom X Y) → Is-proposition (H p q f)
    H-id            : ∀ {X} {p : P X} → H p p id
    H-∘             : ∀ {X Y Z} {p : P X} {q : P Y} {r : P Z} {f g} →
                      H p q f → H q r g → H p r (g ∙ f)
    H-antisymmetric : ∀ {X} (p q : P X) →
                      H p q id → H q p id → p ≡ q

  -- P constructs sets. (The proof was suggested by Michael Shulman in
  -- a mailing list post.)

  P-set : ∀ A → Is-set (P A)
  P-set A = propositional-identity⇒set
    (λ p q → H p q id × H q p id)
    (λ _ _ → ×-closure 1 (H-prop id) (H-prop id))
    (λ _ → H-id , H-id)
    (λ p q → uncurry (H-antisymmetric p q))

  -- Two Str morphisms (see below) of equal type are equal if their
  -- first components are equal.

  lift-equality : {X Y : ∃ P} {f g : ∃ (H (proj₂ X) (proj₂ Y))} →
                  proj₁ f ≡ proj₁ g → f ≡ g
  lift-equality eq = Σ-≡,≡→≡ eq (H-prop _ _ _)

  -- A derived precategory.

  Str : Precategory (c₁ ⊔ ℓ₁) (c₂ ⊔ ℓ₂)
  Str = record { precategory =
    ∃ P ,
    (λ { (X , p) (Y , q) →
         ∃ (H p q) ,
         Σ-closure 2 Hom-is-set (λ f → mono₁ 1 (H-prop f)) }) ,
    (id , H-id) ,
    (λ { (f , hf) (g , hg) → f ∙ g , H-∘ hg hf }) ,
    lift-equality left-identity ,
    lift-equality right-identity ,
    lift-equality assoc }

  module Str = Precategory Str

  -- A rearrangement lemma.

  proj₁-≡→≅-¹ :
    ∀ {X Y} (X≡Y : X ≡ Y) →
    proj₁ (Str.≡→≅ X≡Y Str.¹) ≡
    elim (λ {X Y} _ → Hom X Y) (λ _ → id) (cong proj₁ X≡Y)
  proj₁-≡→≅-¹ {X , p} = elim¹
    (λ X≡Y → proj₁ (Str.≡→≅ X≡Y Str.¹) ≡
             elim (λ {X Y} _ → Hom X Y) (λ _ → id) (cong proj₁ X≡Y))
    (proj₁ (Str.≡→≅ (refl (X , p)) Str.¹)                               ≡⟨ cong (proj₁ ∘ Str._¹) $ elim-refl (λ {X Y} _ → X Str.≅ Y) _ ⟩
     proj₁ (Str.id {X = X , p})                                         ≡⟨⟩
     id {X = X}                                                         ≡⟨ sym $ elim-refl (λ {X Y} _ → Hom X Y) _ ⟩
     elim (λ {X Y} _ → Hom X Y) (λ _ → id) (refl X)                     ≡⟨ cong (elim (λ {X Y} _ → Hom X Y) _) $ sym $ cong-refl proj₁ ⟩∎
     elim (λ {X Y} _ → Hom X Y) (λ _ → id) (cong proj₁ (refl (X , p)))  ∎)

-- The structure identity principle states that the precategory Str is
-- a category (assuming extensionality).
--
-- The proof below is based on (but not quite identical to) the one in
-- "Homotopy Type Theory: Univalent Foundations of Mathematics" (first
-- edition).

abstract

  structure-identity-principle :
    ∀ {c₁ c₂ ℓ₁ ℓ₂} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
    (C : Category c₁ c₂) →
    (S : Standard-notion-of-structure ℓ₁ ℓ₂ (Category.precategory C)) →
    ∀ {X Y} → Is-equivalence
                (Precategory.≡→≅ (Standard-notion-of-structure.Str S)
                                 {X} {Y})
  structure-identity-principle ext C S =
    Str.≡→≅-equivalence-lemma ≡≃≅ ≡≃≅-refl
    where
    open Standard-notion-of-structure S
    module C = Category C

    -- _≡_ is pointwise equivalent to Str._≅_.

    module ≅HH≃≅ where

      to : ∀ {X Y} {p : P X} {q : P Y} →
           (∃ λ (f : X C.≅ Y) → H p q (f C.¹) × H q p (f C.⁻¹)) →
           (X , p) Str.≅ (Y , q)
      to ((f , f⁻¹ , f∙f⁻¹ , f⁻¹∙f) , Hf , Hf⁻¹) =
        (f , Hf) , (f⁻¹ , Hf⁻¹) ,
        lift-equality f∙f⁻¹ ,
        lift-equality f⁻¹∙f

    ≅HH≃≅ : ∀ {X Y} {p : P X} {q : P Y} →
            (∃ λ (f : X C.≅ Y) → H p q (f C.¹) × H q p (f C.⁻¹)) ≃
            ((X , p) Str.≅ (Y , q))
    ≅HH≃≅ {X} {Y} {p} {q} = ↔⇒≃ (record
      { surjection = record
        { logical-equivalence = record
          { to   = ≅HH≃≅.to
          ; from = from
          }
        ; right-inverse-of = to∘from
        }
      ; left-inverse-of = from∘to
      })
      where
      from : (X , p) Str.≅ (Y , q) →
             ∃ λ (f : X C.≅ Y) → H p q (f C.¹) × H q p (f C.⁻¹)
      from ((f , Hf) , (f⁻¹ , Hf⁻¹) , f∙f⁻¹ , f⁻¹∙f) =
        (f , f⁻¹ , cong proj₁ f∙f⁻¹ , cong proj₁ f⁻¹∙f) , Hf , Hf⁻¹

      to∘from : ∀ p → ≅HH≃≅.to (from p) ≡ p
      to∘from ((f , Hf) , (f⁻¹ , Hf⁻¹) , f∙f⁻¹ , f⁻¹∙f) =
        cong₂ (λ f∙f⁻¹ f⁻¹∙f →
                 (f , Hf) , (f⁻¹ , Hf⁻¹) , f∙f⁻¹ , f⁻¹∙f)
              (Str.Hom-is-set _ _)
              (Str.Hom-is-set _ _)

      from∘to : ∀ p → from (≅HH≃≅.to p) ≡ p
      from∘to ((f , f⁻¹ , f∙f⁻¹ , f⁻¹∙f) , Hf , Hf⁻¹) =
        cong₂ (λ f∙f⁻¹ f⁻¹∙f → (f , f⁻¹ , f∙f⁻¹ , f⁻¹∙f) , Hf , Hf⁻¹)
              (C.Hom-is-set _ _)
              (C.Hom-is-set _ _)

    module ≡≡≃≅HH where

      to : ∀ {X Y} {p : P X} {q : P Y} →
           (X≡Y : X ≡ Y) → subst P X≡Y p ≡ q →
           H p q (C.≡→≅ X≡Y C.¹) × H q p (C.≡→≅ X≡Y C.⁻¹)
      to {X} {p = p} X≡Y p≡q = elim¹
        (λ X≡Y → ∀ {q} → subst P X≡Y p ≡ q →
                 H p q (C.≡→≅ X≡Y C.¹) × H q p (C.≡→≅ X≡Y C.⁻¹))
        (elim¹
           (λ {q} _ → H p q (C.≡→≅ (refl X) C.¹) ×
                      H q p (C.≡→≅ (refl X) C.⁻¹))
           ( subst (λ { (q , f) → H p q f })
                   (sym $ cong₂ _,_
                            (subst P (refl X) p  ≡⟨ subst-refl P _ ⟩∎
                             p                   ∎)
                            (C.≡→≅ (refl X) C.¹  ≡⟨ cong C._¹ C.≡→≅-refl ⟩∎
                             C.id                ∎))
                   H-id
           , subst (λ { (q , f) → H q p f })
                   (sym $ cong₂ _,_
                            (subst P (refl X) p  ≡⟨ subst-refl P _ ⟩∎
                             p                   ∎)
                            (C.≡→≅ (refl X) C.⁻¹  ≡⟨ cong C._⁻¹ C.≡→≅-refl ⟩∎
                             C.id                 ∎))
                   H-id
           ))
        X≡Y p≡q

      to-refl : ∀ {X} {p : P X} →
                subst (λ f → H p p (f C.¹) × H p p (f C.⁻¹))
                      C.≡→≅-refl
                      (to (refl X) (subst-refl P p)) ≡
                (H-id , H-id)
      to-refl = cong₂ _,_ (H-prop _ _ _) (H-prop _ _ _)

    ≡≡≃≅HH : ∀ {X Y} {p : P X} {q : P Y} →
             (∃ λ (eq : X ≡ Y) → subst P eq p ≡ q) ≃
             (∃ λ (f : X C.≅ Y) → H p q (f C.¹) × H q p (f C.⁻¹))
    ≡≡≃≅HH {X} {p = p} {q} =
      Σ-preserves C.≡≃≅ λ X≡Y →
        _↔_.to (⇔↔≃ ext (P-set _) (×-closure 1 (H-prop _) (H-prop _)))
               (record { to = ≡≡≃≅HH.to X≡Y ; from = from X≡Y })
      where
      from : ∀ X≡Y → H p q (C.≡→≅ X≡Y C.¹) × H q p (C.≡→≅ X≡Y C.⁻¹) →
             subst P X≡Y p ≡ q
      from X≡Y (H¹ , H⁻¹) = elim¹
        (λ {Y} X≡Y → ∀ {q} →
                     H p q (C.≡→≅ X≡Y C.¹) → H q p (C.≡→≅ X≡Y C.⁻¹) →
                     subst P X≡Y p ≡ q)
        (λ {q} H¹ H⁻¹ →
           subst P (refl X) p  ≡⟨ subst-refl P _ ⟩
           p                   ≡⟨ H-antisymmetric p q
                                    (subst (H p q) (cong C._¹  C.≡→≅-refl) H¹)
                                    (subst (H q p) (cong C._⁻¹ C.≡→≅-refl) H⁻¹) ⟩∎
           q                   ∎)
        X≡Y H¹ H⁻¹

    ≡≃≅ : ∀ {X Y} {p : P X} {q : P Y} →
          _≡_ {A = ∃ P} (X , p) (Y , q) ≃ ((X , p) Str.≅ (Y , q))
    ≡≃≅ = ≅HH≃≅ ⊚ ≡≡≃≅HH ⊚ ↔⇒≃ (inverse Σ-≡,≡↔≡)

    -- …and the proof maps reflexivity to the identity morphism.

    ≡≃≅-refl : ∀ {Xp} → _≃_.to ≡≃≅ (refl Xp) Str.¹ ≡ Str.id
    ≡≃≅-refl {X , p} = cong Str._¹ (
      ≅HH≃≅.to (_≃_.to ≡≡≃≅HH (Σ-≡,≡←≡ (refl (_,_ {B = P} X p))))      ≡⟨ cong (≅HH≃≅.to ∘ _≃_.to ≡≡≃≅HH) $ Σ-≡,≡←≡-refl {B = P} ⟩
      ≅HH≃≅.to (_≃_.to ≡≡≃≅HH (refl X , subst-refl P p))               ≡⟨⟩
      ≅HH≃≅.to (C.≡→≅ (refl X) , ≡≡≃≅HH.to (refl X) (subst-refl P p))  ≡⟨ cong ≅HH≃≅.to $ Σ-≡,≡→≡ C.≡→≅-refl ≡≡≃≅HH.to-refl ⟩
      ≅HH≃≅.to (C.id≅ , H-id , H-id)                                   ≡⟨ refl _ ⟩∎
      Str.id≅                                                          ∎)
