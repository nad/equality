------------------------------------------------------------------------
-- 1-categories
------------------------------------------------------------------------

-- The code is based on the presentation in the HoTT book (but might
-- not follow it exactly).

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Category
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection using (_↔_)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq
  using (_≃_; ⟨_,_⟩; module _≃_; Is-equivalence)
open import Extensionality eq
open import Function-universe eq as F hiding (id) renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence using (module _⇔_)
import Nat eq as Nat
open import Prelude as P hiding (id; Unit)
open import Univalence-axiom eq

------------------------------------------------------------------------
-- Precategories

-- This definition of precategories takes the type of objects as a
-- parameter.

Precategory-with-Obj :
  ∀ {ℓ₁} → Type ℓ₁ → (ℓ₂ : Level) → Type (ℓ₁ ⊔ lsuc ℓ₂)
Precategory-with-Obj Obj ℓ₂ =
  -- Morphisms (a /set/).
  ∃ λ (HOM : Obj → Obj → Set ℓ₂) →
  let Hom = λ X Y → proj₁ (HOM X Y) in

  -- Identity.
  ∃ λ (id : ∀ {X} → Hom X X) →

  -- Composition.
  ∃ λ (_∙_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z) →

  -- Identity laws.
  (∀ {X Y} {f : Hom X Y} → (id ∙ f) ≡ f) ×
  (∀ {X Y} {f : Hom X Y} → (f ∙ id) ≡ f) ×

  -- Associativity.
  (∀ {X Y Z U} {f : Hom X Y} {g : Hom Y Z} {h : Hom Z U} →
     (h ∙ (g ∙ f)) ≡ ((h ∙ g) ∙ f))

-- Precategories.

Precategory′ : (ℓ₁ ℓ₂ : Level) → Type (lsuc (ℓ₁ ⊔ ℓ₂))
Precategory′ ℓ₁ ℓ₂ =
  -- Objects.
  ∃ λ (Obj : Type ℓ₁) →

  Precategory-with-Obj Obj ℓ₂

-- A wrapper.

record Precategory (ℓ₁ ℓ₂ : Level) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    precategory : Precategory′ ℓ₁ ℓ₂

  -- Objects.

  Obj : Type ℓ₁
  Obj = proj₁ precategory

  -- Morphisms.

  HOM : Obj → Obj → Set ℓ₂
  HOM = proj₁ (proj₂ precategory)

  -- The morphism type family.

  Hom : Obj → Obj → Type ℓ₂
  Hom X Y = proj₁ (HOM X Y)

  -- The morphism types are sets.

  Hom-is-set : ∀ {X Y} → Is-set (Hom X Y)
  Hom-is-set = proj₂ (HOM _ _)

  -- Identity.

  id : ∀ {X} → Hom X X
  id = proj₁ (proj₂ (proj₂ precategory))

  -- Composition.

  infixr 10 _∙_

  _∙_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
  _∙_ = proj₁ (proj₂ (proj₂ (proj₂ precategory)))

  -- The left identity law.

  left-identity : ∀ {X Y} {f : Hom X Y} → id ∙ f ≡ f
  left-identity = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ precategory))))

  -- The right identity law.

  right-identity : ∀ {X Y} {f : Hom X Y} → f ∙ id ≡ f
  right-identity =
    proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ precategory)))))

  -- The associativity law.

  assoc : ∀ {X Y Z U} {f : Hom X Y} {g : Hom Y Z} {h : Hom Z U} →
          h ∙ (g ∙ f) ≡ (h ∙ g) ∙ f
  assoc =
    proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ precategory)))))

  -- Isomorphisms.

  Is-isomorphism : ∀ {X Y} → Hom X Y → Type ℓ₂
  Is-isomorphism f = ∃ λ g → (f ∙ g ≡ id) × (g ∙ f ≡ id)

  infix 4 _≅_

  _≅_ : Obj → Obj → Type ℓ₂
  X ≅ Y = ∃ λ (f : Hom X Y) → Is-isomorphism f

  -- Some projections.

  infix 15 _¹ _⁻¹ _¹⁻¹ _⁻¹¹

  _¹ : ∀ {X Y} → X ≅ Y → Hom X Y
  f ¹ = proj₁ f

  _⁻¹ : ∀ {X Y} → X ≅ Y → Hom Y X
  f ⁻¹ = proj₁ (proj₂ f)

  _¹⁻¹ : ∀ {X Y} (f : X ≅ Y) → f ¹ ∙ f ⁻¹ ≡ id
  f ¹⁻¹ = proj₁ (proj₂ (proj₂ f))

  _⁻¹¹ : ∀ {X Y} (f : X ≅ Y) → f ⁻¹ ∙ f ¹ ≡ id
  f ⁻¹¹ = proj₂ (proj₂ (proj₂ f))

  opaque

    -- "Is-isomorphism f" is a proposition.

    Is-isomorphism-propositional :
      ∀ {X Y} (f : Hom X Y) →
      Is-proposition (Is-isomorphism f)
    Is-isomorphism-propositional f (g , fg , gf) (g′ , fg′ , g′f) =
      Σ-≡,≡→≡ (g             ≡⟨ sym left-identity ⟩
               id ∙ g        ≡⟨ cong (λ h → h ∙ g) $ sym g′f ⟩
               (g′ ∙ f) ∙ g  ≡⟨ sym assoc ⟩
               g′ ∙ (f ∙ g)  ≡⟨ cong (_∙_ g′) fg ⟩
               g′ ∙ id       ≡⟨ right-identity ⟩∎
               g′            ∎)
              (Σ-≡,≡→≡ (Hom-is-set _ _) (Hom-is-set _ _))

    -- Isomorphism equality is equivalent to "forward morphism"
    -- equality.

    ≡≃≡¹ : ∀ {X Y} {f g : X ≅ Y} → (f ≡ g) ≃ (f ¹ ≡ g ¹)
    ≡≃≡¹ {f} {g} =
      (f ≡ g)      ↔⟨ inverse $ ignore-propositional-component $ Is-isomorphism-propositional _ ⟩□
      (f ¹ ≡ g ¹)  □

    -- The type of isomorphisms (between two objects) is a set.

    ≅-set : ∀ {X Y} → Is-set (X ≅ Y)
    ≅-set = Σ-closure 2 Hom-is-set
                      (λ _ → mono₁ 1 $ Is-isomorphism-propositional _)

  -- Identity isomorphism.

  id≅ : ∀ {X} → X ≅ X
  id≅ = id , id , left-identity , right-identity

  -- Composition of isomorphisms.

  infixr 10 _∙≅_

  _∙≅_ : ∀ {X Y Z} → Y ≅ Z → X ≅ Y → X ≅ Z
  f ∙≅ g = (f ¹ ∙ g ¹) , (g ⁻¹ ∙ f ⁻¹) , fg f g , gf f g
    where
    opaque

      fg : ∀ {X Y Z} (f : Y ≅ Z) (g : X ≅ Y) →
           (f ¹ ∙ g ¹) ∙ (g ⁻¹ ∙ f ⁻¹) ≡ id
      fg f g =
        (f ¹ ∙ g ¹) ∙ (g ⁻¹ ∙ f ⁻¹)  ≡⟨ sym assoc ⟩
        f ¹ ∙ (g ¹ ∙ (g ⁻¹ ∙ f ⁻¹))  ≡⟨ cong (_∙_ (f ¹)) assoc ⟩
        f ¹ ∙ ((g ¹ ∙ g ⁻¹) ∙ f ⁻¹)  ≡⟨ cong (λ h → f ¹ ∙ (h ∙ f ⁻¹)) $ g ¹⁻¹ ⟩
        f ¹ ∙ (id ∙ f ⁻¹)            ≡⟨ cong (_∙_ (f ¹)) left-identity ⟩
        f ¹ ∙ f ⁻¹                   ≡⟨ f ¹⁻¹ ⟩∎
        id                           ∎

      gf : ∀ {X Y Z} (f : Y ≅ Z) (g : X ≅ Y) →
           (g ⁻¹ ∙ f ⁻¹) ∙ (f ¹ ∙ g ¹) ≡ id
      gf f g =
        (g ⁻¹ ∙ f ⁻¹) ∙ (f ¹ ∙ g ¹)  ≡⟨ sym assoc ⟩
        g ⁻¹ ∙ (f ⁻¹ ∙ (f ¹ ∙ g ¹))  ≡⟨ cong (_∙_ (g ⁻¹)) assoc ⟩
        g ⁻¹ ∙ ((f ⁻¹ ∙ f ¹) ∙ g ¹)  ≡⟨ cong (λ h → g ⁻¹ ∙ (h ∙ g ¹)) $ f ⁻¹¹ ⟩
        g ⁻¹ ∙ (id ∙ g ¹)            ≡⟨ cong (_∙_ (g ⁻¹)) left-identity ⟩
        g ⁻¹ ∙ g ¹                   ≡⟨ g ⁻¹¹ ⟩∎
        id                           ∎

  -- The inverse of an isomorphism.

  infix 15 _⁻¹≅

  _⁻¹≅ : ∀ {X Y} → X ≅ Y → Y ≅ X
  f ⁻¹≅ = f ⁻¹ , f ¹ , f ⁻¹¹ , f ¹⁻¹

  -- Isomorphisms form a precategory.

  precategory-≅ : Precategory ℓ₁ ℓ₂
  precategory-≅ = record { precategory =
    Obj ,
    (λ X Y → (X ≅ Y) , ≅-set) ,
    id≅ , _∙≅_ ,
    _≃_.from ≡≃≡¹ left-identity ,
    _≃_.from ≡≃≡¹ right-identity ,
    _≃_.from ≡≃≡¹ assoc }

  -- Equal objects are isomorphic.

  ≡→≅ : ∀ {X Y} → X ≡ Y → X ≅ Y
  ≡→≅ = elim (λ {X Y} _ → X ≅ Y) (λ _ → id≅)

  -- "Computation rule" for ≡→≅.

  ≡→≅-refl : ∀ {X} → ≡→≅ (refl X) ≡ id≅
  ≡→≅-refl = elim-refl (λ {X Y} _ → X ≅ Y) _

  -- Rearrangement lemma for ≡→≅.

  ≡→≅-¹ :
    ∀ {X Y} (X≡Y : X ≡ Y) →
    ≡→≅ X≡Y ¹ ≡ elim (λ {X Y} _ → Hom X Y) (λ _ → id) X≡Y
  ≡→≅-¹ {X} = elim¹
    (λ X≡Y → ≡→≅ X≡Y ¹ ≡
             elim (λ {X Y} _ → Hom X Y) (λ _ → id) X≡Y)
    (≡→≅ (refl X) ¹                                  ≡⟨ cong _¹ ≡→≅-refl ⟩
     id≅ ¹                                           ≡⟨⟩
     id                                              ≡⟨ sym $ elim-refl (λ {X Y} _ → Hom X Y) _ ⟩∎
     elim (λ {X Y} _ → Hom X Y) (λ _ → id) (refl X)  ∎)

  -- A lemma that can be used to prove that ≡→≅ is an equivalence.

  ≡→≅-equivalence-lemma :
    ∀ {X} →
    (≡≃≅ : ∀ {Y} → (X ≡ Y) ≃ (X ≅ Y)) →
    _≃_.to ≡≃≅ (refl X) ¹ ≡ id →
    ∀ {Y} → Is-equivalence (≡→≅ {X = X} {Y = Y})
  ≡→≅-equivalence-lemma {X} ≡≃≅ ≡≃≅-refl {Y} =
    Eq.respects-extensional-equality
      (elim¹ (λ X≡Y → _≃_.to ≡≃≅ X≡Y ≡ ≡→≅ X≡Y)
             (_≃_.to ≡≃≅ (refl X)  ≡⟨ _≃_.from ≡≃≡¹ ≡≃≅-refl ⟩
              id≅                  ≡⟨ sym ≡→≅-refl ⟩∎
              ≡→≅ (refl X)         ∎))
      (_≃_.is-equivalence ≡≃≅)

-- An example: sets and functions. (Defined using extensionality.)

precategory-Set :
  (ℓ : Level) →
  Extensionality ℓ ℓ →
  Precategory (lsuc ℓ) ℓ
precategory-Set ℓ ext = record { precategory =

  -- Objects: sets.
  Set ℓ ,

  -- Morphisms: functions.
  (λ { (A , A-set) (B , B-set) →
       (A → B) , Π-closure ext 2 (λ _ → B-set) }) ,

  -- Identity.
  P.id ,

  -- Composition.
  (λ f g → f ∘ g) ,

  -- Laws.
  refl _ , refl _ , refl _ }

-- Isomorphisms in this category are equivalent to equivalences
-- (assuming extensionality).

≃≃≅-Set :
  (ℓ : Level) (ext : Extensionality ℓ ℓ) →
  let open Precategory (precategory-Set ℓ ext) in
  (X Y : Obj) → (⌞ X ⌟ ≃ ⌞ Y ⌟) ≃ (X ≅ Y)
≃≃≅-Set ℓ ext X Y = Eq.↔⇒≃ record
  { surjection = record
    { logical-equivalence = record
      { to   = λ X≃Y → _≃_.to X≃Y , _≃_.from X≃Y ,
                       apply-ext ext (_≃_.right-inverse-of X≃Y) ,
                       apply-ext ext (_≃_.left-inverse-of  X≃Y)
      ; from = λ X≅Y → Eq.↔⇒≃ record
                 { surjection = record
                   { logical-equivalence = record
                     { to   = proj₁ X≅Y
                     ; from = proj₁ (proj₂ X≅Y)
                     }
                   ; right-inverse-of = λ x →
                       cong (_$ x) $ proj₁ (proj₂ (proj₂ X≅Y))
                   }
                 ; left-inverse-of = λ x →
                     cong (_$ x) $ proj₂ (proj₂ (proj₂ X≅Y))
                 }
      }
    ; right-inverse-of = λ X≅Y →
        _≃_.from (≡≃≡¹ {X = X} {Y = Y}) (refl (proj₁ X≅Y))
    }
  ; left-inverse-of = λ X≃Y →
      Eq.lift-equality ext (refl (_≃_.to X≃Y))
  }
  where open Precategory (precategory-Set ℓ ext) using (≡≃≡¹)

-- Equality characterisation lemma for Precategory′.

equality-characterisation-Precategory′ :
  ∀ {ℓ₁ ℓ₂} {C D : Precategory′ ℓ₁ ℓ₂} →
  Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ lsuc ℓ₂) →
  Univalence ℓ₁ →
  Univalence ℓ₂ →
  let module C = Precategory (record { precategory = C })
      module D = Precategory (record { precategory = D })
  in
  (∃ λ (eqO : C.Obj ≃ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.Hom (_≃_.from eqO X) (_≃_.from eqO Y) ≃
                      D.Hom X Y) →
     (∀ X → _≃_.to (eqH X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        _≃_.to (eqH X Z) (C._∙_ (_≃_.from (eqH Y Z) f)
                                (_≃_.from (eqH X Y) g)) ≡
        f D.∙ g))
    ↔
  C ≡ D
equality-characterisation-Precategory′ {ℓ₁} {ℓ₂} {C} {D}
                                       ext univ₁ univ₂ =
  (∃ λ (eqO : C.Obj ≃ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.Hom (_≃_.from eqO X) (_≃_.from eqO Y) ≃
                      D.Hom X Y) →
     (∀ X → _≃_.to (eqH X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        _≃_.to (eqH X Z) (C._∙_ (_≃_.from (eqH Y Z) f)
                                (_≃_.from (eqH X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ ∃-cong (λ _ → inverse $
                                                                              Σ-cong (∀-cong ext₁₁₂₊ λ _ →
                                                                                      ∀-cong ext₁₂₊  λ _ →
                                                                                      ≡≃≃ univ₂)
                                                                                     (λ _ → F.id)) ⟩
  (∃ λ (eqO : C.Obj ≃ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.Hom (_≃_.from eqO X) (_≃_.from eqO Y) ≡
                      D.Hom X Y) →
     (∀ X → ≡⇒→ (eqH X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        ≡⇒→ (eqH X Z) (C._∙_ (≡⇒← (eqH Y Z) f) (≡⇒← (eqH X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ inverse $ Σ-cong (≡≃≃ univ₁) (λ _ → F.id) ⟩

  (∃ λ (eqO : C.Obj ≡ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.Hom (≡⇒← eqO X) (≡⇒← eqO Y) ≡ D.Hom X Y) →
     (∀ X → ≡⇒→ (eqH X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        ≡⇒→ (eqH X Z) (C._∙_ (≡⇒← (eqH Y Z) f) (≡⇒← (eqH X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ ∃-cong (λ _ → inverse $
                                                                              Σ-cong (∀-cong ext₁₁₂₊ λ _ →
                                                                                      ∀-cong ext₁₂₊  λ _ →
                                                                                      inverse $
                                                                                      ignore-propositional-component $
                                                                                        H-level-propositional ext₂₂ 2)
                                                                                     (λ _ → F.id)) ⟩
  (∃ λ (eqO : C.Obj ≡ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.HOM (≡⇒← eqO X) (≡⇒← eqO Y) ≡ D.HOM X Y) →
     let eqH′ = λ X Y → proj₁ (Σ-≡,≡←≡ (eqH X Y))
     in
     (∀ X → ≡⇒→ (eqH′ X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        ≡⇒→ (eqH′ X Z) (C._∙_ (≡⇒← (eqH′ Y Z) f) (≡⇒← (eqH′ X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ ∃-cong (λ _ → ∃-cong λ _ → ≡⇒↝ _ $
                                                                              cong (λ (eqH′ : ∀ _ _ → _) →
                                                                                      (∀ X → ≡⇒→ (eqH′ X X) C.id ≡ D.id) ×
                                                                                      (∀ X Y Z f g →
                                                                                         ≡⇒→ (eqH′ X Z)
                                                                                           (C._∙_ (≡⇒← (eqH′ Y Z) f) (≡⇒← (eqH′ X Y) g)) ≡ f D.∙ g))
                                                                                   (apply-ext ext₁₁₂₊ λ _ → apply-ext ext₁₂₊ λ _ →
                                                                                      proj₁-Σ-≡,≡←≡ _)) ⟩
  (∃ λ (eqO : C.Obj ≡ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.HOM (≡⇒← eqO X) (≡⇒← eqO Y) ≡ D.HOM X Y) →
     let eqH′ = λ X Y → cong proj₁ (eqH X Y)
     in
     (∀ X → ≡⇒→ (eqH′ X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        ≡⇒→ (eqH′ X Z) (C._∙_ (≡⇒← (eqH′ Y Z) f) (≡⇒← (eqH′ X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ ∃-cong (λ _ → inverse $
                                                                               Σ-cong (∀-cong ext₁₁₂₊ λ _ →
                                                                                       inverse $ Eq.extensionality-isomorphism ext₁₂₊)
                                                                                      (λ _ → F.id)) ⟩
  (∃ λ (eqO : C.Obj ≡ D.Obj) →
   ∃ λ (eqH : ∀ X → (λ Y → C.HOM (≡⇒← eqO X) (≡⇒← eqO Y)) ≡ D.HOM X) →
     let eqH′ = λ X Y → cong proj₁ (ext⁻¹ (eqH X) Y)
     in
     (∀ X → ≡⇒→ (eqH′ X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        ≡⇒→ (eqH′ X Z) (C._∙_ (≡⇒← (eqH′ Y Z) f) (≡⇒← (eqH′ X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ ∃-cong (λ _ → inverse $
                                                                               Σ-cong (inverse $ Eq.extensionality-isomorphism ext₁₁₂₊)
                                                                                      (λ _ → F.id)) ⟩
  (∃ λ (eqO : C.Obj ≡ D.Obj) →
   ∃ λ (eqH : (λ X Y → C.HOM (≡⇒← eqO X) (≡⇒← eqO Y)) ≡ D.HOM) →
     let eqH′ = λ X Y → cong proj₁ (ext⁻¹ (ext⁻¹ eqH X) Y)
     in
     (∀ X → ≡⇒→ (eqH′ X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        ≡⇒→ (eqH′ X Z) (C._∙_ (≡⇒← (eqH′ Y Z) f) (≡⇒← (eqH′ X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ ∃-cong (λ eqO → inverse $
                                                                              Σ-cong (inverse $ ≡⇒↝ equivalence (HOM-lemma eqO))
                                                                                     (λ _ → F.id)) ⟩
  (∃ λ (eqO : C.Obj ≡ D.Obj) →
   ∃ λ (eqH : subst (λ Obj → Obj → Obj → Set _) eqO C.HOM ≡ D.HOM) →
     let eqH′ = λ X Y →
                  cong proj₁
                    (ext⁻¹ (ext⁻¹ (≡⇒← (HOM-lemma eqO) eqH) X) Y)
     in
     (∀ X → ≡⇒→ (eqH′ X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        ≡⇒→ (eqH′ X Z) (C._∙_ (≡⇒← (eqH′ Y Z) f) (≡⇒← (eqH′ X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ ∃-cong (λ eqO → ∃-cong λ eqH → ≡⇒↝ _ $
                                                                              cong (λ (eqH′ : ∀ _ _ → _) →
                                                                                      (∀ X → ≡⇒→ (eqH′ X X) C.id ≡ D.id) ×
                                                                                      (∀ X Y Z f g →
                                                                                         ≡⇒→ (eqH′ X Z)
                                                                                           (C._∙_ (≡⇒← (eqH′ Y Z) f) (≡⇒← (eqH′ X Y) g)) ≡ f D.∙ g))
                                                                                   (apply-ext ext₁₁₂₊ λ X → apply-ext ext₁₂₊ λ Y →
      cong proj₁ (ext⁻¹ (ext⁻¹ (≡⇒← (HOM-lemma eqO) eqH) X) Y)                        ≡⟨⟩
      cong proj₁ (cong (_$ Y) (cong (_$ X) (≡⇒← (HOM-lemma eqO) eqH)))                ≡⟨ cong (cong _) $ cong-∘ _ _ _ ⟩
      cong proj₁ (cong (λ f → f X Y) (≡⇒← (HOM-lemma eqO) eqH))                       ≡⟨ cong-∘ _ _ _ ⟩∎
      cong (λ F → ⌞ F X Y ⌟) (≡⇒← (HOM-lemma eqO) eqH)                                ∎)) ⟩

  (∃ λ (eqO : C.Obj ≡ D.Obj) →
   ∃ λ (eqH : subst (λ Obj → Obj → Obj → Set _) eqO C.HOM ≡ D.HOM) →
     let eqH′ = λ X Y → cong (λ F → ⌞ F X Y ⌟) (≡⇒← (HOM-lemma eqO) eqH)
     in
     (∀ X → ≡⇒→ (eqH′ X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        ≡⇒→ (eqH′ X Z) (C._∙_ (≡⇒← (eqH′ Y Z) f) (≡⇒← (eqH′ X Y) g)) ≡
        f D.∙ g))                                                        ↝⟨ ∃-cong (λ eqO → ∃-cong λ eqH →
                                                                              (∀-cong ext₁₂ λ _ →
                                                                                 ≡⇒↝ _ $ cong (_≡ _) P-lemma)
                                                                                ×-cong
                                                                              (∀-cong ext₁₁₂ λ X →
                                                                               ∀-cong ext₁₁₂ λ Y →
                                                                               ∀-cong ext₁₂  λ Z →
                                                                               ∀-cong ext₂₂  λ f →
                                                                               ∀-cong ext₂₂  λ g →
                                                                                 ≡⇒↝ _ $ cong (_≡ _) Q-lemma)) ⟩
  (∃ λ (eqO : C.Obj ≡ D.Obj) →
   ∃ λ (eqH : subst (λ Obj → Obj → Obj → Set _) eqO C.HOM ≡ D.HOM) →
     (∀ X → subst₂ (uncurry P) eqO eqH C.id {X = X} ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        subst₂ (uncurry Q) eqO eqH C._∙_ f g ≡ f D.∙ g))                 ↝⟨ Σ-assoc ⟩

  (∃ λ (eq : ∃ λ (eqO : C.Obj ≡ D.Obj) →
               subst (λ Obj → Obj → Obj → Set _) eqO C.HOM ≡ D.HOM) →
     (∀ X → subst (uncurry P) (uncurry Σ-≡,≡→≡ eq) C.id {X = X} ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        subst (uncurry Q) (uncurry Σ-≡,≡→≡ eq) C._∙_ f g ≡ f D.∙ g))     ↝⟨ Σ-cong Bijection.Σ-≡,≡↔≡ (λ _ → F.id) ⟩

  (∃ λ (eq : (C.Obj , C.HOM) ≡ (D.Obj , D.HOM)) →
     (∀ X → subst (uncurry P) eq C.id {X = X} ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        subst (uncurry Q) eq C._∙_ f g ≡ f D.∙ g))                       ↔⟨ ∃-cong (λ _ → ∃-cong λ _ → ∀-cong ext₁₁₂ λ _ →
                                                                              ∀-cong ext₁₁₂ λ _ → ∀-cong ext₁₂ λ _ →
                                                                                ∀-cong ext₂₂ λ _ →
                                                                                  Eq.extensionality-isomorphism ext₂₂) ⟩
  (∃ λ (eq : (C.Obj , C.HOM) ≡ (D.Obj , D.HOM)) →
     (∀ X → subst (uncurry P) eq C.id {X = X} ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) →
        subst (uncurry Q) eq C._∙_ {X = X} f ≡ D._∙_ f))                 ↔⟨ ∃-cong (λ _ → ∃-cong λ _ → ∀-cong ext₁₁₂ λ _ →
                                                                              ∀-cong ext₁₁₂ λ _ → ∀-cong ext₁₂ λ _ →
                                                                                Eq.extensionality-isomorphism ext₂₂) ⟩
  (∃ λ (eq : (C.Obj , C.HOM) ≡ (D.Obj , D.HOM)) →
     (∀ X → subst (uncurry P) eq C.id {X = X} ≡ D.id)
       ×
     (∀ X Y Z →
        subst (uncurry Q) eq C._∙_ {X = X} {Y = Y} {Z = Z} ≡ D._∙_))     ↝⟨ ∃-cong (λ _ → ∃-cong λ _ →
                                                                              ∀-cong ext₁₁₂ λ _ → ∀-cong ext₁₁₂ λ _ →
                                                                                implicit-extensionality-isomorphism ext₁₂) ⟩
  (∃ λ (eq : (C.Obj , C.HOM) ≡ (D.Obj , D.HOM)) →
     (∀ X → subst (uncurry P) eq C.id {X = X} ≡ D.id)
       ×
     (∀ X Y →
        (λ {_} → subst (uncurry Q) eq C._∙_ {X = X} {Y = Y}) ≡ D._∙_))   ↝⟨ ∃-cong (λ _ → ∃-cong λ _ → ∀-cong ext₁₁₂ λ _ →
                                                                              implicit-extensionality-isomorphism ext₁₁₂) ⟩
  (∃ λ (eq : (C.Obj , C.HOM) ≡ (D.Obj , D.HOM)) →
     (∀ X → subst (uncurry P) eq C.id {X = X} ≡ D.id)
       ×
     (∀ X → (λ {_ _} → subst (uncurry Q) eq C._∙_ {X = X}) ≡ D._∙_))     ↝⟨ ∃-cong (λ _ →
                                                                              implicit-extensionality-isomorphism ext₁₂
                                                                                ×-cong
                                                                              implicit-extensionality-isomorphism ext₁₁₂) ⟩
  (∃ λ (eq : (C.Obj , C.HOM) ≡ (D.Obj , D.HOM)) →
     (λ {_} → subst (uncurry P) eq (λ {_} → C.id)) ≡
     (λ {_} → D.id)
       ×
     (λ {_ _ _} → subst (uncurry Q) eq (λ {_ _ _} → C._∙_)) ≡
     (λ {_ _ _} → D._∙_))                                                ↝⟨ ∃-cong (λ _ → ≡×≡↔≡) ⟩

  (∃ λ (eq : (C.Obj , C.HOM) ≡ (D.Obj , D.HOM)) →
     ( (λ {_}     → subst (uncurry P) eq (λ {_}     → C.id))
     , (λ {_ _ _} → subst (uncurry Q) eq (λ {_ _ _} → C._∙_))
     ) ≡
     ((λ {_} → D.id) , λ {_ _ _} → D._∙_))                               ↝⟨ ∃-cong (λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $ push-subst-, _ _) ⟩

  (∃ λ (eq : (C.Obj , C.HOM) ≡ (D.Obj , D.HOM)) →
     subst _ eq ((λ {_} → C.id) , λ {_ _ _} → C._∙_) ≡
     ((λ {_} → D.id) , λ {_ _ _} → D._∙_))                               ↝⟨ Bijection.Σ-≡,≡↔≡ ⟩

  ((C.Obj , C.HOM) , (λ {_} → C.id) , λ {_ _ _} → C._∙_) ≡
  ((D.Obj , D.HOM) , (λ {_} → D.id) , λ {_ _ _} → D._∙_)                 ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ Σ-assoc) ⟩

  (C.Obj , C.HOM , (λ {_} → C.id) , λ {_ _ _} → C._∙_) ≡
  (D.Obj , D.HOM , (λ {_} → D.id) , λ {_ _ _} → D._∙_)                   ↝⟨ ignore-propositional-component (
                                                                              ×-closure 1 (implicit-Π-closure ext₁₁₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₁₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₂₂ 1 λ _ →
                                                                                           D.Hom-is-set) $
                                                                              ×-closure 1 (implicit-Π-closure ext₁₁₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₁₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₂₂ 1 λ _ →
                                                                                           D.Hom-is-set)
                                                                                          (implicit-Π-closure ext₁₁₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₁₁₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₁₁₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₁₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₂₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₂₂ 1 λ _ →
                                                                                           implicit-Π-closure ext₂₂ 1 λ _ →
                                                                                           D.Hom-is-set)) ⟩
  ((C.Obj , C.HOM , (λ {_} → C.id) , λ {_ _ _} → C._∙_) , _) ≡
  ((D.Obj , D.HOM , (λ {_} → D.id) , λ {_ _ _} → D._∙_) , _)             ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ rearrange) ⟩□

  C ≡ D                                                                  □
  where
  module C = Precategory (record { precategory = C })
  module D = Precategory (record { precategory = D })

  ext₁₁₂₊ : Extensionality ℓ₁ (ℓ₁ ⊔ lsuc ℓ₂)
  ext₁₁₂₊ = lower-extensionality ℓ₂ lzero ext

  ext₁₁₂ : Extensionality ℓ₁ (ℓ₁ ⊔ ℓ₂)
  ext₁₁₂ = lower-extensionality ℓ₂ (lsuc ℓ₂) ext

  ext₁₂₊ : Extensionality ℓ₁ (lsuc ℓ₂)
  ext₁₂₊ = lower-extensionality ℓ₂ ℓ₁ ext

  ext₁₂ : Extensionality ℓ₁ ℓ₂
  ext₁₂ = lower-extensionality ℓ₂ _ ext

  ext₂₂ : Extensionality ℓ₂ ℓ₂
  ext₂₂ = lower-extensionality ℓ₁ _ ext

  rearrange :
    ∀ {a b c d e}
      {A : Type a} {B : A → Type b} {C : (a : A) → B a → Type c}
      {D : (a : A) (b : B a) → C a b → Type d}
      {E : (a : A) (b : B a) (c : C a b) → D a b c → Type e} →
    (∃ λ (a : A) → ∃ λ (b : B a) → ∃ λ (c : C a b) → ∃ λ (d : D a b c) →
       E a b c d)
      ↔
    (∃ λ (p : ∃ λ (a : A) → ∃ λ (b : B a) → ∃ λ (c : C a b) → D a b c) →
       E (proj₁ p) (proj₁ (proj₂ p)) (proj₁ (proj₂ (proj₂ p)))
         (proj₂ (proj₂ (proj₂ p))))
  rearrange {A} {B} {C} {D} {E} =
    (∃ λ (a : A) → ∃ λ (b : B a) → ∃ λ (c : C a b) → ∃ λ (d : D a b c) →
       E a b c d)                                                         ↝⟨ ∃-cong (λ _ → ∃-cong λ _ → Σ-assoc) ⟩

    (∃ λ (a : A) → ∃ λ (b : B a) → ∃ λ (p : ∃ λ (c : C a b) → D a b c) →
       E a b (proj₁ p) (proj₂ p))                                         ↝⟨ ∃-cong (λ _ → Σ-assoc) ⟩

    (∃ λ (a : A) → ∃ λ (p : ∃ λ (b : B a) → ∃ λ (c : C a b) → D a b c) →
       E a (proj₁ p) (proj₁ (proj₂ p)) (proj₂ (proj₂ p)))                 ↝⟨ Σ-assoc ⟩□

    (∃ λ (p : ∃ λ (a : A) → ∃ λ (b : B a) → ∃ λ (c : C a b) → D a b c) →
       E (proj₁ p) (proj₁ (proj₂ p)) (proj₁ (proj₂ (proj₂ p)))
         (proj₂ (proj₂ (proj₂ p))))                                       □

  ≡⇒←-subst :
    {C D : Type ℓ₁} {H : C → C → Set ℓ₂}
    (eqO : C ≡ D) →
    (λ X Y → H (≡⇒← eqO X) (≡⇒← eqO Y))
      ≡
    subst (λ Obj → Obj → Obj → Set _) eqO H
  ≡⇒←-subst {C} {H} eqO =
    elim¹ (λ eqO → (λ X Y → H (≡⇒← eqO X) (≡⇒← eqO Y)) ≡
                   subst (λ Obj → Obj → Obj → Set _) eqO H)
          ((λ X Y → H (≡⇒← (refl C) X) (≡⇒← (refl C) Y))  ≡⟨ cong (λ f X Y → H (f X) (f Y)) ≡⇒←-refl ⟩
           H                                              ≡⟨ sym $ subst-refl _ _ ⟩∎
           subst (λ Obj → Obj → Obj → Set _) (refl C) H   ∎)
          eqO

  ≡⇒←-subst-refl : {C : Type ℓ₁} {H : C → C → Set ℓ₂} → _
  ≡⇒←-subst-refl {C} {H} =
    ≡⇒←-subst {H = H} (refl C)                       ≡⟨ elim¹-refl _ _ ⟩∎

    trans (cong (λ f X Y → H (f X) (f Y)) ≡⇒←-refl)
          (sym $ subst-refl _ _)                     ∎

  HOM-lemma :
    (eqO : C.Obj ≡ D.Obj) →
    ((λ X Y → C.HOM (≡⇒← eqO X) (≡⇒← eqO Y)) ≡ D.HOM)
      ≡
    (subst (λ Obj → Obj → Obj → Set _) eqO C.HOM ≡ D.HOM)
  HOM-lemma eqO = cong (_≡ _) (≡⇒←-subst eqO)

  ≡⇒→-lemma :
    ∀ {eqO eqH X Y} {f : C.Hom (≡⇒← eqO X) (≡⇒← eqO Y)} → _
  ≡⇒→-lemma {eqO} {eqH} {X} {Y} {f} =
    ≡⇒→ (cong (λ H → ⌞ H X Y ⌟) (≡⇒← (HOM-lemma eqO) eqH)) f  ≡⟨ sym $ subst-in-terms-of-≡⇒↝ equivalence
                                                                         (≡⇒← (HOM-lemma eqO) eqH) (λ H → ⌞ H X Y ⌟) _ ⟩
    subst (λ H → ⌞ H X Y ⌟) (≡⇒← (HOM-lemma eqO) eqH) f       ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) eq _) $ sym $
                                                                   subst-in-terms-of-inverse∘≡⇒↝ equivalence (≡⇒←-subst eqO) (_≡ _) _ ⟩
    subst (λ H → ⌞ H X Y ⌟)
      (subst (_≡ _) (sym $ ≡⇒←-subst eqO) eqH) f              ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) eq _) $
                                                                   subst-trans (≡⇒←-subst eqO) ⟩
    subst (λ H → ⌞ H X Y ⌟) (trans (≡⇒←-subst eqO) eqH) f     ≡⟨ sym $ subst-subst _ _ _ _ ⟩∎

    subst (λ H → ⌞ H X Y ⌟) eqH
      (subst (λ H → ⌞ H X Y ⌟) (≡⇒←-subst eqO) f)             ∎

  ≡⇒←-lemma : ∀ {eqO eqH X Y} {f : D.Hom X Y} → _
  ≡⇒←-lemma {eqO} {eqH} {X} {Y} {f} =
    ≡⇒← (cong (λ H → ⌞ H X Y ⌟) (≡⇒← (HOM-lemma eqO) eqH)) f           ≡⟨ sym $ subst-in-terms-of-inverse∘≡⇒↝ equivalence
                                                                                  (≡⇒← (HOM-lemma eqO) eqH) (λ H → ⌞ H X Y ⌟) _ ⟩
    subst (λ H → ⌞ H X Y ⌟) (sym $ ≡⇒← (HOM-lemma eqO) eqH) f          ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) (sym eq) _) $ sym $
                                                                            subst-in-terms-of-inverse∘≡⇒↝ equivalence (≡⇒←-subst eqO) (_≡ _) _ ⟩
    subst (λ H → ⌞ H X Y ⌟)
      (sym $ subst (_≡ _) (sym $ ≡⇒←-subst eqO) eqH) f                 ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) (sym eq) _) $
                                                                            subst-trans (≡⇒←-subst eqO) ⟩
    subst (λ H → ⌞ H X Y ⌟) (sym $ trans (≡⇒←-subst eqO) eqH) f        ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) eq _) $
                                                                            sym-trans (≡⇒←-subst eqO) eqH ⟩
    subst (λ H → ⌞ H X Y ⌟) (trans (sym eqH) (sym $ ≡⇒←-subst eqO)) f  ≡⟨ sym $ subst-subst _ _ _ _ ⟩∎

    subst (λ H → ⌞ H X Y ⌟) (sym $ ≡⇒←-subst eqO)
      (subst (λ H → ⌞ H X Y ⌟) (sym eqH) f)                            ∎

  expand-≡⇒←-subst :
    ∀ {C : Type ℓ₁} {X Y}
      {F G : C → C → Set ℓ₂}
      {eqH : subst (λ Obj → Obj → Obj → Set ℓ₂) (refl C) F ≡ G}
      {f : ⌞ F (≡⇒← (refl C) X) (≡⇒← (refl C) Y) ⌟} →
    _
  expand-≡⇒←-subst {C} {X} {Y} {F} {eqH} {f} =
    subst (λ H → ⌞ H X Y ⌟) eqH
      (subst (λ H → ⌞ H X Y ⌟) (≡⇒←-subst (refl C)) f)      ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) eqH $ subst (λ H → ⌞ H X Y ⌟) eq f)
                                                                 ≡⇒←-subst-refl ⟩
    subst (λ H → ⌞ H X Y ⌟) eqH
      (subst (λ H → ⌞ H X Y ⌟)
         (trans (cong (λ f X Y → F (f X) (f Y)) ≡⇒←-refl)
                (sym $ subst-refl _ _))
         f)                                                 ≡⟨ cong (subst (λ H → ⌞ H X Y ⌟) eqH) $ sym $
                                                                 subst-subst _ _ _ _ ⟩
    subst (λ H → ⌞ H X Y ⌟) eqH
      (subst (λ H → ⌞ H X Y ⌟)
         (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
         (subst (λ H → ⌞ H X Y ⌟)
                (cong (λ f X Y → F (f X) (f Y)) ≡⇒←-refl)
                f))                                         ≡⟨ cong (λ f → subst (λ H → ⌞ H X Y ⌟) eqH $
                                                                             subst (λ H → ⌞ H X Y ⌟)
                                                                               (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _) f) $ sym $
                                                                 subst-∘ (λ H → ⌞ H X Y ⌟) (λ f X Y → F (f X) (f Y)) ≡⇒←-refl ⟩∎
    subst (λ H → ⌞ H X Y ⌟) eqH
      (subst (λ H → ⌞ H X Y ⌟)
         (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
         (subst (λ f → ⌞ F (f X) (f Y) ⌟) ≡⇒←-refl f))      ∎

  expand-sym-≡⇒←-subst :
    ∀ {C : Type ℓ₁} {X Y}
      {F G : C → C → Set ℓ₂}
      {eqH : subst (λ Obj → Obj → Obj → Set ℓ₂) (refl C) F ≡ G}
      {f : ⌞ G X Y ⌟} →
    _
  expand-sym-≡⇒←-subst {C} {X} {Y} {F} {eqH} {f} =
     subst (λ H → ⌞ H X Y ⌟) (sym $ ≡⇒←-subst (refl C))
       (subst (λ H → ⌞ H X Y ⌟) (sym eqH) f)                   ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) (sym eq) $
                                                                                 subst (λ H → ⌞ H X Y ⌟) (sym eqH) f)
                                                                    ≡⇒←-subst-refl ⟩
     subst (λ H → ⌞ H X Y ⌟)
       (sym $ trans (cong (λ f X Y → F (f X) (f Y)) ≡⇒←-refl)
                    (sym $ subst-refl _ _))
       (subst (λ H → ⌞ H X Y ⌟) (sym eqH) f)                   ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) eq $
                                                                                 subst (λ H → ⌞ H X Y ⌟) (sym eqH) f) $
                                                                    sym-trans (cong (λ f X Y → F (f X) (f Y)) ≡⇒←-refl) _ ⟩
     subst (λ H → ⌞ H X Y ⌟)
       (trans (sym $ sym $
                 subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
              (sym $ cong (λ f X Y → F (f X) (f Y))
                          ≡⇒←-refl))
       (subst (λ H → ⌞ H X Y ⌟) (sym eqH) f)                   ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟)
                                                                                 (trans eq (sym $ cong (λ f X Y → F (f X) (f Y)) ≡⇒←-refl)) $
                                                                                 subst (λ H → ⌞ H X Y ⌟) (sym eqH) f) $
                                                                    sym-sym _ ⟩
     subst (λ H → ⌞ H X Y ⌟)
       (trans (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
              (sym $ cong (λ f X Y → F (f X) (f Y))
                          ≡⇒←-refl))
       (subst (λ H → ⌞ H X Y ⌟) (sym eqH) f)                   ≡⟨ sym $ subst-subst _ _ _ _ ⟩

     subst (λ H → ⌞ H X Y ⌟)
       (sym $ cong (λ f X Y → F (f X) (f Y)) ≡⇒←-refl)
       (subst (λ H → ⌞ H X Y ⌟)
          (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
          (subst (λ H → ⌞ H X Y ⌟) (sym eqH) f))               ≡⟨ cong (λ eq → subst (λ H → ⌞ H X Y ⌟) eq $
                                                                                 subst (λ H → ⌞ H X Y ⌟)
                                                                                       (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _) $
                                                                                   subst (λ H → ⌞ H X Y ⌟) (sym eqH) f) $ sym $
                                                                    cong-sym (λ f X Y → F (f X) (f Y)) ≡⇒←-refl ⟩
     subst (λ H → ⌞ H X Y ⌟)
       (cong (λ f X Y → F (f X) (f Y)) $ sym ≡⇒←-refl)
       (subst (λ H → ⌞ H X Y ⌟)
          (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
          (subst (λ H → ⌞ H X Y ⌟) (sym eqH) f))               ≡⟨ sym $ subst-∘ _ _ _ ⟩∎

     subst (λ f → ⌞ F (f X) (f Y) ⌟) (sym ≡⇒←-refl)
       (subst (λ H → ⌞ H X Y ⌟)
          (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
          (subst (λ H → ⌞ H X Y ⌟) (sym eqH) f))               ∎

  subst-Σ-≡,≡→≡ :
    ∀ {C : Type ℓ₁}
      {F G : C → C → Set ℓ₂}
      {eqH : subst (λ Obj → Obj → Obj → Set ℓ₂) (refl C) F ≡ G}
      {P : (Obj : Type ℓ₁) (HOM : Obj → Obj → Set ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)} →
    _
  subst-Σ-≡,≡→≡ {C} {F} {eqH} {P} =
    subst (P C) eqH ∘
    subst (P C) (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) F)       ≡⟨ apply-ext (lower-extensionality lzero (lsuc ℓ₂) ext) (λ _ →
                                                                             subst-subst (P C) _ _ _) ⟩
    subst (P C) (trans (sym $ subst-refl _ _) eqH)                      ≡⟨ apply-ext (lower-extensionality lzero (lsuc ℓ₂) ext) (λ _ →
                                                                             subst-∘ (uncurry P) (C ,_) _) ⟩
    subst (uncurry P) (cong (C ,_) (trans (sym $ subst-refl _ _) eqH))  ≡⟨ cong (subst (uncurry P)) $ sym $ Σ-≡,≡→≡-reflˡ eqH ⟩∎

    subst (uncurry P) (Σ-≡,≡→≡ (refl C) eqH)                            ∎

  P = λ Obj (HOM : Obj → Obj → Set _) →
        ∀ {X} → ⌞ HOM X X ⌟

  opaque

    P-lemma :
      ∀ {eqO eqH X} →
      ≡⇒→ (cong (λ H → ⌞ H X X ⌟) (≡⇒← (HOM-lemma eqO) eqH)) C.id ≡
      subst₂ (uncurry P) eqO eqH C.id {X = X}
    P-lemma {eqO} {eqH} {X} =
      ≡⇒→ (cong (λ H → ⌞ H X X ⌟) (≡⇒← (HOM-lemma eqO) eqH)) C.id     ≡⟨ ≡⇒→-lemma ⟩

      subst (λ H → ⌞ H X X ⌟) eqH
        (subst (λ H → ⌞ H X X ⌟) (≡⇒←-subst eqO)
               (C.id {X = ≡⇒← eqO X}))                                ≡⟨ elim
                                                                           (λ eqO →
                                                                                    ∀ {X F G}
                                                                                    (eqH : subst (λ Obj → Obj → Obj → Set ℓ₂) eqO F ≡ G)
                                                                                    (id : ∀ X → ⌞ F X X ⌟) →
                                                                              subst (λ H → ⌞ H X X ⌟) eqH
                                                                                (subst (λ H → ⌞ H X X ⌟) (≡⇒←-subst eqO) (id (≡⇒← eqO X)))
                                                                                ≡
                                                                              subst (uncurry P) (Σ-≡,≡→≡ eqO eqH) (λ {X} → id X))
                                                                           (λ C {X F G} eqH id →
          subst (λ H → ⌞ H X X ⌟) eqH
            (subst (λ H → ⌞ H X X ⌟) (≡⇒←-subst (refl C))
                   (id (≡⇒← (refl C) X)))                                     ≡⟨ expand-≡⇒←-subst ⟩

          subst (λ H → ⌞ H X X ⌟) eqH
            (subst
               (λ H → ⌞ H X X ⌟)
               (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
               (subst (λ f → ⌞ F (f X) (f X) ⌟)
                      ≡⇒←-refl
                      (id (≡⇒← (refl C) X))))                                 ≡⟨ cong (λ f → subst (λ H → ⌞ H X X ⌟) eqH
                                                                                               (subst
                                                                                                  (λ H → ⌞ H X X ⌟)
                                                                                                  (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                                                                                                  f)) $
                                                                                   dcong (λ f → id (f X)) ≡⇒←-refl ⟩
          subst (λ H → ⌞ H X X ⌟) eqH
            (subst (λ H → ⌞ H X X ⌟)
                   (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) F)
                   (id X))                                                    ≡⟨ cong (subst (λ H → ⌞ H X X ⌟) eqH) $
                                                                                   push-subst-implicit-application _ _ ⟩
          subst (λ H → ⌞ H X X ⌟) eqH
            (subst (P C)
                   (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) F)
                   (λ {X} → id X) {X = X})                                    ≡⟨ push-subst-implicit-application _ _ ⟩

          subst (P C) eqH
            (subst (P C)
                   (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) F)
                   (λ {X} → id X)) {X = X}                                    ≡⟨ cong (λ (f : P C F → P C G) → f _)
                                                                                   subst-Σ-≡,≡→≡ ⟩∎
          subst (uncurry P) (Σ-≡,≡→≡ (refl C) eqH) (λ {X} → id X)             ∎)
                                                                           eqO eqH (λ _ → C.id) ⟩
      subst (uncurry P) (Σ-≡,≡→≡ eqO eqH)
            (λ {X} → C.id {X = X}) {X = X}                            ≡⟨⟩

      subst₂ (uncurry P) eqO eqH C.id                                 ∎

  Q = λ Obj (HOM : Obj → Obj → Set _) →
        ∀ {X Y Z} → ⌞ HOM Y Z ⌟ → ⌞ HOM X Y ⌟ → ⌞ HOM X Z ⌟

  push-Q :
    {C : Type ℓ₁} {X Y Z : C} {F G : C → C → Set ℓ₂}
    {c : (X Y Z : C) → ⌞ F Y Z ⌟ → ⌞ F X Y ⌟ → ⌞ F X Z ⌟}
    {F≡G : F ≡ G} {f : ⌞ G Y Z ⌟} {g : ⌞ G X Y ⌟} →
    subst (λ H → ⌞ H X Z ⌟) F≡G
      (c X Y Z
         (subst (λ H → ⌞ H Y Z ⌟) (sym F≡G) f)
         (subst (λ H → ⌞ H X Y ⌟) (sym F≡G) g)) ≡
    subst (Q C) F≡G (c _ _ _) f g
  push-Q {C} {X} {Y} {Z} {c} {F≡G} {f} {g} =
    subst (λ H → ⌞ H X Z ⌟) F≡G
      (c X Y Z (subst (λ H → ⌞ H Y Z ⌟) (sym F≡G) f)
               (subst (λ H → ⌞ H X Y ⌟) (sym F≡G) g))          ≡⟨ sym subst-→ ⟩

    subst (λ H → ⌞ H X Y ⌟ → ⌞ H X Z ⌟) F≡G
      (c X Y Z (subst (λ H → ⌞ H Y Z ⌟) (sym F≡G) f)) g        ≡⟨ cong (_$ g) $ sym subst-→ ⟩

    subst (λ H → ⌞ H Y Z ⌟ → ⌞ H X Y ⌟ → ⌞ H X Z ⌟) F≡G
      (c X Y Z) f g                                            ≡⟨ cong (λ h → h f g) $
                                                                    push-subst-implicit-application _
                                                                      (λ H Z → ⌞ H Y Z ⌟ → ⌞ H X Y ⌟ → ⌞ H X Z ⌟) ⟩
    subst (λ H → ∀ {Z} → ⌞ H Y Z ⌟ → ⌞ H X Y ⌟ → ⌞ H X Z ⌟)
      F≡G (c X Y _) f g                                        ≡⟨ cong (λ h → h {Z = Z} f g) $
                                                                    push-subst-implicit-application F≡G
                                                                      (λ H Y → ∀ {Z} → ⌞ H Y Z ⌟ → ⌞ H X Y ⌟ → ⌞ H X Z ⌟) ⟩
    subst (λ H → ∀ {Y Z} → ⌞ H Y Z ⌟ → ⌞ H X Y ⌟ → ⌞ H X Z ⌟)
      F≡G (c X _ _) f g                                        ≡⟨ cong (λ h → h {Y = Y} {Z = Z} f g) $
                                                                    push-subst-implicit-application F≡G
                                                                      (λ H X → ∀ {Y Z} → ⌞ H Y Z ⌟ → ⌞ H X Y ⌟ → ⌞ H X Z ⌟) ⟩∎
    subst (Q C) F≡G (c _ _ _) f g                              ∎

  opaque

    Q-lemma :
      ∀ {eqO eqH X Y Z f g} →
      let eqH′ = λ X Y →
                   cong (λ H → ⌞ H X Y ⌟) (≡⇒← (HOM-lemma eqO) eqH)
      in
      ≡⇒→ (eqH′ X Z) (≡⇒← (eqH′ Y Z) f C.∙ ≡⇒← (eqH′ X Y) g) ≡
      subst₂ (uncurry Q) eqO eqH C._∙_ f g
    Q-lemma {eqO} {eqH} {X} {Y} {Z} {f} {g} =

      let eqH′ = λ X Y →
                   cong (λ F → ⌞ F X Y ⌟) (≡⇒← (HOM-lemma eqO) eqH)
      in

      ≡⇒→ (eqH′ X Z) (≡⇒← (eqH′ Y Z) f C.∙ ≡⇒← (eqH′ X Y) g)              ≡⟨ cong₂ (λ f g → ≡⇒→ (eqH′ X Z) (f C.∙ g))
                                                                               ≡⇒←-lemma
                                                                               ≡⇒←-lemma ⟩
      ≡⇒→ (eqH′ X Z)
        (subst (λ H → ⌞ H Y Z ⌟) (sym $ ≡⇒←-subst eqO)
           (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)
           C.∙
         subst (λ H → ⌞ H X Y ⌟) (sym $ ≡⇒←-subst eqO)
           (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))                         ≡⟨ ≡⇒→-lemma ⟩

      subst (λ H → ⌞ H X Z ⌟) eqH
        (subst (λ H → ⌞ H X Z ⌟) (≡⇒←-subst eqO)
           (subst (λ H → ⌞ H Y Z ⌟) (sym $ ≡⇒←-subst eqO)
              (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)
              C.∙
            subst (λ H → ⌞ H X Y ⌟) (sym $ ≡⇒←-subst eqO)
              (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g)))                     ≡⟨ elim
                                                                               (λ eqO → ∀ {X Y Z F G}
                                                                                        (eqH : subst (λ Obj → Obj → Obj → Set ℓ₂) eqO F ≡ G)
                                                                                        (comp : ∀ X Y Z →
                                                                                                ⌞ F Y Z ⌟ → ⌞ F X Y ⌟ → ⌞ F X Z ⌟)
                                                                                        (f : ⌞ G Y Z ⌟) (g : ⌞ G X Y ⌟) →
                                                                                  subst (λ H → ⌞ H X Z ⌟) eqH
                                                                                    (subst (λ H → ⌞ H X Z ⌟) (≡⇒←-subst eqO)
                                                                                       (comp (≡⇒← eqO X) (≡⇒← eqO Y) (≡⇒← eqO Z)
                                                                                          (subst (λ H → ⌞ H Y Z ⌟) (sym $ ≡⇒←-subst eqO)
                                                                                             (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f))
                                                                                          (subst (λ H → ⌞ H X Y ⌟) (sym $ ≡⇒←-subst eqO)
                                                                                             (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))))
                                                                                    ≡
                                                                                  subst (uncurry Q) (Σ-≡,≡→≡ eqO eqH) (λ {X Y Z} → comp X Y Z) f g)
                                                                               (λ C {X Y Z F G} eqH comp f g →
          subst (λ H → ⌞ H X Z ⌟) eqH
            (subst (λ H → ⌞ H X Z ⌟) (≡⇒←-subst (refl C))
               (comp (≡⇒← (refl C) X) (≡⇒← (refl C) Y) (≡⇒← (refl C) Z)
                  (subst (λ H → ⌞ H Y Z ⌟) (sym $ ≡⇒←-subst (refl C))
                     (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f))
                  (subst (λ H → ⌞ H X Y ⌟) (sym $ ≡⇒←-subst (refl C))
                     (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))))                     ≡⟨ cong₂ (λ f g →
                                                                                              subst (λ H → ⌞ H X Z ⌟) eqH $
                                                                                                subst (λ H → ⌞ H X Z ⌟) (≡⇒←-subst (refl C)) $
                                                                                                  comp (≡⇒← (refl C) X) (≡⇒← (refl C) Y)
                                                                                                       (≡⇒← (refl C) Z) f g)
                                                                                       expand-sym-≡⇒←-subst
                                                                                       expand-sym-≡⇒←-subst ⟩
          subst (λ H → ⌞ H X Z ⌟) eqH
            (subst (λ H → ⌞ H X Z ⌟) (≡⇒←-subst (refl C))
               (comp (≡⇒← (refl C) X) (≡⇒← (refl C) Y) (≡⇒← (refl C) Z)
                  (subst (λ f → ⌞ F (f Y) (f Z) ⌟) (sym ≡⇒←-refl)
                     (subst (λ H → ⌞ H Y Z ⌟)
                        (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                        (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)))
                  (subst (λ f → ⌞ F (f X) (f Y) ⌟) (sym ≡⇒←-refl)
                     (subst (λ H → ⌞ H X Y ⌟)
                        (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                        (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g)))))                 ≡⟨ expand-≡⇒←-subst ⟩

          subst (λ H → ⌞ H X Z ⌟) eqH
            (subst (λ H → ⌞ H X Z ⌟)
               (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
               (subst (λ f → ⌞ F (f X) (f Z) ⌟) ≡⇒←-refl
                  (comp (≡⇒← (refl C) X) (≡⇒← (refl C) Y)
                        (≡⇒← (refl C) Z)
                     (subst (λ f → ⌞ F (f Y) (f Z) ⌟) (sym ≡⇒←-refl)
                        (subst (λ H → ⌞ H Y Z ⌟)
                           (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                           (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)))
                     (subst (λ f → ⌞ F (f X) (f Y) ⌟) (sym ≡⇒←-refl)
                        (subst (λ H → ⌞ H X Y ⌟)
                           (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                           (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))))))             ≡⟨ cong (subst (λ H → ⌞ H X Z ⌟) eqH ∘
                                                                                           subst (λ H → ⌞ H X Z ⌟)
                                                                                             (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)) $
                                                                                       dcong′
                                                                                         (λ h eq →
                                                                                            comp (h X) (h Y) (h Z)
                                                                                              (subst (λ f → ⌞ F (f Y) (f Z) ⌟) (sym eq)
                                                                                                 (subst (λ H → ⌞ H Y Z ⌟)
                                                                                                    (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                                                                                                    (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)))
                                                                                              (subst (λ f → ⌞ F (f X) (f Y) ⌟) (sym eq)
                                                                                                 (subst (λ H → ⌞ H X Y ⌟)
                                                                                                    (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                                                                                                    (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))))
                                                                                         _ ⟩
          subst (λ H → ⌞ H X Z ⌟) eqH
            (subst (λ H → ⌞ H X Z ⌟)
               (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
               (comp X Y Z
                  (subst (λ f → ⌞ F (f Y) (f Z) ⌟) (sym (refl P.id))
                     (subst (λ H → ⌞ H Y Z ⌟)
                        (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                        (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)))
                  (subst (λ f → ⌞ F (f X) (f Y) ⌟) (sym (refl P.id))
                     (subst (λ H → ⌞ H X Y ⌟)
                        (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                        (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g)))))                 ≡⟨ cong₂ (λ p q →
                                                                                       subst (λ H → ⌞ H X Z ⌟) eqH
                                                                                         (subst (λ H → ⌞ H X Z ⌟)
                                                                                            (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                                                                                            (comp X Y Z
                                                                                               (subst (λ f → ⌞ F (f Y) (f Z) ⌟) p
                                                                                                  (subst (λ H → ⌞ H Y Z ⌟)
                                                                                                     (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                                                                                                     (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)))
                                                                                               (subst (λ f → ⌞ F (f X) (f Y) ⌟) q
                                                                                                  (subst (λ H → ⌞ H X Y ⌟)
                                                                                                     (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                                                                                                     (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))))))
                                                                                       (sym-refl {x = P.id})
                                                                                       (sym-refl {x = P.id}) ⟩
          subst (λ H → ⌞ H X Z ⌟) eqH
            (subst (λ H → ⌞ H X Z ⌟)
               (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
               (comp X Y Z
                  (subst (λ f → ⌞ F (f Y) (f Z) ⌟) (refl P.id)
                     (subst (λ H → ⌞ H Y Z ⌟)
                        (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                        (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)))
                  (subst (λ f → ⌞ F (f X) (f Y) ⌟) (refl P.id)
                     (subst (λ H → ⌞ H X Y ⌟)
                        (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                        (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g)))))                 ≡⟨ cong₂ (λ f g →
                                                                                              subst (λ H → ⌞ H X Z ⌟) eqH
                                                                                                (subst (λ H → ⌞ H X Z ⌟)
                                                                                                   (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                                                                                                   (comp X Y Z f g)))
                                                                                       (subst-refl _ _)
                                                                                       (subst-refl _ _) ⟩
          subst (λ H → ⌞ H X Z ⌟) eqH
            (subst (λ H → ⌞ H X Z ⌟)
               (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
               (comp X Y Z
                  (subst (λ H → ⌞ H Y Z ⌟)
                     (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                     (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f))
                  (subst (λ H → ⌞ H X Y ⌟)
                     (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                     (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))))                     ≡⟨ sym $ cong₂ (λ p q →
                                                                                             subst (λ H → ⌞ H X Z ⌟) eqH
                                                                                               (subst (λ H → ⌞ H X Z ⌟)
                                                                                                  (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                                                                                                  (comp X Y Z
                                                                                                     (subst (λ H → ⌞ H Y Z ⌟) p
                                                                                                        (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f))
                                                                                                     (subst (λ H → ⌞ H X Y ⌟) q
                                                                                                        (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g)))))
                                                                                       (sym-sym (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _))
                                                                                       (sym-sym (subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)) ⟩
          subst (λ H → ⌞ H X Z ⌟) eqH
            (subst (λ H → ⌞ H X Z ⌟)
               (sym $ subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
               (comp X Y Z
                  (subst (λ H → ⌞ H Y Z ⌟)
                     (sym $ sym $
                        subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                     (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f))
                  (subst (λ H → ⌞ H X Y ⌟)
                     (sym $ sym $
                        subst-refl (λ Obj → Obj → Obj → Set ℓ₂) _)
                     (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))))                     ≡⟨ cong (subst (λ H → ⌞ H X Z ⌟) eqH) push-Q ⟩

          subst (λ H → ⌞ H X Z ⌟) eqH
            (subst (Q C)
               (sym $ subst-refl _ _)
               (λ {X Y Z} → comp X Y Z)
               (subst (λ H → ⌞ H Y Z ⌟) (sym eqH) f)
               (subst (λ H → ⌞ H X Y ⌟) (sym eqH) g))                             ≡⟨ push-Q ⟩

          subst (Q C) eqH
            (subst (Q C)
               (sym $ subst-refl _ _)
               (λ {X Y Z} → comp X Y Z)) f g                                      ≡⟨ cong (λ (h : Q C F → Q C G) → h _ _ _)
                                                                                       subst-Σ-≡,≡→≡ ⟩∎
          subst (uncurry Q)
            (Σ-≡,≡→≡ (refl C) eqH)
            (λ {X Y Z} → comp X Y Z) f g                                          ∎)
                                                                               eqO eqH (λ _ _ _ → C._∙_) f g ⟩
      subst (uncurry Q) (Σ-≡,≡→≡ eqO eqH) C._∙_ f g                       ≡⟨⟩

      subst₂ (uncurry Q) eqO eqH C._∙_ f g                                ∎

-- Equality characterisation lemma for Precategory.

equality-characterisation-Precategory :
  ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} →
  Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ lsuc ℓ₂) →
  Univalence ℓ₁ →
  Univalence ℓ₂ →
  let module C = Precategory C
      module D = Precategory D
  in
  (∃ λ (eqO : C.Obj ≃ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.Hom (_≃_.from eqO X) (_≃_.from eqO Y) ≃
                      D.Hom X Y) →
     (∀ X → _≃_.to (eqH X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        _≃_.to (eqH X Z) (C._∙_ (_≃_.from (eqH Y Z) f)
                                (_≃_.from (eqH X Y) g)) ≡
        f D.∙ g))
    ↔
  C ≡ D
equality-characterisation-Precategory {ℓ₁} {ℓ₂} {C} {D}
                                      ext univ₁ univ₂ =
  _                              ↝⟨ equality-characterisation-Precategory′ ext univ₁ univ₂ ⟩
  C.precategory ≡ D.precategory  ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ rearrange) ⟩□
  C ≡ D                          □
  where
  module C = Precategory C
  module D = Precategory D

  rearrange : Precategory ℓ₁ ℓ₂ ↔ Precategory′ ℓ₁ ℓ₂
  rearrange = record
    { surjection = record
      { logical-equivalence = record
        { to   = Precategory.precategory
        ; from = λ C → record { precategory = C }
        }
      ; right-inverse-of = λ _ → refl _
      }
    ; left-inverse-of = λ _ → refl _
    }

-- Lifts a precategory's object type.

lift-precategory-Obj :
  ∀ {ℓ₁} ℓ₁′ {ℓ₂} →
  Precategory ℓ₁ ℓ₂ → Precategory (ℓ₁ ⊔ ℓ₁′) ℓ₂
lift-precategory-Obj ℓ₁′ C .Precategory.precategory =
    ↑ ℓ₁′ C.Obj
  , (λ (lift A) (lift B) → C.HOM A B)
  , C.id
  , C._∙_
  , C.left-identity
  , C.right-identity
  , C.assoc
  where
  module C = Precategory C

-- Lifts a precategory's morphism type family.

lift-precategory-Hom :
  ∀ {ℓ₁ ℓ₂} ℓ₂′ →
  Precategory ℓ₁ ℓ₂ → Precategory ℓ₁ (ℓ₂ ⊔ ℓ₂′)
lift-precategory-Hom ℓ₂′ C .Precategory.precategory =
    C.Obj
  , (λ A B → ↑ ℓ₂′ (C.Hom A B)
           , ↑-closure 2 C.Hom-is-set)
  , lift C.id
  , (λ (lift f) (lift g) → lift (f C.∙ g))
  , cong lift C.left-identity
  , cong lift C.right-identity
  , cong lift C.assoc
  where
  module C = Precategory C

------------------------------------------------------------------------
-- Categories

Category′ : (ℓ₁ ℓ₂ : Level) → Type (lsuc (ℓ₁ ⊔ ℓ₂))
Category′ ℓ₁ ℓ₂ =
  -- A precategory.
  ∃ λ (C : Precategory ℓ₁ ℓ₂) →

  -- The function ≡→≅ is an equivalence (for each pair of objects).
  ∀ {X Y} → Is-equivalence (Precategory.≡→≅ C {X = X} {Y = Y})

-- A wrapper.

record Category (ℓ₁ ℓ₂ : Level) : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    category : Category′ ℓ₁ ℓ₂

  -- Precategory.

  precategory : Precategory ℓ₁ ℓ₂
  precategory = proj₁ category

  open Precategory precategory public hiding (precategory)

  -- The function ≡→≅ is an equivalence (for each pair of objects).

  ≡→≅-equivalence : ∀ {X Y} → Is-equivalence (≡→≅ {X = X} {Y = Y})
  ≡→≅-equivalence = proj₂ category

  ≡≃≅ : ∀ {X Y} → (X ≡ Y) ≃ (X ≅ Y)
  ≡≃≅ = ⟨ _ , ≡→≅-equivalence ⟩

  ≅→≡ : ∀ {X Y} → X ≅ Y → X ≡ Y
  ≅→≡ = _≃_.from ≡≃≅

  -- "Computation rule" for ≅→≡.

  ≅→≡-refl : ∀ {X} → ≅→≡ id≅ ≡ refl X
  ≅→≡-refl {X} =
    ≅→≡ id≅             ≡⟨ cong ≅→≡ $ sym ≡→≅-refl ⟩
    ≅→≡ (≡→≅ (refl X))  ≡⟨ _≃_.left-inverse-of ≡≃≅ _ ⟩∎
    refl X              ∎

  -- Obj has h-level 3.

  Obj-3 : H-level 3 Obj
  Obj-3 =
    respects-surjection
      (_≃_.surjection (Eq.inverse ≡≃≅))
      2 ≅-set

  -- Isomorphisms form a category.

  category-≅ : Category ℓ₁ ℓ₂
  category-≅ = record { category = precategory-≅ , is-equiv }
    where
    module P≅ = Precategory precategory-≅

    opaque

      is-equiv : ∀ {X Y} → Is-equivalence (P≅.≡→≅ {X = X} {Y = Y})
      is-equiv =
        _⇔_.from (Is-equivalence≃Is-equivalence-CP _)
          λ (X≅Y , X≅Y-iso) →
        Σ-map (Σ-map
          P.id
          (λ {X≡Y} ≡→≅[X≡Y]≡X≅Y →
             elim (λ {X Y} X≡Y →
                     (X≅Y : X ≅ Y) (X≅Y-iso : P≅.Is-isomorphism X≅Y) →
                     ≡→≅ X≡Y ≡ X≅Y →
                     P≅.≡→≅ X≡Y ≡ (X≅Y , X≅Y-iso))
                  (λ X X≅X X≅X-iso ≡→≅[refl]≡X≅X →
                     P≅.≡→≅ (refl X)  ≡⟨ P≅.≡→≅-refl ⟩
                     P≅.id≅           ≡⟨ Σ-≡,≡→≡ (id≅           ≡⟨ sym ≡→≅-refl ⟩
                                                  ≡→≅ (refl X)  ≡⟨ ≡→≅[refl]≡X≅X ⟩∎
                                                  X≅X           ∎)
                                                 (P≅.Is-isomorphism-propositional _ _ _) ⟩∎
                     (X≅X , X≅X-iso)  ∎)
                  X≡Y X≅Y X≅Y-iso
                  ≡→≅[X≡Y]≡X≅Y))
          (λ { {X≡Y , _} ∀y→≡y → λ { (X≡Y′ , ≡→≅[X≡Y′]≡X≅Y) →
             let lemma =
                   ≡→≅ X≡Y′             ≡⟨ elim (λ X≡Y′ → ≡→≅ X≡Y′ ≡ proj₁ (P≅.≡→≅ X≡Y′))
                                                (λ X → ≡→≅ (refl X)             ≡⟨ ≡→≅-refl ⟩
                                                       id≅                      ≡⟨ cong proj₁ $ sym P≅.≡→≅-refl ⟩∎
                                                       proj₁ (P≅.≡→≅ (refl X))  ∎)
                                                X≡Y′ ⟩
                   proj₁ (P≅.≡→≅ X≡Y′)  ≡⟨ cong proj₁ ≡→≅[X≡Y′]≡X≅Y ⟩∎
                   X≅Y                  ∎ in
             (X≡Y , _)   ≡⟨ Σ-≡,≡→≡ (cong proj₁ (∀y→≡y (X≡Y′ , lemma))) (P≅.≅-set _ _) ⟩∎
             (X≡Y′ , _)  ∎ } }) $
        _⇔_.to (Is-equivalence≃Is-equivalence-CP _)
          ≡→≅-equivalence X≅Y

  -- Some equality rearrangement lemmas.

  Hom-, : ∀ {X X′ Y Y′} {f : Hom X Y}
          (p : X ≡ X′) (q : Y ≡ Y′) →
          subst (uncurry Hom) (cong₂ _,_ p q) f ≡ ≡→≅ q ¹ ∙ f ∙ ≡→≅ p ⁻¹
  Hom-, p q = elim
    (λ p → ∀ q → ∀ {f} → subst (uncurry Hom) (cong₂ _,_ p q) f ≡
                         ≡→≅ q ¹ ∙ f ∙ ≡→≅ p ⁻¹)
    (λ X q → elim
       (λ q → ∀ {f} → subst (uncurry Hom) (cong₂ _,_ (refl X) q) f ≡
                      ≡→≅ q ¹ ∙ f ∙ ≡→≅ (refl X) ⁻¹)
       (λ Y {f} →
          subst (uncurry Hom) (cong₂ _,_ (refl X) (refl Y)) f  ≡⟨ cong (λ eq → subst (uncurry Hom) eq f) $ cong₂-refl _,_ ⟩
          subst (uncurry Hom) (refl (X , Y)) f                 ≡⟨ subst-refl (uncurry Hom) _ ⟩
          f                                                    ≡⟨ sym left-identity ⟩
          id ∙ f                                               ≡⟨ cong (λ g → g ¹ ∙ f) $ sym ≡→≅-refl ⟩
          ≡→≅ (refl Y) ¹ ∙ f                                   ≡⟨ sym right-identity ⟩
          (≡→≅ (refl Y) ¹ ∙ f) ∙ id                            ≡⟨ sym assoc ⟩
          ≡→≅ (refl Y) ¹ ∙ f ∙ id                              ≡⟨ cong (λ g → ≡→≅ (refl Y) ¹ ∙ f ∙ g ⁻¹) $ sym ≡→≅-refl ⟩∎
          ≡→≅ (refl Y) ¹ ∙ f ∙ ≡→≅ (refl X) ⁻¹                 ∎)
       q)
    p q

  ≡→≅-trans : ∀ {X Y Z} (p : X ≡ Y) (q : Y ≡ Z) →
              ≡→≅ (trans p q) ≡ ≡→≅ q ∙≅ ≡→≅ p
  ≡→≅-trans {X} = elim¹
    (λ p → ∀ q → ≡→≅ (trans p q) ≡ ≡→≅ q ∙≅ ≡→≅ p)
    (elim¹
       (λ q → ≡→≅ (trans (refl X) q) ≡ ≡→≅ q ∙≅ ≡→≅ (refl X))
       (≡→≅ (trans (refl X) (refl X))  ≡⟨ cong ≡→≅ trans-refl-refl ⟩
        ≡→≅ (refl X)                   ≡⟨ ≡→≅-refl ⟩
        id≅                            ≡⟨ sym $ Precategory.left-identity precategory-≅ ⟩
        id≅ ∙≅ id≅                     ≡⟨ sym $ cong₂ _∙≅_ ≡→≅-refl ≡→≅-refl ⟩∎
        ≡→≅ (refl X) ∙≅ ≡→≅ (refl X)   ∎))

-- Equality of categories is isomorphic to equality of the underlying
-- precategories (assuming extensionality).

≡↔precategory≡precategory′ :
  ∀ {ℓ₁ ℓ₂} {C D : Category′ ℓ₁ ℓ₂} →
  Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
  C ≡ D ↔ proj₁ C ≡ proj₁ D
≡↔precategory≡precategory′ {ℓ₂} ext =
  inverse $
  ignore-propositional-component
    (implicit-Π-closure (lower-extensionality ℓ₂ lzero ext) 1 λ _ →
     implicit-Π-closure (lower-extensionality ℓ₂ lzero ext) 1 λ _ →
     Is-equivalence-propositional ext)

-- Equality of categories is isomorphic to equality of the underlying
-- precategories (assuming extensionality).

≡↔precategory≡precategory :
  ∀ {ℓ₁ ℓ₂} {C D : Category ℓ₁ ℓ₂} →
  Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
  C ≡ D ↔ Category.precategory C ≡ Category.precategory D
≡↔precategory≡precategory {C} {D} ext =
  C ≡ D                          ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ rearrange) ⟩
  C.category ≡ D.category        ↝⟨ ≡↔precategory≡precategory′ ext ⟩□
  C.precategory ≡ D.precategory  □
  where
  module C = Category C
  module D = Category D

  rearrange : Category′ _ _ ↔ Category _ _
  rearrange = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ C → record { category = C }
        ; from = Category.category
        }
      ; right-inverse-of = λ _ → refl _
      }
    ; left-inverse-of = λ _ → refl _
    }

-- Equality characterisation lemma for Category′.

equality-characterisation-Category′ :
  ∀ {ℓ₁ ℓ₂} {C D : Category′ ℓ₁ ℓ₂} →
  Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ lsuc ℓ₂) →
  Univalence ℓ₁ →
  Univalence ℓ₂ →
  let module C = Category (record { category = C })
      module D = Category (record { category = D })
  in
  (∃ λ (eqO : C.Obj ≃ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.Hom (_≃_.from eqO X) (_≃_.from eqO Y) ≃
                      D.Hom X Y) →
     (∀ X → _≃_.to (eqH X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        _≃_.to (eqH X Z) (C._∙_ (_≃_.from (eqH Y Z) f)
                                (_≃_.from (eqH X Y) g)) ≡
        f D.∙ g))
    ↔
  C ≡ D
equality-characterisation-Category′ {ℓ₂} {C} {D} ext univ₁ univ₂ =
  _                              ↝⟨ equality-characterisation-Precategory ext univ₁ univ₂ ⟩
  C.precategory ≡ D.precategory  ↝⟨ inverse $ ≡↔precategory≡precategory′ (lower-extensionality lzero (lsuc ℓ₂) ext) ⟩□
  C ≡ D                          □
  where
  module C = Category (record { category = C })
  module D = Category (record { category = D })

-- Equality characterisation lemma for Category.

equality-characterisation-Category :
  ∀ {ℓ₁ ℓ₂} {C D : Category ℓ₁ ℓ₂} →
  Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ lsuc ℓ₂) →
  Univalence ℓ₁ →
  Univalence ℓ₂ →
  let module C = Category C
      module D = Category D
  in
  (∃ λ (eqO : C.Obj ≃ D.Obj) →
   ∃ λ (eqH : ∀ X Y → C.Hom (_≃_.from eqO X) (_≃_.from eqO Y) ≃
                      D.Hom X Y) →
     (∀ X → _≃_.to (eqH X X) C.id ≡ D.id)
       ×
     (∀ X Y Z (f : D.Hom Y Z) (g : D.Hom X Y) →
        _≃_.to (eqH X Z) (C._∙_ (_≃_.from (eqH Y Z) f)
                                (_≃_.from (eqH X Y) g)) ≡
        f D.∙ g))
    ↔
  C ≡ D
equality-characterisation-Category {ℓ₂} {C} {D} ext univ₁ univ₂ =
  _                              ↝⟨ equality-characterisation-Precategory ext univ₁ univ₂ ⟩
  C.precategory ≡ D.precategory  ↝⟨ inverse $ ≡↔precategory≡precategory (lower-extensionality lzero (lsuc ℓ₂) ext) ⟩□
  C ≡ D                          □
  where
  module C = Category C
  module D = Category D

-- A lemma that can be used to turn a precategory into a category.

precategory-to-category :
  ∀ {c₁ c₂}
  (C : Precategory c₁ c₂) →
  let open Precategory C in
  (≡≃≅ : ∀ {X Y} → (X ≡ Y) ≃ (X ≅ Y)) →
  (∀ {X} → _≃_.to ≡≃≅ (refl X) ¹ ≡ id) →
  Category c₁ c₂
precategory-to-category C ≡≃≅ ≡≃≅-refl = record
  { category = C , Precategory.≡→≅-equivalence-lemma C ≡≃≅ ≡≃≅-refl
  }

-- A variant of the previous lemma for precategories with Set c₁ as
-- the type of objects. (The lemma is defined using extensionality and
-- univalence for sets.)

precategory-with-Set-to-category :
  ∀ {c₁ c₂} →
  Extensionality c₁ c₁ →
  ((A B : Set c₁) → Univalence′ ⌞ A ⌟ ⌞ B ⌟) →
  (C : Precategory-with-Obj (Set c₁) c₂) →
  let open Precategory (record { precategory = _ , C }) in
  (≃≃≅ : ∀ X Y → (⌞ X ⌟ ≃ ⌞ Y ⌟) ≃ (X ≅ Y)) →
  (∀ X → _≃_.to (≃≃≅ X X) Eq.id ¹ ≡ id) →
  Category (lsuc c₁) c₂
precategory-with-Set-to-category ext univ C ≃≃≅ ≃≃≅-id =
  precategory-to-category C′ ≡≃≅ ≡≃≅-refl
  where
  C′ = record { precategory = _ , C }
  open Precategory C′

  -- _≡_ and _≅_ are pointwise equivalent…

  cong-⌞⌟ : {X Y : Obj} → (X ≡ Y) ≃ (⌞ X ⌟ ≡ ⌞ Y ⌟)
  cong-⌞⌟ = Eq.↔⇒≃ $ inverse $
    ignore-propositional-component (H-level-propositional ext 2)

  ≡≃≅ : ∀ {X Y} → (X ≡ Y) ≃ (X ≅ Y)
  ≡≃≅ {X} {Y} = ≃≃≅ X Y ⊚ ≡≃≃ (univ X Y) ⊚ cong-⌞⌟

  -- …and the proof maps reflexivity to the identity isomorphism.

  ≡≃≅-refl :
    ∀ {X} → _¹ {X = X} {Y = X} (_≃_.to ≡≃≅ (refl X)) ≡ id
  ≡≃≅-refl {X} = cong (_¹ {X = X} {Y = X}) (
    _≃_.to (≃≃≅ X X) (≡⇒≃ (proj₁ (Σ-≡,≡←≡ (refl X))))  ≡⟨ cong (_≃_.to (≃≃≅ X X) ∘ ≡⇒≃ ∘ proj₁) Σ-≡,≡←≡-refl ⟩
    _≃_.to (≃≃≅ X X) (≡⇒≃ (refl ⌞ X ⌟))                ≡⟨ cong (_≃_.to (≃≃≅ X X)) ≡⇒≃-refl ⟩
    _≃_.to (≃≃≅ X X) Eq.id                             ≡⟨ _≃_.from (≡≃≡¹ {X = X} {Y = X}) $ ≃≃≅-id X ⟩∎
    id≅                                                ∎)

-- An example: sets and functions. (Defined using extensionality and
-- univalence for sets.)

category-Set :
  (ℓ : Level) →
  Extensionality ℓ ℓ →
  ((A B : Set ℓ) → Univalence′ ⌞ A ⌟ ⌞ B ⌟) →
  Category (lsuc ℓ) ℓ
category-Set ℓ ext univ =
  precategory-with-Set-to-category
    ext
    univ
    (proj₂ precategory)
    (≃≃≅-Set ℓ ext)
    (λ _ → refl P.id)
  where
  C = precategory-Set ℓ ext
  open Precategory C

-- An example: sets and bijections. (Defined using extensionality and
-- univalence for sets.)

category-Set-≅ :
  (ℓ : Level) →
  Extensionality ℓ ℓ →
  ((A B : Set ℓ) → Univalence′ ⌞ A ⌟ ⌞ B ⌟) →
  Category (lsuc ℓ) ℓ
category-Set-≅ ℓ ext univ =
  Category.category-≅ (category-Set ℓ ext univ)

private

  -- The objects are sets.

  Obj-category-Set-≅ :
    ∀ ℓ (ext : Extensionality ℓ ℓ)
    (univ : (A B : Set ℓ) → Univalence′ ⌞ A ⌟ ⌞ B ⌟) →
    Category.Obj (category-Set-≅ ℓ ext univ) ≡ Set ℓ
  Obj-category-Set-≅ _ _ _ = refl _

  -- The morphisms are bijections.

  Hom-category-Set-≅ :
    ∀ ℓ (ext : Extensionality ℓ ℓ)
    (univ : (A B : Set ℓ) → Univalence′ ⌞ A ⌟ ⌞ B ⌟) →
    Category.Hom (category-Set-≅ ℓ ext univ) ≡
    Category._≅_ (category-Set ℓ ext univ)
  Hom-category-Set-≅ _ _ _ = refl _

-- A trivial category (with a singleton type of objects and singleton
-- homsets).

Unit : ∀ ℓ₁ ℓ₂ → Category ℓ₁ ℓ₂
Unit ℓ₁ ℓ₂ =
  precategory-to-category record
    { precategory =
          ↑ ℓ₁ ⊤
        , (λ _ _ → ↑ ℓ₂ ⊤ , ↑⊤-set)
        , _
        , _
        , refl _
        , refl _
        , refl _
    }
  (λ {x y} →
     x ≡ y                                                    ↔⟨ ≡↔⊤ ⟩
     ⊤                                                        ↔⟨ inverse ≡↔⊤ ⟩
     lift tt ≡ lift tt                                        ↔⟨ inverse $ drop-⊤-left-Σ ≡↔⊤ ⟩
     lift tt ≡ lift tt × lift tt ≡ lift tt                    ↔⟨ inverse $ drop-⊤-left-Σ Bijection.↑↔ ⟩
     ↑ ℓ₂ ⊤ × lift tt ≡ lift tt × lift tt ≡ lift tt           ↔⟨ inverse $ drop-⊤-left-Σ Bijection.↑↔ ⟩□
     ↑ ℓ₂ ⊤ × ↑ ℓ₂ ⊤ × lift tt ≡ lift tt × lift tt ≡ lift tt  □)
  (refl _)
  where
  ↑⊤-set : ∀ {ℓ} → Is-set (↑ ℓ ⊤)
  ↑⊤-set = mono (Nat.zero≤ 2) (↑-closure 0 ⊤-contractible)

  ≡↔⊤ : ∀ {ℓ} {x y : ↑ ℓ ⊤} → (x ≡ y) ↔ ⊤
  ≡↔⊤ = _⇔_.to contractible⇔↔⊤ $
          propositional⇒inhabited⇒contractible ↑⊤-set (refl _)

-- An "empty" category, without objects.

Empty : ∀ ℓ₁ ℓ₂ → Category ℓ₁ ℓ₂
Empty ℓ₁ ℓ₂ =
  precategory-to-category record
    { precategory =
          ⊥
        , ⊥-elim
        , (λ {x} → ⊥-elim x)
        , (λ {x} → ⊥-elim x)
        , (λ {x} → ⊥-elim x)
        , (λ {x} → ⊥-elim x)
        , (λ {x} → ⊥-elim x)
    }
  (λ {x} → ⊥-elim x)
  (λ {x} → ⊥-elim x)

-- Lifts a category's object type.

lift-category-Obj :
  ∀ {ℓ₁} ℓ₁′ {ℓ₂} →
  Category ℓ₁ ℓ₂ → Category (ℓ₁ ⊔ ℓ₁′) ℓ₂
lift-category-Obj ℓ₁′ C .Category.category =
    C′
  , ≡→≅-equivalence
  where
  C′ = lift-precategory-Obj ℓ₁′ (Category.precategory C)

  module C  = Category C
  module C′ = Precategory C′

  ≡→≅-equivalence :
    {X Y : Precategory.Obj C′} →
    Is-equivalence (C′.≡→≅ {X = X} {Y = Y})
  ≡→≅-equivalence {X} {Y} =
    _≃_.is-equivalence $
    Eq.with-other-function
      (X ≡ Y                ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Bijection.↑↔ ⟩
       lower X ≡ lower Y    ↝⟨ Eq.⟨ _ , C.≡→≅-equivalence ⟩ ⟩
       lower X C.≅ lower Y  ↔⟨⟩
       X C′.≅ Y             □)
      C′.≡→≅
      (elim (λ X≡Y → C.≡→≅ (cong lower X≡Y) ≡ C′.≡→≅ X≡Y)
         (λ X →
            C.≡→≅ (cong lower (refl X))  ≡⟨ cong C.≡→≅ $ cong-refl lower ⟩
            C.≡→≅ (refl (lower X))       ≡⟨ C.≡→≅-refl ⟩
            C.id≅                        ≡⟨⟩
            C′.id≅                       ≡⟨ sym C′.≡→≅-refl ⟩∎
            C′.≡→≅ (refl X)              ∎))

-- Lifts a category's morphism type family.

lift-category-Hom :
  ∀ {ℓ₁ ℓ₂} ℓ₂′ →
  Category ℓ₁ ℓ₂ → Category ℓ₁ (ℓ₂ ⊔ ℓ₂′)
lift-category-Hom ℓ₂′ C .Category.category =
    C′
  , ≡→≅-equivalence
  where
  C′ = lift-precategory-Hom ℓ₂′ (Category.precategory C)

  module C  = Category C
  module C′ = Precategory C′

  ≡→≅-equivalence :
    {X Y : Precategory.Obj C′} →
    Is-equivalence (C′.≡→≅ {X = X} {Y = Y})
  ≡→≅-equivalence {X} {Y} =
    _≃_.is-equivalence $
    Eq.with-other-function
      (X ≡ Y     ↝⟨ Eq.⟨ _ , C.≡→≅-equivalence ⟩ ⟩
       X C.≅ Y   ↝⟨ equiv ⟩□
       X C′.≅ Y  □)
      C′.≡→≅
      (elim (λ X≡Y → _≃_.to equiv (C.≡→≅ X≡Y) ≡ C′.≡→≅ X≡Y)
         (λ X →
            _≃_.to equiv (C.≡→≅ (refl X))  ≡⟨ cong (_≃_.to equiv) C.≡→≅-refl ⟩
            _≃_.to equiv C.id≅             ≡⟨ _≃_.from C′.≡≃≡¹ (refl _) ⟩
            C′.id≅                         ≡⟨ sym C′.≡→≅-refl ⟩∎
            C′.≡→≅ (refl X)                ∎))
    where
    equiv : ∀ {X Y} → (X C.≅ Y) ≃ (X C′.≅ Y)
    equiv =
      Σ-cong (inverse Bijection.↑↔) λ _ →
      Σ-cong (inverse Bijection.↑↔) λ _ →
      (Eq.≃-≡ $ Eq.↔⇒≃ Bijection.↑↔)
        ×-cong
      (Eq.≃-≡ $ Eq.↔⇒≃ Bijection.↑↔)
