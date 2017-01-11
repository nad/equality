------------------------------------------------------------------------
-- 1-categories
------------------------------------------------------------------------

-- The code is based on the presentation in the HoTT book (but might
-- not follow it exactly).

{-# OPTIONS --without-K #-}

open import Equality

module Category
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq hiding (id; _∘_; inverse; finally-↔)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq
  using (_≃_; ⟨_,_⟩; module _≃_; Is-equivalence)
open import Function-universe eq hiding (id) renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence using (module _⇔_)
open import Prelude as P hiding (id)
open import Univalence-axiom eq

------------------------------------------------------------------------
-- Precategories

Precategory′ : (ℓ₁ ℓ₂ : Level) → Set (lsuc (ℓ₁ ⊔ ℓ₂))
Precategory′ ℓ₁ ℓ₂ =
  -- Objects.
  ∃ λ (Obj : Set ℓ₁) →

  -- Morphisms (a /set/).
  ∃ λ (HOM : Obj → Obj → SET ℓ₂) →
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

-- A wrapper.

record Precategory (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    precategory : Precategory′ ℓ₁ ℓ₂

  -- Objects.

  Obj : Set ℓ₁
  Obj = proj₁ precategory

  -- Morphisms.

  HOM : Obj → Obj → SET ℓ₂
  HOM = proj₁ (proj₂ precategory)

  -- The morphism type family.

  Hom : Obj → Obj → Set ℓ₂
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

  Is-isomorphism : ∀ {X Y} → Hom X Y → Set ℓ₂
  Is-isomorphism f = ∃ λ g → (f ∙ g ≡ id) × (g ∙ f ≡ id)

  infix 4 _≅_

  _≅_ : Obj → Obj → Set ℓ₂
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

  abstract

    -- "Is-isomorphism f" is a proposition.

    Is-isomorphism-propositional :
      ∀ {X Y} (f : Hom X Y) →
      Is-proposition (Is-isomorphism f)
    Is-isomorphism-propositional f =
      _⇔_.from propositional⇔irrelevant
        λ { (g , fg , gf) (g′ , fg′ , g′f) →
            Σ-≡,≡→≡ (g             ≡⟨ sym left-identity ⟩
                     id ∙ g        ≡⟨ cong (λ h → h ∙ g) $ sym g′f ⟩
                     (g′ ∙ f) ∙ g  ≡⟨ sym assoc ⟩
                     g′ ∙ (f ∙ g)  ≡⟨ cong (_∙_ g′) fg ⟩
                     g′ ∙ id       ≡⟨ right-identity ⟩∎
                     g′            ∎)
                    (Σ-≡,≡→≡ (_⇔_.to set⇔UIP Hom-is-set _ _)
                             (_⇔_.to set⇔UIP Hom-is-set _ _)) }

    -- Isomorphism equality is equivalent to "forward morphism"
    -- equality.

    ≡≃≡¹ : ∀ {X Y} {f g : X ≅ Y} → (f ≡ g) ≃ (f ¹ ≡ g ¹)
    ≡≃≡¹ {f = f} {g} =
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
    abstract
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
    _≃_.to ≡≃≅ (refl X) ≡ id≅ →
    ∀ {Y} → Is-equivalence (≡→≅ {X = X} {Y = Y})
  ≡→≅-equivalence-lemma {X} ≡≃≅ ≡≃≅-refl {Y} =
    Eq.respects-extensional-equality
      (elim¹ (λ X≡Y → _≃_.to ≡≃≅ X≡Y ≡ ≡→≅ X≡Y)
             (_≃_.to ≡≃≅ (refl X)  ≡⟨ ≡≃≅-refl ⟩
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
  SET ℓ ,

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
  (X Y : Obj) → (Type X ≃ Type Y) ≃ (X ≅ Y)
≃≃≅-Set ℓ ext X Y = Eq.↔⇒≃ record
  { surjection = record
    { logical-equivalence = record
      { to   = λ X≃Y → _≃_.to X≃Y , _≃_.from X≃Y ,
                       ext (_≃_.right-inverse-of X≃Y) ,
                       ext (_≃_.left-inverse-of  X≃Y)
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

------------------------------------------------------------------------
-- Categories

Category′ : (ℓ₁ ℓ₂ : Level) → Set (lsuc (ℓ₁ ⊔ ℓ₂))
Category′ ℓ₁ ℓ₂ =
  -- A precategory.
  ∃ λ (C : Precategory ℓ₁ ℓ₂) →

  -- The function ≡→≅ is an equivalence (for each pair of objects).
  ∀ {X Y} → Is-equivalence (Precategory.≡→≅ C {X = X} {Y = Y})

-- A wrapper.

record Category (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
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
  Obj-3 X Y =
    respects-surjection
      (_≃_.surjection (Eq.inverse ≡≃≅))
      2 ≅-set

  -- Isomorphisms form a category.

  category-≅ : Category ℓ₁ ℓ₂
  category-≅ = record { category = precategory-≅ , is-equiv }
    where
    module P≅ = Precategory precategory-≅

    abstract

      is-equiv : ∀ {X Y} → Is-equivalence (P≅.≡→≅ {X = X} {Y = Y})
      is-equiv (X≅Y , X≅Y-iso) =
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
                                                 (_⇔_.to propositional⇔irrelevant (P≅.Is-isomorphism-propositional _) _ _) ⟩∎
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
             (X≡Y , _)   ≡⟨ Σ-≡,≡→≡ (cong proj₁ (∀y→≡y (X≡Y′ , lemma)))
                                    (_⇔_.to set⇔UIP P≅.≅-set _ _) ⟩∎
             (X≡Y′ , _)  ∎ } })
          (≡→≅-equivalence X≅Y)

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

-- A lemma that can be used to turn a precategory into a category.

precategory-to-category :
  ∀ {c₁ c₂}
  (C : Precategory c₁ c₂) →
  let open Precategory C in
  (≡≃≅ : ∀ {X Y} → (X ≡ Y) ≃ (X ≅ Y)) →
  (∀ {X} → _≃_.to ≡≃≅ (refl X) ≡ id≅) →
  Category c₁ c₂
precategory-to-category C ≡≃≅ ≡≃≅-refl = record
  { category = C , Precategory.≡→≅-equivalence-lemma C ≡≃≅ ≡≃≅-refl
  }

-- An example: sets and functions. (Defined using extensionality and
-- univalence.)

category-Set :
  (ℓ : Level) →
  Extensionality ℓ ℓ →
  Univalence ℓ →
  Category (lsuc ℓ) ℓ
category-Set ℓ ext univ =
  precategory-to-category precategory ≡≃≅ ≡≃≅-refl-is-id≅
  where
  precategory = precategory-Set ℓ ext
  open Precategory precategory hiding (precategory)

  abstract

    -- _≡_ and _≅_ are pointwise equivalent…

    cong-Type : {X Y : Obj} → (X ≡ Y) ≃ (Type X ≡ Type Y)
    cong-Type = Eq.↔⇒≃ $ inverse $
      ignore-propositional-component (H-level-propositional ext 2)

    ≃≃≅ : (X Y : Obj) → (Type X ≃ Type Y) ≃ (X ≅ Y)
    ≃≃≅ = ≃≃≅-Set ℓ ext

    ≡≃≅ : ∀ {X Y} → (X ≡ Y) ≃ (X ≅ Y)
    ≡≃≅ {X} {Y} = ≃≃≅ X Y ⊚ ≡≃≃ univ ⊚ cong-Type

    -- …and the proof maps reflexivity to the identity isomorphism.

    ≡≃≅-refl-is-id≅ : ∀ {X} → _≃_.to ≡≃≅ (refl X) ≡ id≅ {X = X}
    ≡≃≅-refl-is-id≅ {X} =
      _≃_.to (≃≃≅ X X) (≡⇒≃ (proj₁ (Σ-≡,≡←≡ (refl X))))  ≡⟨ cong (_≃_.to (≃≃≅ X X) ∘ ≡⇒≃ ∘ proj₁) Σ-≡,≡←≡-refl ⟩
      _≃_.to (≃≃≅ X X) (≡⇒≃ (refl (Type X)))             ≡⟨ cong (_≃_.to (≃≃≅ X X)) ≡⇒≃-refl ⟩
      _≃_.to (≃≃≅ X X) Eq.id                             ≡⟨ _≃_.from (≡≃≡¹ {X = X} {Y = X}) (refl P.id) ⟩∎
      id≅ {X = X}                                        ∎

-- An example: sets and bijections. (Defined using extensionality and
-- univalence.)

category-Set-≅ :
  (ℓ : Level) →
  Extensionality ℓ ℓ →
  Univalence ℓ →
  Category (lsuc ℓ) ℓ
category-Set-≅ ℓ ext univ =
  Category.category-≅ (category-Set ℓ ext univ)

private

  -- The objects are sets.

  Obj-category-Set-≅ :
    ∀ ℓ (ext : Extensionality ℓ ℓ) (univ : Univalence ℓ) →
    Category.Obj (category-Set-≅ ℓ ext univ) ≡ SET ℓ
  Obj-category-Set-≅ _ _ _ = refl _

  -- The morphisms are bijections.

  Hom-category-Set-≅ :
    ∀ ℓ (ext : Extensionality ℓ ℓ) (univ : Univalence ℓ) →
    Category.Hom (category-Set-≅ ℓ ext univ) ≡
    Category._≅_ (category-Set ℓ ext univ)
  Hom-category-Set-≅ _ _ _ = refl _
