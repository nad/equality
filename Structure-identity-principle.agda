------------------------------------------------------------------------
-- Aczel's structure identity principle (for 1-categories), more or
-- less as found in "Homotopy Type Theory: Univalent Foundations of
-- Mathematics" (first edition)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Structure-identity-principle
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq using (_↔_; module _↔_; Σ-≡,≡↔≡)
open import Category eq
open Derived-definitions-and-properties eq
open import Equality.Decidable-UIP eq
open import Equivalence eq as Eq
  hiding (id; _∘_; inverse; lift-equality)
open import Function-universe eq hiding (id) renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence using (module _⇔_)
open import Prelude as P hiding (id)
open import Univalence-axiom eq
open import Univalence-axiom.Isomorphism-is-equality.Simple eq
  using (Assumptions; module Assumptions;
         Universe; module Universe;
         module Class)

-- Standard notions of structure.

record Standard-notion-of-structure
         {c₁ c₂} ℓ₁ ℓ₂ (C : Precategory c₁ c₂) :
         Set (c₁ ⊔ c₂ ⊔ lsuc (ℓ₁ ⊔ ℓ₂)) where
  open Precategory C

  field
    P               : Obj → Set ℓ₁
    H               : ∀ {X Y} (p : P X) (q : P Y) → Hom X Y → Set ℓ₂
    H-prop          : ∀ {X Y} {p : P X} {q : P Y}
                      (f : Hom X Y) → Is-proposition (H p q f)
    H-id            : ∀ {X} {p : P X} → H p p id
    H-∘             : ∀ {X Y Z} {p : P X} {q : P Y} {r : P Z} {f g} →
                      H p q f → H q r g → H p r (f ∙ g)
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
  lift-equality eq =
    Σ-≡,≡→≡ eq (_⇔_.to propositional⇔irrelevant (H-prop _) _ _)

  -- A derived precategory.

  Str : Precategory (c₁ ⊔ ℓ₁) (c₂ ⊔ ℓ₂)
  Str = record { precategory =
    ∃ P ,
    (λ { (X , p) (Y , q) →
         ∃ (H p q) ,
         Σ-closure 2 Hom-is-set (λ f → mono₁ 1 (H-prop f)) }) ,
    (id , H-id) ,
    (λ { (f , hf) (g , hg) → f ∙ g , H-∘ hf hg }) ,
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
              (_⇔_.to set⇔UIP Str.Hom-is-set _ _)
              (_⇔_.to set⇔UIP Str.Hom-is-set _ _)

      from∘to : ∀ p → from (≅HH≃≅.to p) ≡ p
      from∘to ((f , f⁻¹ , f∙f⁻¹ , f⁻¹∙f) , Hf , Hf⁻¹) =
        cong₂ (λ f∙f⁻¹ f⁻¹∙f → (f , f⁻¹ , f∙f⁻¹ , f⁻¹∙f) , Hf , Hf⁻¹)
              (_⇔_.to set⇔UIP C.Hom-is-set _ _)
              (_⇔_.to set⇔UIP C.Hom-is-set _ _)

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
      to-refl =
        cong₂ _,_ (_⇔_.to propositional⇔irrelevant (H-prop _) _ _)
                  (_⇔_.to propositional⇔irrelevant (H-prop _) _ _)

    ≡≡≃≅HH : ∀ {X Y} {p : P X} {q : P Y} →
             (∃ λ (eq : X ≡ Y) → subst P eq p ≡ q) ≃
             (∃ λ (f : X C.≅ Y) → H p q (f C.¹) × H q p (f C.⁻¹))
    ≡≡≃≅HH {X} {p = p} {q} =
      Σ-preserves C.≡≃≅ λ X≡Y →
        _↔_.to (⇔↔≃ ext (P-set _ _ _)
                        (×-closure 1 (H-prop _) (H-prop _)))
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

    ≡≃≅-refl : ∀ {Xp} → _≃_.to ≡≃≅ (refl Xp) ≡ Str.id≅
    ≡≃≅-refl {X , p} =
      ≅HH≃≅.to (_≃_.to ≡≡≃≅HH (Σ-≡,≡←≡ (refl (_,_ {B = P} X p))))      ≡⟨ cong (≅HH≃≅.to ∘ _≃_.to ≡≡≃≅HH) $ Σ-≡,≡←≡-refl {B = P} ⟩
      ≅HH≃≅.to (_≃_.to ≡≡≃≅HH (refl X , subst-refl P p))               ≡⟨⟩
      ≅HH≃≅.to (C.≡→≅ (refl X) , ≡≡≃≅HH.to (refl X) (subst-refl P p))  ≡⟨ cong ≅HH≃≅.to $ Σ-≡,≡→≡ C.≡→≅-refl ≡≡≃≅HH.to-refl ⟩
      ≅HH≃≅.to (C.id≅ , H-id , H-id)                                   ≡⟨ refl _ ⟩∎
      Str.id≅                                                          ∎

------------------------------------------------------------------------
-- An example

-- The structure identity principle can be used to prove a slightly
-- restricted variant of isomorphism-is-equality (which is defined in
-- Univalence-axiom.Isomorphism-is-equality.Simple.Class).

isomorphism-is-equality′ :
  (Univ : Universe) → let open Universe Univ in
  Assumptions →
  ∀ c X Y →
  (∀ {B} → Is-set B → Is-set (El (proj₁ c) B)) →  -- Extra assumption.
  Is-set (proj₁ X) → Is-set (proj₁ Y) →           -- Extra assumptions.
  Class.Isomorphic Univ c X Y ↔ (X ≡ Y)
isomorphism-is-equality′ Univ ass
  (a , P) (C , x , p) (D , y , q) El-set C-set D-set = isomorphic

  module Isomorphism-is-equality′ where

  open Assumptions ass
  open Universe Univ
  open Class Univ using (Isomorphic; Carrier)

  -- The category of sets and functions.

  Fun : Category (# 2) (# 1)
  Fun = category-Set (# 1) ext univ₁

  module Fun = Category Fun

  -- The category of sets and bijections.

  Bij : Category (# 2) (# 1)
  Bij = category-Set-≅ (# 1) ext univ₁

  module Bij = Category Bij

  -- If two sets are isomorphic, then the underlying types are
  -- equivalent.

  ≅⇒≃ : (C D : Fun.Obj) → C Fun.≅ D → Type C ≃ Type D
  ≅⇒≃ C D = _≃_.from (≃≃≅-Set (# 1) ext C D)

  -- The "standard notion of structure" that the structure identity
  -- principle is instantiated with.

  S : Standard-notion-of-structure (# 1) (# 1) Bij.precategory
  S = record
    { P               = El a ∘ Type
    ; H               = λ {C D} x y C≅D →
                          Is-isomorphism a (≅⇒≃ C D C≅D) x y
    ; H-prop          = λ {_ C} _ → El-set (proj₂ C) _ _
    ; H-id            = λ {C x} →
                          resp a (≅⇒≃ C C (Bij.id {X = C})) x  ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
                          resp a Eq.id x                       ≡⟨ resp-id ass a x ⟩∎
                          x                                    ∎
    ; H-∘             = λ {B C D x y z B≅C C≅D} x≅y y≅z →
                          resp a (≅⇒≃ B D (B≅C Bij.∙ C≅D)) x             ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
                          resp a (≅⇒≃ C D C≅D ⊚ ≅⇒≃ B C B≅C) x           ≡⟨ resp-preserves-compositions (El a) (resp a) (resp-id ass a)
                                                                                                        univ₁ ext (≅⇒≃ B C B≅C) (≅⇒≃ C D C≅D) x ⟩
                          resp a (≅⇒≃ C D C≅D) (resp a (≅⇒≃ B C B≅C) x)  ≡⟨ cong (resp a (≅⇒≃ C D C≅D)) x≅y ⟩
                          resp a (≅⇒≃ C D C≅D) y                         ≡⟨ y≅z ⟩∎
                          z                                              ∎
    ; H-antisymmetric = λ {C} x y x≡y _ →
                          x                                    ≡⟨ sym $ resp-id ass a x ⟩
                          resp a Eq.id x                       ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
                          resp a (≅⇒≃ C C (Bij.id {X = C})) x  ≡⟨ x≡y ⟩∎
                          y                                    ∎
    }

  open module S = Standard-notion-of-structure S
    using (H; Str; module Str)

  abstract

    -- Every Str morphism is an isomorphism.

    Str-homs-are-isos :
      ∀ {C D x y} (f : ∃ (H {X = C} {Y = D} x y)) →
      Str.Is-isomorphism {X = C , x} {Y = D , y} f
    Str-homs-are-isos {C} {D} {x} {y} (C≅D , x≅y) =

      (D≅C ,
       (resp a (≅⇒≃ D C D≅C) y            ≡⟨ cong (λ eq → resp a eq y) $ Eq.lift-equality ext (refl _) ⟩
        resp a (inverse $ ≅⇒≃ C D C≅D) y  ≡⟨ resp-preserves-inverses (El a) (resp a) (resp-id ass a) univ₁ ext (≅⇒≃ C D C≅D) _ _ x≅y ⟩∎
        x                                 ∎)) ,

      S.lift-equality {X = C , x} {Y = C , x} (
        C≅D Fun.∙≅ D≅C   ≡⟨ _≃_.from (Fun.≡≃≡¹ {X = C} {Y = C}) (Fun._¹⁻¹ {X = C} {Y = D} C≅D) ⟩∎
        Fun.id≅ {X = C}  ∎) ,

      S.lift-equality {X = D , y} {Y = D , y} (
        D≅C Fun.∙≅ C≅D   ≡⟨ _≃_.from (Fun.≡≃≡¹ {X = D} {Y = D}) (Fun._⁻¹¹ {X = C} {Y = D} C≅D) ⟩∎
        Fun.id≅ {X = D}  ∎)

      where

      D≅C : D Fun.≅ C
      D≅C = Fun._⁻¹≅ {X = C} {Y = D} C≅D

    -- The isomorphism that should be constructed.

    isomorphic : Isomorphic (a , P) (C , x , p) (D , y , q) ↔
                 ((C , x , p) ≡ (D , y , q))
    isomorphic =
      Σ (C ≃ D) (λ eq → Is-isomorphism a eq x y)     ↝⟨ (let ≃≃≅-CD = ≃≃≅-Set (# 1) ext (C , C-set) (D , D-set) in
                                                         Σ-cong ≃≃≅-CD (λ eq →
                                                           let eq′ = _≃_.from ≃≃≅-CD (_≃_.to ≃≃≅-CD eq) in
                                                           Is-isomorphism a eq  x y  ↝⟨ ≡⇒↝ _ $ cong (λ eq → Is-isomorphism a eq x y) $ sym $
                                                                                          _≃_.left-inverse-of ≃≃≅-CD eq ⟩
                                                           Is-isomorphism a eq′ x y  □)) ⟩
      ∃ (H {X = C , C-set} {Y = D , D-set} x y)      ↝⟨ inverse ×-right-identity ⟩
      ∃ (H {X = C , C-set} {Y = D , D-set} x y) × ⊤  ↝⟨ ∃-cong (λ X≅Y → inverse $ contractible↔⊤ $ propositional⇒inhabited⇒contractible
                                                                          (Str.Is-isomorphism-propositional X≅Y)
                                                                          (Str-homs-are-isos X≅Y)) ⟩
      (((C , C-set) , x) Str.≅ ((D , D-set) , y))    ↔⟨ inverse ⟨ _ , structure-identity-principle ext Bij S
                                                                        {X = (C , C-set) , x} {Y = (D , D-set) , y} ⟩ ⟩
      (((C , C-set) , x) ≡ ((D , D-set) , y))        ↔⟨ ≃-≡ $ ↔⇒≃ (Σ-assoc ⊚ ∃-cong (λ _ → ×-comm) ⊚ inverse Σ-assoc) ⟩
      (((C , x) , C-set) ≡ ((D , y) , D-set))        ↝⟨ inverse $ ignore-propositional-component (H-level-propositional ext 2) ⟩
      ((C , x) ≡ (D , y))                            ↝⟨ ignore-propositional-component (proj₂ (P D y) ass) ⟩
      (((C , x) , p) ≡ ((D , y) , q))                ↔⟨ ≃-≡ $ ↔⇒≃ Σ-assoc ⟩□
      ((C , x , p) ≡ (D , y , q))                    □

    -- A simplification lemma.

    proj₁-from-isomorphic :
      ∀ X≡Y →
      proj₁ (_↔_.from isomorphic X≡Y) ≡
      elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y) (λ _ → Eq.id) X≡Y
    proj₁-from-isomorphic X≡Y = Eq.lift-equality ext (

      _≃_.to (proj₁ (_↔_.from isomorphic X≡Y))                         ≡⟨⟩

      cast C-set D-set X≡Y                                             ≡⟨ lemma ⟩∎

      _≃_.to (elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y) (λ _ → Eq.id) X≡Y)  ∎)

      where

      cast : ∀ {X Y} →
             Is-set (Carrier (a , P) X) → Is-set (Carrier (a , P) Y) →
             X ≡ Y → Carrier (a , P) X → Carrier (a , P) Y
      cast {C , x , p} {D , y , q} C-set D-set X≡Y =
        proj₁ $ proj₁ $ proj₁ $
        Str.≡→≅ {X = (C , C-set) , x} {Y = (D , D-set) , y} $
        cong (λ { ((C , x) , C-set) → (C , C-set) , x }) $
        Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡
                   (cong (λ { (C , (x , p)) → (C , x) , p }) X≡Y)))
                (proj₁ (H-level-propositional ext 2 _ _))

      lemma :
        cast C-set D-set X≡Y ≡
        _≃_.to (elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y) (λ _ → Eq.id) X≡Y)
      lemma = elim¹
        (λ X≡Y → ∀ D-set → cast C-set D-set X≡Y ≡
                           _≃_.to (elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y)
                                        (λ _ → Eq.id) X≡Y))
        (λ C-set′ →

           cast C-set C-set′ (refl (C , x , p))                      ≡⟨ cong (λ eq →
                                                                                proj₁ $ proj₁ $ proj₁ $
                                                                                Str.≡→≅ {X = (C , C-set) , x} {Y = (C , C-set′) , x} $
                                                                                cong (λ { ((C , x) , C-set) → (C , C-set) , x }) $
                                                                                Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ {B = proj₁ ∘ uncurry P} eq))
                                                                                        (proj₁ (H-level-propositional ext 2 _ _)))
                                                                             (cong-refl (λ { (C , (x , p)) → (C , x) , p })) ⟩
           (proj₁ $ proj₁ $ proj₁ $
            Str.≡→≅ {X = (C , C-set) , x} {Y = (C , C-set′) , x} $
            cong (λ { ((C , x) , C-set) → (C , C-set) , x }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (H-level-propositional ext 2 _ _)))       ≡⟨ cong proj₁ (S.proj₁-≡→≅-¹ _) ⟩

           (proj₁ $
            Fun.≡→≅ $
            cong proj₁ $
            cong (λ { ((C , x) , C-set) → (C , C-set) , x }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (H-level-propositional ext 2 _ _)))       ≡⟨ cong (proj₁ ∘ Fun.≡→≅) $
                                                                          cong-∘ proj₁ (λ { ((C , x) , C-set) → (C , C-set) , x }) _ ⟩
           (proj₁ $
            Fun.≡→≅ $
            cong (λ { ((C , _) , C-set) → C , C-set }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (H-level-propositional ext 2 _ _)))       ≡⟨ Fun.≡→≅-¹ _ ⟩

           (elim (λ {X Y} _ → Fun.Hom X Y) (λ _ → P.id) $
            cong (λ { ((C , _) , C-set) → C , C-set }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (H-level-propositional ext 2 _ _)))       ≡⟨ elim¹ (λ eq → elim (λ {X Y} _ → Fun.Hom X Y) (λ _ → P.id) eq ≡
                                                                                      ≡⇒↝ implication (cong proj₁ eq))
                        (elim (λ {X Y} _ → Fun.Hom X Y) (λ _ → P.id)
                              (refl (C , C-set))                          ≡⟨ elim-refl (λ {X Y} _ → Fun.Hom X Y) _ ⟩
                         P.id                                             ≡⟨ sym $ elim-refl (λ {A B} _ → A → B) _ ⟩
                         ≡⇒↝ implication (refl C)                         ≡⟨ cong (≡⇒↝ implication) (sym $ cong-refl proj₁) ⟩∎
                         ≡⇒↝ implication (cong proj₁ (refl (C , C-set)))  ∎) _ ⟩

           (≡⇒↝ implication $
            cong proj₁ $
            cong (λ { ((C , _) , C-set) → C , C-set }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (H-level-propositional ext 2 _ _)))       ≡⟨ cong (≡⇒↝ implication)
                                                                             (cong-∘ proj₁ (λ { ((C , _) , C-set) → C , C-set }) _) ⟩
           (≡⇒↝ implication $
            cong (λ { ((C , _) , _) → C }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (H-level-propositional ext 2 _ _)))       ≡⟨ cong (λ eq →
                                                                                ≡⇒↝ implication $
                                                                                cong (λ { ((C , _) , _) → C }) $
                                                                                Σ-≡,≡→≡ (proj₁ {B = λ q → subst (proj₁ ∘ uncurry P) q p ≡ p} eq)
                                                                                        (proj₁ (H-level-propositional ext 2 _ C-set′)))
                                                                             (Σ-≡,≡←≡-refl {B = λ { (C , x) → proj₁ (P C x)}}) ⟩
           (≡⇒↝ implication $
            cong (λ { ((C , _) , _) → C }) $
            Σ-≡,≡→≡ (refl (C , x))
                    (proj₁ (H-level-propositional ext 2 _ _)))       ≡⟨ cong (≡⇒↝ implication ∘ cong (λ { ((C , _) , _) → C }))
                                                                             (Σ-≡,≡→≡-reflˡ (proj₁ (H-level-propositional ext 2 _ _))) ⟩
           (≡⇒↝ implication $
            cong (λ { ((C , _) , _) → C }) $
            cong (_,_ (C , x))
                 (trans (sym $ subst-refl (Is-set ∘ proj₁) C-set)
                        (proj₁ (H-level-propositional ext 2 _ _))))  ≡⟨ cong (≡⇒↝ implication)
                                                                             (cong-∘ (λ { ((C , _) , _) → C }) (_,_ (C , x)) _) ⟩
           (≡⇒↝ implication $
            cong (const C)
                 (trans (sym $ subst-refl (Is-set ∘ proj₁) C-set)
                        (proj₁ (H-level-propositional ext 2 _ _))))  ≡⟨ cong (≡⇒↝ implication) (cong-const _) ⟩

           ≡⇒↝ implication (refl C)                                  ≡⟨ ≡⇒↝-refl ⟩

           P.id                                                      ≡⟨ sym $ cong _≃_.to $ elim-refl (λ {X Y} _ → proj₁ X ≃ proj₁ Y) _ ⟩∎

           _≃_.to (elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y)
                        (λ _ → Eq.id)
                        (refl (C , x , p)))                          ∎)

        X≡Y D-set

abstract

  -- The from component of isomorphism-is-equality′ is equal
  -- to a simple function.

  from-isomorphism-is-equality′ :
    ∀ Univ ass c X Y → let open Universe Univ; open Class Univ in
    (El-set : ∀ {B} → Is-set B → Is-set (El (proj₁ c) B)) →
    ∀ I-set J-set →
    _↔_.from (isomorphism-is-equality′
                Univ ass c X Y El-set I-set J-set) ≡
    elim (λ {X Y} _ → Isomorphic c X Y)
         (λ { (_ , x , _) → Eq.id , resp-id ass (proj₁ c) x })
  from-isomorphism-is-equality′ Univ ass c X Y El-set I-set J-set =
    ext λ eq →
      Σ-≡,≡→≡ (lemma eq) (_⇔_.to set⇔UIP (El-set J-set) _ _)
    where
    open Assumptions ass
    open Universe Univ
    open Class Univ

    lemma :
      ∀ eq →
      proj₁ (_↔_.from (isomorphism-is-equality′
                         Univ ass c X Y El-set I-set J-set) eq) ≡
      proj₁ (elim (λ {X Y} _ → Isomorphic c X Y)
                  (λ { (_ , x , _) → Eq.id , resp-id ass (proj₁ c) x })
                  eq)
    lemma eq =
      proj₁ (_↔_.from (isomorphism-is-equality′
                         Univ ass c X Y El-set I-set J-set) eq)          ≡⟨ Isomorphism-is-equality′.proj₁-from-isomorphic
                                                                              Univ ass _ _ _ _ _ _ _ _ El-set I-set J-set eq ⟩
      elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y) (λ _ → Eq.id) eq              ≡⟨ sym $ elim-∘ (λ {X Y} _ → Isomorphic c X Y) _ proj₁ _ ⟩∎
      proj₁ (elim (λ {X Y} _ → Isomorphic c X Y)
                  (λ { (_ , x , _) → Eq.id , resp-id ass (proj₁ c) x })
                  eq)                                                    ∎
