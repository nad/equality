------------------------------------------------------------------------
-- The structure identity principle can be used to establish that
-- isomorphism coincides with equality (assuming univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module
  Univalence-axiom.Isomorphism-is-equality.Structure-identity-principle
    {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq using (_↔_)
open import Category eq
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq hiding (_∘_; inverse)
open import Function-universe eq renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence using (_⇔_)
open import Prelude as P
open import Structure-identity-principle eq
open import Univalence-axiom eq
open import Univalence-axiom.Isomorphism-is-equality.Simple eq
  using (Assumptions; module Assumptions;
         Universe; module Universe;
         module Class)

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
  open Class Univ using (Carrier; Instance; Isomorphic)

  -- The category of sets and functions.

  Fun : Category (# 2) (# 1)
  Fun = category-Set (# 1) ext (λ _ _ → univ₁)

  module Fun = Category Fun

  -- The category of sets and bijections.

  Bij : Category (# 2) (# 1)
  Bij = category-Set-≅ (# 1) ext (λ _ _ → univ₁)

  module Bij = Category Bij

  -- If two sets are isomorphic, then the underlying types are
  -- equivalent.

  ≅⇒≃ : (C D : Fun.Obj) → C Fun.≅ D → ⌞ C ⌟ ≃ ⌞ D ⌟
  ≅⇒≃ C D = _≃_.from (≃≃≅-Set (# 1) ext C D)

  -- The "standard notion of structure" that the structure identity
  -- principle is instantiated with.

  S : Standard-notion-of-structure (# 1) (# 1) Bij.precategory
  S = record
    { P               = El a ∘ ⌞_⌟
    ; H               = λ {C D} x y C≅D →
                          Is-isomorphism a (≅⇒≃ C D C≅D) x y
    ; H-prop          = λ {C D} → H-prop′ C D
    ; H-id            = λ {C} → H-id′ C
    ; H-∘             = λ {B C D} → H-∘′ B C D
    ; H-antisymmetric = λ {C} → H-antisymmetric′ C
    }
    where

    module Separate-abstract-block where

      abstract

        H-prop′ :
          (C D : Set (# 1))
          {x : El a ⌞ C ⌟} {y : El a ⌞ D ⌟}
          (f : Bij.Hom C D) →
          Is-proposition (Is-isomorphism a (≅⇒≃ C D f) x y)
        H-prop′ _ D _ = El-set (proj₂ D)

        H-id′ :
          (C : Set (# 1)) {x : El a ⌞ C ⌟} →
          Is-isomorphism a (≅⇒≃ C C (Bij.id {X = C})) x x
        H-id′ C {x} =
          resp a (≅⇒≃ C C (Bij.id {X = C})) x  ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
          resp a Eq.id x                       ≡⟨ resp-id ass a x ⟩∎
          x                                    ∎

        H-∘′ :
          (B C D : Set (# 1))
          {x : El a ⌞ B ⌟} {y : El a ⌞ C ⌟} {z : El a ⌞ D ⌟}
          {B≅C : Bij.Hom B C} {C≅D : Bij.Hom C D} →
          Is-isomorphism a (≅⇒≃ B C B≅C) x y →
          Is-isomorphism a (≅⇒≃ C D C≅D) y z →
          Is-isomorphism a
            (≅⇒≃ B D (Bij._∙_ {X = B} {Y = C} {Z = D} C≅D B≅C)) x z
        H-∘′ B C D {x} {y} {z} {B≅C} {C≅D} x≅y y≅z =
          resp a (≅⇒≃ B D (C≅D Bij.∙ B≅C)) x             ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
          resp a (≅⇒≃ C D C≅D ⊚ ≅⇒≃ B C B≅C) x           ≡⟨ resp-preserves-compositions (El a) (resp a) (resp-id ass a)
                                                                                        univ₁ ext (≅⇒≃ B C B≅C) (≅⇒≃ C D C≅D) x ⟩
          resp a (≅⇒≃ C D C≅D) (resp a (≅⇒≃ B C B≅C) x)  ≡⟨ cong (resp a (≅⇒≃ C D C≅D)) x≅y ⟩
          resp a (≅⇒≃ C D C≅D) y                         ≡⟨ y≅z ⟩∎
          z                                              ∎

        H-antisymmetric′ :
          (C : Set (# 1))
          (x y : El a ⌞ C ⌟) →
          Is-isomorphism a (≅⇒≃ C C (Bij.id {X = C})) x y →
          Is-isomorphism a (≅⇒≃ C C (Bij.id {X = C})) y x →
          x ≡ y
        H-antisymmetric′ C x y x≡y _ =
          x                                    ≡⟨ sym $ resp-id ass a x ⟩
          resp a Eq.id x                       ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
          resp a (≅⇒≃ C C (Bij.id {X = C})) x  ≡⟨ x≡y ⟩∎
          y                                    ∎

    open Separate-abstract-block

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

      S.lift-equality {X = D , y} {Y = D , y} (
        C≅D Fun.∙≅ D≅C   ≡⟨ _≃_.from (Fun.≡≃≡¹ {X = D} {Y = D}) (Fun._¹⁻¹ {X = C} {Y = D} C≅D) ⟩∎
        Fun.id≅ {X = D}  ∎) ,

      S.lift-equality {X = C , x} {Y = C , x} (
        D≅C Fun.∙≅ C≅D   ≡⟨ _≃_.from (Fun.≡≃≡¹ {X = C} {Y = C}) (Fun._⁻¹¹ {X = C} {Y = D} C≅D) ⟩∎
        Fun.id≅ {X = C}  ∎)

      where

      D≅C : D Fun.≅ C
      D≅C = Fun._⁻¹≅ {X = C} {Y = D} C≅D

    -- The isomorphism that should be constructed.

    isomorphic : Isomorphic (a , P) (C , x , p) (D , y , q) ↔
                 _≡_ {A = Instance (a , P)} (C , x , p) (D , y , q)
    isomorphic =
      Σ (C ≃ D) (λ eq → Is-isomorphism a eq x y)                   ↝⟨ (let ≃≃≅-CD = ≃≃≅-Set (# 1) ext (C , C-set) (D , D-set) in
                                                                       Σ-cong ≃≃≅-CD (λ eq →
                                                                         let eq′ = _≃_.from ≃≃≅-CD (_≃_.to ≃≃≅-CD eq) in
                                                                         Is-isomorphism a eq  x y  ↝⟨ ≡⇒↝ _ $
                                                                                                      cong (λ eq → Is-isomorphism a eq x y) $ sym $
                                                                                                      _≃_.left-inverse-of ≃≃≅-CD eq ⟩
                                                                         Is-isomorphism a eq′ x y  □)) ⟩
      ∃ (H {X = C , C-set} {Y = D , D-set} x y)                    ↝⟨ inverse ×-right-identity ⟩
      ∃ (H {X = C , C-set} {Y = D , D-set} x y) × ⊤                ↝⟨ ∃-cong (λ X≅Y → inverse $ _⇔_.to contractible⇔↔⊤ $
                                                                                      propositional⇒inhabited⇒contractible
                                                                                        (Str.Is-isomorphism-propositional X≅Y)
                                                                                        (Str-homs-are-isos X≅Y)) ⟩
      (((C , C-set) , x) Str.≅ ((D , D-set) , y))                  ↔⟨ inverse ⟨ _ , structure-identity-principle ext Bij S
                                                                                      {X = (C , C-set) , x} {Y = (D , D-set) , y} ⟩ ⟩
      (((C , λ {_ _} → C-set) , x) ≡ ((D , λ {_ _} → D-set) , y))  ↔⟨ ≃-≡ $ ↔⇒≃ (Σ-assoc ⊚ ∃-cong (λ _ → ×-comm) ⊚ inverse Σ-assoc) ⟩
      (((C , x) , λ {_ _} → C-set) ≡ ((D , y) , λ {_ _} → D-set))  ↝⟨ inverse $ ignore-propositional-component (H-level-propositional ext 2) ⟩
      ((C , x) ≡ (D , y))                                          ↝⟨ ignore-propositional-component (proj₂ (P D y) ass) ⟩
      (((C , x) , p) ≡ ((D , y) , q))                              ↔⟨ ≃-≡ $ ↔⇒≃ Σ-assoc ⟩□
      ((C , x , p) ≡ (D , y , q))                                  □

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
                (proj₁ (+⇒≡ $ H-level-propositional ext 2))

      lemma :
        cast C-set D-set X≡Y ≡
        _≃_.to (elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y) (λ _ → Eq.id) X≡Y)
      lemma = elim¹
        (λ X≡Y → (D-set : Is-set _) →
                 cast C-set D-set X≡Y ≡
                 _≃_.to (elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y)
                              (λ _ → Eq.id) X≡Y))
        (λ C-set′ →

           cast C-set C-set′ (refl (C , x , p))                           ≡⟨ cong (λ eq →
                                                                                     proj₁ $ proj₁ $ proj₁ $
                                                                                     Str.≡→≅ {X = (C , C-set) , x} {Y = (C , C-set′) , x} $
                                                                                     cong (λ { ((C , x) , C-set) → (C , C-set) , x }) $
                                                                                     Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ {B = proj₁ ∘ uncurry P} eq))
                                                                                             (proj₁ (+⇒≡ $ H-level-propositional ext 2)))
                                                                                  (cong-refl (λ { (C , (x , p)) → (C , x) , p })) ⟩
           (proj₁ $ proj₁ $ proj₁ $
            Str.≡→≅ {X = (C , C-set) , x} {Y = (C , C-set′) , x} $
            cong (λ { ((C , x) , C-set) → (C , C-set) , x }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (+⇒≡ $ H-level-propositional ext 2)))          ≡⟨ cong proj₁ (S.proj₁-≡→≅-¹ _) ⟩

           (proj₁ $
            Fun.≡→≅ $
            cong proj₁ $
            cong (λ { ((C , x) , C-set) → (C , C-set) , x }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (+⇒≡ $ H-level-propositional ext 2)))          ≡⟨ cong (proj₁ ∘ Fun.≡→≅) $
                                                                               cong-∘ proj₁ (λ { ((C , x) , C-set) → (C , C-set) , x }) _ ⟩
           (proj₁ $
            Fun.≡→≅ $
            cong (λ { ((C , _) , C-set) → C , C-set }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (+⇒≡ $ H-level-propositional ext 2)))          ≡⟨ Fun.≡→≅-¹ _ ⟩

           (elim (λ {X Y} _ → Fun.Hom X Y) (λ _ → P.id) $
            cong (λ { ((C , _) , C-set) → C , C-set }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (+⇒≡ $ H-level-propositional ext 2)))          ≡⟨ elim¹ (λ eq → elim (λ {X Y} _ → Fun.Hom X Y) (λ _ → P.id) eq ≡
                                                                                      ≡⇒↝ implication (cong proj₁ eq)) (
               elim (λ {X Y} _ → Fun.Hom X Y) (λ _ → P.id)
                    (refl (C , λ {_ _} → C-set))                                        ≡⟨ elim-refl (λ {X Y} _ → Fun.Hom X Y) _ ⟩
               P.id                                                                     ≡⟨ sym $ elim-refl (λ {A B} _ → A → B) _ ⟩
               ≡⇒↝ implication (refl C)                                                 ≡⟨ cong (≡⇒↝ implication) (sym $ cong-refl proj₁) ⟩∎
               ≡⇒↝ implication (cong proj₁ (refl (C , λ {_ _} → C-set)))                ∎) _ ⟩

           (≡⇒↝ implication $
            cong proj₁ $
            cong (λ { ((C , _) , C-set) → C , C-set }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (+⇒≡ $ H-level-propositional ext 2)))          ≡⟨ cong (≡⇒↝ implication)
                                                                                  (cong-∘ proj₁ (λ { ((C , _) , C-set) → C , C-set }) _) ⟩
           (≡⇒↝ implication $
            cong (λ { ((C , _) , _) → C }) $
            Σ-≡,≡→≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p))))
                    (proj₁ (+⇒≡ $ H-level-propositional ext 2)))          ≡⟨ cong (λ (eq : ∃ λ q → subst (proj₁ ∘ uncurry P) q p ≡ p) →
                                                                                     ≡⇒↝ implication $
                                                                                     cong (λ { ((C , _) , _) → C }) $
                                                                                     Σ-≡,≡→≡ (proj₁ eq)
                                                                                             (proj₁ (+⇒≡ $ H-level-propositional ext 2)))
                                                                                  (Σ-≡,≡←≡-refl {B = λ { (C , x) → proj₁ (P C x)}}) ⟩
           (≡⇒↝ implication $
            cong (λ { ((C , _) , _) → C }) $
            Σ-≡,≡→≡ (refl (C , x))
                    (proj₁ (+⇒≡ $ H-level-propositional ext 2)))          ≡⟨ cong (≡⇒↝ implication ∘ cong (λ { ((C , _) , _) → C }))
                                                                                  (Σ-≡,≡→≡-reflˡ (proj₁ (+⇒≡ $ H-level-propositional ext 2))) ⟩
           (≡⇒↝ implication $
            cong (λ { ((C , _) , _) → C }) $
            cong (_,_ (C , x))
                 (trans (sym $ subst-refl (Is-set ∘ proj₁) C-set)
                        (proj₁ (+⇒≡ $ H-level-propositional ext 2))))     ≡⟨ cong (≡⇒↝ implication)
                                                                                  (cong-∘ (λ { ((C , _) , _) → C }) (_,_ (C , x)) _) ⟩
           (≡⇒↝ implication $
            cong (const C)
                 (trans (sym $ subst-refl (Is-set ∘ proj₁) C-set)
                        (proj₁ (+⇒≡ $ H-level-propositional ext 2))))     ≡⟨ cong (≡⇒↝ implication) (cong-const _) ⟩

           ≡⇒↝ implication (refl C)                                       ≡⟨ ≡⇒↝-refl ⟩

           P.id                                                           ≡⟨ sym $ cong _≃_.to $ elim-refl (λ {X Y} _ → proj₁ X ≃ proj₁ Y) _ ⟩∎

           _≃_.to (elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y)
                        (λ _ → Eq.id)
                        (refl (C , x , p)))                               ∎)

        X≡Y D-set

abstract

  -- The from component of isomorphism-is-equality′ is equal
  -- to a simple function.

  from-isomorphism-is-equality′ :
    ∀ Univ ass c X Y → let open Universe Univ; open Class Univ in
    (El-set : ∀ {B} → Is-set B → Is-set (El (proj₁ c) B)) →
    (X-set : Is-set (proj₁ X)) (Y-set : Is-set (proj₁ Y)) →
    _↔_.from (isomorphism-is-equality′
                Univ ass c X Y El-set X-set Y-set) ≡
    elim (λ {X Y} _ → Isomorphic c X Y)
         (λ { (_ , x , _) → Eq.id , resp-id ass (proj₁ c) x })
  from-isomorphism-is-equality′ Univ ass c X Y El-set X-set Y-set =
    apply-ext ext λ eq →
      Σ-≡,≡→≡ (lemma eq) (El-set Y-set _ _)
    where
    open Assumptions ass
    open Universe Univ
    open Class Univ

    lemma :
      ∀ eq →
      proj₁ (_↔_.from (isomorphism-is-equality′
                         Univ ass c X Y El-set X-set Y-set) eq) ≡
      proj₁ (elim (λ {X Y} _ → Isomorphic c X Y)
                  (λ { (_ , x , _) → Eq.id , resp-id ass (proj₁ c) x })
                  eq)
    lemma eq =
      proj₁ (_↔_.from (isomorphism-is-equality′
                         Univ ass c X Y El-set X-set Y-set) eq)          ≡⟨ Isomorphism-is-equality′.proj₁-from-isomorphic
                                                                              Univ ass _ _ _ _ _ _ _ _ El-set X-set Y-set eq ⟩
      elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y) (λ _ → Eq.id) eq              ≡⟨ sym $ elim-∘ (λ {X Y} _ → Isomorphic c X Y) _ proj₁ _ ⟩∎
      proj₁ (elim (λ {X Y} _ → Isomorphic c X Y)
                  (λ { (_ , x , _) → Eq.id , resp-id ass (proj₁ c) x })
                  eq)                                                    ∎
