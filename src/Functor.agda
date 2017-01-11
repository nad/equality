------------------------------------------------------------------------
-- Functors and natural transformations (for 1-categories)
------------------------------------------------------------------------

-- The code is based on the presentation in the HoTT book (but might
-- not follow it exactly).

{-# OPTIONS --without-K #-}

open import Equality

module Functor
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq hiding (id; _∘_; inverse; step-↔; finally-↔)
open import Category eq
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq using (_≃_; module _≃_; ↔⇒≃)
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Prelude as P hiding (id; _^_)

------------------------------------------------------------------------
-- Functors

Functor : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
          Precategory ℓ₁ ℓ₂ → Precategory ℓ₃ ℓ₄ → Set _
Functor C D =
  -- Object map.
  ∃ λ (F₀ : Obj C → Obj D) →

  -- Morphism map.
  ∃ λ (F : ∀ {X Y} → Hom C X Y → Hom D (F₀ X) (F₀ Y)) →

  -- F should be homomorphic with respect to identity and composition.
  (∀ {X} → F (id C {X = X}) ≡ id D) ×
  (∀ {X Y Z} {f : Hom C X Y} {g : Hom C Y Z} →
     F (_∙_ C g f) ≡ _∙_ D (F g) (F f))

  where open Precategory

-- A wrapper.

infix 4 _⇨_

record _⇨_ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
           (C : Precategory ℓ₁ ℓ₂) (D : Precategory ℓ₃ ℓ₄) :
           Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    functor : Functor C D

  open Precategory

  infixr 10 _⊚_ _⊙_

  -- Object map.

  _⊚_ : Obj C → Obj D
  _⊚_ = proj₁ functor

  -- Morphism map.

  _⊙_ : ∀ {X Y} → Hom C X Y → Hom D (_⊚_ X) (_⊚_ Y)
  _⊙_ = proj₁ (proj₂ functor)

  -- The morphism map is homomorphic with respect to identity.

  ⊙-id : ∀ {X} → _⊙_ (id C {X = X}) ≡ id D
  ⊙-id = proj₁ (proj₂ (proj₂ functor))

  -- The morphism map is homomorphic with respect to composition.

  ⊙-∙ : ∀ {X Y Z} {f : Hom C X Y} {g : Hom C Y Z} →
        _⊙_ (_∙_ C g f) ≡ _∙_ D (_⊙_ g) (_⊙_ f)
  ⊙-∙ = proj₂ (proj₂ (proj₂ functor))

open _⇨_ public

private
 module Dummy₁ where
  abstract

   -- The homomorphism properties are propositional (assuming
   -- extensionality).

   functor-properties-propositional :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
     Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄) →
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄}
     (F : C ⇨ D) → let open Precategory in

     Is-proposition ((∀ {X} → F ⊙ id C {X = X} ≡ id D) ×
                     (∀ {X Y Z} {f : Hom C X Y} {g : Hom C Y Z} →
                      F ⊙ (_∙_ C g f) ≡ _∙_ D (F ⊙ g) (F ⊙ f)))

   functor-properties-propositional {ℓ₁} {ℓ₂} ext {D = D} _ = ×-closure 1
     (implicit-Π-closure (lower-extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) ext) 1 λ _ →
      Precategory.Hom-is-set D _ _)
     (implicit-Π-closure (lower-extensionality ℓ₂ lzero     ext) 1 λ _ →
      implicit-Π-closure (lower-extensionality ℓ₂ lzero     ext) 1 λ _ →
      implicit-Π-closure (lower-extensionality ℓ₂ ℓ₁        ext) 1 λ _ →
      implicit-Π-closure (lower-extensionality ℓ₁ ℓ₁        ext) 1 λ _ →
      implicit-Π-closure (lower-extensionality ℓ₁ (ℓ₁ ⊔ ℓ₂) ext) 1 λ _ →
      Precategory.Hom-is-set D _ _)

open Dummy₁ public

private
 module Dummy₂ where
  abstract

   -- Functor equality is equivalent to equality of the corresponding
   -- maps, suitably transported (assuming extensionality).

   equality-characterisation⇨ :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
     Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄) →
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄} {F G : C ⇨ D} →
     let open Precategory in

     (F ≡ G)

       ≃

     ∃ λ (⊚F≡⊚G : _⊚_ F ≡ _⊚_ G) →
         _≡_ {A = ∀ {X Y} → Hom C X Y → Hom D (G ⊚ X) (G ⊚ Y)}
             (subst (λ F → ∀ {X Y} → Hom C X Y → Hom D (F X) (F Y))
                    ⊚F≡⊚G (_⊙_ F))
             (_⊙_ G)

   equality-characterisation⇨ ext {C} {D} {F} {G} =
     let P : (Obj C → Obj D) → Set _
         P = λ F₀ → ∀ {X Y} → Hom C X Y → Hom D (F₀ X) (F₀ Y)

         Q : ∃ P → Set _
         Q = λ { (F₀ , F) → (∀ {X} → F (id C {X = X}) ≡ id D) ×
                            (∀ {X Y Z} {f : Hom C X Y} {g : Hom C Y Z} →
                               F (_∙_ C g f) ≡ _∙_ D (F g) (F f)) }
     in

     (F ≡ G)                                                              ↝⟨ ↔⇒≃ record
                                                                               { surjection = record
                                                                                 { logical-equivalence = record
                                                                                   { to   = cong functor
                                                                                   ; from = cong λ f → record { functor = f }
                                                                                   }
                                                                                 ; right-inverse-of = λ _ → trans (cong-∘ _ _ _) (sym $ cong-id _)
                                                                                 }
                                                                               ; left-inverse-of = λ _ → trans (cong-∘ _ _ _) (sym $ cong-id _)
                                                                               } ⟩
     (functor F ≡ functor G)                                              ↔⟨ inverse Σ-≡,≡↔≡ ⟩

     (∃ λ (⊚F≡⊚G : _⊚_ F ≡ _⊚_ G) →
          subst (λ F₀ → ∃ λ (F : P F₀) → Q (F₀ , F)) ⊚F≡⊚G
                (proj₂ $ functor F) ≡ proj₂ (functor G))                  ↝⟨ ∃-cong (λ ⊚F≡⊚G → ≡⇒↝ _ $ cong (λ x → x ≡ proj₂ (functor G)) $
                                                                               push-subst-pair P Q) ⟩
     (∃ λ (⊚F≡⊚G : _⊚_ F ≡ _⊚_ G) →
          _≡_ {A = ∃ λ (H : P (_⊚_ G)) → Q (_⊚_ G , H)}
          ( subst P ⊚F≡⊚G (_⊙_ F)
          , subst Q (Σ-≡,≡→≡ ⊚F≡⊚G (refl _)) (proj₂ $ proj₂ $ functor F)
          )
          (proj₂ (functor G)))                                            ↔⟨ ∃-cong (λ ⊚F≡⊚G → inverse $
                                                                               ignore-propositional-component
                                                                                 (functor-properties-propositional ext G)) ⟩□
     (∃ λ (⊚F≡⊚G : _⊚_ F ≡ _⊚_ G) →
          (λ {_ _} → subst P ⊚F≡⊚G (_⊙_ F)) ≡ _⊙_ G)                      □

     where open Precategory

   -- Some simplification lemmas.

   proj₁-to-equality-characterisation⇨ :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
     (ext : Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄))
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄} {F G : C ⇨ D} →
     let open Precategory in
     (F≡G : F ≡ G) →

     proj₁ (_≃_.to (equality-characterisation⇨ ext {F = F} {G = G}) F≡G)
       ≡
     cong _⊚_ F≡G

   proj₁-to-equality-characterisation⇨ ext F≡G =
     proj₁ (_≃_.to (equality-characterisation⇨ ext) F≡G)  ≡⟨ proj₁-Σ-≡,≡←≡ _ ⟩
     cong proj₁ (cong functor F≡G)                        ≡⟨ cong-∘ _ _ _ ⟩∎
     cong _⊚_ F≡G                                         ∎

   cong-⊚-from-equality-characterisation⇨ :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
     (ext : Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄))
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄} {F G : C ⇨ D} →
     let open Precategory in
     (⊚F≡⊚G : _⊚_ F ≡ _⊚_ G) →
     (⊙F≡⊙G : _≡_ {A = ∀ {X Y} → Hom C X Y → Hom D (G ⊚ X) (G ⊚ Y)}
                  (subst (λ F → ∀ {X Y} → Hom C X Y → Hom D (F X) (F Y))
                         ⊚F≡⊚G (_⊙_ F))
                  (_⊙_ G)) →

     cong _⊚_ (_≃_.from (equality-characterisation⇨ ext {F = F} {G = G})
                        (⊚F≡⊚G , ⊙F≡⊙G))
       ≡
     ⊚F≡⊚G

   cong-⊚-from-equality-characterisation⇨ ext {F = F} {G} ⊚F≡⊚G ⊙F≡⊙G =
     cong _⊚_ (_≃_.from (equality-characterisation⇨ ext {F = F} {G = G})
                        (⊚F≡⊚G , ⊙F≡⊙G))                                  ≡⟨ cong-∘ _ _ _ ⟩

     cong proj₁ (Σ-≡,≡→≡ ⊚F≡⊚G _)                                         ≡⟨ proj₁-Σ-≡,≡→≡ _ _ ⟩∎

     ⊚F≡⊚G                                                                ∎

open Dummy₂ public

private
 module Dummy₃ where
  abstract

   -- Another equality characterisation lemma.

   equality-characterisation≡⇨ :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
     Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄) →
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄} {F G : C ⇨ D}
     {eq₁ eq₂ : F ≡ G} →
     (eq₁ ≡ eq₂) ≃ (cong _⊚_ eq₁ ≡ cong _⊚_ eq₂)
   equality-characterisation≡⇨ {ℓ₁} {ℓ₂} ext {D = D} {eq₁ = eq₁} {eq₂} =
     eq₁ ≡ eq₂                                              ↝⟨ inverse $ Eq.≃-≡ (equality-characterisation⇨ ext) ⟩

     _≃_.to (equality-characterisation⇨ ext) eq₁ ≡
     _≃_.to (equality-characterisation⇨ ext) eq₂            ↔⟨ inverse $ ignore-propositional-component $
                                                                 (implicit-Π-closure (lower-extensionality ℓ₂ lzero     ext) 2 λ _ →
                                                                  implicit-Π-closure (lower-extensionality ℓ₂ ℓ₁        ext) 2 λ _ →
                                                                  Π-closure          (lower-extensionality ℓ₁ (ℓ₁ ⊔ ℓ₂) ext) 2 λ _ →
                                                                  Precategory.Hom-is-set D) _ _ ⟩
     proj₁ (_≃_.to (equality-characterisation⇨ ext) eq₁) ≡
     proj₁ (_≃_.to (equality-characterisation⇨ ext) eq₂)    ↝⟨ ≡⇒↝ _ (cong₂ _≡_ (proj₁-to-equality-characterisation⇨ _ _)
                                                                                (proj₁-to-equality-characterisation⇨ _ _)) ⟩□
     cong _⊚_ eq₁ ≡ cong _⊚_ eq₂                            □

open Dummy₃ public

------------------------------------------------------------------------
-- Natural transformations

Natural-transformation :
  ∀ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
    {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄} →
  C ⇨ D → C ⇨ D → Set _
Natural-transformation {C = C} {D = D} F G =
  -- Morphisms.
  ∃ λ (γ : ∀ {X} → Hom D (F ⊚ X) (G ⊚ X)) →

  -- Naturality.
  ∀ {X Y} {f : Hom C X Y} → (G ⊙ f) ∙ γ ≡ γ ∙ (F ⊙ f)

  where
  open Precategory hiding (_∙_)
  open Precategory D using (_∙_)

-- A wrapper.

infix 4 _⇾_

record _⇾_ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
           {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄}
           (F G : C ⇨ D) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    natural-transformation : Natural-transformation F G

  open Precategory hiding (_∙_)
  open Precategory D using (_∙_)

  -- Morphisms.

  transformation : ∀ {X} → Hom D (F ⊚ X) (G ⊚ X)
  transformation = proj₁ natural-transformation

  -- Naturality.

  natural : ∀ {X Y} {f : Hom C X Y} →
            (G ⊙ f) ∙ transformation ≡ transformation ∙ (F ⊙ f)
  natural = proj₂ natural-transformation

private
 module Dummy₄ where
  abstract

   -- The naturality property is a proposition (assuming
   -- extensionality).

   naturality-propositional :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
     Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄) →
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄}
     (F G : C ⇨ D) →
     let open Precategory hiding (_∙_); open Precategory D using (_∙_) in
     {transformation : ∀ {X} → Hom D (F ⊚ X) (G ⊚ X)} →

     Is-proposition (∀ {X Y} {f : Hom C X Y} →
                     (G ⊙ f) ∙ transformation ≡
                     transformation ∙ (F ⊙ f))

   naturality-propositional {ℓ₁} {ℓ₂} ext {D = D} _ _ =
     implicit-Π-closure (lower-extensionality ℓ₂ lzero     ext) 1 λ _ →
     implicit-Π-closure (lower-extensionality ℓ₂ ℓ₁        ext) 1 λ _ →
     implicit-Π-closure (lower-extensionality ℓ₁ (ℓ₁ ⊔ ℓ₂) ext) 1 λ _ →
     Precategory.Hom-is-set D _ _

   -- Natural transformation equality is equivalent to pointwise
   -- equality of the corresponding "transformations" (assuming
   -- extensionality).

   equality-characterisation⇾ :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
     Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄) →
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄}
     {F G : C ⇨ D} {γ δ : F ⇾ G} →

     (γ ≡ δ)
       ≃
     (∀ {X} → _⇾_.transformation γ {X = X} ≡
              _⇾_.transformation δ {X = X})

   equality-characterisation⇾ {ℓ₁} {ℓ₂} ext {F = F} {G} {γ} {δ} =
     γ ≡ δ                                                          ↝⟨ inverse $ Eq.≃-≡ $ ↔⇒≃ record
                                                                         { surjection = record
                                                                           { logical-equivalence = record
                                                                             { to   = _⇾_.natural-transformation
                                                                             ; from = λ γ → record { natural-transformation = γ }
                                                                             }
                                                                           ; right-inverse-of = refl
                                                                           }
                                                                         ; left-inverse-of = refl
                                                                         } ⟩
     _⇾_.natural-transformation γ ≡ _⇾_.natural-transformation δ    ↔⟨ inverse $ ignore-propositional-component
                                                                                   (naturality-propositional ext F G) ⟩
     (λ {X} → _⇾_.transformation γ {X = X}) ≡ _⇾_.transformation δ  ↝⟨ inverse $ Eq.≃-≡ (Eq.↔⇒≃ implicit-Π↔Π) ⟩

     (λ X → _⇾_.transformation γ {X = X}) ≡
     (λ X → _⇾_.transformation δ {X = X})                           ↝⟨ inverse $ Eq.extensionality-isomorphism
                                                                                   (lower-extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) ext) ⟩
     (∀ X → _⇾_.transformation γ {X = X} ≡
            _⇾_.transformation δ {X = X})                           ↔⟨ inverse implicit-Π↔Π ⟩□

     (∀ {X} → _⇾_.transformation γ {X = X} ≡
              _⇾_.transformation δ {X = X})                         □

   -- Natural transformations form sets (assuming extensionality).

   ⇾-set :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
     Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄) →
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄} {F G : C ⇨ D} →
     Is-set (F ⇾ G)
   ⇾-set {ℓ₁} {ℓ₂} ext {D = D} {F = F} {G = G} =
     let surj = record
           { logical-equivalence = record
             { to   = λ γ → record { natural-transformation = γ }
             ; from = _⇾_.natural-transformation
             }
           ; right-inverse-of = refl
           } in

     respects-surjection surj 2 $
       Σ-closure 2
         (implicit-Π-closure
            (lower-extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) ext) 2 λ _ →
          Precategory.Hom-is-set D)
         (λ _ → mono₁ 1 $ naturality-propositional ext F G)

open Dummy₄ public

-- Identity natural transformation.

id⇾ : ∀ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
        {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄}
      (F : C ⇨ D) → F ⇾ F
id⇾ {C = C} {D = D} F =
  record { natural-transformation = id , Dummy₅.nat }
  where
  open Precategory D

  module Dummy₅ where
   abstract

    nat : ∀ {X Y} {f : Precategory.Hom C X Y} →
          (F ⊙ f) ∙ id ≡ id ∙ (F ⊙ f)
    nat {f = f} =
      (F ⊙ f) ∙ id  ≡⟨ right-identity ⟩
      F ⊙ f         ≡⟨ sym $ left-identity ⟩∎
      id ∙ (F ⊙ f)  ∎

-- Composition of natural transformations.

infixr 10 _∙⇾_

_∙⇾_ : ∀ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
         {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄}
         {F G H : C ⇨ D} →
       G ⇾ H → F ⇾ G → F ⇾ H
_∙⇾_ {C = C} {D = D} {F} {G} {H} γ δ =
  record { natural-transformation = ε , Dummy₅.nat }
  where
  open Precategory D
  open _⇾_

  ε : ∀ {X} → Hom (F ⊚ X) (H ⊚ X)
  ε = transformation γ ∙ transformation δ

  module Dummy₅ where
   abstract

    nat : ∀ {X Y} {f : Precategory.Hom C X Y} →
          (H ⊙ f) ∙ ε ≡ ε ∙ (F ⊙ f)
    nat {f = f} =
      (H ⊙ f) ∙ (transformation γ ∙ transformation δ)  ≡⟨ assoc ⟩
      ((H ⊙ f) ∙ transformation γ) ∙ transformation δ  ≡⟨ cong (λ f → f ∙ _) $ natural γ ⟩
      (transformation γ ∙ (G ⊙ f)) ∙ transformation δ  ≡⟨ sym assoc ⟩
      transformation γ ∙ ((G ⊙ f) ∙ transformation δ)  ≡⟨ cong (_∙_ _) $ natural δ ⟩
      transformation γ ∙ (transformation δ ∙ (F ⊙ f))  ≡⟨ assoc ⟩∎
      (transformation γ ∙ transformation δ) ∙ (F ⊙ f)  ∎

------------------------------------------------------------------------
-- Functor precategories

-- Functor precategories are defined using extensionality.

infix 10 _^_

_^_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
      Precategory ℓ₁ ℓ₂ → Precategory ℓ₃ ℓ₄ →
      Extensionality (ℓ₃ ⊔ ℓ₄) (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) →
      Precategory _ _
(D ^ C) ext = record
  { precategory =
        (C ⇨ D)
      , (λ F G → (F ⇾ G) , ⇾-set ext)
      , id⇾ _
      , _∙⇾_
      , _≃_.from (equality-characterisation⇾ ext) left-identity
      , _≃_.from (equality-characterisation⇾ ext) right-identity
      , _≃_.from (equality-characterisation⇾ ext) assoc
  }
  where
  open Precategory D

private
 module Dummy₅ where
  abstract

   -- The natural transformation γ is an isomorphism in (D ^ C) ext iff
   -- _⇾_.transformation γ {X = X} is an isomorphism in D for every X.

   natural-isomorphism-lemma :
     ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
     (ext : Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)) →
     {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄}
     {F G : C ⇨ D} {γ : F ⇾ G} → let open Precategory in

     Is-isomorphism ((D ^ C) ext) γ ⇔
     (∀ {X} → Is-isomorphism D (_⇾_.transformation γ {X = X}))

   natural-isomorphism-lemma ext {D = D} {F} {G} {γ} = record
     { to = λ { (δ , γδ , δγ) →
         transformation δ ,
         (transformation γ ∙ transformation δ  ≡⟨⟩
          transformation (γ ∙⇾ δ)              ≡⟨ cong (λ ε → transformation ε) γδ ⟩
          transformation (id⇾ G)               ≡⟨⟩
          id                                   ∎) ,
         (transformation δ ∙ transformation γ  ≡⟨⟩
          transformation (δ ∙⇾ γ)              ≡⟨ cong (λ ε → transformation ε) δγ ⟩
          transformation (id⇾ F)               ≡⟨⟩
          id                                   ∎) }
     ; from = λ iso →
         record { natural-transformation =
           proj₁ iso ,
           (λ {_ _ f} →
                (F ⊙ f) ∙ proj₁ iso                                     ≡⟨ sym left-identity ⟩
                id ∙ (F ⊙ f) ∙ proj₁ iso                                ≡⟨ cong (λ g → g ∙ (F ⊙ f) ∙ proj₁ iso) $ sym $ proj₂ (proj₂ iso) ⟩
                (proj₁ iso ∙ transformation γ) ∙ (F ⊙ f) ∙ proj₁ iso    ≡⟨ sym assoc ⟩
                proj₁ iso ∙ (transformation γ ∙ (F ⊙ f) ∙ proj₁ iso)    ≡⟨ cong (_ ∙_) assoc ⟩
                proj₁ iso ∙ ((transformation γ ∙ (F ⊙ f)) ∙ proj₁ iso)  ≡⟨ cong (λ g → _ ∙ (g ∙ _)) $ sym $ natural γ ⟩
                proj₁ iso ∙ (((G ⊙ f) ∙ transformation γ) ∙ proj₁ iso)  ≡⟨ cong (_ ∙_) $ sym assoc ⟩
                proj₁ iso ∙ (G ⊙ f) ∙ (transformation γ ∙ proj₁ iso)    ≡⟨ cong ((_ ∙_) ∘ (_ ∙_)) $ proj₁ (proj₂ iso) ⟩
                proj₁ iso ∙ (G ⊙ f) ∙ id                                ≡⟨ assoc ⟩
                (proj₁ iso ∙ (G ⊙ f)) ∙ id                              ≡⟨ right-identity ⟩∎
                proj₁ iso ∙ (G ⊙ f)                                     ∎) } ,
         _≃_.from (equality-characterisation⇾ ext) (proj₁ (proj₂ iso)) ,
         _≃_.from (equality-characterisation⇾ ext) (proj₂ (proj₂ iso))
     }
     where
     open Precategory D
     open _⇾_

open Dummy₅ public

abstract

  -- If D is a category, then (D ^ C) ext is also a category.

  infix 10 _↑_

  _↑_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
        Category ℓ₁ ℓ₂ → Precategory ℓ₃ ℓ₄ →
        Extensionality (ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) →
        Category (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
  _↑_ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} D C ext = record { category =
    D^C ,

    (λ {F G} → _≃_.is-equivalence $ ↔⇒≃ $ record
       { surjection = record
         { logical-equivalence = record
           { to   = Precategory.≡→≅ D^C
           ; from = λ { (F⇾G , F⇾G-iso) →

               let γ : ∀ X → F ⊚ X ≅ G ⊚ X
                   γ _ = _⇾_.transformation F⇾G ,
                         _⇔_.to (natural-isomorphism-lemma ext₁) F⇾G-iso

                   ⊚F≡⊚G : _⊚_ F ≡ _⊚_ G
                   ⊚F≡⊚G = Eq.good-ext ext₂ λ X →
                     F ⊚ X  ≡⟨ ≅→≡ (γ X) ⟩∎
                     G ⊚ X  ∎

                   cong-⊚F≡⊚G : ∀ {X} → cong (λ H → H X) ⊚F≡⊚G ≡ ≅→≡ (γ X)
                   cong-⊚F≡⊚G = Eq.cong-good-ext ext₂ (≅→≡ ∘ γ)

                   ⊙F≡⊙G : _≡_ {A = ∀ {X Y} → HomC X Y → Hom (G ⊚ X) (G ⊚ Y)}
                               (subst (λ F → ∀ {X Y} → HomC X Y → Hom (F X) (F Y))
                                      ⊚F≡⊚G
                                      (_⊙_ F))
                               (_⊙_ G)
                   ⊙F≡⊙G =
                     implicit-extensionality (lower-extensionality ℓ₄ ℓ₁        ext) λ X →
                     implicit-extensionality (lower-extensionality ℓ₄ (ℓ₁ ⊔ ℓ₃) ext) λ Y →
                     lower-extensionality ℓ₃ (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄) ext λ f →

                     subst (λ F → ∀ {X Y} → HomC X Y → Hom (F X) (F Y))
                           ⊚F≡⊚G (_⊙_ F) f                               ≡⟨ cong (λ H → H f) $ sym $
                                                                                 push-subst-implicit-application ⊚F≡⊚G
                                                                                   (λ X F → ∀ {Y} → HomC X Y → Hom (F X) (F Y)) ⟩
                     subst (λ F → ∀ {Y} → HomC X Y → Hom (F X) (F Y))
                           ⊚F≡⊚G (_⊙_ F) f                               ≡⟨ cong (λ H → H f) $ sym $
                                                                                 push-subst-implicit-application ⊚F≡⊚G
                                                                                   (λ Y F → HomC X Y → Hom (F X) (F Y)) ⟩
                     subst (λ F → HomC X Y → Hom (F X) (F Y))
                           ⊚F≡⊚G (_⊙_ F) f                               ≡⟨ sym $ push-subst-application ⊚F≡⊚G
                                                                                    (λ _ F → Hom (F X) (F Y)) ⟩
                     subst (λ F → Hom (F X) (F Y)) ⊚F≡⊚G (F ⊙ f)         ≡⟨ subst-∘ (uncurry Hom) (λ H → (H X , H Y)) ⊚F≡⊚G ⟩

                     subst (uncurry Hom)
                           (cong (λ H → (H X , H Y)) ⊚F≡⊚G) (F ⊙ f)      ≡⟨ cong (λ p → subst (uncurry Hom) p (F ⊙ f)) $ sym $
                                                                                 cong₂-cong-cong {eq = ⊚F≡⊚G} (λ H → H X) (λ H → H Y) _,_ ⟩
                     subst (uncurry Hom)
                           (cong₂ _,_ (cong (λ H → H X) ⊚F≡⊚G)
                                      (cong (λ H → H Y) ⊚F≡⊚G)) (F ⊙ f)  ≡⟨ cong₂ (λ p q → subst (uncurry Hom) (cong₂ _,_ p q) (F ⊙ f))
                                                                                  cong-⊚F≡⊚G cong-⊚F≡⊚G ⟩
                     subst (uncurry Hom)
                           (cong₂ _,_ (≅→≡ (γ X)) (≅→≡ (γ Y))) (F ⊙ f)   ≡⟨ Hom-, (≅→≡ (γ X)) (≅→≡ (γ Y)) ⟩

                     ≡→≅ (≅→≡ (γ Y)) ¹ ∙ (F ⊙ f) ∙ ≡→≅ (≅→≡ (γ X)) ⁻¹    ≡⟨ cong₂ (λ p q → p ¹ ∙ (F ⊙ f) ∙ q ⁻¹)
                                                                                  (_≃_.right-inverse-of ≡≃≅ _)
                                                                                  (_≃_.right-inverse-of ≡≃≅ _) ⟩
                     γ Y ¹ ∙ (F ⊙ f) ∙ γ X ⁻¹                            ≡⟨ assoc ⟩

                     (γ Y ¹ ∙ (F ⊙ f)) ∙ γ X ⁻¹                          ≡⟨ cong (_∙ γ X ⁻¹) $ sym $ _⇾_.natural F⇾G ⟩

                     ((G ⊙ f) ∙ γ X ¹) ∙ γ X ⁻¹                          ≡⟨ sym assoc ⟩

                     (G ⊙ f) ∙ γ X ¹ ∙ γ X ⁻¹                            ≡⟨ cong (_ ∙_) $ γ X ¹⁻¹ ⟩

                     (G ⊙ f) ∙ id                                        ≡⟨ right-identity ⟩∎

                     G ⊙ f                                               ∎

               in _≃_.from (equality-characterisation⇨ ext₁)
                           (⊚F≡⊚G , ⊙F≡⊙G) }
           }
         ; right-inverse-of = λ { (F⇾G , F⇾G-iso) →
             _≃_.from (Precategory.≡≃≡¹ D^C) $
             _≃_.from (equality-characterisation⇾ ext₁) λ {X} →
               _⇾_.transformation (proj₁ (Precategory.≡→≅ D^C _))         ≡⟨⟩

               _⇾_.transformation
                 (proj₁ (elim (λ {F G} _ → Precategory._≅_ D^C F G)
                              (λ _ → Precategory.id≅ D^C) _))             ≡⟨ elim (λ {F G} F≡G →
                                                                                     _⇾_.transformation (proj₁ (Precategory.≡→≅ D^C F≡G)) ≡
                                                                                     elim (λ {F G} _ → Hom (F X) (G X)) (λ _ → id) (cong _⊚_ F≡G))
                                                                                  (λ F →
                   _⇾_.transformation
                     (proj₁ (elim (λ {F G} _ → Precategory._≅_ D^C F G)
                                  (λ _ → Precategory.id≅ D^C) (refl F)))             ≡⟨ cong (λ f → _⇾_.transformation (proj₁ f) {X = X}) $
                                                                                          elim-refl (λ {X Y} _ → Precategory._≅_ D^C X Y) _ ⟩
                   _⇾_.transformation {F = F}
                     (proj₁ (Precategory.id≅ D^C))                                   ≡⟨⟩

                   id                                                                ≡⟨ sym $ elim-refl (λ {F G} _ → Hom (F X) (G X)) _ ⟩

                   elim (λ {F G} _ → Hom (F X) (G X))
                        (λ _ → id) (refl (_⊚_ F))                                    ≡⟨ cong (elim (λ {F G} _ → Hom (F X) (G X)) _) $
                                                                                          sym $ cong-refl _⊚_ ⟩∎
                   elim (λ {F G} _ → Hom (F X) (G X))
                        (λ _ → id) (cong _⊚_ (refl F))                               ∎)
                                                                                  _ ⟩
               elim (λ {F G} _ → Hom (F X) (G X))
                    (λ _ → id) (cong _⊚_ _)                               ≡⟨ cong (elim (λ {F G} _ → Hom (F X) (G X)) (λ _ → id)) $
                                                                               cong-⊚-from-equality-characterisation⇨ _ _ _ ⟩
               elim (λ {F G} _ → Hom (F X) (G X)) (λ _ → id)
                    (Eq.good-ext ext₂ λ Y →
                       ≅→≡ (_⇾_.transformation F⇾G {X = Y} , _))          ≡⟨ Eq.elim-good-ext ext₂ _ _ _ ⟩

               elim (λ {X Y} _ → Hom X Y) (λ _ → id)
                    (≅→≡ (_⇾_.transformation F⇾G {X = X} , _))            ≡⟨ elim (λ {X Y} X≡Y → elim (λ {X Y} _ → Hom X Y) (λ _ → id) X≡Y ≡
                                                                                                 proj₁ (≡→≅ X≡Y))
                                                                                  (λ X →
                   elim (λ {X Y} _ → Hom X Y) (λ _ → id) (refl X)                    ≡⟨ elim-refl (λ {X Y} _ → Hom X Y) _ ⟩
                   id                                                                ≡⟨⟩
                   proj₁ id≅                                                         ≡⟨ cong proj₁ (sym ≡→≅-refl) ⟩∎
                   proj₁ (≡→≅ (refl X))                                              ∎ )
                                                                                  _ ⟩
               proj₁ (≡→≅ (≅→≡ (_⇾_.transformation F⇾G {X = X} , _)))     ≡⟨ cong proj₁ (_≃_.right-inverse-of ≡≃≅ _) ⟩∎

               _⇾_.transformation F⇾G {X = X}                             ∎ }
           }
       ; left-inverse-of = λ F≡G →
           _≃_.from (equality-characterisation≡⇨ ext₁) (
              cong _⊚_ _                                           ≡⟨ cong-⊚-from-equality-characterisation⇨ _ _ _ ⟩

              Eq.good-ext ext₂ (λ X →
                ≅→≡ ( _⇾_.transformation
                        (proj₁ $ Precategory.≡→≅ D^C F≡G) {X = X}
                    , _
                    ))                                             ≡⟨ elim
                                                                        (λ {F G} F≡G → (f : (X : _) → _) →
                                                                           Eq.good-ext ext₂ (λ X →
                                                                             ≅→≡ (_⇾_.transformation (proj₁ $ Precategory.≡→≅ D^C F≡G) , f X)) ≡
                                                                           cong _⊚_ F≡G)
                                                                        (λ F _ →
                  Eq.good-ext ext₂ (λ _ →
                    ≅→≡ ( _⇾_.transformation
                            (proj₁ $ Precategory.≡→≅ D^C (refl F))
                        , _
                        ))                                                  ≡⟨ cong (Eq.good-ext ext₂) (ext₂ λ X → cong ≅→≡ $
                                                                                 Σ-≡,≡→≡ (cong (λ f → _⇾_.transformation (proj₁ f) {X = X}) $
                                                                                            Precategory.≡→≅-refl D^C)
                                                                                         (refl _)) ⟩
                  Eq.good-ext ext₂ (λ _ →
                    ≅→≡ ( _⇾_.transformation {F = F}
                            (proj₁ $ Precategory.id≅ D^C)
                        , _
                        ))                                                  ≡⟨⟩

                  Eq.good-ext ext₂ (λ _ → ≅→≡ (id , _))                     ≡⟨ cong (Eq.good-ext ext₂) (ext₂ λ _ →
                                                                                 cong ≅→≡ $ _≃_.from ≡≃≡¹ $ refl _) ⟩
                  Eq.good-ext ext₂ (λ _ → ≅→≡ id≅)                          ≡⟨ cong (Eq.good-ext ext₂) (ext₂ λ _ → ≅→≡-refl) ⟩

                  Eq.good-ext ext₂ (λ X → refl (F ⊚ X))                     ≡⟨ Eq.good-ext-refl ext₂ _ ⟩

                  refl (_⊚_ F)                                              ≡⟨ sym $ cong-refl _ ⟩∎

                  cong _⊚_ (refl F)                                         ∎)
                                                                        F≡G _ ⟩∎
              cong _⊚_ F≡G                                         ∎)
       }) }
    where
    open Category D
    open Precategory C using () renaming (Hom to HomC)

    ext₁ : Extensionality (ℓ₃ ⊔ ℓ₄) (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
    ext₁ = lower-extensionality lzero ℓ₁ ext

    ext₂ : Extensionality ℓ₃ ℓ₁
    ext₂ = lower-extensionality ℓ₄ (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) ext

    D^C : Precategory (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
    D^C = (precategory ^ C) ext₁
