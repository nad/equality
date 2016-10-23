------------------------------------------------------------------------
-- Functors and natural transformations (for 1-categories)
------------------------------------------------------------------------

-- Based on a draft of the chapter "Category theory" from "Homotopy
-- Type Theory: Univalent Foundations of Mathematics". I think the
-- parts of this chapter that I make use of were written by Mike
-- Shulman.

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
     F (_∙_ C f g) ≡ _∙_ D (F f) (F g))

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
        _⊙_ (_∙_ C f g) ≡ _∙_ D (_⊙_ f) (_⊙_ g)
  ⊙-∙ = proj₂ (proj₂ (proj₂ functor))

open _⇨_ public

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
                     F ⊙ (_∙_ C f g) ≡ _∙_ D (F ⊙ f) (F ⊙ g)))

  functor-properties-propositional {ℓ₁} {ℓ₂} ext {D = D} _ = ×-closure 1
    (implicit-Π-closure (lower-extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) ext) 1 λ _ →
     Precategory.Hom-is-set D _ _)
    (implicit-Π-closure (lower-extensionality ℓ₂ lzero     ext) 1 λ _ →
     implicit-Π-closure (lower-extensionality ℓ₂ lzero     ext) 1 λ _ →
     implicit-Π-closure (lower-extensionality ℓ₂ ℓ₁        ext) 1 λ _ →
     implicit-Π-closure (lower-extensionality ℓ₁ ℓ₁        ext) 1 λ _ →
     implicit-Π-closure (lower-extensionality ℓ₁ (ℓ₁ ⊔ ℓ₂) ext) 1 λ _ →
     Precategory.Hom-is-set D _ _)

  -- Functor equality is equivalent to equality of the corresponding
  -- maps, suitably transported (assuming extensionality).

  ≡≃≡⊚≡⊙ :
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

  ≡≃≡⊚≡⊙ ext {C} {D} {F} {G} =
    let P : (Obj C → Obj D) → Set _
        P = λ F₀ → ∀ {X Y} → Hom C X Y → Hom D (F₀ X) (F₀ Y)

        Q : ∃ P → Set _
        Q = λ { (F₀ , F) → (∀ {X} → F (id C {X = X}) ≡ id D) ×
                           (∀ {X Y Z} {f : Hom C X Y} {g : Hom C Y Z} →
                              F (_∙_ C f g) ≡ _∙_ D (F f) (F g)) }
    in

    (F ≡ G)                                                              ↝⟨ inverse $ Eq.≃-≡ $ ↔⇒≃ record
                                                                              { surjection = record
                                                                                { logical-equivalence = record
                                                                                  { to   = functor
                                                                                  ; from = λ f → record { functor = f }
                                                                                  }
                                                                                ; right-inverse-of = refl
                                                                                }
                                                                              ; left-inverse-of = refl
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
  ∀ {X Y} {f : Hom C X Y} → γ ∙ (G ⊙ f) ≡ (F ⊙ f) ∙ γ

  where
  open Precategory hiding (_∙_)
  open Precategory D using (_∙_)

-- A wrapper.

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
            transformation ∙ (G ⊙ f) ≡ (F ⊙ f) ∙ transformation
  natural = proj₂ natural-transformation

abstract

  -- The naturality property is a proposition (assuming extensionality).

  naturality-propositional :
    ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄) →
    {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄}
    (F G : C ⇨ D) →
    let open Precategory hiding (_∙_); open Precategory D using (_∙_) in
    {transformation : ∀ {X} → Hom D (F ⊚ X) (G ⊚ X)} →

    Is-proposition (∀ {X Y} {f : Hom C X Y} →
                      transformation ∙ (G ⊙ f) ≡
                      (F ⊙ f) ∙ transformation)

  naturality-propositional {ℓ₁} {ℓ₂} ext {D = D} _ _ =
    implicit-Π-closure (lower-extensionality ℓ₂ lzero     ext) 1 λ _ →
    implicit-Π-closure (lower-extensionality ℓ₂ ℓ₁        ext) 1 λ _ →
    implicit-Π-closure (lower-extensionality ℓ₁ (ℓ₁ ⊔ ℓ₂) ext) 1 λ _ →
    Precategory.Hom-is-set D _ _

  -- Two natural transformations are equal if the corresponding
  -- "transformations" are pointwise equal (assuming extensionality).

  -- TODO: Update.

  [_,_]⇾ :
    ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
    Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄) →
    {C : Precategory ℓ₁ ℓ₂} {D : Precategory ℓ₃ ℓ₄}
    {F G : C ⇨ D} {γ δ : F ⇾ G} →

    (∀ {X} → _⇾_.transformation γ {X = X} ≡
             _⇾_.transformation δ {X = X}) →
    γ ≡ δ

  [_,_]⇾ {ℓ₁} {ℓ₂} ext {C} {D = D} {F} {G} tγ≡tδ =
    cong (λ nt → record { natural-transformation = nt }) $
         Σ-≡,≡→≡
           (implicit-extensionality
              (lower-extensionality ℓ₂ (ℓ₁ ⊔ ℓ₂) ext) λ _ → tγ≡tδ)
           (_⇔_.to propositional⇔irrelevant
                   (naturality-propositional ext F G) _ _)

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

-- Identity natural transformation.

id⇾ : ∀ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
        {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄}
      (F : C ⇨ D) → F ⇾ F
id⇾ {C = C} {D = D} F = record { natural-transformation = id , nat }
  where
  open Precategory D

  abstract
    nat : ∀ {X Y} {f : Precategory.Hom C X Y} →
          id ∙ (F ⊙ f) ≡ (F ⊙ f) ∙ id
    nat {f = f} =
      id ∙ (F ⊙ f)  ≡⟨ left-identity ⟩
      F ⊙ f         ≡⟨ sym $ right-identity ⟩∎
      (F ⊙ f) ∙ id  ∎

-- Composition of natural transformations.

infixl 10 _∙⇾_

_∙⇾_ : ∀ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
         {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄}
         {F G H : C ⇨ D} →
       F ⇾ G → G ⇾ H → F ⇾ H
_∙⇾_ {C = C} {D = D} {F} {G} {H} γ δ =
  record { natural-transformation = ε , nat }
  where
  open Precategory D
  open _⇾_

  ε : ∀ {X} → Hom (F ⊚ X) (H ⊚ X)
  ε = transformation γ ∙ transformation δ

  abstract
    nat : ∀ {X Y} {f : Precategory.Hom C X Y} →
          ε ∙ (H ⊙ f) ≡ (F ⊙ f) ∙ ε
    nat {f = f} =
      (transformation γ ∙ transformation δ) ∙ (H ⊙ f)  ≡⟨ sym assoc ⟩
      transformation γ ∙ (transformation δ ∙ (H ⊙ f))  ≡⟨ cong (_∙_ _) $ natural δ ⟩
      transformation γ ∙ ((G ⊙ f) ∙ transformation δ)  ≡⟨ assoc ⟩
      (transformation γ ∙ (G ⊙ f)) ∙ transformation δ  ≡⟨ cong (λ f → f ∙ _) $ natural γ ⟩
      ((F ⊙ f) ∙ transformation γ) ∙ transformation δ  ≡⟨ sym assoc ⟩∎
      (F ⊙ f) ∙ (transformation γ ∙ transformation δ)  ∎

------------------------------------------------------------------------
-- Functor precategories

-- Functor precategories are defined using extensionality.

infix 10 _^_

_^_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
      Precategory ℓ₁ ℓ₂ → Precategory ℓ₃ ℓ₄ →
      Extensionality (ℓ₃ ⊔ ℓ₄) (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) →
      Precategory _ _
(D ^ C) ext = record { precategory =
  (C ⇨ D) ,
  (λ F G → (F ⇾ G) , ⇾-set ext) ,
  id⇾ _ ,
  _∙⇾_ ,
  [ ext , left-identity ]⇾ ,
  [ ext , right-identity ]⇾ ,
  [ ext , assoc ]⇾ }
  where open Precategory D

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
         transformation (id⇾ F)               ≡⟨ refl _ ⟩∎
         id                                   ∎) ,
        (transformation δ ∙ transformation γ  ≡⟨⟩
         transformation (δ ∙⇾ γ)              ≡⟨ cong (λ ε → transformation ε) δγ ⟩
         transformation (id⇾ G)               ≡⟨ refl _ ⟩∎
         id                                   ∎) }
    ; from = λ iso →
        record { natural-transformation =
          proj₁ iso ,
          (λ {_ _ f} →
               proj₁ iso ∙ (F ⊙ f)                                     ≡⟨ sym right-identity ⟩
               proj₁ iso ∙ (F ⊙ f) ∙ id                                ≡⟨ cong (_∙_ _) $ sym $ proj₁ (proj₂ iso) ⟩
               proj₁ iso ∙ (F ⊙ f) ∙ (transformation γ ∙ proj₁ iso)    ≡⟨ sym assoc ⟩
               proj₁ iso ∙ ((F ⊙ f) ∙ (transformation γ ∙ proj₁ iso))  ≡⟨ cong (_∙_ _) assoc ⟩
               proj₁ iso ∙ (((F ⊙ f) ∙ transformation γ) ∙ proj₁ iso)  ≡⟨ cong (λ g → _ ∙ (g ∙ _)) $ sym $ natural γ ⟩
               proj₁ iso ∙ ((transformation γ ∙ (G ⊙ f)) ∙ proj₁ iso)  ≡⟨ cong (_∙_ _) $ sym assoc ⟩
               proj₁ iso ∙ (transformation γ ∙ ((G ⊙ f) ∙ proj₁ iso))  ≡⟨ assoc ⟩
               proj₁ iso ∙ transformation γ ∙ ((G ⊙ f) ∙ proj₁ iso)    ≡⟨ cong (λ g → g ∙ ((G ⊙ f) ∙ proj₁ iso)) $ proj₂ (proj₂ iso) ⟩
               id ∙ ((G ⊙ f) ∙ proj₁ iso)                              ≡⟨ left-identity ⟩∎
               (G ⊙ f) ∙ proj₁ iso                                     ∎) } ,
        [ ext , proj₁ (proj₂ iso) ]⇾ ,
        [ ext , proj₂ (proj₂ iso) ]⇾
    }
    where
    open Precategory D
    open _⇾_

{-

-- If D is a category, then (D ^ C) ext is also a category.

-- TODO: Abstract.

infix 10 _↑_

_↑_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
      Category ℓ₁ ℓ₂ → Precategory ℓ₃ ℓ₄ →
      Extensionality (ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) →
      Category _ _
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

                   ≡→≅ (≅→≡ (γ X)) ⁻¹ ∙ (F ⊙ f) ∙ ≡→≅ (≅→≡ (γ Y)) ¹    ≡⟨ cong₂ (λ p q → p ⁻¹ ∙ (F ⊙ f) ∙ q ¹)
                                                                                (_≃_.right-inverse-of ≡≃≅ _)
                                                                                (_≃_.right-inverse-of ≡≃≅ _) ⟩
                   γ X ⁻¹ ∙ (F ⊙ f) ∙ γ Y ¹                            ≡⟨ sym assoc ⟩

                   γ X ⁻¹ ∙ ((F ⊙ f) ∙ γ Y ¹)                          ≡⟨ cong (_∙_ _) $ sym $ _⇾_.natural F⇾G ⟩

                   γ X ⁻¹ ∙ (γ X ¹ ∙ (G ⊙ f))                          ≡⟨ assoc ⟩

                   γ X ⁻¹ ∙ γ X ¹ ∙ (G ⊙ f)                            ≡⟨ cong (λ g → g ∙ _) $ γ X ⁻¹¹ ⟩

                   id ∙ (G ⊙ f)                                        ≡⟨ left-identity ⟩∎

                   G ⊙ f                                               ∎

             in _≃_.from (≡≃≡⊚≡⊙ ext₁) (⊚F≡⊚G , ⊙F≡⊙G) }
         }
       ; right-inverse-of = {!!}
       }
     ; left-inverse-of = {!!}
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

-}
