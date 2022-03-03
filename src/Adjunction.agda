------------------------------------------------------------------------
-- Adjunctions and monads (for 1-categories)
------------------------------------------------------------------------

-- The code is based on the presentation in the HoTT book (but might
-- not follow it exactly).

{-# OPTIONS --without-K --safe #-}

open import Equality

module Adjunction
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude hiding (id)

open import Category eq
open Derived-definitions-and-properties eq
open import Extensionality eq
open import Functor eq

------------------------------------------------------------------------
-- Adjunctions

private

  -- Is-left-adjoint-of ext F G means that F is a left adjoint of G.
  -- This definition tries to follow the HoTT book closely.

  Is-left-adjoint-of :
    ∀ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
      {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄} →
    Extensionality (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) →
    C ⇨ D → D ⇨ C → Type _
  Is-left-adjoint-of {ℓ₁} {ℓ₂} {C} {ℓ₃} {ℓ₄} {D} ext F G =
    ∃ λ (η : id⇨ ⇾ G ∙⇨ F) →
    ∃ λ (ε : F ∙⇨ G ⇾ id⇨) →
    subst ((F ∙⇨ G) ∙⇨ F ⇾_) (id⇨∙⇨ ext₁) (ε ⇾∙⇨ F) ∙⇾
      subst (_⇾ (F ∙⇨ G) ∙⇨ F) (∙⇨id⇨ ext₁)
        (subst (F ∙⇨ id⇨ ⇾_) (∙⇨-assoc ext₁ F G) (F ⇨∙⇾ η))
      ≡
    id⇾ F
      ×
    subst (G ∙⇨ F ∙⇨ G ⇾_) (∙⇨id⇨ ext₂) (G ⇨∙⇾ ε) ∙⇾
      subst (_⇾ G ∙⇨ F ∙⇨ G) (id⇨∙⇨ ext₂)
        (subst (id⇨ ∙⇨ G ⇾_) (sym $ ∙⇨-assoc ext₂ G F) (η ⇾∙⇨ G))
      ≡
    id⇾ G
    where
    ext₁ : Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
    ext₁ = lower-extensionality (ℓ₃ ⊔ ℓ₄) ℓ₃ ext

    ext₂ : Extensionality (ℓ₃ ⊔ ℓ₄) (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
    ext₂ = lower-extensionality (ℓ₁ ⊔ ℓ₂) ℓ₁ ext

-- F ⊣ G means that F is a left adjoint of G.
--
-- This definition avoids the use of subst in the previous definition
-- by making use of the equality characterisation for natural
-- transformations (equality-characterisation⇾). I (NAD) took the idea
-- for this definition from the HoTT-Agda library
-- (https://github.com/HoTT/HoTT-Agda/blob/2871c6f6dbe90b47b3b2770e57abc4732cd1c295/theorems/homotopy/PtdAdjoint.agda).
--
-- TODO: Prove that the two definitions are equivalent.

_⊣_ :
  ∀ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
    {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄} →
  C ⇨ D → D ⇨ C → Type _
_⊣_ {ℓ₁} {ℓ₂} {C} {ℓ₃} {ℓ₄} {D} F G =
  ∃ λ (η : id⇨ ⇾ G ∙⇨ F) →
  ∃ λ (ε : F ∙⇨ G ⇾ id⇨) →
  (∀ {X} → transformation ε D.∙ (F ⊙ transformation η {X = X}) ≡ D.id)
    ×
  (∀ {X} → (G ⊙ transformation ε {X = X}) C.∙ transformation η ≡ C.id)
  where
  open _⇾_
  module C = Precategory C
  module D = Precategory D

-- Adjunctions.

Adjunction :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
  Precategory ℓ₁ ℓ₂ → Precategory ℓ₃ ℓ₄ → Type _
Adjunction C D = ∃ λ (F : C ⇨ D) → ∃ λ (G : D ⇨ C) → F ⊣ G

------------------------------------------------------------------------
-- Monads

-- A monad on a precategory.
--
-- This definition is taken from Wikipedia
-- (https://en.wikipedia.org/wiki/Monad_%28category_theory%29).

Monad : ∀ {ℓ₁ ℓ₂} (C : Precategory ℓ₁ ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
Monad C =
  ∃ λ (F : C ⇨ C) →
  ∃ λ (η : id⇨ ⇾ F) →
  ∃ λ (μ : F ∙⇨ F ⇾ F) →
  (∀ {X} → transformation μ ∙ (F ⊙ transformation μ {X = X})
             ≡
           transformation μ ∙ transformation μ {X = F ⊚ X})
    ×
  (∀ {X} → transformation μ ∙ (F ⊙ transformation η {X = X}) ≡ id)
    ×
  (∀ {X} → transformation μ ∙ transformation η {X = F ⊚ X} ≡ id)
  where
  open _⇾_
  open Precategory C

-- Adjunctions give rise to monads.
--
-- This definition is taken from Wikipedia
-- (https://en.wikipedia.org/wiki/Monad_%28category_theory%29).

adjunction→monad :
  ∀ {ℓ₁ ℓ₂} {C : Precategory ℓ₁ ℓ₂}
    {ℓ₃ ℓ₄} {D : Precategory ℓ₃ ℓ₄} →
  Adjunction C D → Monad C
adjunction→monad {C = C} {D = D} (F , G , η , ε , εFFη≡1 , GεηG≡1) =
    G ∙⇨ F
  , η
  , GεF
  , lemma₁
  , lemma₂
  , lemma₃
  where
  open _⇾_
  module C = Precategory C
  module D = Precategory D

  -- This natural transformation is defined directly, rather than by
  -- using composition, to avoid the use of casts.

  GεF : (G ∙⇨ F) ∙⇨ (G ∙⇨ F) ⇾ G ∙⇨ F
  natural-transformation GεF =
      G ⊙ transformation ε
    , nat
    where
    abstract
      nat :
        ∀ {X Y} {f : C.Hom X Y} →
        ((G ∙⇨ F) ⊙ f) C.∙ (G ⊙ transformation ε) ≡
        (G ⊙ transformation ε) C.∙ (((G ∙⇨ F) ∙⇨ (G ∙⇨ F)) ⊙ f)
      nat {f = f} =
        ((G ∙⇨ F) ⊙ f) C.∙ (G ⊙ transformation ε)                ≡⟨⟩
        (G ⊙ F ⊙ f) C.∙ (G ⊙ transformation ε)                   ≡⟨ sym (⊙-∙ G) ⟩
        G ⊙ ((F ⊙ f) D.∙ transformation ε)                       ≡⟨ cong (G ⊙_) (natural ε) ⟩
        G ⊙ (transformation ε D.∙ (F ⊙ G ⊙ F ⊙ f))               ≡⟨ ⊙-∙ G ⟩
        (G ⊙ transformation ε) C.∙ (G ⊙ F ⊙ G ⊙ F ⊙ f)           ≡⟨⟩
        (G ⊙ transformation ε) C.∙ (((G ∙⇨ F) ∙⇨ (G ∙⇨ F)) ⊙ f)  ∎

  abstract

    lemma₁ :
      ∀ {X} →
      transformation GεF {X = X} C.∙ ((G ∙⇨ F) ⊙ transformation GεF) ≡
      transformation GεF C.∙ transformation GεF
    lemma₁ =
      (G ⊙ transformation ε) C.∙ (G ⊙ F ⊙ G ⊙ transformation ε)  ≡⟨ sym (⊙-∙ G) ⟩
      G ⊙ (transformation ε D.∙ (F ⊙ G ⊙ transformation ε))      ≡⟨ cong (G ⊙_) (sym $ natural ε) ⟩
      G ⊙ (transformation ε D.∙ transformation ε)                ≡⟨ ⊙-∙ G ⟩∎
      (G ⊙ transformation ε) C.∙ (G ⊙ transformation ε)          ∎

    lemma₂ :
      ∀ {X} →
      transformation GεF {X = X} C.∙ ((G ∙⇨ F) ⊙ transformation η) ≡
      C.id
    lemma₂ =
      (G ⊙ transformation ε) C.∙ (G ⊙ F ⊙ transformation η)  ≡⟨ sym (⊙-∙ G) ⟩
      G ⊙ (transformation ε D.∙ (F ⊙ transformation η))      ≡⟨ cong (G ⊙_) εFFη≡1 ⟩
      G ⊙ D.id                                               ≡⟨ ⊙-id G ⟩∎
      C.id                                                   ∎

    lemma₃ :
      ∀ {X} →
      transformation GεF {X = X} C.∙ transformation η ≡ C.id
    lemma₃ =
      (G ⊙ transformation ε) C.∙ transformation η  ≡⟨ GεηG≡1 ⟩∎
      C.id                                         ∎
