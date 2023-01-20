------------------------------------------------------------------------
-- Equivalences with erased "proofs", defined in terms of partly
-- erased contractible fibres
------------------------------------------------------------------------

-- This module contains some basic definitions with few dependencies.
-- See Equivalence.Erased.Contractible-preimages for more definitions.
-- The definitions below are reexported from
-- Equivalence.Erased.Contractible-preimages.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Equivalence.Erased.Contractible-preimages.Basics
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Erased.Basics
open import Prelude

open import Bijection eq using (_↔_)
import Equivalence.Contractible-preimages eq as CP
open import Extensionality eq
open import H-level eq as H-level
open import H-level.Closure eq
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    a b ℓ ℓ₁ ℓ₂      : Level
    A B              : Type a
    c ext k k′ p x y : A
    P                : A → Type p
    f                : (x : A) → P x

------------------------------------------------------------------------
-- Some basic types

-- "Preimages" with erased proofs.

infix 5 _⁻¹ᴱ_

_⁻¹ᴱ_ : {A : Type a} {@0 B : Type b} → @0 (A → B) → @0 B → Type (a ⊔ b)
f ⁻¹ᴱ y = ∃ λ x → Erased (f x ≡ y)

-- Contractibility with an erased proof.

Contractibleᴱ : Type ℓ → Type ℓ
Contractibleᴱ A = ∃ λ (x : A) → Erased (∀ y → x ≡ y)

-- The property of being an equivalence (with erased proofs).

Is-equivalenceᴱ : {A : Type a} {B : Type b} → @0 (A → B) → Type (a ⊔ b)
Is-equivalenceᴱ f = ∀ y → Contractibleᴱ (f ⁻¹ᴱ y)

-- Equivalences with erased proofs.

_≃ᴱ_ : Type a → Type b → Type (a ⊔ b)
A ≃ᴱ B = ∃ λ (f : A → B) → Is-equivalenceᴱ f

------------------------------------------------------------------------
-- Some conversion lemmas

-- Conversions between _⁻¹_ and _⁻¹ᴱ_.

⁻¹→⁻¹ᴱ :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} {@0 y : B} →
  f ⁻¹ y → f ⁻¹ᴱ y
⁻¹→⁻¹ᴱ = Σ-map id [_]→

@0 ⁻¹ᴱ→⁻¹ : f ⁻¹ᴱ x → f ⁻¹ x
⁻¹ᴱ→⁻¹ = Σ-map id erased

-- Conversions between Contractible and Contractibleᴱ.

Contractible→Contractibleᴱ :
  {@0 A : Type a} →
  Contractible A → Contractibleᴱ A
Contractible→Contractibleᴱ = Σ-map id [_]→

@0 Contractibleᴱ→Contractible : Contractibleᴱ A → Contractible A
Contractibleᴱ→Contractible = Σ-map id erased

-- Conversions between CP.Is-equivalence and Is-equivalenceᴱ.

Is-equivalence→Is-equivalenceᴱ :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  CP.Is-equivalence f → Is-equivalenceᴱ f
Is-equivalence→Is-equivalenceᴱ eq y =
    ⁻¹→⁻¹ᴱ (proj₁₀ (eq y))
  , [ cong ⁻¹→⁻¹ᴱ ∘ proj₂ (eq y) ∘ ⁻¹ᴱ→⁻¹ ]

@0 Is-equivalenceᴱ→Is-equivalence :
  Is-equivalenceᴱ f → CP.Is-equivalence f
Is-equivalenceᴱ→Is-equivalence eq y =
    ⁻¹ᴱ→⁻¹ (proj₁ (eq y))
  , cong ⁻¹ᴱ→⁻¹ ∘ erased (proj₂ (eq y)) ∘ ⁻¹→⁻¹ᴱ

-- Conversions between CP._≃_ and _≃ᴱ_.

≃→≃ᴱ :
  {@0 A : Type a} {@0 B : Type b} →
  A CP.≃ B → A ≃ᴱ B
≃→≃ᴱ = Σ-map id Is-equivalence→Is-equivalenceᴱ

@0 ≃ᴱ→≃ : A ≃ᴱ B → A CP.≃ B
≃ᴱ→≃ = Σ-map id Is-equivalenceᴱ→Is-equivalence

------------------------------------------------------------------------
-- Some results related to Contractibleᴱ

-- Contractibleᴱ respects split surjections with erased proofs.

Contractibleᴱ-respects-surjection :
  {@0 A : Type a} {@0 B : Type b}
  (f : A → B) → @0 Split-surjective f →
  Contractibleᴱ A → Contractibleᴱ B
Contractibleᴱ-respects-surjection {A} {B} f s h@(x , _) =
    f x
  , [ proj₂ (H-level.respects-surjection surj 0
               (Contractibleᴱ→Contractible h))
    ]
  where
  @0 surj : A ↠ B
  surj = record
    { logical-equivalence = record
      { to   = f
      ; from = proj₁ ∘ s
      }
    ; right-inverse-of = proj₂ ∘ s
    }

-- "Preimages" (with erased proofs) of an erased function with a
-- quasi-inverse with erased proofs are contractible.

Contractibleᴱ-⁻¹ᴱ :
  {@0 A : Type a} {@0 B : Type b}
  (@0 f : A → B)
  (g : B → A)
  (@0 f∘g : ∀ x → f (g x) ≡ x)
  (@0 g∘f : ∀ x → g (f x) ≡ x) →
  ∀ y → Contractibleᴱ (f ⁻¹ᴱ y)
Contractibleᴱ-⁻¹ᴱ {A} {B} f g f∘g g∘f y =
    (g y , [ proj₂ (proj₁ c′) ])
  , [ cong ⁻¹→⁻¹ᴱ ∘ proj₂ c′ ∘ ⁻¹ᴱ→⁻¹ ]
  where
  @0 A↔B : A ↔ B
  A↔B = record
    { surjection = record
      { logical-equivalence = record
        { to   = f
        ; from = g
        }
      ; right-inverse-of = f∘g
      }
    ; left-inverse-of = g∘f
    }

  @0 c′ : Contractible (f ⁻¹ y)
  c′ = Preimage.bijection⁻¹-contractible A↔B y

-- If an inhabited type comes with an erased proof of
-- propositionality, then it is contractible (with erased proofs).

inhabited→Is-proposition→Contractibleᴱ :
  {@0 A : Type a} →
  A → @0 Is-proposition A → Contractibleᴱ A
inhabited→Is-proposition→Contractibleᴱ x prop = (x , [ prop x ])

-- Some closure properties.

Contractibleᴱ-Σ :
  {@0 A : Type a} {@0 P : A → Type p} →
  Contractibleᴱ A → (∀ x → Contractibleᴱ (P x)) → Contractibleᴱ (Σ A P)
Contractibleᴱ-Σ cA@(a , _) cP =
    (a , proj₁₀ (cP a))
  , [ proj₂ $ Σ-closure 0 (Contractibleᴱ→Contractible cA)
                          (Contractibleᴱ→Contractible ∘ cP)
    ]

Contractibleᴱ-× :
  {@0 A : Type a} {@0 B : Type b} →
  Contractibleᴱ A → Contractibleᴱ B → Contractibleᴱ (A × B)
Contractibleᴱ-× cA cB = Contractibleᴱ-Σ cA (λ _ → cB)

Contractibleᴱ-Π :
  {@0 A : Type a} {@0 P : A → Type p} →
  @0 Extensionality a p →
  (∀ x → Contractibleᴱ (P x)) → Contractibleᴱ ((x : A) → P x)
Contractibleᴱ-Π ext c =
    proj₁₀ ∘ c
  , [ proj₂ $ Π-closure ext 0 (Contractibleᴱ→Contractible ∘ c)
    ]

Contractibleᴱ-↑ :
  {@0 A : Type a} →
  Contractibleᴱ A → Contractibleᴱ (↑ ℓ A)
Contractibleᴱ-↑ c@(a , _) =
    lift a
  , [ proj₂ $ ↑-closure 0 (Contractibleᴱ→Contractible c)
    ]
