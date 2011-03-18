------------------------------------------------------------------------
-- All instances of the equality axioms are isomorphic
------------------------------------------------------------------------

module Equality.Instances-isomorphic where

import Bijection
open import Equality
open import Prelude

-- One of the instances is used to define what "isomorphic" means.

all-instances-isomorphic :
  ∀ {refl₁ refl₂}
  (eq₁ : Equality-with-J refl₁) (eq₂ : Equality-with-J refl₂) →
  let open Bijection eq₁ in
  ∀ {A} {x y : A} → Reflexive._≡_ refl₁ x y ↔ Reflexive._≡_ refl₂ x y
all-instances-isomorphic {refl₁} {refl₂} eq₁ eq₂ = record
  { surjection = record
    { equivalence = record
      { to   = to refl₂ eq₁
      ; from = to refl₁ eq₂
      }
    ; right-inverse-of = to refl₁ eq₂ ∘ to∘to _ _ eq₂ eq₁
    }
  ; left-inverse-of = to∘to _ _ eq₁ eq₂
  }
  where
  open Reflexive
  open Equality-with-J

  to : ∀ {refl₁} refl₂ (eq₁ : Equality-with-J refl₁) {A} {x y : A} →
       _≡_ refl₁ x y → _≡_ refl₂ x y
  to refl₂ eq₁ {x = x} x≡y = subst eq₁ (_≡_ refl₂ x) x≡y (refl refl₂ x)

  to∘to : ∀ refl₁ refl₂
          (eq₁ : Equality-with-J refl₁) (eq₂ : Equality-with-J refl₂) →
          ∀ {A} {x y : A} (x≡y : _≡_ refl₁ x y) →
          _≡_ refl₁ (to refl₁ eq₂ (to refl₂ eq₁ x≡y)) x≡y
  to∘to refl₁ refl₂ eq₁ eq₂ = elim eq₁
    (λ {x y} x≡y → _≡_ refl₁ (to refl₁ eq₂ (to refl₂ eq₁ x≡y)) x≡y)
    (λ x → to refl₁ eq₂ (to refl₂ eq₁ (refl refl₁ x))  ≡⟨ cong eq₁ (to refl₁ eq₂) (subst-refl eq₁ (_≡_ refl₂ x) (refl refl₂ x)) ⟩
           to refl₁ eq₂ (refl refl₂ x)                 ≡⟨ to refl₁ eq₂ $ subst-refl eq₂ (_≡_ refl₁ x) (refl refl₁ x) ⟩∎
           refl refl₁ x                                ∎)
    where
    open Derived-definitions-and-properties eq₁
      using (_≡⟨_⟩_; finally)
