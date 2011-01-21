------------------------------------------------------------------------
-- An equality without the K rule
------------------------------------------------------------------------

module Equality-without-K where

------------------------------------------------------------------------
-- Trusted kernel

abstract

  infix 4 _≡_

  -- Equality. Note that the implementation of _≡_ is kept abstract.

  data _≡_ {A : Set} : A → A → Set where
    refl′ : ∀ x → x ≡ x

  -- Reflexivity.

  refl : {A : Set} (x : A) → x ≡ x
  refl = refl′

  -- The J rule.

  elim : {A : Set} (P : {x y : A} → x ≡ y → Set) →
         (∀ x → P (refl x)) →
         ∀ {x y} (x≡y : x ≡ y) → P x≡y
  elim P r (refl′ x) = r x

  -- Intended computational behaviour of the J rule.

  elim-refl : ∀ {A : Set} (P : {x y : A} → x ≡ y → Set)
              (r : ∀ x → P (refl x)) {x} →
              elim P r (refl x) ≡ r x
  elim-refl P r = refl _

------------------------------------------------------------------------
-- Some simple properties

-- Symmetry.

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym = elim (λ {x} {y} _ → y ≡ x) refl

-- Transitivity.

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {z = z} = elim (λ {x} {y} _ → y ≡ z → x ≡ z) (λ x x≡z → x≡z)

-- Congruence.

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f = elim (λ {u v} _ → f u ≡ f v) (λ x → refl (f x))

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f {x} {y} x≡y =
  elim (λ {u v} _ → f x u ≡ f y v) (λ x → cong (λ u → f u x) x≡y)

-- Substitutivity.

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P = elim (λ {u v} _ → P u → P v) (λ x p → p)

-- Equational reasoning combinators.

infix  2 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : ∀ {A} x {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀ {A} (x : A) → x ≡ x
_∎ = refl
