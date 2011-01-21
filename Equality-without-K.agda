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

------------------------------------------------------------------------
-- The K rule and proof irrelevance

open import Function.Equivalence as Eq
  using (_⇔_; equivalent; module Equivalent)

-- The K rule (without computational content).

K-rule : Set₁
K-rule = {A : Set} (P : {x : A} → x ≡ x → Set) →
         (∀ x → P (refl x)) →
         ∀ {x} (x≡x : x ≡ x) → P x≡x

-- Proof irrelevance.

Proof-irrelevance : Set → Set
Proof-irrelevance A = ∀ {x y : A} (x≡y x≡y′ : x ≡ y) → x≡y ≡ x≡y′

-- The K rule is equivalent to (general) proof irrelevance.

k⇔irrelevance : K-rule ⇔ (∀ {A} → Proof-irrelevance A)
k⇔irrelevance =
  equivalent
    (λ K {_} →
       elim (λ p → ∀ q → p ≡ q)
            (λ x → K (λ {x} p → refl x ≡ p) (λ x → refl (refl x))))
    (λ irr P r {x} x≡x → subst P (irr (refl x) x≡x) (r x))

------------------------------------------------------------------------
-- Relation to ordinary propositional equality with the K rule

open import Function using (_$_)
open import Function.Equality using (_⟨$⟩_)
open import Function.LeftInverse
  using (LeftInverse; RightInverse; module LeftInverse)
import Relation.Binary.PropositionalEquality as P

-- The two equalities are equivalent. In fact, there exists a left
-- inverse from P._≡_ to _≡_.

≡⇔≡ : ∀ {A} {x y : A} →
      LeftInverse (P.setoid (P._≡_ x y)) (P.setoid (x ≡ y))
≡⇔≡ {x = x} = record
  { to              = P.→-to-⟶ λ x≡y → P.subst   (_≡_ x) x≡y  (refl x)
  ; from            = P.→-to-⟶ λ x≡y →   subst (P._≡_ x) x≡y P.refl
  ; left-inverse-of = λ _ → P.proof-irrelevance _ _
  }

-- However, I suspect that there is no right inverse. Existence of a
-- right inverse (for any set and elements in this set) is equivalent
-- to (general) proof irrelevance, and hence also to the K rule.

right⇔irrelevance :
  (∀ {A} {x y : A} →
   RightInverse (P.setoid (P._≡_ x y)) (P.setoid (x ≡ y))) ⇔
  (∀ {A} → Proof-irrelevance A)
right⇔irrelevance = equivalent ⇒ ⇐
  where
  ⇒ : _ → (∀ {A} → Proof-irrelevance A)
  ⇒ right p q =
    p                   ≡⟨ sym $ from ⟨$⟩ left-inverse-of p ⟩
    from ⟨$⟩ (to ⟨$⟩ p) ≡⟨ cong (_⟨$⟩_ from) $
                                from ⟨$⟩ P.proof-irrelevance
                                           (to ⟨$⟩ p) (to ⟨$⟩ q) ⟩
    from ⟨$⟩ (to ⟨$⟩ q) ≡⟨ from ⟨$⟩ left-inverse-of q ⟩
    q                   ∎
    where
    open module LI {A : Set} {x y : A} = LeftInverse (right {A} {x} {y})

  ⇐ : _ →
      (∀ {A} {x y : A} →
         RightInverse (P.setoid (P._≡_ x y)) (P.setoid (x ≡ y)))
  ⇐ irr {x = x} {y} = record
    { to              = from
    ; from            = to
    ; left-inverse-of = λ x≡y → from ⟨$⟩ irr (to ⟨$⟩ (from ⟨$⟩ x≡y)) x≡y
    }
    where
    open module LI {A : Set} {x y : A} = LeftInverse (≡⇔≡ {A} {x} {y})

right⇔K : (∀ {A} {x y : A} →
           RightInverse (P.setoid (P._≡_ x y)) (P.setoid (x ≡ y))) ⇔
          K-rule
right⇔K = Eq._∘_ (Eq.sym k⇔irrelevance) right⇔irrelevance
