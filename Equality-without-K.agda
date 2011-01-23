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

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Function.Surjection using (Surjection; module Surjection)
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (¬_)

-- Symmetry.

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym = elim (λ {x} {y} _ → y ≡ x) refl

-- Transitivity.

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {z = z} = elim (λ {x} {y} _ → y ≡ z → x ≡ z) (λ x x≡z → x≡z)

-- Equational reasoning combinators.

infix  2 finally
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : ∀ {A} x {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

finally : ∀ {A} (x y : A) → x ≡ y → x ≡ y
finally _ _ x≡y = x≡y

syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

-- Congruence.

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f = elim (λ {u v} _ → f u ≡ f v) (λ x → refl (f x))

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f {x} {y} {u} {v} x≡y u≡v =
  f x u  ≡⟨ cong (λ g → g u) (cong f x≡y) ⟩
  f y u  ≡⟨ cong (f y) u≡v ⟩∎
  f y v  ∎

-- Substitutivity.

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P = elim (λ {u v} _ → P u → P v) (λ x p → p)

subst-refl : {A : Set} (P : A → Set) {x : A} (p : P x) →
             subst P (refl x) p ≡ p
subst-refl P p =
  cong (λ f → f p) (elim-refl (λ {u v} _ → P u → P v) (λ x p → p))

-- The boolean true is not equal to false.

true≢false : ¬ true ≡ false
true≢false true≡false = subst (λ b → if b then ⊤ else ⊥) true≡false _

-- Setoid.

setoid : Set → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = record
    { refl  = refl _
    ; sym   = sym
    ; trans = trans
    }
  }

-- Lifts ordinary functions to equality-preserving functions.

→-to-⟶ : {A B : Set} → (A → B) → setoid A ⟶ setoid B
→-to-⟶ f = record { _⟨$⟩_ = f; cong = cong f }

-- An abbreviation.

infix 4 _↠_

_↠_ : Set → Set → Set
A ↠ B = Surjection (setoid A) (setoid B)

------------------------------------------------------------------------
-- The K rule and proof irrelevance

open import Function.Equivalence as Eq
  using (_⇔_; equivalent; module Equivalent)

-- The K rule (without computational content).

K-rule : Set₁
K-rule = {A : Set} (P : {x : A} → x ≡ x → Set) →
         (∀ x → P (refl x)) →
         ∀ {x} (x≡x : x ≡ x) → P x≡x

-- Sets for which _≡_ is a trivial relation.

Trivial-≡ : Set → Set
Trivial-≡ A = (x y : A) → x ≡ y

-- Proof irrelevance.

Proof-irrelevance : Set → Set
Proof-irrelevance A = {x y : A} → Trivial-≡ (x ≡ y)

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
import Relation.Binary.PropositionalEquality as P

-- The two equalities are equivalent. In fact, there is a surjection
-- from _≡_ (and any other relation which is reflexive and
-- substitutive) to P._≡_.

≡⇔≡ : ∀ {A} {x y : A} → (x ≡ y) ↠ P._≡_ x y
≡⇔≡ {x = x} = record
  { to         = →-to-⟶ λ x≡y → subst (P._≡_ x) x≡y P.refl
  ; surjective = record
    { from             = →-to-⟶ to
    ; right-inverse-of = λ _ → to $ P.proof-irrelevance _ _
    }
  }
  where
  to : ∀ {A} {x y : A} → P._≡_ x y → x ≡ y
  to {x = x} x≡y = P.subst (_≡_ x) x≡y (refl x)

-- However, I don't know if the surjection is a bijection. Existence
-- of surjections in the other direction (for any set and elements in
-- this set) is equivalent to (general) proof irrelevance, and hence
-- also to the K rule.

bijection⇔irrelevance :
  (∀ {A} {x y : A} → P._≡_ x y ↠ (x ≡ y)) ⇔
  (∀ {A} → Proof-irrelevance A)
bijection⇔irrelevance = equivalent ⇒ ⇐
  where
  ⇒ : (∀ {A} {x y : A} → P._≡_ x y ↠ (x ≡ y)) →
      (∀ {A} → Proof-irrelevance A)
  ⇒ left p q =
    p                   ≡⟨ sym $ right-inverse-of p ⟩
    to ⟨$⟩ (from ⟨$⟩ p) ≡⟨ cong (_⟨$⟩_ to) $
                                to ⟨$⟩ P.proof-irrelevance
                                         (from ⟨$⟩ p) (from ⟨$⟩ q) ⟩
    to ⟨$⟩ (from ⟨$⟩ q) ≡⟨ right-inverse-of q ⟩∎
    q                   ∎
    where
    open module S {A : Set} {x y : A} = Surjection (left {A} {x} {y})

  ⇐ : (∀ {A} → Proof-irrelevance A) →
      (∀ {A} {x y : A} → P._≡_ x y ↠ (x ≡ y))
  ⇐ irr {x = x} {y} = record
    { to         = from
    ; surjective = record
      { from             = to
      ; right-inverse-of = λ x≡y → irr (from ⟨$⟩ (to ⟨$⟩ x≡y)) x≡y
      }
    }
    where
    open module S {A : Set} {x y : A} = Surjection (≡⇔≡ {A} {x} {y})

bijection⇔K : (∀ {A} {x y : A} → P._≡_ x y ↠ (x ≡ y)) ⇔ K-rule
bijection⇔K = Eq._∘_ (Eq.sym k⇔irrelevance) bijection⇔irrelevance
