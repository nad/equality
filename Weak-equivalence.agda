------------------------------------------------------------------------
-- Weak equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

module Weak-equivalence where

open import Bijection hiding (id; _∘_; inverse)
open import Equality
open import Equality.Groupoid hiding (groupoid)
import Equality.Tactic as Tactic; open Tactic.Eq
open import Equivalence hiding (id; _∘_; inverse)
open import H-level as H
open import H-level.Closure
open import Preimage using (_⁻¹_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
open import Surjection hiding (id; _∘_)

-- A function f is a weak equivalence if all preimages under f are
-- contractible.

Is-weak-equivalence : {A B : Set} → (A → B) → Set
Is-weak-equivalence f = ∀ y → Contractible (f ⁻¹ y)

abstract

  -- Is-weak-equivalence f is a proposition, assuming extensional
  -- equality.

  propositional :
    (∀ {A B} → Extensionality A B) →
    ∀ {A B} (f : A → B) → Propositional (Is-weak-equivalence f)
  propositional ext f =
    Π-closure ext 1 λ _ → Contractible-propositional ext

-- Is-weak-equivalence respects extensional equality.

respects-extensional-equality :
  ∀ {A B} {f g : A → B} →
  (∀ x → f x ≡ g x) →
  Is-weak-equivalence f → Is-weak-equivalence g
respects-extensional-equality f≡g f-weq = λ b →
  H.respects-surjection
    (_↔_.surjection (Preimage.respects-extensional-equality f≡g))
    0
    (f-weq b)

-- Weak equivalences.

infix 4 _≈_

record _≈_ (A B : Set) : Set where
  constructor weq
  field
    to                  : A → B
    is-weak-equivalence : Is-weak-equivalence to

  -- Weakly equivalent sets are isomorphic.

  abstract
    right-inverse-of = proj₂ ⊚ proj₁ ⊚ is-weak-equivalence
    left-inverse-of  = λ x →
      cong proj₁ $
        proj₂ (is-weak-equivalence (to x)) (x , refl (to x))

  bijection : A ↔ B
  bijection = record
    { surjection = record
      { equivalence = record
        { to   = to
        ; from = proj₁ ⊚ proj₁ ⊚ is-weak-equivalence
        }
      ; right-inverse-of = right-inverse-of
      }
    ; left-inverse-of = left-inverse-of
    }

  open _↔_ bijection public
    hiding (to; right-inverse-of; left-inverse-of)

  abstract

    -- All preimages of an element under the weak equivalence are
    -- equal.

    irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
    irrelevance = proj₂ ⊚ is-weak-equivalence

    -- The two proofs left-inverse-of and right-inverse-of are
    -- related.

    left-right-lemma :
      ∀ x → cong to (left-inverse-of x) ≡ right-inverse-of (to x)
    left-right-lemma x =
      lemma₁ to _ _ (lemma₂ (irrelevance (to x) (x , refl (to x))))
      where
      lemma₁ : ∀ {A} {x y : A}
               (f : A → B) (p : x ≡ y) (q : f x ≡ f y) →
               refl (f y) ≡ trans (cong f (sym p)) q →
               cong f p ≡ q
      lemma₁ f = elim
        (λ {x y} p → ∀ q → refl (f y) ≡ trans (cong f (sym p)) q →
                           cong f p ≡ q)
        (λ x q hyp →
           cong f (refl x)                  ≡⟨ Tactic.prove (Cong f Refl) Refl (refl _) ⟩
           refl (f x)                       ≡⟨ hyp ⟩
           trans (cong f (sym (refl x))) q  ≡⟨ Tactic.prove (Trans (Cong f (Sym Refl)) (Lift q)) (Lift q) (refl _) ⟩∎
           q                                ∎)

      lemma₂ : ∀ {A B} {f : A → B} {y} {f⁻¹y₁ f⁻¹y₂ : f ⁻¹ y}
               (p : f⁻¹y₁ ≡ f⁻¹y₂) →
               proj₂ f⁻¹y₂ ≡
               trans (cong f (sym (cong proj₁ p))) (proj₂ f⁻¹y₁)
      lemma₂ {f = f} = elim
        (λ {f⁻¹y₁ f⁻¹y₂} p →
           proj₂ f⁻¹y₂ ≡
           trans (cong f (sym (cong proj₁ p))) (proj₂ f⁻¹y₁))
        (λ f⁻¹y →
           Tactic.prove
             (Lift (proj₂ f⁻¹y))
             (Trans (Cong f (Sym (Cong proj₁ Refl)))
                    (Lift (proj₂ f⁻¹y)))
             (refl _))

-- Bijections are weak equivalences.

bijection⇒weak-equivalence : ∀ {A B} → A ↔ B → A ≈ B
bijection⇒weak-equivalence A↔B = record
  { to                  = to
  ; is-weak-equivalence = to-weq
  }
  where
  open _↔_ A↔B

  to∘from-weq : Is-weak-equivalence (to ⊚ from)
  to∘from-weq = respects-extensional-equality
                  (sym ⊚ right-inverse-of)
                  Preimage.id⁻¹-contractible

  to-weq : Is-weak-equivalence to
  to-weq y = H.respects-surjection
               (Preimage.lift-surjection
                  (_↔_.surjection (Bijection.inverse A↔B)))
               0
               (to∘from-weq y)

-- Weak equivalences are equivalence relations.

id : ∀ {A} → A ≈ A
id = record
  { to                  = P.id
  ; is-weak-equivalence = Preimage.id⁻¹-contractible
  }

inverse : ∀ {A B} → A ≈ B → B ≈ A
inverse =
  bijection⇒weak-equivalence ⊚
  Bijection.inverse ⊚
  _≈_.bijection

infixr 9 _∘_

_∘_ : ∀ {A B C} → B ≈ C → A ≈ B → A ≈ C
f ∘ g =
  bijection⇒weak-equivalence $
    Bijection._∘_ (_≈_.bijection f) (_≈_.bijection g)

-- Equational reasoning combinators.

infix  2 finally-≈
infixr 2 _≈⟨_⟩_

_≈⟨_⟩_ : ∀ A {B C} → A ≈ B → B ≈ C → A ≈ C
_ ≈⟨ A≈B ⟩ B≈C = B≈C ∘ A≈B

finally-≈ : ∀ A B → A ≈ B → A ≈ B
finally-≈ _ _ A≈B = A≈B

syntax finally-≈ A B A≈B = A ≈⟨ A≈B ⟩∎ B ∎

abstract

  -- Two proofs of weak equivalence are equal if the function
  -- components are equal (assuming extensionality).

  lift-equality : (∀ {A B} → Extensionality A B) →
                  ∀ {A B} {p q : A ≈ B} →
                  (∀ x → _≈_.to p x ≡ _≈_.to q x) → p ≡ q
  lift-equality ext {p = weq f f-weq} {q = weq g g-weq} f≡g =
    elim (λ {f g} f≡g → ∀ f-weq g-weq → weq f f-weq ≡ weq g g-weq)
         (λ f f-weq g-weq →
            cong (weq f)
              (_⇔_.to propositional⇔irrelevant
                 (propositional ext f) f-weq g-weq))
         (ext f≡g) f-weq g-weq

-- _≈_ comes with a groupoid structure (assuming extensionality).
--
-- Note that, at the time of writing (and on a particular system), the
-- following proof takes about three times as long to type-check as
-- the rest of the development.

groupoid : (∀ {A B} → Extensionality A B) →
           Groupoid (suc zero)
groupoid ext = record
  { Object         = Set
  ; _∼_            = _≈_
  ; id             = id
  ; _∘_            = _∘_
  ; _⁻¹            = inverse
  ; left-identity  = left-identity
  ; right-identity = right-identity
  ; assoc          = assoc
  ; left-inverse   = left-inverse
  ; right-inverse  = right-inverse
  }
  where
  abstract
    left-identity : ∀ {X Y} (p : X ≈ Y) → id ∘ p ≡ p
    left-identity _ = lift-equality ext (λ _ → refl _)

    right-identity : ∀ {X Y} (p : X ≈ Y) → p ∘ id ≡ p
    right-identity _ = lift-equality ext (λ _ → refl _)

    assoc : ∀ {W X Y Z} (p : Y ≈ Z) (q : X ≈ Y) (r : W ≈ X) →
            p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    assoc _ _ _ = lift-equality ext (λ _ → refl _)

    left-inverse : ∀ {X Y} (p : X ≈ Y) → inverse p ∘ p ≡ id
    left-inverse p = lift-equality ext (_≈_.left-inverse-of p)

    right-inverse : ∀ {X Y} (p : X ≈ Y) → p ∘ inverse p ≡ id
    right-inverse p = lift-equality ext (_≈_.right-inverse-of p)

abstract

  -- Positive h-levels are closed under the weak equivalence operator
  -- (assuming extensionality).

  right-closure :
    (∀ {A B} → Extensionality A B) →
    ∀ {A B} n → H-level (1 + n) B → H-level (1 + n) (A ≈ B)
  right-closure ext {A} {B} n h =
    H.respects-surjection surj (1 + n) lemma
    where
    lemma : H-level (1 + n) (∃ λ (to : A → B) → Is-weak-equivalence to)
    lemma = Σ-closure (1 + n)
              (Π-closure ext (1 + n) (const h))
              (mono (m≤m+n 1 n) ⊚ propositional ext)

    surj : (∃ λ (to : A → B) → Is-weak-equivalence to) ↠ (A ≈ B)
    surj = record
      { equivalence = record
          { to   = λ A≈B → weq (proj₁ A≈B) (proj₂ A≈B)
          ; from = λ A≈B → (_≈_.to A≈B , _≈_.is-weak-equivalence A≈B)
          }
      ; right-inverse-of = λ _ → refl _
      }

  left-closure :
    (∀ {A B} → Extensionality A B) →
    ∀ {A B} n → H-level (1 + n) A → H-level (1 + n) (A ≈ B)
  left-closure ext {A} {B} n h =
    H.[inhabited⇒+]⇒+ n λ (A≈B : A ≈ B) →
      right-closure ext n $
        H.respects-surjection (_≈_.surjection A≈B) (1 + n) h
