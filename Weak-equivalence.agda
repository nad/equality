------------------------------------------------------------------------
-- Weak equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

module Weak-equivalence where

open import Bijection hiding (id; _∘_; inverse)
open import Equality
import Equality.Tactic as Tactic; open Tactic.Eq
open import Equivalence hiding (id; _∘_; inverse)
open import H-level as H
open import H-level.Closure
open import Preimage
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

-- Weak equivalences.

infix 4 _≈_

record _≈_ (A B : Set) : Set where
  constructor weq
  field
    to                  : A → B
    is-weak-equivalence : Is-weak-equivalence to

  -- Weakly equivalent sets are isomorphic.

  private
    abstract
      to∘from = proj₂ ⊚ proj₁ ⊚ is-weak-equivalence
      from∘to = λ x →
        cong proj₁ $
          proj₂ (is-weak-equivalence (to x)) (x , refl (to x))

  bijection : A ↔ B
  bijection = record
    { surjection = record
      { equivalence = record
        { to   = to
        ; from = proj₁ ⊚ proj₁ ⊚ is-weak-equivalence
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of = from∘to
    }

  open _↔_ bijection public hiding (to)

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
  ; is-weak-equivalence = λ y →
      let lemma₁ : Contractible ((to ⊚ from) ⁻¹ y)
          lemma₁ = H.respects-surjection
                     (_↔_.surjection $
                        Preimage.respects-extensional-equality
                          (sym ⊚ right-inverse-of))
                     0
                     (id⁻¹-contractible y)

          lemma₂ : Contractible (to ⁻¹ y)
          lemma₂ = H.respects-surjection
                     (Preimage.lift-surjection
                        (_↔_.surjection (Bijection.inverse A↔B)))
                     0
                     lemma₁
      in lemma₂
  } where open _↔_ A↔B

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

-- Weak equivalences are equivalence relations.

id : ∀ {A} → A ≈ A
id = record
  { to                  = P.id
  ; is-weak-equivalence = id⁻¹-contractible
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

abstract

  -- Two proofs of weak equality are equal if the function components
  -- are equal (assuming extensionality).

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

