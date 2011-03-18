------------------------------------------------------------------------
-- Surjections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Surjection where

open import Equality
import Equality.Groupoid as EG
private module G {A : Set} = EG.Groupoid (EG.groupoid A)
open import Equality.Tactic as Tactic
open import Equivalence
  using (_⇔_; module _⇔_) renaming (_∘_ to _⊚_)
open import Prelude as P hiding (id; _∘_)

infix 4 _↠_

-- Surjections.

record _↠_ (From To : Set) : Set where
  field
    equivalence : From ⇔ To

  open _⇔_ equivalence

  field
    right-inverse-of : ∀ x → to (from x) ≡ x

  open _⇔_ equivalence public

-- _↠_ is a preorder.

id : ∀ {A} → A ↠ A
id = record
  { equivalence      = Equivalence.id
  ; right-inverse-of = refl
  }

infixr 9 _∘_

_∘_ : ∀ {A B C} → B ↠ C → A ↠ B → A ↠ C
f ∘ g = record
  { equivalence      = equivalence f ⊚ equivalence g
  ; right-inverse-of = to∘from
  }
  where
  open _↠_

  abstract
    to∘from = λ x →
      to f (to g (from g (from f x)))  ≡⟨ cong (to f) (right-inverse-of g (from f x)) ⟩
      to f (from f x)                  ≡⟨ right-inverse-of f x ⟩∎
      x                                ∎

-- "Equational" reasoning combinators.

infix  2 finally-↠
infixr 2 _↠⟨_⟩_

_↠⟨_⟩_ : ∀ A {B C} → A ↠ B → B ↠ C → A ↠ C
_ ↠⟨ A↠B ⟩ B↠C = B↠C ∘ A↠B

finally-↠ : ∀ A B → A ↠ B → A ↠ B
finally-↠ _ _ A↠B = A↠B

syntax finally-↠ A B A↠B = A ↠⟨ A↠B ⟩∎ B ∎

-- Σ A preserves surjections.

Σ-preserves : ∀ {A B₁ B₂} → (∀ x → B₁ x ↠ B₂ x) → Σ A B₁ ↠ Σ A B₂
Σ-preserves {B₁ = B₁} {B₂} B₁↠B₂ = record
  { equivalence = record
    { to   = Σ-map P.id (to (B₁↠B₂ _))
    ; from = Σ-map P.id (from (B₁↠B₂ _))
    }
  ; right-inverse-of = right-inverse-of′
  }
  where
  open _↠_

  abstract
    right-inverse-of′ = λ p →
      cong (_,_ _) (right-inverse-of (B₁↠B₂ _) _)

-- A lemma relating surjections and equality.

↠-≡ : ∀ {A B} (A↠B : A ↠ B) {x y : B} →
      (_↠_.from A↠B x ≡ _↠_.from A↠B y) ↠ (x ≡ y)
↠-≡ A↠B {x} {y} = record
  { equivalence = record
    { from = cong from
    ; to   = λ from-x≡from-y →
               x            ≡⟨ sym $ right-inverse-of _ ⟩
               to (from x)  ≡⟨ cong to from-x≡from-y ⟩
               to (from y)  ≡⟨ right-inverse-of _ ⟩∎
               y            ∎
    }
  ; right-inverse-of = right-inverse-of′
  }
  where
  open _↠_ A↠B

  abstract
    right-inverse-of′ = elim
      (λ {x y} x≡y → trans (sym (right-inverse-of x)) (
                       trans (cong to (cong from x≡y)) (
                       right-inverse-of y)) ≡
                     x≡y)
      (λ x → trans (sym (right-inverse-of x)) (
               trans (cong to (cong from (refl x))) (
               right-inverse-of x))                                 ≡⟨ (let eq = Lift (right-inverse-of x) in
                                                                        Tactic.prove (Trans (Sym eq)
                                                                                            (Trans (Cong to (Cong from Refl)) eq))
                                                                                     (Trans (Sym eq) eq)
                                                                                     (refl _)) ⟩
             trans (sym (right-inverse-of x)) (right-inverse-of x)  ≡⟨ G.right-inverse _ ⟩∎
             refl x                                                 ∎)
