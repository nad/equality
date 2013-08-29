------------------------------------------------------------------------
-- Split surjections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Surjection
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence
  using (_⇔_; module _⇔_) renaming (_∘_ to _⊙_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- Split surjections

infix 0 _↠_

-- Split surjections. Note that in this development split surjections
-- are often called simply "surjections".

record _↠_ {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    logical-equivalence : From ⇔ To

  open _⇔_ logical-equivalence

  field
    right-inverse-of : ∀ x → to (from x) ≡ x

  -- A lemma.

  from-to : ∀ {x y} → from x ≡ y → to y ≡ x
  from-to {x} {y} from-x≡y =
    to y         ≡⟨ cong to $ sym from-x≡y ⟩
    to (from x)  ≡⟨ right-inverse-of x ⟩∎
    x            ∎

  open _⇔_ logical-equivalence public

------------------------------------------------------------------------
-- Preorder

-- _↠_ is a preorder.

id : ∀ {a} {A : Set a} → A ↠ A
id = record
  { logical-equivalence = Logical-equivalence.id
  ; right-inverse-of    = refl
  }

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ↠ C → A ↠ B → A ↠ C
f ∘ g = record
  { logical-equivalence = logical-equivalence f ⊙ logical-equivalence g
  ; right-inverse-of    = to∘from
  }
  where
  open _↠_

  abstract
    to∘from : ∀ x → to f (to g (from g (from f x))) ≡ x
    to∘from = λ x →
      to f (to g (from g (from f x)))  ≡⟨ cong (to f) (right-inverse-of g (from f x)) ⟩
      to f (from f x)                  ≡⟨ right-inverse-of f x ⟩∎
      x                                ∎

-- "Equational" reasoning combinators.

infix  0 finally-↠
infixr 0 _↠⟨_⟩_

_↠⟨_⟩_ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↠ B → B ↠ C → A ↠ C
_ ↠⟨ A↠B ⟩ B↠C = B↠C ∘ A↠B

finally-↠ : ∀ {a b} (A : Set a) (B : Set b) → A ↠ B → A ↠ B
finally-↠ _ _ A↠B = A↠B

syntax finally-↠ A B A↠B = A ↠⟨ A↠B ⟩□ B □

------------------------------------------------------------------------
-- Some preservation/respectfulness lemmas

-- ∃ preserves surjections.

∃-cong : ∀ {a b₁ b₂} {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
         (∀ x → B₁ x ↠ B₂ x) → ∃ B₁ ↠ ∃ B₂
∃-cong {B₁ = B₁} {B₂} B₁↠B₂ = record
  { logical-equivalence = record
    { to   = to′
    ; from = from′
    }
  ; right-inverse-of = right-inverse-of′
  }
  where
  open _↠_

  to′ : ∃ B₁ → ∃ B₂
  to′ = Σ-map P.id (to (B₁↠B₂ _))

  from′ : ∃ B₂ → ∃ B₁
  from′ = Σ-map P.id (from (B₁↠B₂ _))

  abstract
    right-inverse-of′ : ∀ p → to′ (from′ p) ≡ p
    right-inverse-of′ = λ p →
      cong (_,_ (proj₁ p)) (right-inverse-of (B₁↠B₂ (proj₁ p)) _)

-- A lemma relating surjections and equality.

↠-≡ : ∀ {a b} {A : Set a} {B : Set b} (A↠B : A ↠ B) {x y : B} →
      (_↠_.from A↠B x ≡ _↠_.from A↠B y) ↠ (x ≡ y)
↠-≡ A↠B {x} {y} = record
  { logical-equivalence = record
    { from = cong from
    ; to   = to′
    }
  ; right-inverse-of = right-inverse-of′
  }
  where
  open _↠_ A↠B

  to′ : from x ≡ from y → x ≡ y
  to′ = λ from-x≡from-y →
    x            ≡⟨ sym $ right-inverse-of _ ⟩
    to (from x)  ≡⟨ cong to from-x≡from-y ⟩
    to (from y)  ≡⟨ right-inverse-of _ ⟩∎
    y            ∎

  abstract
    right-inverse-of′ : ∀ p → to′ (cong from p) ≡ p
    right-inverse-of′ = elim
      (λ {x y} x≡y → trans (sym (right-inverse-of x)) (
                       trans (cong to (cong from x≡y)) (
                       right-inverse-of y)) ≡
                     x≡y)
      (λ x → trans (sym (right-inverse-of x)) (
               trans (cong to (cong from (refl x))) (
               right-inverse-of x))                                 ≡⟨ cong (λ p → trans (sym (right-inverse-of x))
                                                                                         (trans (cong to p) (right-inverse-of x)))
                                                                            (cong-refl from) ⟩
             trans (sym (right-inverse-of x)) (
               trans (cong to (refl (from x))) (
               right-inverse-of x))                                 ≡⟨ cong (λ p → trans (sym (right-inverse-of x))
                                                                                         (trans p (right-inverse-of x)))
                                                                            (cong-refl to) ⟩
             trans (sym (right-inverse-of x)) (
               trans (refl (to (from x))) (
               right-inverse-of x))                                 ≡⟨ cong (trans (sym _)) (trans-reflˡ _) ⟩
             trans (sym (right-inverse-of x)) (right-inverse-of x)  ≡⟨ trans-symˡ _ ⟩∎
             refl x                                                 ∎)

-- Decidable-equality respects surjections.

Decidable-equality-respects :
  ∀ {a b} {A : Set a} {B : Set b} →
  A ↠ B → Decidable-equality A → Decidable-equality B
Decidable-equality-respects A↠B _≟A_ x y =
  ⊎-map (to (↠-≡ A↠B))
        (λ from-x≢from-y → from-x≢from-y ⊚ from (↠-≡ A↠B))
        (from A↠B x ≟A from A↠B y)
  where open _↠_
