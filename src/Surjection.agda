------------------------------------------------------------------------
-- Split surjections
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Surjection
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence
  using (_⇔_; module _⇔_) renaming (_∘_ to _⊙_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- Split surjections

-- The property of being a split surjection.

Split-surjective :
  ∀ {a b} {A : Type a} {B : Type b} → (A → B) → Type (a ⊔ b)
Split-surjective f = ∀ y → ∃ λ x → f x ≡ y

infix 0 _↠_

-- Split surjections. Note that in this development split surjections
-- are often called simply "surjections".

record _↠_ {f t} (From : Type f) (To : Type t) : Type (f ⊔ t) where
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

  -- The to function is split surjective.

  split-surjective : Split-surjective to
  split-surjective = λ y → from y , right-inverse-of y

  -- Every left inverse of to is pointwise equal to from.

  left-inverse-unique :
    (f : To → From) →
    (∀ x → f (to x) ≡ x) →
    (∀ x → f x ≡ from x)
  left-inverse-unique f left x =
    f x              ≡⟨ cong f $ sym $ right-inverse-of _ ⟩
    f (to (from x))  ≡⟨ left _ ⟩∎
    from x           ∎

  -- Every right inverse of from is pointwise equal to to.

  right-inverse-of-from-unique :
    (f : From → To) →
    (∀ x → from (f x) ≡ x) →
    (∀ x → f x ≡ to x)
  right-inverse-of-from-unique _ right x = sym $ from-to (right x)

  open _⇔_ logical-equivalence public

------------------------------------------------------------------------
-- Preorder

-- _↠_ is a preorder.

id : ∀ {a} {A : Type a} → A ↠ A
id = record
  { logical-equivalence = Logical-equivalence.id
  ; right-inverse-of    = refl
  }

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
      B ↠ C → A ↠ B → A ↠ C
f ∘ g = record
  { logical-equivalence = logical-equivalence f ⊙ logical-equivalence g
  ; right-inverse-of    = to∘from
  }
  where
  open _↠_

  to∘from : ∀ x → to f (to g (from g (from f x))) ≡ x
  to∘from = λ x →
    to f (to g (from g (from f x)))  ≡⟨ cong (to f) (right-inverse-of g (from f x)) ⟩
    to f (from f x)                  ≡⟨ right-inverse-of f x ⟩∎
    x                                ∎

-- "Equational" reasoning combinators.

infix  -1 finally-↠
infixr -2 step-↠

-- For an explanation of why step-↠ is defined in this way, see
-- Equality.step-≡.

step-↠ : ∀ {a b c} (A : Type a) {B : Type b} {C : Type c} →
         B ↠ C → A ↠ B → A ↠ C
step-↠ _ = _∘_

syntax step-↠ A B↠C A↠B = A ↠⟨ A↠B ⟩ B↠C

finally-↠ : ∀ {a b} (A : Type a) (B : Type b) → A ↠ B → A ↠ B
finally-↠ _ _ A↠B = A↠B

syntax finally-↠ A B A↠B = A ↠⟨ A↠B ⟩□ B □

------------------------------------------------------------------------
-- Some preservation/respectfulness lemmas

-- ∃ preserves surjections.

∃-cong :
  ∀ {a b₁ b₂} {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
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

-- A preservation lemma involving Σ, _↠_ and _⇔_.

Σ-cong-⇔ :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂}
  (A₁↠A₂ : A₁ ↠ A₂) → (∀ x → B₁ x ⇔ B₂ (_↠_.to A₁↠A₂ x)) →
  Σ A₁ B₁ ⇔ Σ A₂ B₂
Σ-cong-⇔ {B₂ = B₂} A₁↠A₂ B₁⇔B₂ = record
  { to   = Σ-map (_↠_.to A₁↠A₂) (_⇔_.to (B₁⇔B₂ _))
  ; from =
     Σ-map
       (_↠_.from A₁↠A₂)
       (λ {x} y → _⇔_.from
                    (B₁⇔B₂ (_↠_.from A₁↠A₂ x))
                    (subst B₂ (sym (_↠_.right-inverse-of A₁↠A₂ x)) y))
  }

-- A generalisation of ∃-cong.

Σ-cong :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂}
    {B₁ : A₁ → Type b₁} {B₂ : A₂ → Type b₂}
  (A₁↠A₂ : A₁ ↠ A₂) → (∀ x → B₁ x ↠ B₂ (_↠_.to A₁↠A₂ x)) →
  Σ A₁ B₁ ↠ Σ A₂ B₂
Σ-cong {A₁ = A₁} {A₂} {B₁} {B₂} A₁↠A₂ B₁↠B₂ = record
  { logical-equivalence = logical-equivalence′
  ; right-inverse-of    = right-inverse-of′
  }
  where
  open _↠_

  logical-equivalence′ : Σ A₁ B₁ ⇔ Σ A₂ B₂
  logical-equivalence′ = Σ-cong-⇔ A₁↠A₂ (logical-equivalence ⊚ B₁↠B₂)

  abstract
    right-inverse-of′ :
      ∀ p →
      _⇔_.to logical-equivalence′ (_⇔_.from logical-equivalence′ p) ≡ p
    right-inverse-of′ = λ p → Σ-≡,≡→≡
      (_↠_.right-inverse-of A₁↠A₂ (proj₁ p))
      (subst B₂ (_↠_.right-inverse-of A₁↠A₂ (proj₁ p))
         (to (B₁↠B₂ _) (from (B₁↠B₂ _)
            (subst B₂ (sym (_↠_.right-inverse-of A₁↠A₂ (proj₁ p)))
               (proj₂ p))))                                         ≡⟨ cong (subst B₂ _) $ right-inverse-of (B₁↠B₂ _) _ ⟩
       subst B₂ (_↠_.right-inverse-of A₁↠A₂ (proj₁ p))
         (subst B₂ (sym (_↠_.right-inverse-of A₁↠A₂ (proj₁ p)))
            (proj₂ p))                                              ≡⟨ subst-subst-sym B₂ _ _ ⟩∎
       proj₂ p ∎)

-- Π A preserves surjections (assuming extensionality).

∀-cong :
  ∀ {a b₁ b₂} →
  Extensionality a (b₁ ⊔ b₂) →
  {A : Type a} {B₁ : A → Type b₁} {B₂ : A → Type b₂} →
  (∀ x → B₁ x ↠ B₂ x) →
  ((x : A) → B₁ x) ↠ ((x : A) → B₂ x)
∀-cong {b₁ = b₁} ext B₁↠B₂ = record
  { logical-equivalence = equiv
  ; right-inverse-of    = right-inverse-of
  }
  where
  equiv = record
    { to   = (_↠_.to   ⊚ B₁↠B₂) _ ⊚_
    ; from = (_↠_.from ⊚ B₁↠B₂) _ ⊚_
    }

  abstract
    right-inverse-of : ∀ f → _⇔_.to equiv (_⇔_.from equiv f) ≡ f
    right-inverse-of = λ f →
      apply-ext (lower-extensionality lzero b₁ ext) λ x →
        _↠_.to (B₁↠B₂ x) (_↠_.from (B₁↠B₂ x) (f x))  ≡⟨ _↠_.right-inverse-of (B₁↠B₂ x) (f x) ⟩∎
        f x                                          ∎

-- A lemma relating surjections and equality.

↠-≡ : ∀ {a b} {A : Type a} {B : Type b} (A↠B : A ↠ B) {x y : B} →
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

-- A "computation rule" for ↠-≡.

to-↠-≡-refl :
  ∀ {a b} {A : Type a} {B : Type b} (A↠B : A ↠ B) {x : B} →
  _↠_.to (↠-≡ A↠B) (refl (_↠_.from A↠B x)) ≡ refl x
to-↠-≡-refl A↠B {x = x} =
  trans (sym $ _↠_.right-inverse-of A↠B x)
    (trans (cong (_↠_.to A↠B) (refl (_↠_.from A↠B x)))
       (_↠_.right-inverse-of A↠B x))                    ≡⟨ cong (λ p → trans _ (trans p _)) $ cong-refl _ ⟩

  trans (sym $ _↠_.right-inverse-of A↠B x)
    (trans (refl (_↠_.to A↠B (_↠_.from A↠B x)))
       (_↠_.right-inverse-of A↠B x))                    ≡⟨ cong (trans _) $ trans-reflˡ _ ⟩

  trans (sym $ _↠_.right-inverse-of A↠B x)
    (_↠_.right-inverse-of A↠B x)                        ≡⟨ trans-symˡ _ ⟩∎

  refl x                                                ∎

-- Decidable-equality respects surjections.

Decidable-equality-respects :
  ∀ {a b} {A : Type a} {B : Type b} →
  A ↠ B → Decidable-equality A → Decidable-equality B
Decidable-equality-respects A↠B _≟A_ x y =
  ⊎-map (to (↠-≡ A↠B))
        (λ from-x≢from-y → from-x≢from-y ⊚ from (↠-≡ A↠B))
        (from A↠B x ≟A from A↠B y)
  where open _↠_
