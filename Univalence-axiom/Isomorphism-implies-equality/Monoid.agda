------------------------------------------------------------------------
-- Isomorphism of monoids on sets coincides with equality (assuming
-- univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality.Monoid
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq hiding (id; inverse; _↔⟨_⟩_)
open Derived-definitions-and-properties eq
open import Function-universe eq hiding (id)
open import H-level eq
open import H-level.Closure eq
open import Prelude hiding (id)
open import Univalence-axiom eq
open import Weak-equivalence eq hiding (id; inverse)

-- Monoid laws (including the assumption that the carrier type is a
-- set).

Is-monoid : (C : Set) → (C → C → C) → C → Set
Is-monoid C _∙_ id =

  -- C is a set.
  Is-set C ×

  -- Left and right identity laws.
  (∀ x → id ∙ x ≡ x) ×
  (∀ x → x ∙ id ≡ x) ×

  -- Associativity.
  (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z)

-- Monoids (on sets).

Monoid : Set₁
Monoid =
  -- Carrier.
  Σ Set λ C →

  -- Binary operation.
  Σ (C → C → C) λ _∙_ →

  -- Identity.
  Σ C λ id →

  -- Laws.
  Is-monoid C _∙_ id

-- The carrier type.

Carrier : Monoid → Set
Carrier M = proj₁ M

-- The binary operation.

op : (M : Monoid) → Carrier M → Carrier M → Carrier M
op M = proj₁ (proj₂ M)

-- The identity element.

id : (M : Monoid) → Carrier M
id M = proj₁ (proj₂ (proj₂ M))

-- The monoid laws.

laws : (M : Monoid) → Is-monoid (Carrier M) (op M) (id M)
laws M = proj₂ (proj₂ (proj₂ M))

-- Monoid morphisms.

Is-homomorphism :
  (M₁ M₂ : Monoid) → (Carrier M₁ → Carrier M₂) → Set
Is-homomorphism M₁ M₂ f =
  (∀ x y → f (op M₁ x y) ≡ op M₂ (f x) (f y)) ×
  (f (id M₁) ≡ id M₂)

-- Monoid isomorphisms.

_≅_ : Monoid → Monoid → Set
M₁ ≅ M₂ =
  Σ (Carrier M₁ ↔ Carrier M₂) λ f →
  Is-homomorphism M₁ M₂ (_↔_.to f)

-- The monoid laws are propositional (assuming extensionality).

laws-propositional :
  Extensionality (# 0) (# 0) →
  (M : Monoid) →
  Propositional (Is-monoid (Carrier M) (op M) (id M))
laws-propositional ext M =
  ×-closure 1 (H-level-propositional ext 2)
  (×-closure 1 (Π-closure ext 1 λ _ →
                is-set _ _)
  (×-closure 1 (Π-closure ext 1 λ _ →
                is-set _ _)
               (Π-closure ext 1 λ _ →
                Π-closure ext 1 λ _ →
                Π-closure ext 1 λ _ →
                is-set _ _)))
  where is-set = proj₁ (laws M)

-- Monoid equality is isomorphic to equality of the carrier sets,
-- binary operations and identity elements, suitably transported
-- (assuming extensionality).

equality-triple-lemma :
  Extensionality (# 0) (# 0) →
  (M₁ M₂ : Monoid) →
  M₁ ≡ M₂ ↔
  Σ (Carrier M₁ ≡ Carrier M₂) λ C-eq →
    subst (λ C → C → C → C) C-eq (op M₁) ≡ op M₂ ×
    subst (λ C → C) C-eq (id M₁) ≡ id M₂
equality-triple-lemma
  ext (C₁ , op₁ , id₁ , laws₁) (C₂ , op₂ , id₂ , laws₂) =

  ((C₁ , op₁ , id₁ , laws₁) ≡ (C₂ , op₂ , id₂ , laws₂))               ↔⟨ inverse $ ≈-≡ $ ↔⇒≈ bij ⟩

  (((C₁ , op₁ , id₁) , laws₁) ≡ ((C₂ , op₂ , id₂) , laws₂))           ↝⟨ inverse $ ignore-propositional-component $
                                                                           laws-propositional ext (C₂ , op₂ , id₂ , laws₂) ⟩

  ((C₁ , op₁ , id₁) ≡ (C₂ , op₂ , id₂))                               ↝⟨ inverse Σ-≡,≡↔≡ ⟩

  (Σ (C₁ ≡ C₂) λ C-eq →
     subst (λ C → (C → C → C) × C) C-eq (op₁ , id₁) ≡ (op₂ , id₂))    ↝⟨ ∃-cong (λ _ → ≡⇒↝ _ $ cong (λ x → x ≡ _) $
                                                                             push-subst-, (λ C → C → C → C) (λ C → C)) ⟩
  (Σ (C₁ ≡ C₂) λ C-eq →
     (subst (λ C → C → C → C) C-eq op₁ , subst (λ C → C) C-eq id₁) ≡
     (op₂ , id₂))                                                     ↝⟨ ∃-cong (λ _ → inverse ≡×≡↔≡) ⟩□

  (Σ (C₁ ≡ C₂) λ C-eq →
     subst (λ C → C → C → C) C-eq op₁ ≡ op₂ ×
     subst (λ C → C) C-eq id₁ ≡ id₂)                                  □

  where
  bij =

    (Σ Set λ C → Σ (C → C → C) λ op → Σ C λ id → Is-monoid C op id)  ↝⟨ ∃-cong (λ _ → Σ-assoc) ⟩

    (Σ Set λ C → Σ ((C → C → C) × C) λ { (op , id) →
     Is-monoid C op id })                                            ↝⟨ Σ-assoc ⟩□

    (Σ (Σ Set λ C → (C → C → C) × C) λ { (C , op , id) →
     Is-monoid C op id })                                            □

-- If two monoids are isomorphic, then they are equal (assuming
-- univalence).

isomorphic-equal :
  Univalence (# 0) →
  Univalence (# 1) →
  (M₁ M₂ : Monoid) → M₁ ≅ M₂ → M₁ ≡ M₂
isomorphic-equal univ univ₁ M₁ M₂ (bij , bij-op , bij-id) = goal
  where
  open _≈_

  -- Our goal:

  goal : M₁ ≡ M₂

  -- Extensionality follows from univalence.

  ext : Extensionality (# 0) (# 0)
  ext = dependent-extensionality univ₁ (λ _ → univ)

  -- Hence the goal follows from monoids-equal-if, if we can prove
  -- three equalities.

  C-eq  : Carrier M₁ ≡ Carrier M₂
  op-eq : subst (λ A → A → A → A) C-eq (op M₁) ≡ op M₂
  id-eq : subst (λ A → A) C-eq (id M₁) ≡ id M₂

  goal = _↔_.from (equality-triple-lemma ext M₁ M₂)
                  (C-eq , op-eq , id-eq)

  -- Our bijection can be converted into a weak equivalence.

  equiv : Carrier M₁ ≈ Carrier M₂
  equiv = ↔⇒≈ bij

  -- Hence the first equality follows directly from univalence.

  C-eq = ≈⇒≡ univ equiv

  -- For the second equality, let us first define a "cast" operator.

  cast₂ : {A B : Set} → A ≈ B → (A → A → A) → (B → B → B)
  cast₂ eq f = λ x y → to eq (f (from eq x) (from eq y))

  -- The transport theorem implies that cast₂ equiv can be expressed
  -- using subst.

  cast₂-equiv-is-subst :
    ∀ f → cast₂ equiv f ≡ subst (λ A → A → A → A) C-eq f
  cast₂-equiv-is-subst f =
    subst-unique (λ A → A → A → A) cast₂ refl univ equiv f

  -- The second equality op-eq follows from extensionality,
  -- cast₂-equiv-is-subst, and the fact that the bijection is a
  -- monoid homomorphism.

  op-eq = ext λ x → ext λ y →
    subst (λ A → A → A → A) C-eq (op M₁) x y                   ≡⟨ cong (λ f → f x y) $ sym $ cast₂-equiv-is-subst (op M₁) ⟩
    to equiv (op M₁ (from equiv x) (from equiv y))             ≡⟨ bij-op (from equiv x) (from equiv y) ⟩
    op M₂ (to equiv (from equiv x)) (to equiv (from equiv y))  ≡⟨ cong₂ (op M₂) (right-inverse-of equiv x) (right-inverse-of equiv y) ⟩∎
    op M₂ x y                                                  ∎

  -- The development above can be repeated for the identity
  -- elements.

  cast₀ : {A B : Set} → A ≈ B → A → B
  cast₀ eq x = to eq x

  cast₀-equiv-is-subst : ∀ x → cast₀ equiv x ≡ subst (λ A → A) C-eq x
  cast₀-equiv-is-subst x =
    subst-unique (λ A → A) cast₀ refl univ equiv x

  id-eq =
    subst (λ A → A) C-eq (id M₁)  ≡⟨ sym $ cast₀-equiv-is-subst (id M₁) ⟩
    to equiv (id M₁)              ≡⟨ bij-id ⟩∎
    id M₂                         ∎

-- Equality of monoids is in fact in bijective correspondence with
-- isomorphism of monoids (assuming univalence).

isomorphism-is-equality :
  Univalence (# 0) →
  Univalence (# 1) →
  (M₁ M₂ : Monoid) → (M₁ ≅ M₂) ↔ (M₁ ≡ M₂)
isomorphism-is-equality univ univ₁
  (C₁ , op₁ , id₁ , laws₁) (C₂ , op₂ , id₂ , laws₂) =

  (Σ (C₁ ↔ C₂) λ f → Is-homomorphism M₁ M₂ (_↔_.to f))          ↝⟨ Σ-cong (↔↔≈ ext C₁-set) (λ _ → _ □) ⟩

  (Σ (C₁ ≈ C₂) λ eq → Is-homomorphism M₁ M₂ (_≈_.to eq))        ↝⟨ ∃-cong (λ eq → op-lemma eq ×-cong id-lemma eq) ⟩

  (Σ (C₁ ≈ C₂) λ eq →
     subst (λ C → C → C → C) (≈⇒≡ univ eq) op₁ ≡ op₂ ×
     subst (λ C → C) (≈⇒≡ univ eq) id₁ ≡ id₂)                   ↝⟨ inverse $ Σ-cong (≡≈≈ univ) (λ eq → ≡⇒↝ _ $
                                                                     cong (λ eq → subst (λ C → C → C → C) eq op₁ ≡ op₂ ×
                                                                                  subst (λ C → C) eq id₁ ≡ id₂) $ sym $
                                                                       _≈_.left-inverse-of (≡≈≈ univ) eq) ⟩
  (Σ (C₁ ≡ C₂) λ eq →
     subst (λ C → C → C → C) eq op₁ ≡ op₂ ×
     subst (λ C → C) eq id₁ ≡ id₂)                              ↝⟨ inverse $ equality-triple-lemma ext M₁ M₂ ⟩

  ((C₁ , op₁ , id₁ , laws₁) ≡ (C₂ , op₂ , id₂ , laws₂))         □

  where

  -- The two monoids.

  M₁ = (C₁ , op₁ , id₁ , laws₁)
  M₂ = (C₂ , op₂ , id₂ , laws₂)

  -- Extensionality follows from univalence.

  ext : Extensionality (# 0) (# 0)
  ext = dependent-extensionality univ₁ (λ _ → univ)

  -- C₁ is a set.

  C₁-set : Is-set C₁
  C₁-set = proj₁ laws₁

  module _ (eq : C₁ ≈ C₂) where

    open _≈_ eq

    -- Two component lemmas.

    op-lemma :
      (∀ x y → to (op₁ x y) ≡ op₂ (to x) (to y)) ↔
      subst (λ C → C → C → C) (≈⇒≡ univ eq) op₁ ≡ op₂
    op-lemma =
      (∀ x y → to (op₁ x y) ≡ op₂ (to x) (to y))                  ↔⟨ ∀-preserves ext (λ _ → extensionality-isomorphism ext) ⟩

      (∀ x → (λ y → to (op₁ x y)) ≡ (λ y → op₂ (to x) (to y)))    ↔⟨ ∀-preserves ext (λ _ → ↔⇒≈ $ inverse $ ∘from≡↔≡∘to ext eq) ⟩

      (∀ x → (λ y → to (op₁ x (from y))) ≡ (λ y → op₂ (to x) y))  ↔⟨ extensionality-isomorphism ext ⟩

      ((λ x y → to (op₁ x (from y))) ≡ (λ x y → op₂ (to x) y))    ↝⟨ inverse $ ∘from≡↔≡∘to ext eq ⟩

      ((λ x y → to (op₁ (from x) (from y))) ≡ (λ x y → op₂ x y))  ↝⟨ ≡⇒↝ _ $ cong (λ o → o ≡ op₂) $
                                                                       subst-unique
                                                                         (λ C → C → C → C)
                                                                         (λ eq f x y → _≈_.to eq (f (_≈_.from eq x) (_≈_.from eq y)))
                                                                         refl univ eq op₁ ⟩
      (subst (λ C → C → C → C) (≈⇒≡ univ eq) op₁ ≡ op₂)           □

    id-lemma : (to id₁ ≡ id₂) ↔
               (subst (λ C → C) (≈⇒≡ univ eq) id₁ ≡ id₂)
    id-lemma =
      (to id₁ ≡ id₂)                             ↝⟨ ≡⇒↝ _ $ cong (λ i → i ≡ id₂) $
                                                      subst-unique (λ C → C) _≈_.to refl univ eq id₁ ⟩□
      (subst (λ C → C) (≈⇒≡ univ eq) id₁ ≡ id₂)  □
