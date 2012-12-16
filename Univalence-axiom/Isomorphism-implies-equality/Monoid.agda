------------------------------------------------------------------------
-- Isomorphic monoids on sets are equal (assuming univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality.Monoid
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq hiding (id)
open Derived-definitions-and-properties eq
open import Equivalence using (module _⇔_)
open import H-level eq
open import H-level.Closure eq
open import Prelude hiding (id)
open import Univalence-axiom eq
open import Weak-equivalence eq hiding (id)

-- If two monoids (on sets) are isomorphic, then they are equal. This
-- is proved twice, once using a right-nested definition of monoids,
-- and once using a left-nested definition.

module Monoid-right-nested where

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
  --
  -- I got the idea to formulate this property as a separate lemma
  -- from Mike Shulman. /NAD

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

  -- One can prove that two monoids are equal by proving that the
  -- carrier sets, binary operations and identity elements (suitably
  -- transported) are equal (assuming extensionality).
  --
  -- I got the idea to formulate this property as a separate lemma
  -- from Mike Shulman. /NAD

  monoids-equal-if :
    Extensionality (# 0) (# 0) →
    (M₁ M₂ : Monoid)
    (C-eq : Carrier M₁ ≡ Carrier M₂) →
    subst (λ A → A → A → A) C-eq (op M₁) ≡ op M₂ →
    subst (λ A → A) C-eq (id M₁) ≡ id M₂ →
    M₁ ≡ M₂
  monoids-equal-if ext M₁ M₂ C-eq op-eq id-eq =

    (Carrier M₁ , op M₁ , id M₁ , laws M₁)                                ≡⟨ Σ-≡,≡→≡ C-eq (refl _) ⟩

    (Carrier M₂ ,
       subst (λ A → Σ (A → A → A) λ _∙_ → Σ A λ id → Is-monoid A _∙_ id)
             C-eq
             (op M₁ , id M₁ , laws M₁))                                   ≡⟨ cong (λ rest → Carrier M₂ , rest) $
                                                                               push-subst-pair′
                                                                                 (λ A → A → A → A)
                                                                                 (λ { (A , _∙_) → Σ A λ id → Is-monoid A _∙_ id })
                                                                                 op-eq ⟩
    (Carrier M₂ , op M₂ ,
       subst (λ { (A , _∙_) → Σ A λ id → Is-monoid A _∙_ id })
             (Σ-≡,≡→≡ C-eq op-eq)
             (id M₁ , laws M₁))                                           ≡⟨ cong (λ rest → Carrier M₂ , op M₂ , rest) $
                                                                               push-subst-pair′
                                                                                 (λ { (A , _∙_) → A })
                                                                                 (λ { ((A , _∙_) , id) → Is-monoid A _∙_ id })
                                                                                 id-eq′ ⟩
    (Carrier M₂ , op M₂ , id M₂ ,
       subst (λ { ((A , _∙_) , id) → Is-monoid A _∙_ id })
             (Σ-≡,≡→≡ (Σ-≡,≡→≡ C-eq op-eq) id-eq′)
             (laws M₁))                                                   ≡⟨ cong (λ rest → Carrier M₂ , op M₂ , id M₂ , rest) $
                                                                               _⇔_.to propositional⇔irrelevant
                                                                                      (laws-propositional ext M₂) _ _ ⟩∎
    (Carrier M₂ , op M₂ , id M₂ , laws M₂)                                ∎

    where
    id-eq′ =
      subst (λ { (A , _∙_) → A }) (Σ-≡,≡→≡ C-eq op-eq) (id M₁)   ≡⟨ subst-∘ (λ A → A) proj₁ _ ⟩
      subst (λ A → A) (cong proj₁ (Σ-≡,≡→≡ C-eq op-eq)) (id M₁)  ≡⟨ cong (λ eq → subst (λ A → A) eq (id M₁)) $ proj₁-Σ-≡,≡→≡ _ _ ⟩
      subst (λ A → A) C-eq (id M₁)                               ≡⟨ id-eq ⟩∎
      id M₂                                                      ∎

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

    goal = monoids-equal-if ext M₁ M₂ C-eq op-eq id-eq

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

module Monoid-left-nested where

  open Monoid-right-nested public using (Is-monoid)

  -- Monoids (on sets).

  Monoid : Set₁
  Monoid =
    Σ (Σ (Σ

    -- Carrier.
    Set λ A →

    -- Binary operation.
    A → A → A) λ { (A , _) →

    -- Identity.
    A }) λ { ((A , _∙_) , id) →

    -- Laws.
    Is-monoid A _∙_ id }

  -- The carrier type.

  Carrier : Monoid → Set
  Carrier M = proj₁ (proj₁ (proj₁ M))

  -- The binary operation.

  op : (M : Monoid) → Carrier M → Carrier M → Carrier M
  op M = proj₂ (proj₁ (proj₁ M))

  -- The identity element.

  id : (M : Monoid) → Carrier M
  id M = proj₂ (proj₁ M)

  -- The monoid laws.

  laws : (M : Monoid) → Is-monoid (Carrier M) (op M) (id M)
  laws M = proj₂ M

  -- Converts a "left-nested monoid" to a "right-nested" one.

  right-nested : Monoid → Monoid-right-nested.Monoid
  right-nested (((A , op) , id) , laws) = (A , op , id , laws)

  -- Monoid morphisms.

  Is-homomorphism :
    (M₁ M₂ : Monoid) → (Carrier M₁ → Carrier M₂) → Set
  Is-homomorphism M₁ M₂ f =
    Monoid-right-nested.Is-homomorphism
      (right-nested M₁) (right-nested M₂) f

  -- Monoid isomorphisms.

  _≅_ : Monoid → Monoid → Set
  M₁ ≅ M₂ = Monoid-right-nested._≅_ (right-nested M₁) (right-nested M₂)

  -- The monoid laws are propositional (assuming extensionality).
  --
  -- I got the idea to formulate this property as a separate lemma
  -- from Mike Shulman. /NAD

  laws-propositional :
    Extensionality (# 0) (# 0) →
    (M : Monoid) →
    Propositional (Is-monoid (Carrier M) (op M) (id M))
  laws-propositional ext M =
    Monoid-right-nested.laws-propositional
      ext (right-nested M)

  -- One can prove that two monoids are equal by proving that the
  -- carrier sets, binary operations and identity elements (suitably
  -- transported) are equal (assuming extensionality).
  --
  -- I got the idea to formulate this property as a separate lemma
  -- from Mike Shulman. /NAD

  monoids-equal-if :
    Extensionality (# 0) (# 0) →
    (M₁ M₂ : Monoid)
    (C-eq : Carrier M₁ ≡ Carrier M₂) →
    subst (λ A → A → A → A) C-eq (op M₁) ≡ op M₂ →
    subst (λ A → A) C-eq (id M₁) ≡ id M₂ →
    M₁ ≡ M₂
  monoids-equal-if ext M₁ M₂ C-eq op-eq id-eq =
    Σ-≡,≡→≡ (Σ-≡,≡→≡ (Σ-≡,≡→≡ C-eq op-eq) id-eq′)
            (_⇔_.to propositional⇔irrelevant
                    (laws-propositional ext M₂) _ _)
    where
    id-eq′ =
      subst (λ { (A , _∙_) → A }) (Σ-≡,≡→≡ C-eq op-eq) (id M₁)   ≡⟨ subst-∘ (λ A → A) proj₁ _ ⟩
      subst (λ A → A) (cong proj₁ (Σ-≡,≡→≡ C-eq op-eq)) (id M₁)  ≡⟨ cong (λ eq → subst (λ A → A) eq (id M₁)) $ proj₁-Σ-≡,≡→≡ _ _ ⟩
      subst (λ A → A) C-eq (id M₁)                               ≡⟨ id-eq ⟩∎
      id M₂                                                      ∎

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

    goal = monoids-equal-if ext M₁ M₂ C-eq op-eq id-eq

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

-- The main differences between the use of right-nested and
-- left-nested definitions of monoids seem to be the following:
-- * It is a bit harder to write down a left-nested definition.
-- * It is much harder to prove the "monoids-equal-if" property for
--   the right-nested definition.
