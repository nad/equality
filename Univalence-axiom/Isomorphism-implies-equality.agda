------------------------------------------------------------------------
-- A large class of algebraic structures satisfy the property
-- that isomorphic structures are equal (assuming univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq using (_↔_; module _↔_)
open Derived-definitions-and-properties eq
open import Equivalence hiding (_∘_; inverse)
open import Function-universe eq
open import H-level eq
open import H-level.Closure eq
open import Prelude hiding (_∘_)
open import Univalence-axiom eq
open import Weak-equivalence eq as Weak hiding (_∘_; inverse)

------------------------------------------------------------------------
-- N-ary functions

-- N-ary functions.

_^_⟶_ : Set → ℕ → Set → Set
A ^ zero  ⟶ B = B
A ^ suc n ⟶ B = A → A ^ n ⟶ B

module N-ary where

  -- N-ary function morphisms.

  Is-_-ary-morphism :
    (n : ℕ) {A B : Set} → (A ^ n ⟶ A) → (B ^ n ⟶ B) → (A → B) → Set
  Is- zero  -ary-morphism x₁ x₂ m = m x₁ ≡ x₂
  Is- suc n -ary-morphism f₁ f₂ m =
    ∀ x → Is- n -ary-morphism (f₁ x) (f₂ (m x)) m

  abstract

    -- If _↔_.to m is a morphism, then _↔_.from m is also a morphism.

    from-also-_-ary-morphism :
      (n : ℕ) {A B : Set}
      (f₁ : A ^ n ⟶ A) (f₂ : B ^ n ⟶ B) (m : A ↔ B) →
      Is- n -ary-morphism f₁ f₂ (_↔_.to m) →
      Is- n -ary-morphism f₂ f₁ (_↔_.from m)
    from-also- zero  -ary-morphism x₁ x₂ m is = _↔_.to-from m is
    from-also- suc n -ary-morphism f₁ f₂ m is = λ x →
      from-also- n -ary-morphism (f₁ (from x)) (f₂ x) m
        (subst (λ y → Is- n -ary-morphism (f₁ (from x)) (f₂ y) to)
               (right-inverse-of x)
               (is (from x)))
      where open _↔_ m

  -- Changes the type of an n-ary function.

  cast : {A₁ A₂ : Set} → A₁ ≈ A₂ → ∀ n → A₁ ^ n ⟶ A₁ → A₂ ^ n ⟶ A₂
  cast A₁≈A₂ zero    = _≈_.to A₁≈A₂
  cast A₁≈A₂ (suc n) = λ f x → cast A₁≈A₂ n (f (_≈_.from A₁≈A₂ x))

  abstract

    -- Cast simplification lemma.

    cast-id : {A : Set} →
              (∀ n → Extensionality A (λ _ → A ^ n ⟶ A)) →
              ∀ n (f : A ^ n ⟶ A) → cast Weak.id n f ≡ f
    cast-id ext zero    x = refl x
    cast-id ext (suc n) f = ext n $ λ x → cast-id ext n (f x)

    -- We can express cast (applied to an isomorphism) as an instance
    -- of subst (assuming extensionality and univalence).

    cast-is-subst :
      (∀ {A : Set} n → Extensionality A (λ _ → A ^ n ⟶ A)) →
      {A₁ A₂ : Set}
      (univ : Univalence-axiom′ A₁ A₂)
      (A₁≈A₂ : A₁ ≈ A₂) (n : ℕ) (f : A₁ ^ n ⟶ A₁) →
      cast A₁≈A₂ n f ≡
      subst (λ C → C ^ n ⟶ C) (_≈_.from (≡≈≈ univ) A₁≈A₂) f
    cast-is-subst ext univ A₁≈A₂ n =
      subst-unique
        (λ A → A ^ n ⟶ A)
        (λ A≈B f → cast A≈B n f)
        (cast-id ext n)
        univ
        A₁≈A₂

    -- If there is an isomorphism from f₁ to f₂, then the
    -- corresponding instance of cast maps f₁ to f₂ (assuming
    -- extensionality).

    cast-isomorphism :
      {A₁ A₂ : Set} →
      (∀ n → Extensionality A₂ (λ _ → A₂ ^ n ⟶ A₂)) →
      (A₁≈A₂ : A₁ ≈ A₂)
      (n : ℕ) (f₁ : A₁ ^ n ⟶ A₁) (f₂ : A₂ ^ n ⟶ A₂) →
      Is- n -ary-morphism f₁ f₂ (_≈_.to A₁≈A₂) →
      cast A₁≈A₂ n f₁ ≡ f₂
    cast-isomorphism ext A₁≈A₂ zero    x₁ x₂ is = is
    cast-isomorphism ext A₁≈A₂ (suc n) f₁ f₂ is = ext n $ λ x →
      cast A₁≈A₂ n (f₁ (from x))  ≡⟨ cast-isomorphism ext A₁≈A₂ n _ _ (is (from x)) ⟩
      f₂ (to (from x))            ≡⟨ cong f₂ (right-inverse-of x) ⟩∎
      f₂ x                        ∎
      where open _≈_ A₁≈A₂

    -- Combining the results above we get the following: if there is
    -- an isomorphism from f₁ to f₂, then the corresponding instance
    -- of subst maps f₁ to f₂ (assuming extensionality and
    -- univalence).

    subst-isomorphism :
      (∀ {A : Set} n → Extensionality A (λ _ → A ^ n ⟶ A)) →
      {A₁ A₂ : Set}
      (univ : Univalence-axiom′ A₁ A₂)
      (A₁≈A₂ : A₁ ≈ A₂)
      (n : ℕ) (f₁ : A₁ ^ n ⟶ A₁) (f₂ : A₂ ^ n ⟶ A₂) →
      Is- n -ary-morphism f₁ f₂ (_≈_.to A₁≈A₂) →
      subst (λ A → A ^ n ⟶ A) (_≈_.from (≡≈≈ univ) A₁≈A₂) f₁ ≡ f₂
    subst-isomorphism ext univ A₁≈A₂ n f₁ f₂ is =
      subst (λ A → A ^ n ⟶ A) (_≈_.from (≡≈≈ univ) A₁≈A₂) f₁  ≡⟨ sym $ cast-is-subst ext univ A₁≈A₂ n f₁ ⟩
      cast A₁≈A₂ n f₁                                         ≡⟨ cast-isomorphism ext A₁≈A₂ n f₁ f₂ is ⟩∎
      f₂                                                      ∎

------------------------------------------------------------------------
-- Simple types

-- This section contains a generalisation of the development for n-ary
-- functions above.

-- Simple types.

data Type : Set where
  base : Type
  _⟶_  : Type → Type → Type

-- Interpretation of a simple type.

⟦_⟧→ : Type → Set → Set
⟦ base  ⟧→ A = A
⟦ σ ⟶ τ ⟧→ A = ⟦ σ ⟧→ A → ⟦ τ ⟧→ A

module Simple where

  -- Cast.

  cast : (σ : Type) {A B : Set} → A ⇔ B → ⟦ σ ⟧→ A → ⟦ σ ⟧→ B
  cast base    m x = _⇔_.to m x
  cast (σ ⟶ τ) m f = cast τ m ∘ f ∘ cast σ (inverse m)

  -- Isomorphisms between simply typed values.

  Is-isomorphism :
    (σ : Type) {A B : Set} → ⟦ σ ⟧→ A → ⟦ σ ⟧→ B → A ↔ B → Set
  Is-isomorphism base    x₁ x₂ m = _↔_.to m x₁ ≡ x₂
  Is-isomorphism (σ ⟶ τ) f₁ f₂ m =
    ∀ f → Is-isomorphism τ (f₁ f) (f₂ (cast σ (_↔_.equivalence m) f)) m

  -- Alternative definition of isomorphisms.

  Is-isomorphism′ :
    (σ : Type) {A B : Set} → ⟦ σ ⟧→ A → ⟦ σ ⟧→ B → A ↔ B → Set
  Is-isomorphism′ σ f₁ f₂ m = cast σ (_↔_.equivalence m) f₁ ≡ f₂

  abstract

    -- If you cast twice, in a certain way, then you get back what you
    -- started with.

    cast-twice :
      {A B : Set} →
      ((σ τ : Type) → Extensionality (⟦ σ ⟧→ A) (λ _ → ⟦ τ ⟧→ A)) →
      (σ : Type) (m : A ↔ B) (f : ⟦ σ ⟧→ A) →
      let m′ = _↔_.equivalence m in
      cast σ (inverse m′) (cast σ m′ f) ≡ f
    cast-twice ext base    m x = _↔_.left-inverse-of m x
    cast-twice ext (σ ⟶ τ) m f = ext σ τ λ x →
      let m′ = _↔_.equivalence m in
      (cast τ (inverse m′) $ cast τ m′ $
         f $ cast σ (inverse m′) $ cast σ m′ x)  ≡⟨ cast-twice ext τ m _ ⟩
      (f $ cast σ (inverse m′) $ cast σ m′ x)    ≡⟨ cong f $ cast-twice ext σ m x ⟩∎
      f x                                        ∎

    -- If m is an isomorphism, then inverse m is also an isomorphism
    -- (assuming extensionality).

    inverse-also-isomorphism :
      {A B : Set} →
      ((σ τ : Type) → Extensionality (⟦ σ ⟧→ B) (λ _ → ⟦ τ ⟧→ B)) →
      (σ : Type) (f₁ : ⟦ σ ⟧→ A) (f₂ : ⟦ σ ⟧→ B) (m : A ↔ B) →
      Is-isomorphism σ f₁ f₂ m →
      Is-isomorphism σ f₂ f₁ (inverse m)
    inverse-also-isomorphism ext base      f₁ f₂ m is = _↔_.to-from m is
    inverse-also-isomorphism ext (σ₁ ⟶ σ₂) f₁ f₂ m is = λ f →
      let f′ = cast σ₁ (inverse $ _↔_.equivalence m) f in
      inverse-also-isomorphism ext σ₂ (f₁ f′) (f₂ f) m $
        subst (λ g → Is-isomorphism σ₂ (f₁ f′) (f₂ g) m)
              (cast-twice ext σ₁ (inverse m) f)
              (is f′)

    -- Cast simplification lemma.

    cast-id :
      {A : Set} →
      ((σ τ : Type) → Extensionality (⟦ σ ⟧→ A) (λ _ → ⟦ τ ⟧→ A)) →
      ∀ σ (f : ⟦ σ ⟧→ A) → cast σ (_≈_.equivalence Weak.id) f ≡ f
    cast-id ext base    x = refl x
    cast-id ext (σ ⟶ τ) f = ext σ τ $ λ x →
      let id = _≈_.equivalence Weak.id in
      cast τ id (f (cast σ (inverse id) x))  ≡⟨ cast-id ext τ _ ⟩
      f (cast σ (inverse id) x)              ≡⟨ cong f $ cast-id ext σ x ⟩∎
      f x                                    ∎

    -- We can express cast (applied to an isomorphism) as an instance
    -- of subst (assuming extensionality and univalence).

    cast-is-subst :
      ({A : Set} (σ τ : Type) →
       Extensionality (⟦ σ ⟧→ A) (λ _ → ⟦ τ ⟧→ A)) →
      {A₁ A₂ : Set}
      (univ : Univalence-axiom′ A₁ A₂)
      (m : A₁ ↔ A₂) (σ : Type) (f : ⟦ σ ⟧→ A₁) →
      let m′ = bijection⇒weak-equivalence m in
      cast σ (_↔_.equivalence m) f ≡
        subst ⟦ σ ⟧→ (_≈_.from (≡≈≈ univ) m′) f
    cast-is-subst ext univ m σ =
      subst-unique
        ⟦ σ ⟧→
        (λ A≈B f → cast σ (_≈_.equivalence A≈B) f)
        (cast-id ext σ)
        univ
        (bijection⇒weak-equivalence m)

    -- The two definitions of isomorphisms are equivalent (assuming
    -- extensionality).

    isomorphism-definitions-equivalent :
      {A₁ A₂ : Set} →
      ((σ τ : Type) → Extensionality (⟦ σ ⟧→ A₁) (λ _ → ⟦ τ ⟧→ A₁)) →
      ((σ τ : Type) → Extensionality (⟦ σ ⟧→ A₂) (λ _ → ⟦ τ ⟧→ A₂)) →
      (m : A₁ ↔ A₂)
      (σ : Type) (f₁ : ⟦ σ ⟧→ A₁) (f₂ : ⟦ σ ⟧→ A₂) →
      Is-isomorphism σ f₁ f₂ m ⇔ Is-isomorphism′ σ f₁ f₂ m
    isomorphism-definitions-equivalent {A₁} {A₂} ext₁ ext₂ m =
      λ σ f₁ f₂ → record { to = to σ f₁ f₂; from = from σ f₁ f₂ }
      where
      m′ : A₁ ⇔ A₂
      m′ = _↔_.equivalence m

      to : ∀ σ f₁ f₂ →
           Is-isomorphism σ f₁ f₂ m → Is-isomorphism′ σ f₁ f₂ m
      to base    f₁ f₂ is = is
      to (σ ⟶ τ) f₁ f₂ is = ext₂ σ τ λ x →
        cast τ m′ (f₁ (cast σ (inverse m′) x))  ≡⟨ to τ _ _ (is _) ⟩
        f₂ (cast σ m′ (cast σ (inverse m′) x))  ≡⟨ cong f₂ (cast-twice ext₂ σ (inverse m) _) ⟩∎
        f₂ x                                    ∎

      from : ∀ σ f₁ f₂ →
             Is-isomorphism′ σ f₁ f₂ m → Is-isomorphism σ f₁ f₂ m
      from base    f₁ f₂ is = is
      from (σ ⟶ τ) f₁ f₂ is = λ f → from τ (f₁ f) (f₂ (cast σ m′ f))
        (cast τ m′ (f₁ f)                                    ≡⟨ cong (cast τ m′ ∘ f₁) $ sym $ cast-twice ext₁ σ m f ⟩
         cast τ m′ (f₁ (cast σ (inverse m′) (cast σ m′ f)))  ≡⟨ cong (λ g → g (cast σ m′ f)) is ⟩∎
         f₂ (cast σ m′ f)                                    ∎)

    -- Combining the results above we get the following: if there is
    -- an isomorphism from f₁ to f₂, then the corresponding instance
    -- of subst maps f₁ to f₂ (assuming extensionality and
    -- univalence).

    subst-isomorphism :
      ({A : Set} (σ τ : Type) →
       Extensionality (⟦ σ ⟧→ A) (λ _ → ⟦ τ ⟧→ A)) →
      {A₁ A₂ : Set}
      (univ : Univalence-axiom′ A₁ A₂)
      (m : A₁ ↔ A₂)
      (σ : Type) (f₁ : ⟦ σ ⟧→ A₁) (f₂ : ⟦ σ ⟧→ A₂) →
      let m′ = bijection⇒weak-equivalence m in
      Is-isomorphism σ f₁ f₂ m →
      subst ⟦ σ ⟧→ (_≈_.from (≡≈≈ univ) m′) f₁ ≡ f₂
    subst-isomorphism ext univ m σ f₁ f₂ is =
      subst ⟦ σ ⟧→
        (_≈_.from (≡≈≈ univ) (bijection⇒weak-equivalence m)) f₁  ≡⟨ sym $ cast-is-subst ext univ m σ f₁ ⟩
      cast σ (_↔_.equivalence m) f₁                              ≡⟨ _⇔_.to (isomorphism-definitions-equivalent ext ext m σ f₁ f₂) is ⟩∎
      f₂                                                         ∎

------------------------------------------------------------------------
-- A class of algebraic structures

-- An algebraic structure universe.

mutual

  infixl 5 _+operator_ _+ho-operator_ _+axiom_

  -- Codes for structures.

  data Structure : Set₁ where
    empty : Structure

    -- N-ary functions.
    _+operator_ : Structure → (n : ℕ) → Structure

    -- Simply typed functions.
    _+ho-operator_ : Structure → (σ : Type) → Structure

    -- Arbitrary /propositional/ axioms.
    _+axiom_ : (s : Structure)
               (P : ∃ λ (P : (A : Set) → ⟦ s ⟧ A → Set) →
                      ∀ A s → Propositional (P A s)) →
               Structure

  -- Interpretation of the codes.

  ⟦_⟧ : Structure → Set → Set₁
  ⟦ empty                 ⟧ A = ↑ _ ⊤
  ⟦ s +operator n         ⟧ A = ⟦ s ⟧ A × (A ^ n ⟶ A)
  ⟦ s +ho-operator σ      ⟧ A = ⟦ s ⟧ A × ⟦ σ ⟧→ A
  ⟦ s +axiom (P , P-prop) ⟧ A = Σ (⟦ s ⟧ A) (P A)

-- Top-level interpretation.

⟪_⟫ : Structure → Set₁
⟪ s ⟫ = ∃ ⟦ s ⟧

-- The property of being an isomorphism.

Is-structure-isomorphism :
  (s : Structure) →
  {A B : Set} → ⟦ s ⟧ A → ⟦ s ⟧ B →
  A ↔ B → Set
Is-structure-isomorphism empty              _          _          m = ⊤
Is-structure-isomorphism (s +axiom _)       (s₁ , _)   (s₂ , _)   m =
  Is-structure-isomorphism s s₁ s₂ m
Is-structure-isomorphism (s +operator n)    (s₁ , op₁) (s₂ , op₂) m =
  Is-structure-isomorphism s s₁ s₂ m ×
  N-ary.Is- n -ary-morphism op₁ op₂ (_↔_.to m)
Is-structure-isomorphism (s +ho-operator σ) (s₁ , op₁) (s₂ , op₂) m =
  Is-structure-isomorphism s s₁ s₂ m ×
  Simple.Is-isomorphism σ op₁ op₂ m

-- Isomorphisms.

Isomorphism : (s : Structure) → ⟪ s ⟫ → ⟪ s ⟫ → Set
Isomorphism s (A₁ , s₁) (A₂ , s₂) =
  ∃ λ (m : A₁ ↔ A₂) → Is-structure-isomorphism s s₁ s₂ m

abstract

  -- If m is an isomorphism, then inverse m is also an isomorphism
  -- (assuming extensionality).

  inverse-also-structure-isomorphism :
    {A B : Set} →
    ((σ τ : Type) → Extensionality (⟦ σ ⟧→ B) (λ _ → ⟦ τ ⟧→ B)) →
    (s : Structure) {s₁ : ⟦ s ⟧ A} {s₂ : ⟦ s ⟧ B} →
    (m : A ↔ B) →
    Is-structure-isomorphism s s₁ s₂ m →
    Is-structure-isomorphism s s₂ s₁ (inverse m)
  inverse-also-structure-isomorphism ext empty              m = _
  inverse-also-structure-isomorphism ext (s +axiom _)       m =
    inverse-also-structure-isomorphism ext s m
  inverse-also-structure-isomorphism ext (s +operator n)    m =
    Σ-map (inverse-also-structure-isomorphism ext s m)
          (N-ary.from-also- n -ary-morphism _ _ m)
  inverse-also-structure-isomorphism ext (s +ho-operator σ) m =
    Σ-map (inverse-also-structure-isomorphism ext s m)
          (Simple.inverse-also-isomorphism ext σ _ _ m)

  -- Isomorphic structures are equal (assuming univalence).

  isomorphic-equal :
    Univalence-axiom′ (Set ²/≡) Set →
    Univalence-axiom lzero →
    (s : Structure) (s₁ s₂ : ⟪ s ⟫) →
    Isomorphism s s₁ s₂ → s₁ ≡ s₂
  isomorphic-equal univ₁ univ₂
    s (A₁ , s₁) (A₂ , s₂) (m , is) =

    (A₁ , s₁)  ≡⟨ Σ-≡,≡→≡ A₁≡A₂ (lemma s s₁ s₂ is) ⟩∎
    (A₂ , s₂)  ∎

    where

    -- Extensionality follows from univalence.

    ext : {A : Set} {B : A → Set} → Extensionality A B
    ext = dependent-extensionality univ₁ (λ _ → univ₂)

    -- The presence of the bijection implies that the structure's
    -- underlying types are equal (due to univalence).

    A₁≡A₂ : A₁ ≡ A₂
    A₁≡A₂ = _≈_.from (≡≈≈ univ₂) $ bijection⇒weak-equivalence m

    -- We can lift subst-isomorphism to structures by recursion on
    -- structure codes.

    lemma : (s : Structure)
            (s₁ : ⟦ s ⟧ A₁) (s₂ : ⟦ s ⟧ A₂) →
            Is-structure-isomorphism s s₁ s₂ m →
            subst ⟦ s ⟧ A₁≡A₂ s₁ ≡ s₂
    lemma empty _ _ _ = refl _

    lemma (s +axiom (P , P-prop)) (s₁ , ax₁) (s₂ , ax₂) is =
      subst (λ A → Σ (⟦ s ⟧ A) (P A)) A₁≡A₂ (s₁ , ax₁)  ≡⟨ push-subst-pair′ ⟦ s ⟧ (uncurry P) (lemma s s₁ s₂ is) ⟩
      (s₂ , _)                                          ≡⟨ cong (_,_ s₂) $ _⇔_.to propositional⇔irrelevant (P-prop _ _) _ _ ⟩∎
      (s₂ , ax₂)                                        ∎

    lemma (s +operator n) (s₁ , op₁) (s₂ , op₂) (is-s , is-o) =
      subst (λ A → ⟦ s ⟧ A × (A ^ n ⟶ A)) A₁≡A₂ (s₁ , op₁)  ≡⟨ push-subst-pair′ ⟦ s ⟧ (λ { (A , _) → A ^ n ⟶ A }) (lemma s s₁ s₂ is-s) ⟩

      (s₂ , subst₂ (λ { (A , _) → A ^ n ⟶ A }) A₁≡A₂
                   (lemma s s₁ s₂ is-s) op₁)                ≡⟨ cong (_,_ s₂) $ subst₂-proj₁ (λ A → A ^ n ⟶ A) ⟩

      (s₂ , subst (λ A → A ^ n ⟶ A) A₁≡A₂ op₁)              ≡⟨ cong (_,_ s₂) $ N-ary.subst-isomorphism (λ _ → ext) univ₂
                                                                                 (bijection⇒weak-equivalence m) n op₁ op₂ is-o ⟩∎
      (s₂ , op₂)                                            ∎

    lemma (s +ho-operator σ) (s₁ , op₁) (s₂ , op₂) (is-s , is-o) =
      subst (λ A → ⟦ s ⟧ A × ⟦ σ ⟧→ A) A₁≡A₂ (s₁ , op₁)  ≡⟨ push-subst-pair′ ⟦ s ⟧ (λ { (A , _) → ⟦ σ ⟧→ A }) (lemma s s₁ s₂ is-s) ⟩

      (s₂ , subst₂ (λ { (A , _) → ⟦ σ ⟧→ A }) A₁≡A₂
                   (lemma s s₁ s₂ is-s) op₁)             ≡⟨ cong (_,_ s₂) $ subst₂-proj₁ ⟦ σ ⟧→ ⟩

      (s₂ , subst ⟦ σ ⟧→ A₁≡A₂ op₁)                      ≡⟨ cong (_,_ s₂) $ Simple.subst-isomorphism (λ _ _ → ext) univ₂ m σ op₁ op₂ is-o ⟩∎
      (s₂ , op₂)                                         ∎

------------------------------------------------------------------------
-- Some example structures

-- Example: magmas.

magma : Structure
magma = empty +operator 2

Magma : Set₁
Magma = ⟪ magma ⟫

private

  -- An unfolding of Magma.

  Magma-unfolded : Magma ≡ ∃ λ (A : Set) → ↑ _ ⊤ × (A → A → A)
  Magma-unfolded = refl _

-- Example: semigroups. The definition uses extensionality to prove
-- that the axioms are propositional. Note that one axiom states that
-- the underlying type is a set. This assumption is used to prove that
-- the other axioms are propositional.

semigroup :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure
semigroup ext =
  empty

  +axiom
    ( (λ A _ → Is-set A)
    , is-set-prop
    )

  +operator 2

  +axiom
    ( (λ { _ (_ , _∙_) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
    , assoc-prop
    )

  where
  is-set-prop = λ _ _ → H-level-propositional ext 2

  assoc-prop = λ { _ ((_ , A-set) , _) →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

Semigroup :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Semigroup ext = ⟪ semigroup ext ⟫

private

  -- An unfolding of Semigroup.

  Semigroup-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Semigroup ext ≡ Σ
      Set                                    λ A → Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Is-set A                             ) λ _ →
      A → A → A                            ) λ { (_ , _∙_) →
      ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z }
  Semigroup-unfolded _ = refl _

-- Example: abelian groups.

abelian-group :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure
abelian-group ext =
  empty

  -- The underlying type is a set.
  +axiom
    ( (λ A _ → Is-set A)
    , is-set-prop
    )

  -- The binary group operation.
  +operator 2

  -- Commutativity.
  +axiom
    ( (λ { _ (_ , _∙_) →
           ∀ x y → x ∙ y ≡ y ∙ x })
    , comm-prop
    )

  -- Associativity.
  +axiom
    ( (λ { _ ((_ , _∙_) , _) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
    , assoc-prop
    )

  -- Identity.
  +operator 0

  -- Left identity.
  +axiom
    ( (λ { _ ((((_ , _∙_) , _) , _) , e) →
           ∀ x → e ∙ x ≡ x })
    , left-identity-prop
    )

  -- Right identity.
  +axiom
    ( (λ { _ (((((_ , _∙_) , _) , _) , e) , _) →
           ∀ x → x ∙ e ≡ x })
    , right-identity-prop
    )

  -- Inverse.
  +operator 1

  -- Left inverse.
  +axiom
    ( (λ { _ (((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) →
           ∀ x → (x ⁻¹) ∙ x ≡ e })
    , left-inverse-prop
    )

  -- Right inverse.
  +axiom
    ( (λ { _ ((((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) , _) →
           ∀ x → x ∙ (x ⁻¹) ≡ e })
    , right-inverse-prop
    )

  where
  is-set-prop = λ _ _ → H-level-propositional ext 2

  comm-prop =
    λ { _ ((_ , A-set) , _) →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  assoc-prop =
    λ { _ (((_ , A-set) , _) , _) →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  left-identity-prop =
    λ { _ (((((_ , A-set) , _) , _) , _) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  right-identity-prop =
    λ { _ ((((((_ , A-set) , _) , _) , _) , _) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  left-inverse-prop =
    λ { _ ((((((((_ , A-set) , _) , _) , _) , _) , _) , _) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  right-inverse-prop =
    λ { _ (((((((((_ , A-set) , _) , _) , _) , _) , _) , _) , _) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

Abelian-group :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Abelian-group ext = ⟪ abelian-group ext ⟫

private

  -- An unfolding of Abelian-group. Note that the inner structure is
  -- left-nested.

  Abelian-group-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Abelian-group ext ≡ Σ
      Set                                    λ A → Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Is-set A                             ) λ _ →
      A → A → A                            ) λ {        (_ , _∙_) →
      ∀ x y → x ∙ y ≡ y ∙ x               }) λ {       ((_ , _∙_) , _) →
      ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z }) λ _ →
      A                                    ) λ {     ((((_ , _∙_) , _) , _) , e) →
      ∀ x → e ∙ x ≡ x                     }) λ {    (((((_ , _∙_) , _) , _) , e) , _) →
      ∀ x → x ∙ e ≡ x                     }) λ _ →
      A → A                                ) λ {  (((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) →
      ∀ x → (x ⁻¹) ∙ x ≡ e                }) λ { ((((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) , _) →
      ∀ x → x ∙ (x ⁻¹) ≡ e                }

  Abelian-group-unfolded _ = refl _

-- Example: Sets with fixed-point operators.

set-with-fixed-point-operator :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure
set-with-fixed-point-operator ext =
  empty

  +axiom
    ( (λ A _ → Is-set A)
    , is-set-prop
    )

  +ho-operator ((base ⟶ base) ⟶ base)

  +axiom
    ( (λ { _ (_ , fix) →
           ∀ f → fix f ≡ f (fix f) })
    , fixed-point-prop
    )

  where
  is-set-prop = λ _ _ → H-level-propositional ext 2

  fixed-point-prop = λ { _ ((_ , A-set) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

Set-with-fixed-point-operator :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Set-with-fixed-point-operator ext =
  ⟪ set-with-fixed-point-operator ext ⟫

private

  -- An unfolding of Set-with-fixed-point-operator.

  Set-with-fixed-point-operator-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Set-with-fixed-point-operator ext ≡ Σ
      Set                        λ A → Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Is-set A                 ) λ _ →
      (A → A) → A              ) λ { (_ , fix) →
      ∀ f → fix f ≡ f (fix f) }
  Set-with-fixed-point-operator-unfolded _ = refl _

------------------------------------------------------------------------
-- Right-nested structures

-- Right-nested structures are arguably easier to define (see the
-- example below). However, the following class of right-nested
-- structures is in some sense different from the class above. Take
-- "operator 0 f : Structureʳ Bool", for instance. The /shape/ of f op
-- can vary depending on whether the operator op is true or false.
--
-- One could perhaps avoid this issue by only considering values of
-- type ∀ A → Structureʳ A. However, it is not obvious how to convert
-- elements of this type to elements of type Structure in a
-- meaning-preserving way. Furthermore it seems to be awkward to
-- define things like Is-structure-isomorphism when using values of
-- type ∀ A → Structureʳ A (see the definition of
-- Is-structure-isomorphismʳ below).

-- Codes.

data Structureʳ (A : Set) : Set₁ where
  empty : Structureʳ A

  -- N-ary functions.
  operator : (n : ℕ)
             (s : A ^ n ⟶ A → Structureʳ A) →
             Structureʳ A

  -- Simply typed functions.
  ho-operator : (σ : Type)
                (s : ⟦ σ ⟧→ A → Structureʳ A) →
                Structureʳ A

  -- Arbitrary /propositional/ axioms.
  axiom : (P : Set)
          (P-prop : Propositional P)
          (s : P → Structureʳ A) →
          Structureʳ A

-- Interpretation of the codes.

⟦_⟧ʳ : {A : Set} → Structureʳ A → Set₁
⟦ empty            ⟧ʳ = ↑ _ ⊤
⟦ operator n s     ⟧ʳ = ∃ λ op → ⟦ s op ⟧ʳ
⟦ ho-operator σ s  ⟧ʳ = ∃ λ op → ⟦ s op ⟧ʳ
⟦ axiom P P-prop s ⟧ʳ = ∃ λ p  → ⟦ s p  ⟧ʳ

-- Top-level interpretation.

⟪_⟫ʳ : (∀ A → Structureʳ A) → Set₁
⟪ s ⟫ʳ = ∃ λ A → ⟦ s A ⟧ʳ

-- The property of being an isomorphism.

Is-structure-isomorphismʳ :
  (s : ∀ A → Structureʳ A) →
  {A B : Set} → ⟦ s A ⟧ʳ → ⟦ s B ⟧ʳ →
  A ↔ B → Set
Is-structure-isomorphismʳ s {A} {B} S₁ S₂ m =
  helper (s A) (s B) S₁ S₂
  where
  helper : (s₁ : Structureʳ A) (s₂ : Structureʳ B) →
           ⟦ s₁ ⟧ʳ → ⟦ s₂ ⟧ʳ → Set
  helper empty            empty            _          _          = ⊤
  helper (operator n₁ s₁) (operator n₂ s₂) (op₁ , S₁) (op₂ , S₂) =
    (∃ λ (eq : n₁ ≡ n₂) →
       N-ary.Is- n₁ -ary-morphism
         op₁ (subst (λ n → B ^ n ⟶ B) (sym eq) op₂) (_↔_.to m)) ×
    helper (s₁ op₁) (s₂ op₂) S₁ S₂
  helper (ho-operator σ₁ s₁) (ho-operator σ₂ s₂) (op₁ , S₁) (op₂ , S₂) =
    ∃ λ (eq : σ₁ ≡ σ₂) →
       Simple.Is-isomorphism
         σ₁ op₁ (subst (λ σ → ⟦ σ ⟧→ B) (sym eq) op₂) m ×
    helper (s₁ op₁) (s₂ op₂) S₁ S₂
  helper (axiom P₁ _ s₁) (axiom P₂ _ s₂) (p₁ , S₁) (p₂ , S₂) =
    helper (s₁ p₁) (s₂ p₂) S₁ S₂

  helper empty               (operator n s₂)     _ _ = ⊥
  helper empty               (ho-operator σ s₂)  _ _ = ⊥
  helper empty               (axiom P P-prop s₂) _ _ = ⊥
  helper (operator n s₁)     empty               _ _ = ⊥
  helper (operator n s₁)     (ho-operator σ s₂)  _ _ = ⊥
  helper (operator n s₁)     (axiom P P-prop s₂) _ _ = ⊥
  helper (ho-operator σ s₁)  empty               _ _ = ⊥
  helper (ho-operator σ s₁)  (operator n s₂)     _ _ = ⊥
  helper (ho-operator σ s₁)  (axiom P P-prop s₂) _ _ = ⊥
  helper (axiom P P-prop s₁) empty               _ _ = ⊥
  helper (axiom P P-prop s₁) (operator n s₂)     _ _ = ⊥
  helper (axiom P P-prop s₁) (ho-operator σ s₂)  _ _ = ⊥

-- Example: semigroups.

semigroupʳ :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  ∀ A → Structureʳ A
semigroupʳ ext A =
  axiom (Is-set A)

        (H-level-propositional ext 2)

        λ A-set →

  operator 2 λ _∙_ →

  axiom (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z)

        (Π-closure ext 1 λ _ →
         Π-closure ext 1 λ _ →
         Π-closure ext 1 λ _ →
         A-set _ _)

        λ _ →

  empty

Semigroupʳ :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Semigroupʳ ext = ⟪ semigroupʳ ext ⟫ʳ

private

  -- An unfolding of Semigroupʳ.

  Semigroupʳ-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Semigroupʳ ext ≡
    ∃ λ (A   : Set) →
    ∃ λ (_   : Is-set A) →
    ∃ λ (_∙_ : A → A → A) →
    ∃ λ (_   : ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z) →
    ↑ _ ⊤
  Semigroupʳ-unfolded _ = refl _
