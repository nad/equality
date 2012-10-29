------------------------------------------------------------------------
-- A large class of algebraic structures satisfies the property that
-- isomorphic structures are equal (assuming univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq
open Derived-definitions-and-properties eq
open import Equivalence
open import H-level eq
open import H-level.Closure eq
open import Prelude
open import Univalence-axiom eq
open import Weak-equivalence eq as Weak

------------------------------------------------------------------------
-- N-ary functions

-- N-ary functions.

_^_⟶_ : Set → ℕ → Set → Set
A ^ zero  ⟶ B = B
A ^ suc n ⟶ B = A → A ^ n ⟶ B

-- N-ary function morphisms.

Is-_-ary-morphism :
  (n : ℕ) {A B : Set} → A ^ n ⟶ A → B ^ n ⟶ B → (A → B) → Set
Is- zero  -ary-morphism f₁ f₂ m = m f₁ ≡ f₂
Is- suc n -ary-morphism f₁ f₂ m =
  ∀ x → Is- n -ary-morphism (f₁ x) (f₂ (m x)) m

abstract

  -- If _↔_.to m is a morphism, then _↔_.from m is also a morphism.

  from-also-_-ary-morphism :
    (n : ℕ) {A B : Set} (f₁ : A ^ n ⟶ A) (f₂ : B ^ n ⟶ B) (m : A ↔ B) →
    Is- n -ary-morphism f₁ f₂ (_↔_.to m) →
    Is- n -ary-morphism f₂ f₁ (_↔_.from m)
  from-also- zero  -ary-morphism f₁ f₂ m is = _↔_.to-from m is
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
  cast-id ext zero    f = refl f
  cast-id ext (suc n) f = ext n $ λ x → cast-id ext n (f x)

  -- We can express cast as an instance of subst (assuming
  -- extensionality and univalence).

  cast-is-subst :
    (∀ {A : Set} n → Extensionality A (λ _ → A ^ n ⟶ A)) →
    {A₁ A₂ : Set}
    (univ : Univalence-axiom′ A₁ A₂)
    (A₁≈A₂ : A₁ ≈ A₂) (n : ℕ) (f : A₁ ^ n ⟶ A₁) →
    cast A₁≈A₂ n f ≡ subst (λ C → C ^ n ⟶ C) (≈⇒≡ univ A₁≈A₂) f
  cast-is-subst ext univ A₁≈A₂ n =
    subst-unique
      (λ A → A ^ n ⟶ A)
      (λ A≈B f → cast A≈B n f)
      (cast-id ext n)
      univ
      A₁≈A₂

  -- If there is an isomorphism from f₁ to f₂, then the corresponding
  -- instance of cast maps f₁ to f₂ (assuming extensionality).

  cast-isomorphism :
    {A₁ A₂ : Set} →
    (∀ n → Extensionality A₂ (λ _ → A₂ ^ n ⟶ A₂)) →
    (A₁≈A₂ : A₁ ≈ A₂)
    (n : ℕ) (f₁ : A₁ ^ n ⟶ A₁) (f₂ : A₂ ^ n ⟶ A₂) →
    Is- n -ary-morphism f₁ f₂ (_≈_.to A₁≈A₂) →
    cast A₁≈A₂ n f₁ ≡ f₂
  cast-isomorphism ext A₁≈A₂ zero    f₁ f₂ is = is
  cast-isomorphism ext A₁≈A₂ (suc n) f₁ f₂ is = ext n $ λ x →
    cast A₁≈A₂ n (f₁ (from x))  ≡⟨ cast-isomorphism ext A₁≈A₂ n _ _ (is (from x)) ⟩
    f₂ (to (from x))            ≡⟨ cong f₂ (right-inverse-of x) ⟩∎
    f₂ x                        ∎
    where open _≈_ A₁≈A₂

  -- Combining the results above we get the following: if there is an
  -- isomorphism from f₁ to f₂, then the corresponding instance of
  -- subst maps f₁ to f₂ (assuming extensionality and univalence).

  subst-isomorphism :
    (∀ {A : Set} n → Extensionality A (λ _ → A ^ n ⟶ A)) →
    {A₁ A₂ : Set}
    (univ : Univalence-axiom′ A₁ A₂)
    (A₁≈A₂ : A₁ ≈ A₂)
    (n : ℕ) (f₁ : A₁ ^ n ⟶ A₁) (f₂ : A₂ ^ n ⟶ A₂) →
    Is- n -ary-morphism f₁ f₂ (_≈_.to A₁≈A₂) →
    subst (λ A → A ^ n ⟶ A) (≈⇒≡ univ A₁≈A₂) f₁ ≡ f₂
  subst-isomorphism ext univ A₁≈A₂ n f₁ f₂ is =
    subst (λ A → A ^ n ⟶ A) (≈⇒≡ univ A₁≈A₂) f₁  ≡⟨ sym $ cast-is-subst ext univ A₁≈A₂ n f₁ ⟩
    cast A₁≈A₂ n f₁                              ≡⟨ cast-isomorphism ext A₁≈A₂ n f₁ f₂ is ⟩∎
    f₂                                           ∎

------------------------------------------------------------------------
-- A class of algebraic structures

-- An algebraic structure universe.

mutual

  -- Codes for structures.

  infixl 5 _+operator_ _+axiom_

  data Structure : Set₁ where
    empty : Structure

    -- N-ary functions.
    _+operator_ : Structure → (n : ℕ) → Structure

    -- Arbitrary /propositional/ axioms.
    _+axiom_ : (s : Structure)
               (P : ∃ λ (P : (A : Set) → ⟦ s ⟧ A → Set) →
                      ∀ A s → Propositional (P A s)) →
               Structure

  -- Interpretation of the codes.

  ⟦_⟧ : Structure → Set → Set₁
  ⟦ empty                 ⟧ A = ↑ _ ⊤
  ⟦ s +operator n         ⟧ A = ⟦ s ⟧ A × (A ^ n ⟶ A)
  ⟦ s +axiom (P , P-prop) ⟧ A = Σ (⟦ s ⟧ A) (P A)

-- Top-level interpretation.

⟪_⟫ : Structure → Set₁
⟪ s ⟫ = ∃ ⟦ s ⟧

-- Morphisms.

Is-structure-morphism :
  (s : Structure) →
  {A B : Set} → ⟦ s ⟧ A → ⟦ s ⟧ B →
  (A → B) → Set
Is-structure-morphism empty           _          _          m = ⊤
Is-structure-morphism (s +axiom _)    (s₁ , _)   (s₂ , _)   m =
  Is-structure-morphism s s₁ s₂ m
Is-structure-morphism (s +operator n) (s₁ , op₁) (s₂ , op₂) m =
  Is-structure-morphism s s₁ s₂ m × Is- n -ary-morphism op₁ op₂ m

-- Isomorphisms.

Isomorphism : (s : Structure) → ⟪ s ⟫ → ⟪ s ⟫ → Set
Isomorphism s (A₁ , s₁) (A₂ , s₂) =
  ∃ λ (m : A₁ ↔ A₂) → Is-structure-morphism s s₁ s₂ (_↔_.to m)

abstract

  -- If _↔_.to m is a morphism, then _↔_.from m is also a morphism.

  from-also-structure-morphism :
    (s : Structure) →
    {A B : Set} {s₁ : ⟦ s ⟧ A} {s₂ : ⟦ s ⟧ B} →
    (m : A ↔ B) →
    Is-structure-morphism s s₁ s₂ (_↔_.to m) →
    Is-structure-morphism s s₂ s₁ (_↔_.from m)
  from-also-structure-morphism empty           m = _
  from-also-structure-morphism (s +axiom _)    m =
    from-also-structure-morphism s m
  from-also-structure-morphism (s +operator n) m =
    Σ-map (from-also-structure-morphism s m)
          (from-also- n -ary-morphism _ _ m)

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
    open _↔_ m

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
            Is-structure-morphism s s₁ s₂ to →
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

      (s₂ , subst (λ A → A ^ n ⟶ A) A₁≡A₂ op₁)              ≡⟨ cong (_,_ s₂) $ subst-isomorphism (λ _ → ext) univ₂
                                                                                 (bijection⇒weak-equivalence m) n op₁ op₂ is-o ⟩∎
      (s₂ , op₂)                                            ∎

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
-- the other axiom is propositional.

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
