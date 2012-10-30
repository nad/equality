------------------------------------------------------------------------
-- A large(r) class of algebraic structures satisfies the property
-- that isomorphic structures are equal (assuming univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality.More
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq using (_↔_; module _↔_)
open Derived-definitions-and-properties eq
open import Equivalence hiding (_∘_; inverse)
open import Function-universe eq hiding (bijection)
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
      cast A₁≈A₂ n f ≡ subst (λ C → C ^ n ⟶ C) (≈⇒≡ univ A₁≈A₂) f
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
      subst (λ A → A ^ n ⟶ A) (≈⇒≡ univ A₁≈A₂) f₁ ≡ f₂
    subst-isomorphism ext univ A₁≈A₂ n f₁ f₂ is =
      subst (λ A → A ^ n ⟶ A) (≈⇒≡ univ A₁≈A₂) f₁  ≡⟨ sym $ cast-is-subst ext univ A₁≈A₂ n f₁ ⟩
      cast A₁≈A₂ n f₁                              ≡⟨ cast-isomorphism ext A₁≈A₂ n f₁ f₂ is ⟩∎
      f₂                                           ∎

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
      cast σ (_↔_.equivalence m) f ≡ subst ⟦ σ ⟧→ (≈⇒≡ univ m′) f
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
      subst ⟦ σ ⟧→ (≈⇒≡ univ m′) f₁ ≡ f₂
    subst-isomorphism ext univ m σ f₁ f₂ is =
      subst ⟦ σ ⟧→ (≈⇒≡ univ (bijection⇒weak-equivalence m)) f₁  ≡⟨ sym $ cast-is-subst ext univ m σ f₁ ⟩
      cast σ (_↔_.equivalence m) f₁                              ≡⟨ _⇔_.to (isomorphism-definitions-equivalent ext ext m σ f₁ f₂) is ⟩∎
      f₂                                                         ∎

------------------------------------------------------------------------
-- A class of algebraic structures

-- An algebraic structure universe.

mutual

  infixl 5 _+operator_ _+ho-operator_ _+axiom_
  infix  5 _+type

  -- Structure n contains codes for structures containing n types.

  data Structure : ℕ → Set₁ where
    empty : Structure 0

    -- A type.
    _+type : ∀ {n} → Structure n → Structure (1 + n)

    -- N-ary functions.
    _+operator_ :
      ∀ {n} → Structure n → (sig : Fin n × ℕ) → Structure n

    -- Simply typed functions.
    _+ho-operator_ :
      ∀ {n} → Structure n → (sig : Fin n × Type) → Structure n

    -- Arbitrary /propositional/ axioms.
    _+axiom_ : ∀ {n}
               (s : Structure n)
               (P : ∃ λ (P : ⟦ s ⟧ → Set) →
                      ∀ s → Propositional (P s)) →
               Structure n

  -- Interpretation of the codes.

  ⟦_⟧ : ∀ {n} → Structure n → Set₁
  ⟦ empty                  ⟧ = ↑ _ ⊤
  ⟦ s +type                ⟧ = ⟦ s ⟧ × Set
  ⟦ s +operator (j , n)    ⟧ = ∃ λ (S : ⟦ s ⟧) → let A = type s j S in
                                                 A ^ n ⟶ A
  ⟦ s +ho-operator (j , σ) ⟧ = ∃ λ (S : ⟦ s ⟧) → ⟦ σ ⟧→ (type s j S)
  ⟦ s +axiom (P , P-prop)  ⟧ = Σ ⟦ s ⟧ P

  -- A projection: type s j S is the j-th type in S.

  type : ∀ {n} (s : Structure n) → Fin n → ⟦ s ⟧ → Set
  type empty              ()        _
  type (s +type)          (inj₁ tt) (S , A) = A
  type (s +type)          (inj₂ j)  (S , A) = type s j S
  type (s +operator _)    j         (S , _) = type s j S
  type (s +ho-operator _) j         (S , _) = type s j S
  type (s +axiom _)       j         (S , _) = type s j S

mutual

  -- Isomorphisms.

  Isomorphism : ∀ {n} (s : Structure n) → ⟦ s ⟧ → ⟦ s ⟧ → Set
  Isomorphism empty    _          _         = ⊤

  Isomorphism (s +type) (S₁ , A₁)  (S₂ , A₂) =
    Isomorphism s S₁ S₂ × (A₁ ↔ A₂)

  Isomorphism (s +axiom _) (s₁ , _) (s₂ , _) =
    Isomorphism s s₁ s₂

  Isomorphism (s +operator (j , n)) (s₁ , op₁) (s₂ , op₂) =
    ∃ λ (i : Isomorphism s s₁ s₂) →
    N-ary.Is- n -ary-morphism op₁ op₂ (_↔_.to (bijection s j i))

  Isomorphism (s +ho-operator (j , σ)) (s₁ , op₁) (s₂ , op₂) =
    ∃ λ (i : Isomorphism s s₁ s₂) →
    Simple.Is-isomorphism σ op₁ op₂ (bijection s j i)

  -- A projection: bijection s j i is the j-th bijection in i.

  bijection : ∀ {n} (s : Structure n) {S₁ S₂ : ⟦ s ⟧} (j : Fin n) →
              Isomorphism s S₁ S₂ → type s j S₁ ↔ type s j S₂
  bijection empty              ()        _
  bijection (s +type)          (inj₁ tt) (_ , m) = m
  bijection (s +type)          (inj₂ j)  (i , _) = bijection s j i
  bijection (s +operator _)    j         (i , _) = bijection s j i
  bijection (s +ho-operator _) j         (i , _) = bijection s j i
  bijection (s +axiom _)       j         i       = bijection s j i

mutual
 abstract

  -- Isomorphism s is symmetric (assuming extensionality).

  symmetric : ({A B : Set} → Extensionality A (λ _ → B)) →
              ∀ {n} (s : Structure n) {S₁ S₂ : ⟦ s ⟧} →
              Isomorphism s S₁ S₂ → Isomorphism s S₂ S₁
  symmetric ext empty        i       = i
  symmetric ext (s +axiom P) i       = symmetric ext s i
  symmetric ext (s +type)    (i , m) = symmetric ext s i , inverse m
  symmetric ext (s +operator (j , n)) (i , is) =
    symmetric ext s i ,
    subst (N-ary.Is- n -ary-morphism _ _)
          (cong _↔_.to $ bijection-commutes ext s j i)
          (N-ary.from-also- n -ary-morphism _ _ (bijection s j i) is)
  symmetric ext (s +ho-operator (j , σ)) (i , is) =
    symmetric ext s i ,
    subst (Simple.Is-isomorphism σ _ _)
          (bijection-commutes ext s j i)
          (Simple.inverse-also-isomorphism (λ _ _ → ext) σ _ _
                                           (bijection s j i) is)

  -- A kind of commutation property.

  bijection-commutes :
    (ext : {A B : Set} → Extensionality A (λ _ → B)) →
    ∀ {n} (s : Structure n) {S₁ S₂ : ⟦ s ⟧} →
    (j : Fin n) (i : Isomorphism s S₁ S₂) →
    inverse (bijection s j i) ≡ bijection s j (symmetric ext s i)
  bijection-commutes ext empty              ()        _
  bijection-commutes ext (s +type)          (inj₁ tt) (_ , m) = refl (inverse m)
  bijection-commutes ext (s +type)          (inj₂ j)  (i , _) = bijection-commutes ext s j i
  bijection-commutes ext (s +operator _)    j         (i , _) = bijection-commutes ext s j i
  bijection-commutes ext (s +ho-operator _) j         (i , _) = bijection-commutes ext s j i
  bijection-commutes ext (s +axiom P)       j         i       = bijection-commutes ext s j i

-- Isomorphic structures are equal (assuming univalence).

isomorphic-equal :
  Univalence-axiom′ (Set ²/≡) Set →
  Univalence-axiom lzero →
  ∀ {n} (s : Structure n) (S₁ S₂ : ⟦ s ⟧) →
  Isomorphism s S₁ S₂ → S₁ ≡ S₂
isomorphic-equal univ₁ univ₂ s S₁ S₂ is = iso-eq s S₁ S₂ is
  where

  -- Given two isomorphic structures the corresponding types are equal
  -- (due to univalence).

  corresponding-types-equal :
    ∀ {n} (s : Structure n) {S₁ S₂ : ⟦ s ⟧}
    (j : Fin n) (i : Isomorphism s S₁ S₂) →
    type s j S₁ ≡ type s j S₂
  corresponding-types-equal s j i =
    _≈_.from (≡≈≈ univ₂) $
    bijection⇒weak-equivalence $
    bijection s j i

  abstract

    -- Extensionality follows from univalence.

    ext : {A : Set} {B : A → Set} → Extensionality A B
    ext = dependent-extensionality univ₁ (λ _ → univ₂)

  mutual
   abstract

    -- The main lemma.

    iso-eq : ∀ {n} (s : Structure n) (S₁ S₂ : ⟦ s ⟧) →
             Isomorphism s S₁ S₂ → S₁ ≡ S₂
    iso-eq empty _ _ _ = refl _

    iso-eq (s +type) (S₁ , A₁) (S₂ , A₂) (i , m) =
      (S₁ , A₁)  ≡⟨ cong₂ _,_ (iso-eq s S₁ S₂ i) (corresponding-types-equal (s +type) (inj₁ tt) (i , m)) ⟩∎
      (S₂ , A₂)  ∎

    iso-eq (s +axiom (P , P-prop)) (S₁ , ax₁) (S₂ , ax₂) i =
      (S₁ , ax₁)  ≡⟨ Σ-≡,≡→≡ (iso-eq s S₁ S₂ i) (_⇔_.to propositional⇔irrelevant (P-prop _) _ _) ⟩∎
      (S₂ , ax₂)  ∎

    iso-eq (s +operator (j , n)) (S₁ , op₁) (S₂ , op₂) (i , is) =
      let lemma′ =
            subst (λ S → type s j S ^ n ⟶ type s j S)
                  (iso-eq s S₁ S₂ i) op₁                    ≡⟨ subst-∘ (λ A → A ^ n ⟶ A) (type s j) (iso-eq s S₁ S₂ i) ⟩

            subst (λ A → A ^ n ⟶ A)
                  (cong (type s j) (iso-eq s S₁ S₂ i)) op₁  ≡⟨ cong (λ eq → subst (λ A → A ^ n ⟶ A) eq op₁) (cong-type-iso-eq s S₁ S₂ j i) ⟩

            subst (λ A → A ^ n ⟶ A)
                  (corresponding-types-equal s j i) op₁     ≡⟨ N-ary.subst-isomorphism (λ _ → ext) univ₂
                                                                 (bijection⇒weak-equivalence $ bijection s j i) n op₁ op₂ is ⟩∎
            op₂                                             ∎ in

      (S₁ , op₁)  ≡⟨ Σ-≡,≡→≡ (iso-eq s S₁ S₂ i) lemma′ ⟩∎
      (S₂ , op₂)  ∎

    iso-eq (s +ho-operator (j , σ)) (S₁ , op₁) (S₂ , op₂) (i , is) =
      let lemma′ =
            subst (⟦ σ ⟧→ ∘ type s j) (iso-eq s S₁ S₂ i) op₁       ≡⟨ subst-∘ ⟦ σ ⟧→ (type s j) (iso-eq s S₁ S₂ i) ⟩
            subst ⟦ σ ⟧→ (cong (type s j) (iso-eq s S₁ S₂ i)) op₁  ≡⟨ cong (λ eq → subst ⟦ σ ⟧→ eq op₁) (cong-type-iso-eq s S₁ S₂ j i) ⟩
            subst ⟦ σ ⟧→ (corresponding-types-equal s j i) op₁     ≡⟨ Simple.subst-isomorphism (λ _ _ → ext) univ₂
                                                                        (bijection s j i) σ op₁ op₂ is ⟩∎
            op₂                                                   ∎ in

      (S₁ , op₁)  ≡⟨ Σ-≡,≡→≡ (iso-eq s S₁ S₂ i) lemma′ ⟩∎
      (S₂ , op₂)  ∎

    -- A certain projection of iso-eq corresponds to
    -- corresponding-types-equal.

    cong-type-iso-eq :
      ∀ {n} (s : Structure n) (S₁ S₂ : ⟦ s ⟧)
      (j : Fin n) (i : Isomorphism s S₁ S₂) →
      cong (type s j) (iso-eq s S₁ S₂ i) ≡
      corresponding-types-equal s j i
    cong-type-iso-eq empty S₁ S₂ () i

    cong-type-iso-eq (s +type) (S₁ , A₁) (S₂ , A₂) (inj₁ tt) (i , m) =
      let A₁≡A₂ = _≈_.from (≡≈≈ univ₂) $ bijection⇒weak-equivalence m in

      cong proj₂ (cong₂ _,_ (iso-eq s S₁ S₂ i) A₁≡A₂)  ≡⟨ cong-proj₂-cong₂-, (iso-eq s S₁ S₂ i) _ ⟩∎
      A₁≡A₂                                            ∎

    cong-type-iso-eq (s +type) (S₁ , _) (S₂ , _) (inj₂ j) (i , _) =
      cong (type s j ∘ proj₁) (cong₂ _,_ (iso-eq s S₁ S₂ i) _)       ≡⟨ sym $ cong-∘ (type s j) proj₁ _ ⟩
      cong (type s j) (cong proj₁ (cong₂ _,_ (iso-eq s S₁ S₂ i) _))  ≡⟨ cong (cong (type s j)) $ cong-proj₁-cong₂-, (iso-eq s S₁ S₂ i) _ ⟩
      cong (type s j) (iso-eq s S₁ S₂ i)                             ≡⟨ cong-type-iso-eq s S₁ S₂ j i ⟩∎
      corresponding-types-equal s j i                                ∎

    cong-type-iso-eq (s +axiom _) (S₁ , _) (S₂ , _) j i =
      cong-type-iso-eq′ s S₁ S₂ j i _ _

    cong-type-iso-eq (s +operator _) (S₁ , _) (S₂ , _) j (i , _) =
      cong-type-iso-eq′ s S₁ S₂ j i _ _

    cong-type-iso-eq (s +ho-operator _) (S₁ , _) (S₂ , _) j (i , _) =
      cong-type-iso-eq′ s S₁ S₂ j i _ _

    -- A variant of cong-type-iso-eq.

    cong-type-iso-eq′ :
      ∀ {n} (s : Structure n) (S₁ S₂ : ⟦ s ⟧)
      (j : Fin n) (i : Isomorphism s S₁ S₂)
      (P : ⟦ s ⟧ → Set) {p₁ p₂}
      (eq : subst P (iso-eq s S₁ S₂ i) p₁ ≡ p₂) →
      cong (type s j ∘ proj₁) (Σ-≡,≡→≡ {B = P} (iso-eq s S₁ S₂ i) eq) ≡
      corresponding-types-equal s j i
    cong-type-iso-eq′ s S₁ S₂ j i _ eq =
      cong (type s j ∘ proj₁) (Σ-≡,≡→≡ (iso-eq s S₁ S₂ i) eq)       ≡⟨ sym $ cong-∘ (type s j) proj₁ _ ⟩
      cong (type s j) (cong proj₁ $ Σ-≡,≡→≡ (iso-eq s S₁ S₂ i) eq)  ≡⟨ cong (cong (type s j)) $ proj₁-Σ-≡,≡→≡ (iso-eq s S₁ S₂ i) _ ⟩
      cong (type s j) (iso-eq s S₁ S₂ i)                            ≡⟨ cong-type-iso-eq s S₁ S₂ j i ⟩∎
      corresponding-types-equal s j i                               ∎

------------------------------------------------------------------------
-- Some example structures

-- Example: magmas.

magma : Structure 1
magma = empty +type +operator (inj₁ tt , 2)

Magma : Set₁
Magma = ⟦ magma ⟧

private

  -- An unfolding of Magma.

  Magma-unfolded : Magma ≡ Σ (↑ _ ⊤ × Set) λ { (_ , A) → (A → A → A) }
  Magma-unfolded = refl _

-- Example: semigroups. The definition uses extensionality to prove
-- that the axioms are propositional. Note that one axiom states that
-- the underlying type is a set. This assumption is used to prove that
-- the other axioms are propositional.

semigroup :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure 1
semigroup ext =
  empty

  +type

  +axiom
    ( (λ { (_ , A) → Is-set A })
    , is-set-prop
    )

  +operator (inj₁ tt , 2)

  +axiom
    ( (λ { (_ , _∙_) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
    , assoc-prop
    )

  where
  is-set-prop = λ _ → H-level-propositional ext 2

  assoc-prop = λ { ((_ , A-set) , _) →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

Semigroup :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Semigroup ext = ⟦ semigroup ext ⟧

private

  -- An unfolding of Semigroup.

  Semigroup-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Semigroup ext ≡  Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                                  ) λ {  (_ , A) →
      Is-set A                            }) λ { ((_ , A) , _) →
      A → A → A                           }) λ { (_ , _∙_) →
      ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z }
  Semigroup-unfolded _ = refl _

-- Example: abelian groups.

abelian-group :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure 1
abelian-group ext =
  empty

  -- The underlying type.
  +type

  -- The underlying type is a set.
  +axiom
    ( (λ { (_ , A) → Is-set A })
    , is-set-prop
    )

  -- The binary group operation.
  +operator (inj₁ tt , 2)

  -- Commutativity.
  +axiom
    ( (λ { (_ , _∙_) →
           ∀ x y → x ∙ y ≡ y ∙ x })
    , comm-prop
    )

  -- Associativity.
  +axiom
    ( (λ { ((_ , _∙_) , _) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
    , assoc-prop
    )

  -- Identity.
  +operator (inj₁ tt , 0)

  -- Left identity.
  +axiom
    ( (λ { ((((_ , _∙_) , _) , _) , e) →
           ∀ x → e ∙ x ≡ x })
    , left-identity-prop
    )

  -- Right identity.
  +axiom
    ( (λ { (((((_ , _∙_) , _) , _) , e) , _) →
           ∀ x → x ∙ e ≡ x })
    , right-identity-prop
    )

  -- Inverse.
  +operator (inj₁ tt , 1)

  -- Left inverse.
  +axiom
    ( (λ { (((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) →
           ∀ x → (x ⁻¹) ∙ x ≡ e })
    , left-inverse-prop
    )

  -- Right inverse.
  +axiom
    ( (λ { ((((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) , _) →
           ∀ x → x ∙ (x ⁻¹) ≡ e })
    , right-inverse-prop
    )

  where
  is-set-prop = λ _ → H-level-propositional ext 2

  comm-prop =
    λ { ((_ , A-set) , _) →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  assoc-prop =
    λ { (((_ , A-set) , _) , _) →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  left-identity-prop =
    λ { (((((_ , A-set) , _) , _) , _) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  right-identity-prop =
    λ { ((((((_ , A-set) , _) , _) , _) , _) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  left-inverse-prop =
    λ { ((((((((_ , A-set) , _) , _) , _) , _) , _) , _) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

  right-inverse-prop =
    λ { (((((((((_ , A-set) , _) , _) , _) , _) , _) , _) , _) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

Abelian-group :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Abelian-group ext = ⟦ abelian-group ext ⟧

private

  -- An unfolding of Abelian-group. Note that the inner structure is
  -- left-nested.

  Abelian-group-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Abelian-group ext ≡ Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                                  ) λ {        (_ , A) →
      Is-set A                            }) λ {       ((_ , A) , _) →
      A → A → A                           }) λ {                  (_ , _∙_) →
      ∀ x y → x ∙ y ≡ y ∙ x               }) λ {                 ((_ , _∙_) , _) →
      ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z }) λ {    (((((_ , A) , _) , _  ) , _) , _) →
      A                                   }) λ {               ((((_ , _∙_) , _) , _) , e) →
      ∀ x → e ∙ x ≡ x                     }) λ {              (((((_ , _∙_) , _) , _) , e) , _) →
      ∀ x → x ∙ e ≡ x                     }) λ { ((((((((_ , A) , _) , _  ) , _) , _) , _) , _) , _) →
      A → A                               }) λ {            (((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) →
      ∀ x → (x ⁻¹) ∙ x ≡ e                }) λ {           ((((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) , _) →
      ∀ x → x ∙ (x ⁻¹) ≡ e                }

  Abelian-group-unfolded _ = refl _

-- Example: Sets with fixed-point operators.

set-with-fixed-point-operator :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure 1
set-with-fixed-point-operator ext =
  empty

  +type

  +axiom
    ( (λ { (_ , A) → Is-set A })
    , is-set-prop
    )

  +ho-operator (inj₁ tt , (base ⟶ base) ⟶ base)

  +axiom
    ( (λ { (_ , fix) →
           ∀ f → fix f ≡ f (fix f) })
    , fixed-point-prop
    )

  where
  is-set-prop = λ _ → H-level-propositional ext 2

  fixed-point-prop = λ { ((_ , A-set) , _) →
      Π-closure ext 1 λ _ →
      A-set _ _
    }

Set-with-fixed-point-operator :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Set-with-fixed-point-operator ext =
  ⟦ set-with-fixed-point-operator ext ⟧

private

  -- An unfolding of Set-with-fixed-point-operator.

  Set-with-fixed-point-operator-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Set-with-fixed-point-operator ext ≡ Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                      ) λ {  (_ , A) →
      Is-set A                }) λ { ((_ , A) , _) →
      (A → A) → A             }) λ { (_ , fix) →
      ∀ f → fix f ≡ f (fix f) }
  Set-with-fixed-point-operator-unfolded _ = refl _
