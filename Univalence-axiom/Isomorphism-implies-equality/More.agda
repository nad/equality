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

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Equivalence using (_⇔_; module _⇔_)
open import Function-universe eq using (→-cong)
open import H-level eq
open import H-level.Closure eq
open import Prelude
open import Univalence-axiom eq
open import Weak-equivalence eq as Weak
  using (_≈_; module _≈_; bijection⇒weak-equivalence)

------------------------------------------------------------------------
-- A class of algebraic structures

-- An algebraic structure universe.

mutual

  -- Codes for structures.

  infixl 5 _▻_

  data Structure : Set₂ where
    ε   : Structure
    _▻_ : (s : Structure) → Extension s → Structure

  -- Structures can contain arbitrary "extensions".

  record Extension (s : Structure) : Set₂ where
    field
      Ext : ⟦ s ⟧ → Set₁

      Iso : {s₁ s₂ : ⟦ s ⟧} →
            Ext s₁ → Ext s₂ → Isomorphism s s₁ s₂ → Set

      hyp : (ext : {A : Set} {B : A → Set} → Extensionality A B)
            (univ : Univalence-axiom lzero)
            {s₁ s₂ : ⟦ s ⟧} {x₁ : Ext s₁} {x₂ : Ext s₂}
            (iso : Isomorphism s s₁ s₂) (i : Iso x₁ x₂ iso) →
            subst Ext (isomorphic-equal ext univ s iso) x₁ ≡ x₂

  -- Interpretation of the codes.

  ⟦_⟧ : Structure → Set₁
  ⟦ ε     ⟧ = ↑ _ ⊤
  ⟦ s ▻ e ⟧ = Σ ⟦ s ⟧ (Extension.Ext e)

  -- Isomorphisms.

  Isomorphism : (s : Structure) → ⟦ s ⟧ → ⟦ s ⟧ → Set
  Isomorphism ε       _         _         = ⊤
  Isomorphism (s ▻ e) (s₁ , x₁) (s₂ , x₂) =
    Σ (Isomorphism s s₁ s₂) (Extension.Iso e x₁ x₂)

  -- Isomorphic structures are equal (assuming extensionality and
  -- univalence).

  isomorphic-equal :
    ({A : Set} {B : A → Set} → Extensionality A B) →
    Univalence-axiom lzero →
    (s : Structure) {s₁ s₂ : ⟦ s ⟧} →
    Isomorphism s s₁ s₂ → s₁ ≡ s₂
  isomorphic-equal _   _    ε       _ = refl _
  isomorphic-equal ext univ (s ▻ e) {s₁ , x₁} {s₂ , x₂} (iso , i) =
    (s₁ , x₁)  ≡⟨ Σ-≡,≡→≡ (isomorphic-equal ext univ s iso)
                          (Extension.hyp e ext univ iso i) ⟩∎
    (s₂ , x₂)  ∎

open Extension public

------------------------------------------------------------------------
-- Type extractors

-- Type extractors.

record Type-extractor (s : Structure) : Set₁ where
  field
    -- Extracts a type from a structure.
    Typ : ⟦ s ⟧ → Set

    -- Extracts a weak equivalence.
    equ : ∀ {s₁ s₂} → Isomorphism s s₁ s₂ → Typ s₁ ≈ Typ s₂

    -- Typ and equ are related via isomorphic-equal.
    Typ-equ : (ext : {A : Set} {B : A → Set} → Extensionality A B)
              (univ : Univalence-axiom lzero)
              {s₁ s₂ : ⟦ s ⟧} (iso : Isomorphism s s₁ s₂) →
              cong Typ (isomorphic-equal ext univ s iso) ≡
              ≈⇒≡ univ (equ iso)

  abstract

    -- A lemma.

    extractor-lemma :
      (ext : {A : Set} {B : A → Set} → Extensionality A B)
      (univ : Univalence-axiom lzero) →

      ∀ {p s₁ s₂} (P : Set → Set p) (x : P (Typ s₁))
      (iso : Isomorphism s s₁ s₂) →

      subst (P ∘ Typ) (isomorphic-equal ext univ s iso) x ≡
      subst P (≈⇒≡ univ (equ iso)) x

    extractor-lemma ext univ P x iso =
      subst (P ∘ Typ) (isomorphic-equal ext univ s iso) x     ≡⟨ subst-∘ P Typ _ ⟩
      subst P (cong Typ $ isomorphic-equal ext univ s iso) x  ≡⟨ cong (λ eq → subst P eq x) (Typ-equ ext univ iso) ⟩∎
      subst P (≈⇒≡ univ (equ iso)) x                          ∎

-- Successor type extractor.

infix 6 1+_

1+_ : ∀ {s e} → Type-extractor s → Type-extractor (s ▻ e)
1+_ {s} {e} extract = record
  { Typ     = Typ ∘ proj₁
  ; equ     = equ ∘ proj₁
  ; Typ-equ = Typ-equ′
  }
  where
  open Type-extractor extract

  abstract
    Typ-equ′ :
      (ext : {A : Set} {B : A → Set} → Extensionality A B)
      (univ : Univalence-axiom lzero) →
      ∀ {s₁ s₂} (iso : Isomorphism (s ▻ e) s₁ s₂) →
      cong (Typ ∘ proj₁) (isomorphic-equal ext univ (s ▻ e) iso) ≡
      ≈⇒≡ univ (equ (proj₁ iso))
    Typ-equ′ ext univ (iso , i) =
      let iso-eq = isomorphic-equal ext univ in

      cong (Typ ∘ proj₁) (iso-eq (s ▻ e) (iso , i))     ≡⟨ sym $ cong-∘ Typ proj₁ (iso-eq (s ▻ e) (iso , i)) ⟩
      cong Typ (cong proj₁ $ iso-eq (s ▻ e) (iso , i))  ≡⟨ cong (cong Typ) $ proj₁-Σ-≡,≡→≡ _ _ ⟩
      cong Typ (iso-eq s iso)                           ≡⟨ Typ-equ ext univ iso ⟩∎
      ≈⇒≡ univ (equ iso)                                ∎

------------------------------------------------------------------------
-- An "extension": types

-- Extends a structure with a type.

A-type : ∀ {s} → Extension s
A-type {s} = record
  { Ext = λ _ → Set
  ; Iso = λ A B _ → A ↔ B
  ; hyp = λ ext univ {_ _ A B} _ bij →
      subst (λ _ → Set) _ A  ≡⟨ subst-const ⟩
      A                      ≡⟨ ≈⇒≡ univ (bijection⇒weak-equivalence bij) ⟩∎
      B                      ∎
  }

-- A corresponding type extractor.

[0] : ∀ {s} → Type-extractor (s ▻ A-type)
[0] {s} = record
  { Typ     = λ { (_ , A) → A }
  ; equ     = λ { (_ , A↔B) → bijection⇒weak-equivalence A↔B }
  ; Typ-equ = Typ-equ
  }
  where
  abstract
    Typ-equ :
      (ext : {A : Set} {B : A → Set} → Extensionality A B)
      (univ : Univalence-axiom lzero) →
      ∀ {s₁ s₂} (iso : Isomorphism (s ▻ A-type) s₁ s₂) →
      cong proj₂ (isomorphic-equal ext univ (s ▻ A-type) iso) ≡
      ≈⇒≡ univ (bijection⇒weak-equivalence (proj₂ iso))
    Typ-equ ext univ (iso , A↔B) =
      let A≡B = ≈⇒≡ univ $ bijection⇒weak-equivalence A↔B in

      cong proj₂ (Σ-≡,≡→≡ (isomorphic-equal ext univ s iso)
                          (trans subst-const A≡B))                  ≡⟨ cong (cong proj₂) $ Σ-≡,≡→≡-subst-const _ _ ⟩

      cong proj₂ (cong₂ _,_ (isomorphic-equal ext univ s iso) A≡B)  ≡⟨ cong-proj₂-cong₂-, _ _ ⟩∎

      A≡B                                                           ∎

------------------------------------------------------------------------
-- An "extension": propositions

-- Extends a structure with a proposition.

Proposition : ∀ {s} →

              -- The proposition.
              (P : ⟦ s ⟧ → Set) →

              -- The proposition must be propositional (given some
              -- assumptions).
              (({A : Set} {B : A → Set} → Extensionality A B) →
               Univalence-axiom lzero →
               ∀ s → Propositional (P s)) →

              Extension s
Proposition {s} P prop = record
  { Ext = ↑ _ ∘ P
  ; Iso = λ _ _ _ → ⊤
  ; hyp = hyp′
  }
  where
  abstract
    hyp′ : (ext : {A : Set} {B : A → Set} → Extensionality A B)
           (univ : Univalence-axiom lzero) →
           ∀ {s₁ s₂} {x₁ : ↑ (lsuc lzero) (P s₁)} {x₂ : ↑ _ (P s₂)}
           (iso : Isomorphism s s₁ s₂) (i : ⊤) →
           subst (↑ _ ∘ P) (isomorphic-equal ext univ s iso) x₁ ≡ x₂
    hyp′ ext univ _ _ =
      _⇔_.to propositional⇔irrelevant (↑-closure 1 $ prop ext univ _)
             _ _

-- The proposition stating that a given type is a set.

Is-a-set : ∀ {s} → Type-extractor s → Extension s
Is-a-set extract = Proposition (Is-set ∘ Typ) Is-set-prop
  where
  open Type-extractor extract

  abstract
    Is-set-prop :
      ({A : Set} {B : A → Set} → Extensionality A B) →
      Univalence-axiom lzero →
      ∀ s → Propositional (Is-set (Typ s))
    Is-set-prop ext _ _ = H-level-propositional ext 2

------------------------------------------------------------------------
-- An "extension": n-ary functions

-- N-ary functions.

_^_⟶_ : Set → ℕ → Set → Set
A ^ zero  ⟶ B = B
A ^ suc n ⟶ B = A → A ^ n ⟶ B

-- N-ary function morphisms.

Is-_-ary-morphism :
  (n : ℕ) {A B : Set} → (A ^ n ⟶ A) → (B ^ n ⟶ B) → (A → B) → Set
Is- zero  -ary-morphism x₁ x₂ m = m x₁ ≡ x₂
Is- suc n -ary-morphism f₁ f₂ m =
  ∀ x → Is- n -ary-morphism (f₁ x) (f₂ (m x)) m

-- An n-ary function extension.

N-ary : ∀ {s} →

        -- Extracts the underlying type.
        Type-extractor s →

        -- The function's arity.
        ℕ →

        Extension s
N-ary {s} extract n = record
  { Ext = λ s → ↑ _ (Typ s ^ n ⟶ Typ s)
  ; Iso = λ f₁ f₂ iso →
            Is- n -ary-morphism (lower f₁) (lower f₂) (_≈_.to (equ iso))
  ; hyp = hyp′
  }
  where
  open Type-extractor extract

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

    hyp′ :
      (ext : {A : Set} {B : A → Set} → Extensionality A B)
      (univ : Univalence-axiom lzero) →
      ∀ {s₁ s₂ f₁} {f₂ : ↑ (lsuc lzero) _}
      (iso : Isomorphism s s₁ s₂)
      (i : Is- n -ary-morphism
             (lower f₁) (lower f₂) (_≈_.to (equ iso))) →
      subst (λ s → ↑ _ (Typ s ^ n ⟶ Typ s))
            (isomorphic-equal ext univ s iso) f₁ ≡
      f₂
    hyp′ ext univ {f₁ = f₁} {f₂} iso i =
      let lf₁ = lower f₁; lf₂ = lower f₂ in

      subst (λ s → ↑ _ (Typ s ^ n ⟶ Typ s))
            (isomorphic-equal ext univ s iso) f₁               ≡⟨ extractor-lemma ext univ (λ A → ↑ _ (A ^ n ⟶ A)) f₁ iso ⟩
      subst (λ A → ↑ _ (A ^ n ⟶ A)) (≈⇒≡ univ (equ iso)) f₁    ≡⟨ subst-↑ (λ A → A ^ n ⟶ A) ⟩
      lift (subst (λ A → A ^ n ⟶ A) (≈⇒≡ univ (equ iso)) lf₁)  ≡⟨ cong lift $ subst-isomorphism (λ _ → ext) univ (equ iso) n lf₁ lf₂ i ⟩∎
      f₂                                                       ∎

------------------------------------------------------------------------
-- An "extension": simply typed functions

-- This section contains a generalisation of the development for n-ary
-- functions above.

-- Simple types.

data Simple-type (s : Structure) : Set₁ where
  base : Type-extractor s → Simple-type s
  _⟶_  : Simple-type s → Simple-type s → Simple-type s

-- Interpretation of a simple type.

⟦_⟧⟶ : ∀ {s} → Simple-type s → ⟦ s ⟧ → Set
⟦ base A ⟧⟶ s = Type-extractor.Typ A s
⟦ σ ⟶ τ  ⟧⟶ s = ⟦ σ ⟧⟶ s → ⟦ τ ⟧⟶ s

-- A simply typed function extension (defined using extensionality).

Simple : (ext : {A : Set} {B : A → Set} → Extensionality A B) →
         ∀ {s} → Simple-type s → Extension s
Simple ext {s} σ = record
  { Ext = λ s → ↑ _ (⟦ σ ⟧⟶ s)
  ; Iso = λ f₁ f₂ → Is-isomorphism σ (lower f₁) (lower f₂)
  ; hyp = main-lemma
  }
  where
  open Type-extractor

  -- Cast. (Extensionality isn't needed to define the cast
  -- /functions/.)

  cast : (σ : Simple-type s) →
         ∀ {s₁ s₂} → Isomorphism s s₁ s₂ → ⟦ σ ⟧⟶ s₁ ≈ ⟦ σ ⟧⟶ s₂
  cast (base A) iso = equ A iso
  cast (σ ⟶ τ)  iso = →-cong ext (cast σ iso) (cast τ iso)

  -- Isomorphisms between simply typed values.

  Is-isomorphism :
    (σ : Simple-type s) →
    ∀ {s₁ s₂} → ⟦ σ ⟧⟶ s₁ → ⟦ σ ⟧⟶ s₂ → Isomorphism s s₁ s₂ → Set

  Is-isomorphism (base A) x₁ x₂ iso =
    _≈_.to (equ A iso) x₁ ≡ x₂

  Is-isomorphism (σ ⟶ τ) f₁ f₂ iso =
    ∀ f → Is-isomorphism τ (f₁ f) (f₂ (_≈_.to (cast σ iso) f)) iso

  -- Alternative definition of isomorphisms.

  Is-isomorphism′ :
    (σ : Simple-type s) →
    ∀ {s₁ s₂} → ⟦ σ ⟧⟶ s₁ → ⟦ σ ⟧⟶ s₂ → Isomorphism s s₁ s₂ → Set
  Is-isomorphism′ σ f₁ f₂ iso = _≈_.to (cast σ iso) f₁ ≡ f₂

  abstract

    -- The two definitions of isomorphisms are equivalent.

    isomorphism-definitions-equivalent :
      ∀ {s₁ s₂} (iso : Isomorphism s s₁ s₂)
      (σ : Simple-type s) {f₁ f₂} →
      Is-isomorphism σ f₁ f₂ iso ⇔ Is-isomorphism′ σ f₁ f₂ iso
    isomorphism-definitions-equivalent iso =
      λ σ → record { to = to σ; from = from σ }
      where
      to : ∀ σ {f₁ f₂} →
           Is-isomorphism σ f₁ f₂ iso → Is-isomorphism′ σ f₁ f₂ iso
      to (base A)          i = i
      to (σ ⟶ τ) {f₁} {f₂} i = ext λ x →
        _≈_.to (cast τ iso) (f₁ (_≈_.from (cast σ iso) x))  ≡⟨ to τ (i _) ⟩
        f₂ (_≈_.to (cast σ iso) (_≈_.from (cast σ iso) x))  ≡⟨ cong f₂ $ _≈_.right-inverse-of (cast σ iso) x ⟩∎
        f₂ x                                                ∎

      from : ∀ σ {f₁ f₂} →
             Is-isomorphism′ σ f₁ f₂ iso → Is-isomorphism σ f₁ f₂ iso
      from (base A)          i = i
      from (σ ⟶ τ) {f₁} {f₂} i = λ f → from τ
        (_≈_.to (cast τ iso) (f₁ f)                                   ≡⟨ cong (_≈_.to (cast τ iso) ∘ f₁) $ sym $
                                                                           _≈_.left-inverse-of (cast σ iso) f ⟩
         _≈_.to (cast τ iso)
                (f₁ (_≈_.from (cast σ iso) (_≈_.to (cast σ iso) f)))  ≡⟨ cong (λ g → g (_≈_.to (cast σ iso) f)) i ⟩∎

         f₂ (_≈_.to (cast σ iso) f)                                   ∎)

    -- The equality that we get from a cast (via ≈⇒≡) can also be
    -- obtained from isomorphic-equal.

    cast-lemma :
      (ext : {A : Set} {B : A → Set} → Extensionality A B)
      (univ : Univalence-axiom lzero) →
      ∀ (σ : Simple-type s) {s₁ s₂} (iso : Isomorphism s s₁ s₂) →
      cong ⟦ σ ⟧⟶ (isomorphic-equal ext univ s iso) ≡
        ≈⇒≡ univ (cast σ iso)
    cast-lemma ext′ univ (base A)  iso = Typ-equ A ext′ univ iso
    cast-lemma ext′ univ (σ₁ ⟶ σ₂) iso =
      let iso-eq = isomorphic-equal ext′ univ s iso in

      cong ⟦ σ₁ ⟶ σ₂ ⟧⟶ iso-eq                                           ≡⟨ sym $ cong₂-cong-cong ⟦ σ₁ ⟧⟶ ⟦ σ₂ ⟧⟶ (λ A B → A → B) ⟩

      cong₂ (λ A B → A → B) (cong ⟦ σ₁ ⟧⟶ iso-eq) (cong ⟦ σ₂ ⟧⟶ iso-eq)  ≡⟨ cong₂ (cong₂ (λ A B → A → B)) (cast-lemma ext′ univ σ₁ iso)
                                                                                                          (cast-lemma ext′ univ σ₂ iso) ⟩
      cong₂ (λ A B → A → B) (≈⇒≡ univ (cast σ₁ iso))
                            (≈⇒≡ univ (cast σ₂ iso))                     ≡⟨ sym $ ≈⇒≡-→-cong ext univ (cast σ₁ iso) (cast σ₂ iso) ⟩∎

      ≈⇒≡ univ (→-cong ext (cast σ₁ iso) (cast σ₂ iso))                  ∎

    -- The main lemma: If there is an isomorphism from f₁ to f₂, then
    -- a certain instance of subst maps f₁ to f₂.

    main-lemma :
      (ext : {A : Set} {B : A → Set} → Extensionality A B)
      (univ : Univalence-axiom lzero) →
      ∀ {s₁ s₂ f₁} {f₂ : ↑ (lsuc lzero) _} (iso : Isomorphism s s₁ s₂) →
      Is-isomorphism σ (lower f₁) (lower f₂) iso →
      subst (↑ _ ∘ ⟦ σ ⟧⟶) (isomorphic-equal ext univ s iso) f₁ ≡ f₂
    main-lemma ext univ {f₁ = f₁} {f₂} iso i =
      let iso-eq = isomorphic-equal ext univ s iso in

      subst (↑ _ ∘ ⟦ σ ⟧⟶) iso-eq f₁          ≡⟨ subst-∘ (↑ _) ⟦ σ ⟧⟶ _ ⟩
      subst (↑ _) (cong ⟦ σ ⟧⟶ iso-eq) f₁     ≡⟨ cong (λ p → subst (↑ _) p f₁) (cast-lemma ext univ σ iso) ⟩
      subst (↑ _) (≈⇒≡ univ (cast σ iso)) f₁  ≡⟨ sym $ subst-unique (↑ _) (λ A≈B → lift ∘ _≈_.to A≈B ∘ lower) refl univ _ _ ⟩
      lift (_≈_.to (cast σ iso) (lower f₁))   ≡⟨ cong lift $ _⇔_.to (isomorphism-definitions-equivalent iso σ) i ⟩∎
      f₂                                      ∎

------------------------------------------------------------------------
-- Some example structures

-- Example: magmas.

magma : Structure
magma = ε ▻ A-type ▻ N-ary [0] 2

Magma : Set₁
Magma = ⟦ magma ⟧

private

  -- An unfolding of Magma.

  Magma-unfolded : Magma ≡
                   Σ (↑ _ ⊤ × Set) λ { (_ , A) → ↑ _ (A → A → A) }
  Magma-unfolded = refl _

-- Example: semigroups. Note that one axiom states that the underlying
-- type is a set. This assumption is used to prove that the other
-- axiom is propositional.

semigroup : Structure
semigroup =
  ε

  ▻ A-type

  ▻ Is-a-set [0]

  ▻ N-ary (1+ [0]) 2

  ▻ Proposition
      (λ { (_ , lift _∙_) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
      assoc-prop

  where
  assoc-prop = λ { ext _ ((_ , lift Aset) , _) →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Aset _ _ }

Semigroup : Set₁
Semigroup = ⟦ semigroup ⟧

private

  -- An unfolding of Semigroup.

  Semigroup-unfolded :
    Semigroup ≡ Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                                        ) λ {  (_ , A) →
      ↑ _ (Is-set A)                            }) λ { ((_ , A) , _) →
      ↑ _ (A → A → A)                           }) λ { (_ , lift _∙_) →
      ↑ _ (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z) }
  Semigroup-unfolded = refl _

-- Example: Sets with fixed-point operators.

set-with-fixed-point-operator :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure
set-with-fixed-point-operator ext =
  ε

  ▻ A-type

  ▻ Is-a-set [0]

  ▻ Simple ext ((base (1+ [0]) ⟶ base (1+ [0])) ⟶ base (1+ [0]))

  ▻ Proposition
      (λ { (_ , lift fix) →
           ∀ f → fix f ≡ f (fix f) })
      fix-point-prop

  where
  fix-point-prop = λ { ext _ ((_ , lift Aset) , _) →
    Π-closure ext 1 λ _ →
    Aset _ _ }

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
      Set                            ) λ {  (_ , A) →
      ↑ _ (Is-set A)                }) λ { ((_ , A) , _) →
      ↑ _ ((A → A) → A)             }) λ { (_ , lift fix) →
      ↑ _ (∀ f → fix f ≡ f (fix f)) }
  Set-with-fixed-point-operator-unfolded _ = refl _

-- Example: abelian groups.

abelian-group : Structure
abelian-group =
  ε

  -- The underlying type.
  ▻ A-type

  -- The underlying type is a set.
  ▻ Is-a-set [0]

  -- The binary group operation.
  ▻ N-ary (1+ [0]) 2

  -- Commutativity.
  ▻ Comm

  -- Associativity.
  ▻ Assoc

  -- Identity.
  ▻ N-ary (1+ 1+ 1+ 1+ [0]) 0

  -- Left identity.
  ▻ Left-identity

  -- Right identity.
  ▻ Right-identity

  -- Inverse.
  ▻ N-ary (1+ 1+ 1+ 1+ 1+ 1+ 1+ [0]) 1

  -- Left inverse.
  ▻ Left-inverse

  -- Right inverse.
  ▻ Right-inverse

  where
  bin = ε ▻ A-type ▻ Is-a-set [0] ▻ N-ary (1+ [0]) 2

  Comm = Proposition {bin}
    (λ { (_ , lift _∙_) →
       ∀ x y → x ∙ y ≡ y ∙ x })

    (λ { ext _ ((_ , lift Aset) , _) →
       Π-closure ext 1 λ _ →
       Π-closure ext 1 λ _ →
       Aset _ _
     })

  comm = bin ▻ Comm

  Assoc = Proposition {comm}
    (λ { ((_ , lift _∙_) , _) →
         ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })

    (λ { ext _ (((_ , lift Aset) , _) , _) →
       Π-closure ext 1 λ _ →
       Π-closure ext 1 λ _ →
       Π-closure ext 1 λ _ →
       Aset _ _
     })

  identity = comm ▻ Assoc ▻ N-ary (1+ 1+ 1+ 1+ [0]) 0

  Left-identity = Proposition {identity}
    (λ { ((((_ , lift _∙_) , _) , _) , lift e) →
         ∀ x → e ∙ x ≡ x })

    (λ { ext _ (((((_ , lift Aset) , _) , _) , _) , _) →
       Π-closure ext 1 λ _ →
       Aset _ _
     })

  left-identity = identity ▻ Left-identity

  Right-identity = Proposition {left-identity}
    (λ { (((((_ , lift _∙_) , _) , _) , lift e) , _) →
         ∀ x → x ∙ e ≡ x })

    (λ { ext _ ((((((_ , lift Aset) , _) , _) , _) , _) , _) →
       Π-closure ext 1 λ _ →
       Aset _ _
     })

  inv = left-identity ▻ Right-identity ▻
        N-ary (1+ 1+ 1+ 1+ 1+ 1+ 1+ [0]) 1

  Left-inverse = Proposition {inv}
    (λ { (((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) →
         ∀ x → (x ⁻¹) ∙ x ≡ e })

    (λ { ext _ ((((((((_ , lift Aset) , _) , _) , _) , _) , _) , _) , _) →
       Π-closure ext 1 λ _ →
       Aset _ _
     })

  left-inverse = inv ▻ Left-inverse

  Right-inverse = Proposition {left-inverse}
    (λ { ((((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) , _) →
         ∀ x → x ∙ (x ⁻¹) ≡ e })

    (λ { ext _ (((((((((_ , lift Aset) , _) , _) , _) , _) , _) , _) , _) , _) →
       Π-closure ext 1 λ _ →
       Aset _ _
     })

Abelian-group : Set₁
Abelian-group = ⟦ abelian-group ⟧

private

  -- An unfolding of Abelian-group. Note that the inner structure is
  -- left-nested.

  Abelian-group-unfolded :
    Abelian-group ≡ Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                                        ) λ {        (_ , A) →
      ↑ _ (Is-set A)                            }) λ {       ((_ , A) , _) →
      ↑ _ (A → A → A)                           }) λ {                  (_ , lift _∙_) →
      ↑ _ (∀ x y → x ∙ y ≡ y ∙ x)               }) λ {                 ((_ , lift _∙_) , _) →
      ↑ _ (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z) }) λ {    (((((_ , A) , _) , _  ) , _) , _) →
      ↑ _ A                                     }) λ {               ((((_ , lift _∙_) , _) , _) , lift e) →
      ↑ _ (∀ x → e ∙ x ≡ x)                     }) λ {              (((((_ , lift _∙_) , _) , _) , lift e) , _) →
      ↑ _ (∀ x → x ∙ e ≡ x)                     }) λ { ((((((((_ , A) , _) , _  ) , _) , _) , _) , _) , _) →
      ↑ _ (A → A)                               }) λ {            (((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) →
      ↑ _ (∀ x → (x ⁻¹) ∙ x ≡ e)                }) λ {           ((((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) , _) →
      ↑ _ (∀ x → x ∙ (x ⁻¹) ≡ e)                }
  Abelian-group-unfolded = refl _
