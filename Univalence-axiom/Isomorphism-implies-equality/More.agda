------------------------------------------------------------------------
-- A large(r) class of algebraic structures satisfies the property
-- that isomorphic instances of a structure are equal (assuming
-- univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality.More
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq using (_↔_; module _↔_)
open Derived-definitions-and-properties eq
open import Equivalence using (_⇔_; module _⇔_)
open import Function-universe eq using (→-cong-⇔; →-cong)
open import H-level eq hiding (Proposition; Type)
open import H-level.Closure eq
open import Prelude
open import Univalence-axiom eq
open import Weak-equivalence eq as Weak using (_≈_; module _≈_; ↔⇒≈)

------------------------------------------------------------------------
-- A record packing up certain assumptions

record Assumptions : Set₂ where
  field
    ext   : Extensionality (# 1) (# 1)
    univ  : Univalence-axiom (# 0)
    univ₁ : Univalence-axiom (# 1)

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
            Ext s₁ → Ext s₂ → Isomorphism s s₁ s₂ → Set₁

      hyp : (ass : Assumptions) →
            {s₁ s₂ : ⟦ s ⟧} {x₁ : Ext s₁} {x₂ : Ext s₂}
            (iso : Isomorphism s s₁ s₂) (i : Iso x₁ x₂ iso) →
            subst Ext (isomorphic-equal ass s iso) x₁ ≡ x₂

  -- Interpretation of the codes.

  ⟦_⟧ : Structure → Set₁
  ⟦ ε     ⟧ = ↑ _ ⊤
  ⟦ s ▻ e ⟧ = Σ ⟦ s ⟧ (Extension.Ext e)

  -- Isomorphisms.

  Isomorphism : (s : Structure) → ⟦ s ⟧ → ⟦ s ⟧ → Set₁
  Isomorphism ε       _         _         = ↑ _ ⊤
  Isomorphism (s ▻ e) (s₁ , x₁) (s₂ , x₂) =
    Σ (Isomorphism s s₁ s₂) (Extension.Iso e x₁ x₂)

  -- Isomorphic structures are equal (assuming extensionality and
  -- univalence).

  isomorphic-equal : Assumptions →
                     (s : Structure) {s₁ s₂ : ⟦ s ⟧} →
                     Isomorphism s s₁ s₂ → s₁ ≡ s₂
  isomorphic-equal _   ε                           _         = refl _
  isomorphic-equal ass (s ▻ e) {s₁ , x₁} {s₂ , x₂} (iso , i) =
    (s₁ , x₁)  ≡⟨ Σ-≡,≡→≡ (isomorphic-equal ass s iso)
                          (Extension.hyp e ass iso i) ⟩∎
    (s₂ , x₂)  ∎

open Extension public

------------------------------------------------------------------------
-- Type extractors

-- Type extractors.

record Type-extractor (s : Structure) : Set₂ where
  field
    -- Extracts a type from a structure.
    Typ : ⟦ s ⟧ → Set

    -- Extracts a weak equivalence.
    equ : ∀ {s₁ s₂} → Isomorphism s s₁ s₂ → Typ s₁ ≈ Typ s₂

    -- Typ and equ are related via isomorphic-equal.
    Typ-equ : (ass : Assumptions) → let open Assumptions ass in
              {s₁ s₂ : ⟦ s ⟧} (iso : Isomorphism s s₁ s₂) →
              cong Typ (isomorphic-equal ass s iso) ≡
              ≈⇒≡ univ (equ iso)

-- Constant type extractor.

[_] : ∀ {s} → Set → Type-extractor s
[_] {s} A = record
  { Typ     = λ _ → A
  ; equ     = λ _ → Weak.id
  ; Typ-equ = Typ-equ
  }
  where
  abstract
    Typ-equ : (ass : Assumptions) → let open Assumptions ass in
              ∀ {s₁ s₂} (iso : Isomorphism s s₁ s₂) →
              cong (λ _ → A) (isomorphic-equal ass s iso) ≡
              ≈⇒≡ univ Weak.id
    Typ-equ ass _ =
      cong (λ _ → A) _         ≡⟨ cong-const _ ⟩
      refl A                   ≡⟨ sym $ _≈_.left-inverse-of (≡≈≈ univ) (refl A) ⟩
      ≈⇒≡ univ (≡⇒≈ (refl A))  ≡⟨ cong (≈⇒≡ univ) ≡⇒≈-refl ⟩∎
      ≈⇒≡ univ Weak.id         ∎
      where open Assumptions ass

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
    Typ-equ′ : (ass : Assumptions) → let open Assumptions ass in
               ∀ {s₁ s₂} (iso : Isomorphism (s ▻ e) s₁ s₂) →
               cong (Typ ∘ proj₁) (isomorphic-equal ass (s ▻ e) iso) ≡
               ≈⇒≡ univ (equ (proj₁ iso))
    Typ-equ′ ass (iso , i) =
      let open Assumptions ass
          iso-eq = isomorphic-equal ass in

      cong (Typ ∘ proj₁) (iso-eq (s ▻ e) (iso , i))     ≡⟨ sym $ cong-∘ Typ proj₁ (iso-eq (s ▻ e) (iso , i)) ⟩
      cong Typ (cong proj₁ $ iso-eq (s ▻ e) (iso , i))  ≡⟨ cong (cong Typ) $ proj₁-Σ-≡,≡→≡ _ _ ⟩
      cong Typ (iso-eq s iso)                           ≡⟨ Typ-equ ass iso ⟩∎
      ≈⇒≡ univ (equ iso)                                ∎

------------------------------------------------------------------------
-- An "extension": types

-- Extends a structure with a type.

Type : ∀ {s} → Extension s
Type {s} = record
  { Ext = λ _ → Set
  ; Iso = λ A B _ → ↑ _ (A ↔ B)
  ; hyp = λ { ass {x₁ = A} {x₂ = B} _ (lift bij) →
      let open Assumptions ass in

      subst (λ _ → Set) _ A  ≡⟨ subst-const ⟩
      A                      ≡⟨ ≈⇒≡ univ (↔⇒≈ bij) ⟩∎
      B                      ∎ }
  }

-- A corresponding type extractor.

[0] : ∀ {s} → Type-extractor (s ▻ Type)
[0] {s} = record
  { Typ     = λ { (_ , A) → A }
  ; equ     = λ { (_ , lift A↔B) → ↔⇒≈ A↔B }
  ; Typ-equ = Typ-equ
  }
  where
  abstract
    Typ-equ : (ass : Assumptions) → let open Assumptions ass in
              ∀ {s₁ s₂} (iso : Isomorphism (s ▻ Type) s₁ s₂) →
              cong proj₂ (isomorphic-equal ass (s ▻ Type) iso) ≡
              ≈⇒≡ univ (↔⇒≈ $ lower $ proj₂ iso)
    Typ-equ ass (iso , lift A↔B) =
      let open Assumptions ass
          iso-eq = isomorphic-equal ass s iso
          A≡B = ≈⇒≡ univ $ ↔⇒≈ A↔B in

      cong proj₂ (Σ-≡,≡→≡ iso-eq (trans subst-const A≡B))  ≡⟨ cong (cong proj₂) $ Σ-≡,≡→≡-subst-const _ _ ⟩

      cong proj₂ (cong₂ _,_ iso-eq A≡B)                    ≡⟨ cong-proj₂-cong₂-, _ _ ⟩∎

      A≡B                                                  ∎

------------------------------------------------------------------------
-- An "extension": propositions

-- Extends a structure with a proposition.

Proposition : ∀ {s} →

              -- The proposition.
              (P : ⟦ s ⟧ → Set) →

              -- The proposition must be propositional (given some
              -- assumptions).
              (Assumptions → ∀ s → Propositional (P s)) →

              Extension s
Proposition {s} P prop = record
  { Ext = ↑ _ ∘ P
  ; Iso = λ _ _ _ → ↑ _ ⊤
  ; hyp = hyp′
  }
  where
  abstract
    hyp′ : (ass : Assumptions) →
           ∀ {s₁ s₂} {x₁ : ↑ (# 1) (P s₁)} {x₂ : ↑ _ (P s₂)}
           (iso : Isomorphism s s₁ s₂) (i : ↑ (# 1) ⊤) →
           subst (↑ _ ∘ P) (isomorphic-equal ass s iso) x₁ ≡
           x₂
    hyp′ ass _ _ =
      _⇔_.to propositional⇔irrelevant
             (↑-closure 1 $ prop ass _)
             _ _

-- The proposition stating that a given type is a set.

Is-a-set : ∀ {s} → Type-extractor s → Extension s
Is-a-set extract = Proposition (Is-set ∘ Typ) Is-set-prop
  where
  open Type-extractor extract

  abstract
    Is-set-prop : Assumptions →
                  ∀ s → Propositional (Is-set (Typ s))
    Is-set-prop ass _ =
      H-level-propositional (lower-extensionality _ _ ext) 2
      where open Assumptions ass

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
  ; Iso = λ { (lift f₁) (lift f₂) iso →
                ↑ _ (Is- n -ary-morphism f₁ f₂ (_≈_.to (equ iso))) }
  ; hyp = main-lemma
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
              (∀ n → Extensionality′ A (λ _ → A ^ n ⟶ A)) →
              ∀ n (f : A ^ n ⟶ A) → cast Weak.id n f ≡ f
    cast-id ext zero    x = refl x
    cast-id ext (suc n) f = ext n $ λ x → cast-id ext n (f x)

    -- We can express cast (applied to an isomorphism) as an instance
    -- of subst (assuming extensionality and univalence).

    cast-is-subst :
      (∀ {A : Set} n → Extensionality′ A (λ _ → A ^ n ⟶ A)) →
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
      (∀ n → Extensionality′ A₂ (λ _ → A₂ ^ n ⟶ A₂)) →
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
      (∀ {A : Set} n → Extensionality′ A (λ _ → A ^ n ⟶ A)) →
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

    -- The main lemma: If there is an isomorphism from f₁ to f₂, then
    -- a certain instance of subst maps f₁ to f₂.

    main-lemma :
      (ass : Assumptions) →
      ∀ {s₁ s₂ f₁} {f₂ : ↑ (# 1) _}
      (iso : Isomorphism s s₁ s₂) →
      ↑ (# 1)
        (Is- n -ary-morphism (lower f₁) (lower f₂) (_≈_.to (equ iso))) →
      subst (λ s → ↑ _ (Typ s ^ n ⟶ Typ s))
            (isomorphic-equal ass s iso) f₁ ≡
      f₂
    main-lemma ass {f₁ = f₁} {f₂} iso (lift i) =
      let open Assumptions ass
          iso-eq = isomorphic-equal ass s iso
          lf₁ = lower f₁; lf₂ = lower f₂ in

      subst (λ s → ↑ _ (Typ s ^ n ⟶ Typ s)) iso-eq f₁          ≡⟨ subst-∘ (λ A → ↑ _ (A ^ n ⟶ A)) Typ _ ⟩
      subst (λ A → ↑ _ (A ^ n ⟶ A)) (cong Typ iso-eq) f₁       ≡⟨ cong (λ eq → subst (λ A → ↑ _ (A ^ n ⟶ A)) eq f₁) $ Typ-equ ass iso ⟩
      subst (λ A → ↑ _ (A ^ n ⟶ A)) (≈⇒≡ univ (equ iso)) f₁    ≡⟨ subst-↑ (λ A → A ^ n ⟶ A) ⟩
      lift (subst (λ A → A ^ n ⟶ A) (≈⇒≡ univ (equ iso)) lf₁)  ≡⟨ cong lift $ subst-isomorphism (λ _ → lower-extensionality _ _ ext)
                                                                                                univ (equ iso) n lf₁ lf₂ i ⟩∎
      f₂                                                       ∎

------------------------------------------------------------------------
-- An "extension": simply typed functions

-- This section contains a generalisation of the development for n-ary
-- functions above.

-- Simple types.

data Simple-type (s : Structure) : Set₂ where
  base : Type-extractor s → Simple-type s
  _⟶_  : Simple-type s → Simple-type s → Simple-type s

-- Interpretation of a simple type.

⟦_⟧⟶ : ∀ {s} → Simple-type s → ⟦ s ⟧ → Set
⟦ base A ⟧⟶ s = Type-extractor.Typ A s
⟦ σ ⟶ τ  ⟧⟶ s = ⟦ σ ⟧⟶ s → ⟦ τ ⟧⟶ s

-- A simply typed function extension.

Simple : ∀ {s} → Simple-type s → Extension s
Simple {s} σ = record
  { Ext = λ s → ↑ _ (⟦ σ ⟧⟶ s)
  ; Iso = λ { (lift f₁) (lift f₂) iso →
                ↑ _ (Is-isomorphism σ f₁ f₂ iso) }
  ; hyp = main-lemma
  }
  where
  open Type-extractor

  -- Isomorphisms between simply typed values.

  Is-isomorphism :
    (σ : Simple-type s) →
    ∀ {s₁ s₂} → ⟦ σ ⟧⟶ s₁ → ⟦ σ ⟧⟶ s₂ → Isomorphism s s₁ s₂ → Set
  Is-isomorphism (base A) x₁ x₂ iso = _≈_.to (equ A iso) x₁ ≡ x₂
  Is-isomorphism (σ ⟶ τ)  f₁ f₂ iso =
    ∀ {x₁ x₂} →
    Is-isomorphism σ x₁ x₂ iso →
    Is-isomorphism τ (f₁ x₁) (f₂ x₂) iso

  -- Cast (defined using extensionality).

  cast : Extensionality (# 0) (# 0) →
         (σ : Simple-type s) →
         ∀ {s₁ s₂} → Isomorphism s s₁ s₂ → ⟦ σ ⟧⟶ s₁ ≈ ⟦ σ ⟧⟶ s₂
  cast _   (base A) iso = equ A iso
  cast ext (σ ⟶ τ)  iso = →-cong ext (cast ext σ iso) (cast ext τ iso)

  -- Alternative definition of isomorphisms (defined using
  -- extensionality).

  Is-isomorphism′ :
    Extensionality (# 0) (# 0) →
    (σ : Simple-type s) →
    ∀ {s₁ s₂} → ⟦ σ ⟧⟶ s₁ → ⟦ σ ⟧⟶ s₂ → Isomorphism s s₁ s₂ → Set
  Is-isomorphism′ ext σ f₁ f₂ iso = _≈_.to (cast ext σ iso) f₁ ≡ f₂

  abstract

    -- The two definitions of isomorphisms are equivalent (assuming
    -- extensionality).

    isomorphism-definitions-equivalent :
      (ext : Extensionality (# 0) (# 0)) →
      ∀ {s₁ s₂} (iso : Isomorphism s s₁ s₂)
      (σ : Simple-type s) {f₁ f₂} →
      Is-isomorphism σ f₁ f₂ iso ⇔ Is-isomorphism′ ext σ f₁ f₂ iso
    isomorphism-definitions-equivalent ext iso =
      λ σ → record { to = to σ; from = from σ }
      where
      mutual
        to : ∀ σ {f₁ f₂} →
             Is-isomorphism σ f₁ f₂ iso →
             Is-isomorphism′ ext σ f₁ f₂ iso
        to (base A)          i = i
        to (σ ⟶ τ) {f₁} {f₂} i = ext λ x →
          _≈_.to (cast ext τ iso) (f₁ (_≈_.from (cast ext σ iso) x))  ≡⟨ to τ (i (from σ (refl _))) ⟩
          f₂ (_≈_.to (cast ext σ iso) (_≈_.from (cast ext σ iso) x))  ≡⟨ cong f₂ $ _≈_.right-inverse-of (cast ext σ iso) x ⟩∎
          f₂ x                                                        ∎

        from : ∀ σ {f₁ f₂} →
               Is-isomorphism′ ext σ f₁ f₂ iso →
               Is-isomorphism σ f₁ f₂ iso
        from (base A)          x₁∼x₂ = x₁∼x₂
        from (σ ⟶ τ) {f₁} {f₂} f₁∼f₂ = λ {x₁ x₂} x₁∼x₂ → from τ (
          _≈_.to (cast ext τ iso) (f₁ x₁)                              ≡⟨ cong (_≈_.to (cast ext τ iso) ∘ f₁) $ sym $
                                                                               _≈_.to-from (cast ext σ iso) $ to σ x₁∼x₂ ⟩
          _≈_.to (cast ext τ iso) (f₁ (_≈_.from (cast ext σ iso) x₂))  ≡⟨ cong (λ f → f x₂) f₁∼f₂ ⟩∎
          f₂ x₂                                                        ∎)

    -- The equality that we get from a cast (via ≈⇒≡) can also be
    -- obtained from isomorphic-equal.

    cast-lemma :
      (ass : Assumptions) → let open Assumptions ass in
      ∀ (σ : Simple-type s) {s₁ s₂} (iso : Isomorphism s s₁ s₂) →
      cong ⟦ σ ⟧⟶ (isomorphic-equal ass s iso) ≡
      ≈⇒≡ univ (cast (lower-extensionality _ _ ext) σ iso)
    cast-lemma ass (base A)  iso = Typ-equ A ass iso
    cast-lemma ass (σ₁ ⟶ σ₂) iso =
      let open Assumptions ass
          iso-eq = isomorphic-equal ass s iso

          ext₀ : Extensionality (# 0) (# 0)
          ext₀ = lower-extensionality _ _ ext in

      cong ⟦ σ₁ ⟶ σ₂ ⟧⟶ iso-eq                                           ≡⟨ sym $ cong₂-cong-cong ⟦ σ₁ ⟧⟶ ⟦ σ₂ ⟧⟶ (λ A B → A → B) ⟩

      cong₂ (λ A B → A → B) (cong ⟦ σ₁ ⟧⟶ iso-eq) (cong ⟦ σ₂ ⟧⟶ iso-eq)  ≡⟨ cong₂ (cong₂ (λ A B → A → B)) (cast-lemma ass σ₁ iso)
                                                                                                          (cast-lemma ass σ₂ iso) ⟩
      cong₂ (λ A B → A → B) (≈⇒≡ univ (cast ext₀ σ₁ iso))
                            (≈⇒≡ univ (cast ext₀ σ₂ iso))                ≡⟨ sym $ ≈⇒≡-→-cong ext₀ univ (cast ext₀ σ₁ iso) (cast ext₀ σ₂ iso) ⟩∎

      ≈⇒≡ univ (→-cong ext₀ (cast ext₀ σ₁ iso) (cast ext₀ σ₂ iso))       ∎

    -- The main lemma: If there is an isomorphism from f₁ to f₂, then
    -- a certain instance of subst maps f₁ to f₂.

    main-lemma :
      (ass : Assumptions) →
      ∀ {s₁ s₂ f₁} {f₂ : ↑ (# 1) _} (iso : Isomorphism s s₁ s₂) →
      ↑ (# 1) (Is-isomorphism σ (lower f₁) (lower f₂) iso) →
      subst (↑ _ ∘ ⟦ σ ⟧⟶) (isomorphic-equal ass s iso) f₁ ≡
      f₂
    main-lemma ass {f₁ = f₁} {f₂} iso (lift i) =
      let open Assumptions ass
          iso-eq = isomorphic-equal ass s iso

          ext₀ : Extensionality (# 0) (# 0)
          ext₀ = lower-extensionality _ _ ext in

      subst (↑ _ ∘ ⟦ σ ⟧⟶) iso-eq f₁               ≡⟨ subst-∘ (↑ _) ⟦ σ ⟧⟶ _ ⟩
      subst (↑ _) (cong ⟦ σ ⟧⟶ iso-eq) f₁          ≡⟨ cong (λ p → subst (↑ _) p f₁) (cast-lemma ass σ iso) ⟩
      subst (↑ _) (≈⇒≡ univ (cast ext₀ σ iso)) f₁  ≡⟨ sym $ subst-unique (↑ _) (λ A≈B → lift ∘ _≈_.to A≈B ∘ lower) refl univ _ _ ⟩
      lift (_≈_.to (cast ext₀ σ iso) (lower f₁))   ≡⟨ cong lift $ _⇔_.to (isomorphism-definitions-equivalent ext₀ iso σ) i ⟩∎
      f₂                                           ∎

------------------------------------------------------------------------
-- Some example structures

-- Example: magmas.

magma : Structure
magma = ε ▻ Type ▻ N-ary [0] 2

Magma : Set₁
Magma = ⟦ magma ⟧

private

  -- An unfolding of Magma.

  Magma-unfolded : Magma ≡
                   Σ (↑ _ ⊤ × Set) λ { (_ , A) → ↑ _ (A → A → A) }
  Magma-unfolded = refl _

  -- An unfolding of Isomorphism magma.

  Isomorphism-magma-unfolded :
    ∀ {A₁ : Set} {f₁ : A₁ → A₁ → A₁}
      {A₂ : Set} {f₂ : A₂ → A₂ → A₂} →
    Isomorphism magma ((_ , A₁) , lift f₁) ((_ , A₂) , lift f₂) ≡
    Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ↔ A₂)                              ) λ { (_ , lift A₁↔A₂) →
      let open _↔_ A₁↔A₂ in ↑ _ (
        ∀ x y → to (f₁ x y) ≡ f₂ (to x) (to y)) }
  Isomorphism-magma-unfolded = refl _

-- Example: semigroups. Note that one axiom states that the underlying
-- type is a set. This assumption is used to prove that the other
-- axiom is propositional.

semigroup : Structure
semigroup =
  ε

  ▻ Type

  ▻ Is-a-set [0]

  ▻ N-ary (1+ [0]) 2

  ▻ Proposition
      (λ { (_ , lift _∙_) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
      assoc-prop

  where
  assoc-prop = λ { ass ((_ , lift A-set) , _) →
    let open Assumptions ass in
    Π-closure (lower-extensionality _ _ ext) 1 λ _ →
    Π-closure (lower-extensionality _ _ ext) 1 λ _ →
    Π-closure (lower-extensionality _ _ ext) 1 λ _ →
    A-set _ _ }

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

  -- An unfolding of Isomorphism semigroup.

  Isomorphism-semigroup-unfolded :
    ∀ {A₁ : Set} {is₁ : Is-set A₁} {_∙₁_ : A₁ → A₁ → A₁}
      {assoc₁ : ∀ x y z → x ∙₁ (y ∙₁ z) ≡ (x ∙₁ y) ∙₁ z}
      {A₂ : Set} {is₂ : Is-set A₂} {_∙₂_ : A₂ → A₂ → A₂}
      {assoc₂ : ∀ x y z → x ∙₂ (y ∙₂ z) ≡ (x ∙₂ y) ∙₂ z} →
    Isomorphism semigroup
      ((((_ , A₁) , lift is₁) , lift _∙₁_) , lift assoc₁)
      ((((_ , A₂) , lift is₂) , lift _∙₂_) , lift assoc₂) ≡
    Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ↔ A₂)                          ) λ { _ →
      ↑ _ ⊤                                 }) λ { ((_ , lift A₁↔A₂) , _) →
      let open _↔_ A₁↔A₂ in ↑ _ (
        ∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y) }) λ { _ →
      ↑ _ ⊤                                 }
  Isomorphism-semigroup-unfolded = refl _

-- Example: Sets with fixed-point operators.

set-with-fixed-point-operator : Structure
set-with-fixed-point-operator =
  ε

  ▻ Type

  ▻ Is-a-set [0]

  ▻ Simple ((base (1+ [0]) ⟶ base (1+ [0])) ⟶ base (1+ [0]))

  ▻ Proposition
      (λ { (_ , lift fix) →
           ∀ f → fix f ≡ f (fix f) })
      fix-point-prop

  where
  fix-point-prop = λ { ass ((_ , lift A-set) , _) →
    let open Assumptions ass in
    Π-closure (lower-extensionality _ _ ext) 1 λ _ →
    A-set _ _ }

Set-with-fixed-point-operator : Set₁
Set-with-fixed-point-operator = ⟦ set-with-fixed-point-operator ⟧

private

  -- An unfolding of Set-with-fixed-point-operator.

  Set-with-fixed-point-operator-unfolded :
    Set-with-fixed-point-operator ≡ Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                            ) λ {  (_ , A) →
      ↑ _ (Is-set A)                }) λ { ((_ , A) , _) →
      ↑ _ ((A → A) → A)             }) λ { (_ , lift fix) →
      ↑ _ (∀ f → fix f ≡ f (fix f)) }
  Set-with-fixed-point-operator-unfolded = refl _

  -- An unfolding of Isomorphism set-with-fixed-point-operator.

  Isomorphism-set-with-fixed-point-operator-unfolded :
    ∀ {A₁ : Set} {is₁ : Is-set A₁} {fix₁ : (A₁ → A₁) → A₁}
      {fixed-point₁ : ∀ f → fix₁ f ≡ f (fix₁ f)}
      {A₂ : Set} {is₂ : Is-set A₂} {fix₂ : (A₂ → A₂) → A₂}
      {fixed-point₂ : ∀ f → fix₂ f ≡ f (fix₂ f)} →
    Isomorphism set-with-fixed-point-operator
      ((((_ , A₁) , lift is₁) , lift fix₁) , lift fixed-point₁)
      ((((_ , A₂) , lift is₂) , lift fix₂) , lift fixed-point₂) ≡
    Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ↔ A₂)                                       ) λ { _ →
      ↑ _ ⊤                                              }) λ { ((_ , lift A₁↔A₂) , _) →
      let open _↔_ A₁↔A₂ in ↑ _ (
        ∀ {f₁ f₂} →
        (∀ {x₁ x₂} → to x₁ ≡ x₂ → to (f₁ x₁) ≡ f₂ x₂) →
        to (fix₁ f₁) ≡ fix₂ f₂)                          }) λ { _ →
      ↑ _ ⊤                                              }
  Isomorphism-set-with-fixed-point-operator-unfolded = refl _

-- Example: abelian groups.

abelian-group : Structure
abelian-group =
  ε

  -- The underlying type.
  ▻ Type

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
  bin = ε ▻ Type ▻ Is-a-set [0] ▻ N-ary (1+ [0]) 2

  Comm = Proposition {bin}
    (λ { (_ , lift _∙_) →
       ∀ x y → x ∙ y ≡ y ∙ x })

    (λ { ass ((_ , lift A-set) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  comm = bin ▻ Comm

  Assoc = Proposition {comm}
    (λ { ((_ , lift _∙_) , _) →
         ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })

    (λ { ass (((_ , lift A-set) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  identity = comm ▻ Assoc ▻ N-ary (1+ 1+ 1+ 1+ [0]) 0

  Left-identity = Proposition {identity}
    (λ { ((((_ , lift _∙_) , _) , _) , lift e) →
         ∀ x → e ∙ x ≡ x })

    (λ { ass (((((_ , lift A-set) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  left-identity = identity ▻ Left-identity

  Right-identity = Proposition {left-identity}
    (λ { (((((_ , lift _∙_) , _) , _) , lift e) , _) →
         ∀ x → x ∙ e ≡ x })

    (λ { ass ((((((_ , lift A-set) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  inv = left-identity ▻ Right-identity ▻
        N-ary (1+ 1+ 1+ 1+ 1+ 1+ 1+ [0]) 1

  Left-inverse = Proposition {inv}
    (λ { (((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) →
         ∀ x → (x ⁻¹) ∙ x ≡ e })

    (λ { ass ((((((((_ , lift A-set) , _) , _) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  left-inverse = inv ▻ Left-inverse

  Right-inverse = Proposition {left-inverse}
    (λ { ((((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) , _) →
         ∀ x → x ∙ (x ⁻¹) ≡ e })

    (λ { ass (((((((((_ , lift A-set) , _) , _) , _) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
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

  -- An unfolding of Isomorphism abelian-group.

  Isomorphism-abelian-group-unfolded :
    ∀ {A₁ : Set} {is₁ : Is-set A₁} {_∙₁_ : A₁ → A₁ → A₁}
      {comm₁ : ∀ x y → x ∙₁ y ≡ y ∙₁ x}
      {assoc₁ : ∀ x y z → x ∙₁ (y ∙₁ z) ≡ (x ∙₁ y) ∙₁ z}
      {e₁ : A₁} {lid₁ : ∀ x → e₁ ∙₁ x ≡ x} {rid₁ : ∀ x → x ∙₁ e₁ ≡ x}
      {_⁻¹₁ : A₁ → A₁} {linv₁ : ∀ x → (x ⁻¹₁) ∙₁ x ≡ e₁}
      {rinv₁ : ∀ x → x ∙₁ (x ⁻¹₁) ≡ e₁}
      {A₂ : Set} {is₂ : Is-set A₂} {_∙₂_ : A₂ → A₂ → A₂}
      {comm₂ : ∀ x y → x ∙₂ y ≡ y ∙₂ x}
      {assoc₂ : ∀ x y z → x ∙₂ (y ∙₂ z) ≡ (x ∙₂ y) ∙₂ z}
      {e₂ : A₂} {lid₂ : ∀ x → e₂ ∙₂ x ≡ x} {rid₂ : ∀ x → x ∙₂ e₂ ≡ x}
      {_⁻¹₂ : A₂ → A₂} {linv₂ : ∀ x → (x ⁻¹₂) ∙₂ x ≡ e₂}
      {rinv₂ : ∀ x → x ∙₂ (x ⁻¹₂) ≡ e₂} →
    Isomorphism abelian-group
      (((((((((((_ , A₁) , lift is₁) , lift _∙₁_) , lift comm₁) ,
       lift assoc₁) , lift e₁) , lift lid₁) , lift rid₁) , lift _⁻¹₁) ,
       lift linv₁) , lift rinv₁)
      (((((((((((_ , A₂) , lift is₂) , lift _∙₂_) , lift comm₂) ,
       lift assoc₂) , lift e₂) , lift lid₂) , lift rid₂) , lift _⁻¹₂) ,
       lift linv₂) , lift rinv₂) ≡
    Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ↔ A₂)                          ) λ { _ →
      ↑ _ ⊤                                 }) λ {       ((_ , lift A₁↔A₂) , _) →
      let open _↔_ A₁↔A₂ in ↑ _ (
        ∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y) }) λ { _ →
      ↑ _ ⊤                                 }) λ { _ →
      ↑ _ ⊤                                 }) λ {    (((((_ , lift A₁↔A₂) , _) , _) , _) , _) →
      let open _↔_ A₁↔A₂ in ↑ _ (
        to e₁ ≡ e₂)                         }) λ { _ →
      ↑ _ ⊤                                 }) λ { _ →
      ↑ _ ⊤                                 }) λ { ((((((((_ , lift A₁↔A₂) , _) , _) , _) , _) , _) , _) , _) →
      let open _↔_ A₁↔A₂ in ↑ _ (
        ∀ x → to (x ⁻¹₁) ≡ to x ⁻¹₂)        }) λ { _ →
      ↑ _ ⊤                                 }) λ { _ →
      ↑ _ ⊤                                 }
  Isomorphism-abelian-group-unfolded = refl _
