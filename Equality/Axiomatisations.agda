------------------------------------------------------------------------
-- Two equivalent axiomatisations of equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

module Equality.Axiomatisations {ℓ} where

open import Equivalence hiding (id; _∘_)
open import Prelude

------------------------------------------------------------------------
-- Reflexive relations

record Reflexive : Set (suc ℓ) where
  infix 4 _≡_
  field

    -- "Equality".

    _≡_ : {A : Set ℓ} → A → A → Set ℓ

    -- Reflexivity.

    refl : {A : Set ℓ} (x : A) → x ≡ x

  ----------------------------------------------------------------------
  -- Some definitions

  -- A type is contractible if it is inhabited and all elements are
  -- equal.

  Contractible : Set ℓ → Set ℓ
  Contractible A = ∃ λ (x : A) → ∀ y → x ≡ y

  -- Singleton x is a set which contains all elements which are equal
  -- to x.

  Singleton : {A : Set ℓ} → A → Set ℓ
  Singleton x = ∃ λ y → y ≡ x

  -- Extensionality for functions of a certain type.

  Extensionality : (A : Set ℓ) → (B : A → Set ℓ) → Set ℓ
  Extensionality A B =
    {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

  -- Proofs of extensionality which behave well when applied to
  -- reflexivity.

  Well-behaved-extensionality : (A : Set ℓ) → (B : A → Set ℓ) → Set ℓ
  Well-behaved-extensionality A B =
    ∃ λ (ext : Extensionality A B) →
      ∀ f → ext (refl ∘ f) ≡ refl f

------------------------------------------------------------------------
-- Abstract definition of equality based on the J rule

-- Parametrised on a reflexive relation.

record Equality-with-J (reflexive : Reflexive) : Set (suc ℓ) where

  open Reflexive reflexive

  field

    -- The J rule.

    elim : {A : Set ℓ} (P : {x y : A} → x ≡ y → Set ℓ) →
           (∀ x → P (refl x)) →
           ∀ {x y} (x≡y : x ≡ y) → P x≡y

    -- The usual computational behaviour of the J rule.

    elim-refl : ∀ {A : Set ℓ} (P : {x y : A} → x ≡ y → Set ℓ)
                (r : ∀ x → P (refl x)) {x} →
                elim P r (refl x) ≡ r x

  ----------------------------------------------------------------------
  -- Some derived properties

  -- Congruence.

  cong : {A B : Set ℓ} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f = elim (λ {u v} _ → f u ≡ f v) (λ x → refl (f x))

  -- "Evaluation rule" for cong.

  cong-refl : {A B : Set ℓ} (f : A → B) {x : A} →
              cong f (refl x) ≡ refl (f x)
  cong-refl f = elim-refl (λ {u v} _ → f u ≡ f v) (refl ∘ f)

  -- Substitutivity.

  subst : {A : Set ℓ} (P : A → Set ℓ) {x y : A} → x ≡ y → P x → P y
  subst P = elim (λ {u v} _ → P u → P v) (λ x p → p)

  -- "Evaluation rule" for subst.

  subst-refl : ∀ {A} (P : A → Set ℓ) {x} (p : P x) →
               subst P (refl x) p ≡ p
  subst-refl P p =
    cong (λ h → h p) $
      elim-refl (λ {u v} _ → P u → P v) (λ x p → p)

  -- Singleton types are contractible.

  singleton-contractible :
    ∀ {A} (x : A) → Contractible (Singleton x)
  singleton-contractible x =
    (x , refl x) , λ p →
      elim (λ {u v} u≡v → _≡_ {A = Singleton v} (v , refl v) (u , u≡v))
           (λ _ → refl _)
           (proj₂ p)

------------------------------------------------------------------------
-- Abstract definition of equality based on substitutivity and
-- contractibility of singleton types

record Equality-with-substitutivity-and-contractibility
         (reflexive : Reflexive) : Set (suc ℓ) where

  open Reflexive reflexive

  field

    -- Substitutivity.

    subst : {A : Set ℓ} (P : A → Set ℓ) {x y : A} → x ≡ y → P x → P y

    -- The usual computational behaviour of substitutivity.

    subst-refl : {A : Set ℓ} (P : A → Set ℓ) {x : A} (p : P x) →
                 subst P (refl x) p ≡ p

    -- Singleton types are contractible.

    singleton-contractible :
      ∀ {A} (x : A) → Contractible (Singleton x)

  ----------------------------------------------------------------------
  -- Some derived properties

  -- Congruence.

  cong : {A B : Set ℓ} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f {x} x≡y =
    subst (λ y → x ≡ y → f x ≡ f y) x≡y (λ _ → refl (f x)) x≡y

  -- Symmetry.

  sym : {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
  sym {x = x} x≡y = subst (λ z → x ≡ z → z ≡ x) x≡y id x≡y

  -- "Evaluation rule" for sym.

  sym-refl : {A : Set ℓ} {x : A} → sym (refl x) ≡ refl x
  sym-refl {x = x} =
    cong (λ f → f (refl x)) $
      subst-refl (λ z → x ≡ z → z ≡ x) id

  -- Transitivity.

  trans : {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} = flip (subst (_≡_ x))

  -- "Evaluation rule" for trans.

  trans-refl-refl : {A : Set ℓ} {x : A} →
                    trans (refl x) (refl x) ≡ refl x
  trans-refl-refl {x = x} = subst-refl (_≡_ x) (refl x)

  -- Equational reasoning combinators.

  infix  2 finally
  infixr 2 _≡⟨_⟩_

  _≡⟨_⟩_ : ∀ {A} x {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  finally : ∀ {A} (x y : A) → x ≡ y → x ≡ y
  finally _ _ x≡y = x≡y

  syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

  -- The J rule.

  elim : {A : Set ℓ} (P : {x y : A} → x ≡ y → Set ℓ) →
         (∀ x → P (refl x)) →
         ∀ {x y} (x≡y : x ≡ y) → P x≡y
  elim P p {x} {y} x≡y =
    subst {A = Singleton y}
          (P ∘ proj₂)
          ((y , refl y)                      ≡⟨ sym (lemma (y , refl y)) ⟩
           proj₁ (singleton-contractible y)  ≡⟨ lemma (x , x≡y) ⟩∎
           (x , x≡y)                         ∎)
          (p y)
    where lemma = proj₂ (singleton-contractible y)

  -- Transitivity and symmetry sometimes cancel each other out.

  trans-sym : {A : Set ℓ} {x y : A} (x≡y : x ≡ y) →
              trans (sym x≡y) x≡y ≡ refl y
  trans-sym =
    elim (λ {x y} (x≡y : x ≡ y) → trans (sym x≡y) x≡y ≡ refl y)
         (λ x → trans (sym (refl x)) (refl x)  ≡⟨ cong (λ p → trans p (refl x)) sym-refl ⟩
                trans (refl x) (refl x)        ≡⟨ trans-refl-refl ⟩∎
                refl x                         ∎)

  -- "Evaluation rule" for elim.

  elim-refl : ∀ {A : Set ℓ} (P : {x y : A} → x ≡ y → Set ℓ)
              (p : ∀ x → P (refl x)) {x} →
              elim P p (refl x) ≡ p x
  elim-refl {A} P p {x} =
    subst {A = Singleton x} (P ∘ proj₂) (trans (sym lemma) lemma) (p x)  ≡⟨ cong (λ q → subst (P ∘ proj₂) q (p x)) (trans-sym lemma) ⟩
    subst {A = Singleton x} (P ∘ proj₂) (refl (x , refl x))       (p x)  ≡⟨ subst-refl {A = Singleton x} (P ∘ proj₂) (p x) ⟩∎
    p x                                                                  ∎
    where lemma = proj₂ (singleton-contractible x) (x , refl x)

------------------------------------------------------------------------
-- The two abstract definitions are equivalent

J⇔subst+contr :
  ∀ {reflexive} →
  Equality-with-J reflexive ⇔
  Equality-with-substitutivity-and-contractibility reflexive
J⇔subst+contr {reflexive} = equivalent ⇒ ⇐
  where
  ⇒ : Equality-with-J reflexive →
      Equality-with-substitutivity-and-contractibility reflexive
  ⇒ EJ = record
    { subst                  = subst
    ; subst-refl             = subst-refl
    ; singleton-contractible = singleton-contractible
    }
    where open Equality-with-J EJ

  ⇐ : Equality-with-substitutivity-and-contractibility reflexive →
      Equality-with-J reflexive
  ⇐ ESC = record
    { elim      = elim
    ; elim-refl = elim-refl
    }
    where open Equality-with-substitutivity-and-contractibility ESC
