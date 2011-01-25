------------------------------------------------------------------------
-- An equality which I pretend does not come with the K rule
------------------------------------------------------------------------

-- As shown below this equality is isomorphic to Agda's ordinary
-- propositional equality. I don't think I have made use of Agda's K
-- rule in this development, but Agda does not enforce this, so it is
-- possible that the rule is used accidentally.

module Equality-without-K where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Function using (_$_; _∘_; id; flip)
open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalent; module Equivalent)
open import Function.Inverse using (Inverse)
open import Function.Surjection using (Surjection)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Some auxiliary definitions, parametrised on an equality relation

module Auxiliary (_≡_ : {A : Set} → A → A → Set) where

  -- A type is contractible if it is inhabited and all elements are
  -- equal.

  Contractible : Set → Set
  Contractible A = ∃ λ (x : A) → ∀ y → x ≡ y

  -- Singleton x is a set which contains all elements which are equal
  -- to x.

  Singleton : {A : Set} → A → Set
  Singleton x = ∃ λ y → x ≡ y

------------------------------------------------------------------------
-- Abstract definition of equality based on the J rule

record Equality-with-J : Set₁ where

  ----------------------------------------------------------------------
  -- Definition

  infix 4 _≡_
  field

    -- Equality.

    _≡_ : {A : Set} → A → A → Set

    -- Reflexivity.

    refl : {A : Set} (x : A) → x ≡ x

    -- The J rule.

    elim : {A : Set} (P : {x y : A} → x ≡ y → Set) →
           (∀ x → P (refl x)) →
           ∀ {x y} (x≡y : x ≡ y) → P x≡y

    -- The usual computational behaviour of the J rule.

    elim-refl : ∀ {A : Set} (P : {x y : A} → x ≡ y → Set)
                (r : ∀ x → P (refl x)) {x} →
                elim P r (refl x) ≡ r x

  ----------------------------------------------------------------------
  -- Some derived properties

  -- Congruence.

  cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f = elim (λ {u v} _ → f u ≡ f v) (λ x → refl (f x))

  -- "Evaluation rule" for cong.

  cong-refl : {A B : Set} (f : A → B) {x : A} →
              cong f (refl x) ≡ refl (f x)
  cong-refl f = elim-refl (λ {u v} _ → f u ≡ f v) (refl ∘ f)

  -- Substitutivity.

  subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
  subst P = elim (λ {u v} _ → P u → P v) (λ x p → p)

  -- "Evaluation rule" for subst.

  subst-refl : ∀ {A} (P : A → Set) {x} (p : P x) →
               subst P (refl x) p ≡ p
  subst-refl P p =
    cong (λ h → h p) $
      elim-refl (λ {u v} _ → P u → P v) (λ x p → p)

  open Auxiliary _≡_

  -- Singleton types are contractible.

  singleton-contractible :
    ∀ {A} (x : A) → Contractible (Singleton x)
  singleton-contractible x =
    (x , refl x) , λ p →
      elim (λ {u v} u≡v → _≡_ {A = Singleton u} (u , refl u) (v , u≡v))
           (λ _ → refl _)
           (proj₂ p)

------------------------------------------------------------------------
-- Abstract definition of equality based on substitutivity and
-- contractibility of singleton types

record Equality-with-substitutivity-and-contractibility : Set₁ where

  ----------------------------------------------------------------------
  -- Definition

  infix 4 _≡_
  field

    -- Equality.

    _≡_ : {A : Set} → A → A → Set

    -- Reflexivity.

    refl : {A : Set} (x : A) → x ≡ x

    -- Substitutivity.

    subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y

    -- The usual computational behaviour of substitutivity.

    subst-refl : {A : Set} (P : A → Set) {x : A} (p : P x) →
                 subst P (refl x) p ≡ p

  open Auxiliary _≡_

  field

    -- Singleton types are contractible.

    singleton-contractible :
      ∀ {A} (x : A) → Contractible (Singleton x)

  ----------------------------------------------------------------------
  -- Some derived properties

  -- Congruence.

  cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f {x} x≡y =
    subst (λ y → x ≡ y → f x ≡ f y) x≡y (λ _ → refl (f x)) x≡y

  -- Symmetry.

  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym {x = x} x≡y = subst (λ z → x ≡ z → z ≡ x) x≡y id x≡y

  -- "Evaluation rule" for sym.

  sym-refl : {A : Set} {x : A} → sym (refl x) ≡ refl x
  sym-refl {x = x} =
    cong (λ f → f (refl x)) $
      subst-refl (λ z → x ≡ z → z ≡ x) id

  -- Transitivity.

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} = flip (subst (_≡_ x))

  -- "Evaluation rule" for trans.

  trans-refl-refl : {A : Set} {x : A} →
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

  elim : {A : Set} (P : {x y : A} → x ≡ y → Set) →
         (∀ x → P (refl x)) →
         ∀ {x y} (x≡y : x ≡ y) → P x≡y
  elim P p {x} {y} x≡y =
    subst {A = Singleton x}
          (P ∘ proj₂)
          ((x , refl x)                      ≡⟨ sym (lemma (x , refl x)) ⟩
           proj₁ (singleton-contractible x)  ≡⟨ lemma (y , x≡y) ⟩∎
           (y , x≡y)                         ∎)
          (p x)
    where lemma = proj₂ (singleton-contractible x)

  -- Transitivity and symmetry sometimes cancel each other out.

  trans-sym : {A : Set} {x y : A} (x≡y : x ≡ y) →
              trans (sym x≡y) x≡y ≡ refl y
  trans-sym =
    elim (λ {x y} (x≡y : x ≡ y) → trans (sym x≡y) x≡y ≡ refl y)
         (λ x → trans (sym (refl x)) (refl x)  ≡⟨ cong (λ p → trans p (refl x)) sym-refl ⟩
                trans (refl x) (refl x)        ≡⟨ trans-refl-refl ⟩∎
                refl x                         ∎)

  -- "Evaluation rule" for elim.

  elim-refl : ∀ {A : Set} (P : {x y : A} → x ≡ y → Set)
              (p : ∀ x → P (refl x)) {x} →
              elim P p (refl x) ≡ p x
  elim-refl {A} P p {x} =
    subst {A = Singleton x} (P ∘ proj₂) (trans (sym lemma) lemma) (p x)  ≡⟨ cong (λ q → subst (P ∘ proj₂) q (p x)) (trans-sym lemma) ⟩
    subst {A = Singleton x} (P ∘ proj₂) (refl (x , refl x))       (p x)  ≡⟨ subst-refl {A = Singleton x} (P ∘ proj₂) (p x) ⟩∎
    p x                                                                  ∎
    where lemma = proj₂ (singleton-contractible x) (x , refl x)

------------------------------------------------------------------------
-- The two abstract definitions are equivalent

J⇔subst+contr : Equality-with-J ⇔
                Equality-with-substitutivity-and-contractibility
J⇔subst+contr = equivalent ⇒ ⇐
  where
  ⇒ : Equality-with-J →
      Equality-with-substitutivity-and-contractibility
  ⇒ EJ = record
    { _≡_                    = _≡_
    ; refl                   = refl
    ; subst                  = subst
    ; subst-refl             = subst-refl
    ; singleton-contractible = singleton-contractible
    }
    where open Equality-with-J EJ

  ⇐ : Equality-with-substitutivity-and-contractibility →
      Equality-with-J
  ⇐ ESC = record
    { _≡_       = _≡_
    ; refl      = refl
    ; elim      = elim
    ; elim-refl = elim-refl
    }
    where
    open Equality-with-substitutivity-and-contractibility ESC

------------------------------------------------------------------------
-- Concrete definition of equality

abstract

  infix 4 _≡_

  -- Note that the implementation of _≡_ is kept abstract.

  data _≡_ {A : Set} : A → A → Set where
    refl′ : ∀ x → x ≡ x

  refl : {A : Set} (x : A) → x ≡ x
  refl = refl′

  elim : {A : Set} (P : {x y : A} → x ≡ y → Set) →
         (∀ x → P (refl x)) →
         ∀ {x y} (x≡y : x ≡ y) → P x≡y
  elim P r (refl′ x) = r x

  elim-refl : ∀ {A : Set} (P : {x y : A} → x ≡ y → Set)
              (r : ∀ x → P (refl x)) {x} →
              elim P r (refl x) ≡ r x
  elim-refl P r = refl _

private

  equality-with-J : Equality-with-J
  equality-with-J = record
    { _≡_       = _≡_
    ; refl      = refl
    ; elim      = elim
    ; elim-refl = elim-refl
    }

open Auxiliary _≡_ public
open Equality-with-J equality-with-J public
  using ( cong; cong-refl
        ; subst; subst-refl
        ; singleton-contractible
        )
open Equality-with-substitutivity-and-contractibility
       (Equivalent.to J⇔subst+contr ⟨$⟩ equality-with-J) public
  using ( sym; sym-refl
        ; trans; trans-refl-refl
        ; _≡⟨_⟩_; finally
        )

------------------------------------------------------------------------
-- More derived properties

-- Binary congruence.

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f {x} {y} {u} {v} x≡y u≡v =
  f x u  ≡⟨ cong (λ g → g u) (cong f x≡y) ⟩
  f y u  ≡⟨ cong (f y) u≡v ⟩∎
  f y v  ∎

-- The boolean true is not equal to false.

true≢false : ¬ true ≡ false
true≢false true≡false = subst (λ b → if b then ⊤ else ⊥) true≡false _

------------------------------------------------------------------------
-- Definitions related to the setoid machinery

-- The equality can be turned into a setoid.

setoid : Set → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = record
    { refl  = refl _
    ; sym   = sym
    ; trans = trans
    }
  }

-- Lifts ordinary functions to equality-preserving functions.

→-to-⟶ : {A B : Set} → (A → B) → setoid A ⟶ setoid B
→-to-⟶ f = record { _⟨$⟩_ = f; cong = cong f }

-- Some abbreviations: surjections and bijections.

infix 4 _↠_ _↔_

_↠_ : Set → Set → Set
A ↠ B = Surjection (setoid A) (setoid B)

_↔_ : Set → Set → Set
A ↔ B = Inverse (setoid A) (setoid B)

------------------------------------------------------------------------
-- The K rule and uniqueness of identity proofs

-- The K rule (without computational content).

K-rule : Set₁
K-rule = {A : Set} (P : {x : A} → x ≡ x → Set) →
         (∀ x → P (refl x)) →
         ∀ {x} (x≡x : x ≡ x) → P x≡x

-- Proof irrelevance (or maybe "data irrelevance", depending on what
-- the set is used for).

Proof-irrelevant : Set → Set
Proof-irrelevant A = (x y : A) → x ≡ y

-- Uniqueness of identity proofs (for a particular type).

Uniqueness-of-identity-proofs : Set → Set
Uniqueness-of-identity-proofs A =
  {x y : A} → Proof-irrelevant (x ≡ y)

-- The K rule is equivalent to uniqueness of identity proofs.

K⇔UIP : K-rule ⇔ (∀ {A} → Uniqueness-of-identity-proofs A)
K⇔UIP =
  equivalent
    (λ K {_} →
       elim (λ p → ∀ q → p ≡ q)
            (λ x → K (λ {x} p → refl x ≡ p) (λ x → refl (refl x))))
    (λ UIP P r {x} x≡x → subst P (UIP (refl x) x≡x) (r x))

------------------------------------------------------------------------
-- Relation to ordinary propositional equality with the K rule

-- I have marked the results below as private to ensure that I don't
-- use them in other parts of the development.

private

  -- As pointed out by Hofmann and Streicher in "The groupoid
  -- interpretation of type theory" the two equalities are isomorphic.

  ≡↔≡ : ∀ {A} {x y : A} → (x ≡ y) ↔ P._≡_ x y
  ≡↔≡ = record
    { to         = →-to-⟶ to
    ; from       = →-to-⟶ from
    ; inverse-of = record
      { right-inverse-of = λ _ → from $ P.proof-irrelevance _ _
      ; left-inverse-of  =
          elim (λ x≡y → from (to x≡y) ≡ x≡y)
               (λ x → from (to (refl x))  ≡⟨ cong from (subst-refl (P._≡_ x) P.refl) ⟩
                      from P.refl         ≡⟨ refl _ ⟩∎
                      refl x              ∎)
      }
    }
    where
    from : ∀ {A} {x y : A} → P._≡_ x y → x ≡ y
    from {x = x} x≡y = P.subst (_≡_ x) x≡y (refl x)

    to : ∀ {A} {x y : A} → x ≡ y → P._≡_ x y
    to {x = x} x≡y = subst (P._≡_ x) x≡y P.refl

  -- As a corollary _≡_ satisfies the K rule.

  K : K-rule
  K P p x≡x = subst P (Inverse.left-inverse-of ≡↔≡ x≡x) p′
    where
    P-K : {A : Set} (P : {x : A} → P._≡_ x x → Set) →
          (∀ x → P (P.refl {x = x})) →
          ∀ {x} (x≡x : P._≡_ x x) → P x≡x
    P-K P p P.refl = p _

    p′ : P (Inverse.from ≡↔≡ ⟨$⟩ (Inverse.to ≡↔≡ ⟨$⟩ x≡x))
    p′ = P-K (λ x≡x → P (Inverse.from ≡↔≡ ⟨$⟩ x≡x)) p
             (Inverse.to ≡↔≡ ⟨$⟩ x≡x)
