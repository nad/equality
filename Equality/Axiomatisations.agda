------------------------------------------------------------------------
-- Two equivalent axiomatisations of equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality.Axiomatisations where

open import Equivalence hiding (id; _∘_)
open import Prelude

------------------------------------------------------------------------
-- Reflexive relations

record Reflexive : Set₁ where
  infix 4 _≡_
  field

    -- "Equality".

    _≡_ : {A : Set} → A → A → Set

    -- Reflexivity.

    refl : {A : Set} (x : A) → x ≡ x

  ----------------------------------------------------------------------
  -- Some definitions

  -- A type is contractible if it is inhabited and all elements are
  -- equal.

  Contractible : Set → Set
  Contractible A = ∃ λ (x : A) → ∀ y → x ≡ y

  -- Singleton x is a set which contains all elements which are equal
  -- to x.

  Singleton : {A : Set} → A → Set
  Singleton x = ∃ λ y → y ≡ x

  -- Extensionality for functions of a certain type.

  Extensionality : (A : Set) → (B : A → Set) → Set
  Extensionality A B =
    {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

  -- Proofs of extensionality which behave well when applied to
  -- reflexivity.

  Well-behaved-extensionality : (A : Set) → (B : A → Set) → Set
  Well-behaved-extensionality A B =
    ∃ λ (ext : Extensionality A B) →
      ∀ f → ext (refl ∘ f) ≡ refl f

------------------------------------------------------------------------
-- Abstract definition of equality based on the J rule

-- Parametrised on a reflexive relation.

record Equality-with-J (reflexive : Reflexive) : Set₁ where

  open Reflexive reflexive

  field

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

  abstract

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

  -- Singleton types are contractible.

  private
    abstract

      irr : ∀ {A} {x : A} (p : Singleton x) → (x , refl x) ≡ p
      irr p =
        elim (λ {u v} u≡v → _≡_ {A = Singleton v}
                                (v , refl v) (u , u≡v))
             (λ _ → refl _)
             (proj₂ p)

  singleton-contractible : ∀ {A} (x : A) → Contractible (Singleton x)
  singleton-contractible x = ((x , refl x) , irr)

  abstract

    -- "Evaluation rule" for singleton-contractible.

    singleton-contractible-refl :
      ∀ {A} (x : A) →
      proj₂ (singleton-contractible x) (x , refl x) ≡ refl (x , refl x)
    singleton-contractible-refl x =
      elim-refl (λ {u v} u≡v → _≡_ {A = Singleton v}
                                   (v , refl v) (u , u≡v))
                _

------------------------------------------------------------------------
-- Abstract definition of equality based on substitutivity and
-- contractibility of singleton types

record Equality-with-substitutivity-and-contractibility
         (reflexive : Reflexive) : Set₁ where

  open Reflexive reflexive

  field

    -- Substitutivity.

    subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y

    -- The usual computational behaviour of substitutivity.

    subst-refl : {A : Set} (P : A → Set) {x : A} (p : P x) →
                 subst P (refl x) p ≡ p

    -- Singleton types are contractible.

    singleton-contractible :
      ∀ {A} (x : A) → Contractible (Singleton x)

  ----------------------------------------------------------------------
  -- Some derived properties

  abstract

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

  abstract

    -- The J rule.

    elim : {A : Set} (P : {x y : A} → x ≡ y → Set) →
           (∀ x → P (refl x)) →
           ∀ {x y} (x≡y : x ≡ y) → P x≡y
    elim P p {x} {y} x≡y =
      let lemma = proj₂ (singleton-contractible y) in
      subst {A = Singleton y}
            (P ∘ proj₂)
            ((y , refl y)                      ≡⟨ sym (lemma (y , refl y)) ⟩
             proj₁ (singleton-contractible y)  ≡⟨ lemma (x , x≡y) ⟩∎
             (x , x≡y)                         ∎)
            (p y)

    -- Transitivity and symmetry sometimes cancel each other out.

    trans-symˡ : {A : Set} {x y : A} (x≡y : x ≡ y) →
                 trans (sym x≡y) x≡y ≡ refl y
    trans-symˡ =
      elim (λ {x y} (x≡y : x ≡ y) → trans (sym x≡y) x≡y ≡ refl y)
           (λ x → trans (sym (refl x)) (refl x)  ≡⟨ cong (λ p → trans p (refl x)) sym-refl ⟩
                  trans (refl x) (refl x)        ≡⟨ trans-refl-refl ⟩∎
                  refl x                         ∎)

    trans-symʳ : {A : Set} {x y : A} (x≡y : x ≡ y) →
                 trans x≡y (sym x≡y) ≡ refl x
    trans-symʳ =
      elim (λ {x y} (x≡y : x ≡ y) → trans x≡y (sym x≡y) ≡ refl x)
           (λ x → trans (refl x) (sym (refl x))  ≡⟨ cong (trans (refl x)) sym-refl ⟩
                  trans (refl x) (refl x)        ≡⟨ trans-refl-refl ⟩∎
                  refl x                         ∎)

    -- "Evaluation rule" for elim.

    elim-refl : ∀ {A : Set} (P : {x y : A} → x ≡ y → Set)
                (p : ∀ x → P (refl x)) {x} →
                elim P p (refl x) ≡ p x
    elim-refl P p {x} =
      subst {A = Singleton x} (P ∘ proj₂) (trans (sym lemma) lemma) (p x)  ≡⟨ cong (λ q → subst (P ∘ proj₂) q (p x)) (trans-symˡ lemma) ⟩
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

------------------------------------------------------------------------
-- Some derived definitions and properties

module Derived-definitions-and-properties
  {reflexive}
  (Eq : Equality-with-J reflexive)
  where

  -- This module reexports most of the definitions and properties
  -- introduced above.

  open Reflexive reflexive public
  open Equality-with-J Eq public
  open Equality-with-substitutivity-and-contractibility
         (_⇔_.to J⇔subst+contr Eq) public
    using ( sym; sym-refl
          ; trans; trans-refl-refl
          ; _≡⟨_⟩_; finally
          ; trans-symˡ; trans-symʳ
          )

  abstract

    -- A minor variant of Christine Paulin-Mohring's version of the J
    -- rule.
    --
    -- This definition is based on Martin Hofmann's (see the addendum
    -- of Thomas Streicher's Habilitation thesis). Note that it is
    -- also very similar to the definition of
    -- Equality-with-substitutivity-and-contractibility.elim.

    elim₁ : {A : Set} {y : A} (P : ∀ {x} → x ≡ y → Set) →
            P (refl y) →
            ∀ {x} (x≡y : x ≡ y) → P x≡y
    elim₁ {y = y} P p {x} x≡y =
      subst {A = Singleton y}
            (P ∘ proj₂)
            (proj₂ (singleton-contractible y) (x , x≡y))
            p

    -- "Evaluation rule" for elim₁.

    elim₁-refl : {A : Set} {y : A} (P : ∀ {x} → x ≡ y → Set)
                 (p : P (refl y)) →
                 elim₁ P p (refl y) ≡ p
    elim₁-refl {y = y} P p =
      subst {A = Singleton y} (P ∘ proj₂)
            (proj₂ (singleton-contractible y) (y , refl y)) p    ≡⟨ cong (λ q → subst (P ∘ proj₂) q p)
                                                                         (singleton-contractible-refl y) ⟩
      subst {A = Singleton y} (P ∘ proj₂) (refl (y , refl y)) p  ≡⟨ subst-refl {A = Singleton y} (P ∘ proj₂) p ⟩∎
      p                                                          ∎

  -- Binary congruence.

  cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
          x ≡ y → u ≡ v → f x u ≡ f y v
  cong₂ f {x} {y} {u} {v} x≡y u≡v =
    f x u  ≡⟨ cong (flip f u) x≡y ⟩
    f y u  ≡⟨ cong (f y)      u≡v ⟩∎
    f y v  ∎

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
