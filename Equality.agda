------------------------------------------------------------------------
-- Two equivalent axiomatisations of equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality where

open import Equivalence hiding (id; _∘_)
open import Prelude

------------------------------------------------------------------------
-- Reflexive relations

record Reflexive a : Set (lsuc a) where
  infix 4 _≡_
  field

    -- "Equality".

    _≡_ : {A : Set a} → A → A → Set a

    -- Reflexivity.

    refl : ∀ {A} (x : A) → x ≡ x

-- Some definitions.

module Reflexive′ (reflexive : ∀ ℓ → Reflexive ℓ) where

  private
    open module R {ℓ} = Reflexive (reflexive ℓ) public

  -- Non-equality.

  infix 4 _≢_

  _≢_ : ∀ {a} {A : Set a} → A → A → Set a
  x ≢ y = ¬ (x ≡ y)

  -- The property of having decidable equality.

  Decidable-equality : ∀ {ℓ} → Set ℓ → Set ℓ
  Decidable-equality A = Decidable (_≡_ {A = A})

  -- A type is contractible if it is inhabited and all elements are
  -- equal.

  Contractible : ∀ {ℓ} → Set ℓ → Set ℓ
  Contractible A = ∃ λ (x : A) → ∀ y → x ≡ y

  -- Singleton x is a set which contains all elements which are equal
  -- to x.

  Singleton : ∀ {a} → {A : Set a} → A → Set a
  Singleton x = ∃ λ y → y ≡ x

  -- Extensionality for functions of a certain type.

  Extensionality : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
  Extensionality A B =
    {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

  -- Proofs of extensionality which behave well when applied to
  -- reflexivity.

  Well-behaved-extensionality :
    ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
  Well-behaved-extensionality A B =
    ∃ λ (ext : Extensionality A B) →
      ∀ f → ext (λ x → refl (f x)) ≡ refl f

------------------------------------------------------------------------
-- Abstract definition of equality based on the J rule

-- Parametrised by a reflexive relation.

record Equality-with-J
         a p (reflexive : ∀ ℓ → Reflexive ℓ) :
         Set (lsuc (a ⊔ p)) where

  open Reflexive′ reflexive

  field

    -- The J rule.

    elim : {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
           (∀ x → P (refl x)) →
           ∀ {x y} (x≡y : x ≡ y) → P x≡y

    -- The usual computational behaviour of the J rule.

    elim-refl : ∀ {A : Set a} (P : {x y : A} → x ≡ y → Set p)
                (r : ∀ x → P (refl x)) {x} →
                elim P r (refl x) ≡ r x

-- Some derived properties.

module Equality-with-J′
  {reflexive : ∀ ℓ → Reflexive ℓ}
  (eq : ∀ {a p} → Equality-with-J a p reflexive)
  where

  private
    open Reflexive′ reflexive public
    open module E {a p} = Equality-with-J (eq {a} {p}) public

  -- Congruence.

  cong : ∀ {a b} {A : Set a} {B : Set b}
         (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f = elim (λ {u v} _ → f u ≡ f v) (λ x → refl (f x))

  abstract

    -- "Evaluation rule" for cong.

    cong-refl : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x : A} →
                cong f (refl x) ≡ refl (f x)
    cong-refl f = elim-refl (λ {u v} _ → f u ≡ f v) (refl ∘ f)

  -- Substitutivity.

  subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} →
          x ≡ y → P x → P y
  subst P = elim (λ {u v} _ → P u → P v) (λ x p → p)

  abstract

    -- "Evaluation rule" for subst.

    subst-refl : ∀ {a p} {A : Set a} (P : A → Set p) {x} (p : P x) →
                 subst P (refl x) p ≡ p
    subst-refl P p =
      cong (λ h → h p) $
        elim-refl (λ {u v} _ → P u → P v) (λ x p → p)

  -- Singleton types are contractible.

  private
    abstract

      irr : ∀ {a} {A : Set a} {x : A}
            (p : Singleton x) → (x , refl x) ≡ p
      irr p =
        elim (λ {u v} u≡v → _≡_ {A = Singleton v}
                                (v , refl v) (u , u≡v))
             (λ _ → refl _)
             (proj₂ p)

  singleton-contractible :
    ∀ {a} {A : Set a} (x : A) → Contractible (Singleton x)
  singleton-contractible x = ((x , refl x) , irr)

  abstract

    -- "Evaluation rule" for singleton-contractible.

    singleton-contractible-refl :
      ∀ {a} {A : Set a} (x : A) →
      proj₂ (singleton-contractible x) (x , refl x) ≡ refl (x , refl x)
    singleton-contractible-refl x =
      elim-refl (λ {u v} u≡v → _≡_ {A = Singleton v}
                                   (v , refl v) (u , u≡v))
                _

------------------------------------------------------------------------
-- Abstract definition of equality based on substitutivity and
-- contractibility of singleton types

record Equality-with-substitutivity-and-contractibility
         a p (reflexive : ∀ ℓ → Reflexive ℓ) :
         Set (lsuc (a ⊔ p)) where

  open Reflexive′ reflexive

  field

    -- Substitutivity.

    subst : {A : Set a} (P : A → Set p) {x y : A} → x ≡ y → P x → P y

    -- The usual computational behaviour of substitutivity.

    subst-refl : {A : Set a} (P : A → Set p) {x : A} (p : P x) →
                 subst P (refl x) p ≡ p

    -- Singleton types are contractible.

    singleton-contractible :
      {A : Set a} (x : A) → Contractible (Singleton x)

-- Some derived properties.

module Equality-with-substitutivity-and-contractibility′
  {reflexive : ∀ ℓ → Reflexive ℓ}
  (eq :  ∀ {a p} → Equality-with-substitutivity-and-contractibility
                     a p reflexive)
  where

  private
    open Reflexive′ reflexive public
    open module E {a p} =
      Equality-with-substitutivity-and-contractibility (eq {a} {p}) public
      hiding (singleton-contractible)
    open module E′ {a} =
      Equality-with-substitutivity-and-contractibility (eq {a} {a}) public
      using (singleton-contractible)

  abstract

    -- Congruence.

    cong : ∀ {a b} {A : Set a} {B : Set b}
           (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
    cong f {x} x≡y =
      subst (λ y → x ≡ y → f x ≡ f y) x≡y (λ _ → refl (f x)) x≡y

  -- Symmetry.

  sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
  sym {x = x} x≡y = subst (λ z → x ≡ z → z ≡ x) x≡y id x≡y

  abstract

    -- "Evaluation rule" for sym.

    sym-refl : ∀ {a} {A : Set a} {x : A} → sym (refl x) ≡ refl x
    sym-refl {x = x} =
      cong (λ f → f (refl x)) $
        subst-refl (λ z → x ≡ z → z ≡ x) id

  -- Transitivity.

  trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} = flip (subst (_≡_ x))

  abstract

    -- "Evaluation rule" for trans.

    trans-refl-refl : ∀ {a} {A : Set a} {x : A} →
                      trans (refl x) (refl x) ≡ refl x
    trans-refl-refl {x = x} = subst-refl (_≡_ x) (refl x)

  -- Equational reasoning combinators.

  infix  0 finally
  infixr 0 _≡⟨_⟩_

  _≡⟨_⟩_ : ∀ {a} {A : Set a} x {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  finally : ∀ {a} {A : Set a} (x y : A) → x ≡ y → x ≡ y
  finally _ _ x≡y = x≡y

  syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

  abstract

    -- The J rule.

    elim : ∀ {a p} {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
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

    trans-sym : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
                trans (sym x≡y) x≡y ≡ refl y
    trans-sym =
      elim (λ {x y} (x≡y : x ≡ y) → trans (sym x≡y) x≡y ≡ refl y)
           (λ x → trans (sym (refl x)) (refl x)  ≡⟨ cong (λ p → trans p (refl x)) sym-refl ⟩
                  trans (refl x) (refl x)        ≡⟨ trans-refl-refl ⟩∎
                  refl x                         ∎)

    -- "Evaluation rule" for elim.

    elim-refl : ∀ {a p} {A : Set a} (P : {x y : A} → x ≡ y → Set p)
                (p : ∀ x → P (refl x)) {x} →
                elim P p (refl x) ≡ p x
    elim-refl P p {x} =
      let lemma = proj₂ (singleton-contractible x) (x , refl x) in
      subst {A = Singleton x} (P ∘ proj₂) (trans (sym lemma) lemma) (p x)  ≡⟨ cong (λ q → subst {A = Singleton x} (P ∘ proj₂) q (p x))
                                                                                   (trans-sym lemma) ⟩
      subst {A = Singleton x} (P ∘ proj₂) (refl (x , refl x))       (p x)  ≡⟨ subst-refl {A = Singleton x} (P ∘ proj₂) (p x) ⟩∎
      p x                                                                  ∎

------------------------------------------------------------------------
-- The two abstract definitions are equivalent

J⇒subst+contr :
  ∀ {reflexive} →
  (∀ {a p} → Equality-with-J a p reflexive) →
  ∀ {a p} → Equality-with-substitutivity-and-contractibility
              a p reflexive
J⇒subst+contr eq = record
  { subst                  = subst
  ; subst-refl             = subst-refl
  ; singleton-contractible = singleton-contractible
  }
  where open Equality-with-J′ eq

subst+contr⇒J :
  ∀ {reflexive} →
  (∀ {a p} → Equality-with-substitutivity-and-contractibility
               a p reflexive) →
  ∀ {a p} → Equality-with-J a p reflexive
subst+contr⇒J eq = record
  { elim      = elim
  ; elim-refl = elim-refl
  }
  where open Equality-with-substitutivity-and-contractibility′ eq

------------------------------------------------------------------------
-- Some derived definitions and properties

module Derived-definitions-and-properties
  {reflexive}
  (eq : ∀ {a p} → Equality-with-J a p reflexive)
  where

  -- This module reexports most of the definitions and properties
  -- introduced above.

  private
    open Equality-with-J′ eq public
    open Equality-with-substitutivity-and-contractibility′
           (J⇒subst+contr eq) public
      using ( sym; sym-refl
            ; trans; trans-refl-refl
            ; _≡⟨_⟩_; finally
            )

  abstract

    -- A minor variant of Christine Paulin-Mohring's version of the J
    -- rule.
    --
    -- This definition is based on Martin Hofmann's (see the addendum
    -- to Thomas Streicher's Habilitation thesis). Note that it is
    -- also very similar to the definition of
    -- Equality-with-substitutivity-and-contractibility.elim.

    elim₁ : ∀ {a p} {A : Set a} {y : A} (P : ∀ {x} → x ≡ y → Set p) →
            P (refl y) →
            ∀ {x} (x≡y : x ≡ y) → P x≡y
    elim₁ {y = y} P p {x} x≡y =
      subst {A = Singleton y}
            (P ∘ proj₂)
            (proj₂ (singleton-contractible y) (x , x≡y))
            p

    -- "Evaluation rule" for elim₁.

    elim₁-refl : ∀ {a p} {A : Set a} {y : A}
                 (P : ∀ {x} → x ≡ y → Set p) (p : P (refl y)) →
                 elim₁ P p (refl y) ≡ p
    elim₁-refl {y = y} P p =
      subst {A = Singleton y} (P ∘ proj₂)
            (proj₂ (singleton-contractible y) (y , refl y)) p    ≡⟨ cong (λ q → subst {A = Singleton y} (P ∘ proj₂) q p)
                                                                         (singleton-contractible-refl y) ⟩
      subst {A = Singleton y} (P ∘ proj₂) (refl (y , refl y)) p  ≡⟨ subst-refl {A = Singleton y} (P ∘ proj₂) p ⟩∎
      p                                                          ∎

  -- A variant of singleton-contractible.

  Other-singleton : ∀ {a} {A : Set a} → A → Set a
  Other-singleton x = ∃ λ y → x ≡ y

  private
    abstract

      irr : ∀ {a} {A : Set a} {x : A}
            (p : Other-singleton x) → (x , refl x) ≡ p
      irr p =
        elim (λ {u v} u≡v → _≡_ {A = Other-singleton u}
                                (u , refl u) (v , u≡v))
             (λ _ → refl _)
             (proj₂ p)

  other-singleton-contractible :
    ∀ {a} {A : Set a} (x : A) → Contractible (Other-singleton x)
  other-singleton-contractible x = ((x , refl x) , irr)

  abstract

    -- "Evaluation rule" for other-singleton-contractible.

    other-singleton-contractible-refl :
      ∀ {a} {A : Set a} (x : A) →
      proj₂ (other-singleton-contractible x) (x , refl x) ≡
      refl (x , refl x)
    other-singleton-contractible-refl x =
      elim-refl (λ {u v} u≡v → _≡_ {A = Other-singleton u}
                                   (u , refl u) (v , u≡v))
                _

    -- Christine Paulin-Mohring's version of the J rule.

    elim¹ : ∀ {a p} {A : Set a} {x : A} (P : ∀ {y} → x ≡ y → Set p) →
            P (refl x) →
            ∀ {y} (x≡y : x ≡ y) → P x≡y
    elim¹ {x = x} P p {y} x≡y =
      subst {A = Other-singleton x}
            (P ∘ proj₂)
            (proj₂ (other-singleton-contractible x) (y , x≡y))
            p

    -- "Evaluation rule" for elim¹.

    elim¹-refl : ∀ {a p} {A : Set a} {x : A}
                 (P : ∀ {y} → x ≡ y → Set p) (p : P (refl x)) →
                 elim¹ P p (refl x) ≡ p
    elim¹-refl {x = x} P p =
      subst {A = Other-singleton x} (P ∘ proj₂)
            (proj₂ (other-singleton-contractible x) (x , refl x)) p    ≡⟨ cong (λ q → subst {A = Other-singleton x} (P ∘ proj₂) q p)
                                                                               (other-singleton-contractible-refl x) ⟩
      subst {A = Other-singleton x} (P ∘ proj₂) (refl (x , refl x)) p  ≡⟨ subst-refl {A = Other-singleton x} (P ∘ proj₂) p ⟩∎
      p                                                                ∎

  -- Binary congruence.

  cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B → C) {x y : A} {u v : B} →
          x ≡ y → u ≡ v → f x u ≡ f y v
  cong₂ f {x} {y} {u} {v} x≡y u≡v =
    f x u  ≡⟨ cong (flip f u) x≡y ⟩
    f y u  ≡⟨ cong (f y)      u≡v ⟩∎
    f y v  ∎

  -- The inspect idiom.

  data Inspect {a} {A : Set a} (x : A) : Set a where
    _with-≡_ : (y : A) (eq : x ≡ y) → Inspect x

  inspect : ∀ {a} {A : Set a} (x : A) → Inspect x
  inspect x = x with-≡ refl x

  -- The K rule (without computational content).

  K-rule : ∀ a p → Set (lsuc (a ⊔ p))
  K-rule a p = {A : Set a} (P : {x : A} → x ≡ x → Set p) →
               (∀ x → P (refl x)) →
               ∀ {x} (x≡x : x ≡ x) → P x≡x

  -- Proof irrelevance (or maybe "data irrelevance", depending on what
  -- the set is used for).

  Proof-irrelevant : ∀ {ℓ} → Set ℓ → Set ℓ
  Proof-irrelevant A = (x y : A) → x ≡ y

  -- Uniqueness of identity proofs (for a particular type).

  Uniqueness-of-identity-proofs : ∀ {ℓ} → Set ℓ → Set ℓ
  Uniqueness-of-identity-proofs A =
    {x y : A} → Proof-irrelevant (x ≡ y)

  -- The K rule is equivalent to uniqueness of identity proofs (at
  -- least for certain combinations of levels).

  K⇔UIP : ∀ {ℓ} →
          K-rule ℓ ℓ ⇔ ({A : Set ℓ} → Uniqueness-of-identity-proofs A)
  K⇔UIP = record
    { from = λ UIP P r {x} x≡x → subst P (UIP (refl x) x≡x) (r x)
    ; to   = λ K {_} →
        elim (λ p → ∀ q → p ≡ q)
             (λ x → K (λ {x} p → refl x ≡ p) (λ x → refl (refl x)))
    }
