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

  abstract

    -- "Evaluation rule" for cong₂.

    cong₂-refl : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                 (f : A → B → C) {x : A} {y : B} →
                 cong₂ f (refl x) (refl y) ≡ refl (f x y)
    cong₂-refl f {x} {y} =
      trans (cong (flip f y) (refl x)) (cong (f x) (refl y))  ≡⟨ cong₂ trans (cong-refl (flip f y)) (cong-refl (f x)) ⟩
      trans (refl (f x y)) (refl (f x y))                     ≡⟨ trans-refl-refl ⟩∎
      refl (f x y)                                            ∎

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

  abstract

    -- Universal extensionality at given levels works at lower levels
    -- as well.

    lower-extensionality :
      ∀ {a} â {b} b̂ →
      ({A : Set (a ⊔ â)} {B : A → Set (b ⊔ b̂)} → Extensionality A B) →
      ({A : Set  a     } {B : A → Set  b     } → Extensionality A B)
    lower-extensionality â b̂ ext f≡g =
      cong (λ h → lower ∘ h ∘ lift) $
        ext {A = ↑ â _} {B = ↑ b̂ ∘ _} (cong lift ∘ f≡g ∘ lower)

    lower-extensionality₂ :
      ∀ {a} {A : Set a} {b} b̂ →
      ({B : A → Set (b ⊔ b̂)} → Extensionality A B) →
      ({B : A → Set  b     } → Extensionality A B)
    lower-extensionality₂ b̂ ext f≡g =
      cong (λ h → lower ∘ h) $
        ext {B = ↑ b̂ ∘ _} (cong lift ∘ f≡g)

  -- A bunch of lemmas that can be used to rearrange equalities.

  abstract

    trans-reflʳ : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
                  trans x≡y (refl y) ≡ x≡y
    trans-reflʳ =
      elim (λ {u v} u≡v → trans u≡v (refl v) ≡ u≡v)
           (λ _ → trans-refl-refl)

    trans-reflˡ : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
                  trans (refl x) x≡y ≡ x≡y
    trans-reflˡ =
      elim (λ {u v} u≡v → trans (refl u) u≡v ≡ u≡v)
           (λ _ → trans-refl-refl)

    trans-assoc : ∀ {a} {A : Set a} {x y z u : A}
                  (x≡y : x ≡ y) (y≡z : y ≡ z) (z≡u : z ≡ u) →
                  trans (trans x≡y y≡z) z≡u ≡ trans x≡y (trans y≡z z≡u)
    trans-assoc =
      elim (λ x≡y → ∀ y≡z z≡u → trans (trans x≡y y≡z) z≡u ≡
                                trans x≡y (trans y≡z z≡u))
           (λ y y≡z z≡u →
              trans (trans (refl y) y≡z) z≡u ≡⟨ cong₂ trans (trans-reflˡ y≡z) (refl z≡u) ⟩
              trans y≡z z≡u                  ≡⟨ sym $ trans-reflˡ (trans y≡z z≡u) ⟩∎
              trans (refl y) (trans y≡z z≡u) ∎)

    sym-sym : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
              sym (sym x≡y) ≡ x≡y
    sym-sym = elim (λ {u v} u≡v → sym (sym u≡v) ≡ u≡v)
                   (λ x → sym (sym (refl x))  ≡⟨ cong sym (sym-refl {x = x}) ⟩
                          sym (refl x)        ≡⟨ sym-refl ⟩∎
                          refl x              ∎)

    sym-trans : ∀ {a} {A : Set a} {x y z : A}
                (x≡y : x ≡ y) (y≡z : y ≡ z) →
                sym (trans x≡y y≡z) ≡ trans (sym y≡z) (sym x≡y)
    sym-trans {a} =
      elim (λ x≡y → ∀ y≡z → sym (trans x≡y y≡z) ≡ trans (sym y≡z) (sym x≡y))
           (λ y y≡z → sym (trans (refl y) y≡z)        ≡⟨ cong sym (trans-reflˡ y≡z) ⟩
                      sym y≡z                         ≡⟨ sym $ trans-reflʳ (sym y≡z) ⟩
                      trans (sym y≡z) (refl y)        ≡⟨ cong {a = a} {b = a} (trans (sym y≡z)) (sym sym-refl)  ⟩∎
                      trans (sym y≡z) (sym (refl y))  ∎)

    trans-symˡ : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) →
                 trans (sym p) p ≡ refl y
    trans-symˡ =
      elim (λ p → trans (sym p) p ≡ refl _)
           (λ x → trans (sym (refl x)) (refl x)  ≡⟨ trans-reflʳ _ ⟩
                  sym (refl x)                   ≡⟨ sym-refl ⟩∎
                  refl x                         ∎)

    trans-symʳ : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) →
                 trans p (sym p) ≡ refl _
    trans-symʳ =
      elim (λ p → trans p (sym p) ≡ refl _)
           (λ x → trans (refl x) (sym (refl x))  ≡⟨ trans-reflˡ _ ⟩
                  sym (refl x)                   ≡⟨ sym-refl ⟩∎
                  refl x                         ∎)

    cong-trans : ∀ {a b} {A : Set a} {B : Set b} {x y z : A}
                 (f : A → B) (x≡y : x ≡ y) (y≡z : y ≡ z) →
                 cong f (trans x≡y y≡z) ≡ trans (cong f x≡y) (cong f y≡z)
    cong-trans f =
      elim (λ x≡y → ∀ y≡z → cong f (trans x≡y y≡z) ≡
                            trans (cong f x≡y) (cong f y≡z))
           (λ y y≡z → cong f (trans (refl y) y≡z)           ≡⟨ cong (cong f) (trans-reflˡ _) ⟩
                      cong f y≡z                            ≡⟨ sym $ trans-reflˡ (cong f y≡z) ⟩
                      trans (refl (f y)) (cong f y≡z)       ≡⟨ cong₂ trans (sym (cong-refl f {x = y})) (refl (cong f y≡z)) ⟩∎
                      trans (cong f (refl y)) (cong f y≡z)  ∎)

    cong-id : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
              x≡y ≡ cong id x≡y
    cong-id = elim (λ u≡v → u≡v ≡ cong id u≡v)
                   (λ x → refl x            ≡⟨ sym (cong-refl id {x = x}) ⟩∎
                          cong id (refl x)  ∎)

    cong-const : ∀ {a b} {A : Set a} {B : Set b} {x y : A} {z : B}
                 (x≡y : x ≡ y) →
                 cong (const z) x≡y ≡ refl z
    cong-const {z = z} =
      elim (λ u≡v → cong (const z) u≡v ≡ refl z)
           (λ x → cong (const z) (refl x)  ≡⟨ cong-refl (const z) ⟩∎
                  refl z                   ∎)

    cong-∘ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {x y : A}
             (f : B → C) (g : A → B) (x≡y : x ≡ y) →
             cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y
    cong-∘ f g = elim (λ x≡y → cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y)
                      (λ x → cong f (cong g (refl x))  ≡⟨ cong (cong f) (cong-refl g) ⟩
                             cong f (refl (g x))       ≡⟨ cong-refl f ⟩
                             refl (f (g x))            ≡⟨ sym (cong-refl (f ∘ g)) ⟩∎
                             cong (f ∘ g) (refl x)     ∎)

    cong-sym : ∀ {a b} {A : Set a} {B : Set b} {x y : A}
               (f : A → B) (x≡y : x ≡ y) →
               cong f (sym x≡y) ≡ sym (cong f x≡y)
    cong-sym f = elim (λ x≡y → cong f (sym x≡y) ≡ sym (cong f x≡y))
                      (λ x → cong f (sym (refl x))  ≡⟨ cong (cong f) sym-refl ⟩
                             cong f (refl x)        ≡⟨ cong-refl f ⟩
                             refl (f x)             ≡⟨ sym sym-refl ⟩
                             sym (refl (f x))       ≡⟨ cong sym $ sym (cong-refl f {x = x}) ⟩∎
                             sym (cong f (refl x))  ∎)

    subst-const : ∀ {a p} {A : Set a} {x₁ x₂ : A} {x₁≡x₂ : x₁ ≡ x₂}
                    {P : Set p} {p} →
                  subst (const P) x₁≡x₂ p ≡ p
    subst-const {P = P} {p} =
      elim¹ (λ x₁≡x₂ → subst (const P) x₁≡x₂ p ≡ p)
            (subst-refl (const P) _)
            _

    subst-∘ : ∀ {a b p} {A : Set a} {B : Set b} {x y : A}
              (P : B → Set p) (f : A → B) (x≡y : x ≡ y) {p : P (f x)} →
              subst (P ∘ f) x≡y p ≡ subst P (cong f x≡y) p
    subst-∘ P f x≡y =
      elim (λ {x y} x≡y → ∀ p → subst (P ∘ f) x≡y p ≡
                                subst P (cong f x≡y) p)
           (λ x p → subst (P ∘ f) (refl x) p     ≡⟨ subst-refl (P ∘ f) _ ⟩
                    p                            ≡⟨ sym $ subst-refl P _ ⟩
                    subst P (refl (f x)) p       ≡⟨ sym $ cong (λ eq → subst P eq p) (cong-refl f) ⟩∎
                    subst P (cong f (refl x)) p  ∎)
           x≡y _

    -- A fusion law for subst.

    subst-subst :
      ∀ {a p} {A : Set a} (P : A → Set p)
      {x y z : A} (x≡y : x ≡ y) (y≡z : y ≡ z) (p : P x) →
      subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
    subst-subst P x≡y y≡z p =
      elim (λ {x y} x≡y → ∀ {z} (y≡z : y ≡ z) p →
              subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p)
           (λ x y≡z p →
              subst P y≡z (subst P (refl x) p)  ≡⟨ cong (subst P y≡z) $ subst-refl P p ⟩
              subst P y≡z p                     ≡⟨ cong (λ q → subst P q p) (sym $ trans-reflˡ _) ⟩∎
              subst P (trans (refl x) y≡z) p    ∎)
           x≡y y≡z p

    -- Substitutivity and symmetry sometimes cancel each other out.

    subst-subst-sym :
      ∀ {a p} {A : Set a} (P : A → Set p) {x y : A}
      (x≡y : x ≡ y) (p : P y) →
      subst P x≡y (subst P (sym x≡y) p) ≡ p
    subst-subst-sym {A = A} P {y = y} x≡y p =
      subst P x≡y (subst P (sym x≡y) p)  ≡⟨ subst-subst P _ _ _ ⟩
      subst P (trans (sym x≡y) x≡y) p    ≡⟨ cong (λ q → subst P q p) (trans-symˡ x≡y) ⟩
      subst P (refl y) p                 ≡⟨ subst-refl P p ⟩∎
      p                                  ∎

    -- Some corollaries (used in
    -- Weak-equivalence.equality-equivalence-lemma).

    trans-[trans-sym] : ∀ {a} {A : Set a} {a b c : A} →
                        (a≡b : a ≡ b) (c≡b : c ≡ b) →
                        trans (trans a≡b (sym c≡b)) c≡b ≡ a≡b
    trans-[trans-sym] a≡b c≡b = subst-subst-sym (_≡_ _) c≡b a≡b

    trans-[trans]-sym : ∀ {a} {A : Set a} {a b c : A} →
                        (a≡b : a ≡ b) (b≡c : b ≡ c) →
                        trans (trans a≡b b≡c) (sym b≡c) ≡ a≡b
    trans-[trans]-sym a≡b b≡c =
      trans (trans a≡b b≡c)             (sym b≡c)  ≡⟨ sym $ cong (λ eq → trans (trans _ eq) (sym b≡c)) $ sym-sym _ ⟩
      trans (trans a≡b (sym (sym b≡c))) (sym b≡c)  ≡⟨ trans-[trans-sym] _ _ ⟩∎
      a≡b                                          ∎

  -- An equality between pairs can be proved using a pair of
  -- equalities.

  Σ-≡,≡→≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} →
            (p : proj₁ p₁ ≡ proj₁ p₂) →
            subst B p (proj₂ p₁) ≡ proj₂ p₂ →
            p₁ ≡ p₂
  Σ-≡,≡→≡ {B = B} p q = elim
    (λ {x₁ y₁} (p : x₁ ≡ y₁) → ∀ {x₂ y₂} →
       subst B p x₂ ≡ y₂ → (x₁ , x₂) ≡ (y₁ , y₂))
    (λ z₁ {x₂} {y₂} x₂≡y₂ → cong (_,_ z₁) (
       x₂                    ≡⟨ sym $ subst-refl B x₂ ⟩
       subst B (refl z₁) x₂  ≡⟨ x₂≡y₂ ⟩∎
       y₂                    ∎))
    p q

  abstract

    -- "Evaluation rules" for Σ-≡,≡→≡.

    Σ-≡,≡→≡-reflˡ :
      ∀ {a b} {A : Set a} {B : A → Set b} {x y₁ y₂} →
      (y₁≡y₂ : subst B (refl x) y₁ ≡ y₂) →
      Σ-≡,≡→≡ {B = B} (refl x) y₁≡y₂ ≡
      cong (_,_ x) (trans (sym $ subst-refl B y₁) y₁≡y₂)
    Σ-≡,≡→≡-reflˡ {B = B} y₁≡y₂ =
      cong (λ f → f y₁≡y₂) $
        elim-refl (λ {x₁ y₁} (p : x₁ ≡ y₁) → ∀ {x₂ y₂} →
                     subst B p x₂ ≡ y₂ → (x₁ , x₂) ≡ (y₁ , y₂))
                  _

    Σ-≡,≡→≡-refl-refl :
      ∀ {a b} {A : Set a} {B : A → Set b} {x y} →
      Σ-≡,≡→≡ {B = B} (refl x) (refl (subst B (refl x) y)) ≡
      cong (_,_ x) (sym (subst-refl B y))
    Σ-≡,≡→≡-refl-refl {B = B} {x} {y} =
      Σ-≡,≡→≡ (refl x) (refl _)                             ≡⟨ Σ-≡,≡→≡-reflˡ (refl _) ⟩
      cong (_,_ x) (trans (sym $ subst-refl B y) (refl _))  ≡⟨ cong (cong (_,_ x)) (trans-reflʳ _) ⟩∎
      cong (_,_ x) (sym (subst-refl B y))                   ∎

    -- A proof simplification rule for Σ-≡,≡→≡.

    proj₁-Σ-≡,≡→≡ :
      ∀ {a b} {A : Set a} {B : A → Set b} {x₁ x₂ y₁ y₂}
      (x₁≡x₂ : x₁ ≡ x₂) (y₁≡y₂ : subst B x₁≡x₂ y₁ ≡ y₂) →
      cong proj₁ (Σ-≡,≡→≡ {B = B} x₁≡x₂ y₁≡y₂) ≡ x₁≡x₂
    proj₁-Σ-≡,≡→≡ {B = B} {y₁ = y₁} x₁≡x₂ y₁≡y₂ = elim¹
      (λ x₁≡x₂ → ∀ {y₂} (y₁≡y₂ : subst B x₁≡x₂ y₁ ≡ y₂) →
         cong proj₁ (Σ-≡,≡→≡ x₁≡x₂ y₁≡y₂) ≡ x₁≡x₂)
      (λ y₁≡y₂ →
         cong proj₁ (Σ-≡,≡→≡ (refl _) y₁≡y₂)                              ≡⟨ cong (cong proj₁) $ Σ-≡,≡→≡-reflˡ y₁≡y₂ ⟩
         cong proj₁ (cong (_,_ _) (trans (sym $ subst-refl B y₁) y₁≡y₂))  ≡⟨ cong-∘ proj₁ (_,_ _) _ ⟩
         cong (const _) (trans (sym $ subst-refl B y₁) y₁≡y₂)             ≡⟨ cong-const _ ⟩∎
         refl _                                                           ∎)
      x₁≡x₂ y₁≡y₂

  -- A binary variant of subst.

  subst₂ : ∀ {a b p} {A : Set a} {B : A → Set b}
           (P : Σ A B → Set p) {x₁ x₂ y₁ y₂} →
           (x₁≡x₂ : x₁ ≡ x₂) → subst B x₁≡x₂ y₁ ≡ y₂ →
           P (x₁ , y₁) → P (x₂ , y₂)
  subst₂ P x₁≡x₂ y₁≡y₂ = subst P (Σ-≡,≡→≡ x₁≡x₂ y₁≡y₂)

  abstract

    -- "Evaluation rules" for subst₂.

    subst₂-refl-refl :
      ∀ {a b p} {A : Set a} {B : A → Set b}
      (P : Σ A B → Set p) {x y p} →
      subst₂ P (refl _) (refl _) p ≡
      subst (curry P x) (sym $ subst-refl B y) p
    subst₂-refl-refl {B = B} P {x} {y} {p} =
      subst P (Σ-≡,≡→≡ (refl x) (refl _)) p            ≡⟨ cong (λ eq₁ → subst P eq₁ p) Σ-≡,≡→≡-refl-refl ⟩
      subst P (cong (_,_ x) (sym (subst-refl B y))) p  ≡⟨ sym $ subst-∘ P (_,_ x) _ ⟩∎
      subst (curry P x) (sym $ subst-refl B y) p       ∎

    -- The subst function can be "pushed" inside pairs.

    push-subst-pair :
      ∀ {a b c} {A : Set a} {y z : A} {y≡z : y ≡ z}
      (B : A → Set b) (C : Σ A B → Set c) {p} →
      subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
      (subst B y≡z (proj₁ p) , subst₂ C y≡z (refl _) (proj₂ p))
    push-subst-pair {y≡z = y≡z} B C {p} = elim¹
      (λ y≡z →
         subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
         (subst B y≡z (proj₁ p) , subst₂ C y≡z (refl _) (proj₂ p)))
      (subst (λ x → Σ (B x) (curry C x)) (refl _) p  ≡⟨ subst-refl (λ x → Σ (B x) (curry C x)) _ ⟩
       p                                             ≡⟨ Σ-≡,≡→≡ (sym (subst-refl B _)) (sym (subst₂-refl-refl C)) ⟩∎
       (subst B (refl _) (proj₁ p) ,
        subst₂ C (refl _) (refl _) (proj₂ p))        ∎)
      y≡z

    -- A corollary of push-subst-pair.

    push-subst-pair′ :
      ∀ {a b c} {A : Set a} {y z : A} {y≡z : y ≡ z}
      (B : A → Set b) (C : Σ A B → Set c) {p p₁} →
      (p₁≡p₁ : subst B y≡z (proj₁ p) ≡ p₁) →
      subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
      (p₁ , subst₂ C y≡z p₁≡p₁ (proj₂ p))
    push-subst-pair′ {y≡z = y≡z} B C {p} =
      elim¹ (λ {p₁} p₁≡p₁ →
               subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
               (p₁ , subst₂ C y≡z p₁≡p₁ (proj₂ p)))
            (push-subst-pair B C)

    -- A proof simplification rule for subst₂.

    subst₂-proj₁ :
      ∀ {a b p} {A : Set a} {B : A → Set b} {x₁ x₂ y₁ y₂}
        {x₁≡x₂ : x₁ ≡ x₂} {y₁≡y₂ : subst B x₁≡x₂ y₁ ≡ y₂}
      (P : A → Set p) {p} →
      subst₂ {B = B} (P ∘ proj₁) x₁≡x₂ y₁≡y₂ p ≡ subst P x₁≡x₂ p
    subst₂-proj₁ {x₁≡x₂ = x₁≡x₂} {y₁≡y₂} P {p} =
      subst₂ (P ∘ proj₁) x₁≡x₂ y₁≡y₂ p              ≡⟨ subst-∘ P proj₁ _ ⟩
      subst P (cong proj₁ (Σ-≡,≡→≡ x₁≡x₂ y₁≡y₂)) p  ≡⟨ cong (λ eq → subst P eq p) (proj₁-Σ-≡,≡→≡ _ _) ⟩∎
      subst P x₁≡x₂ p                               ∎

    -- If f z evaluates to z for a decidable set of values which
    -- includes x and y, do we have
    --
    --   cong f x≡y ≡ x≡y
    --
    -- for any x≡y : x ≡ y? The equation above is not well-typed if f
    -- is a variable, but the approximation below can be proved.

    cong-roughly-id : ∀ {a} {A : Set a} (f : A → A) (p : A → Bool) {x y : A}
                      (x≡y : x ≡ y) (px : T (p x)) (py : T (p y))
                      (f≡id : ∀ z → T (p z) → f z ≡ z) →
                      cong f x≡y ≡
                      trans (f≡id x px) (trans x≡y $ sym (f≡id y py))
    cong-roughly-id {A = A} f p =
      elim (λ {x y} x≡y →
              (px : T (p x)) (py : T (p y))
              (f≡id : ∀ z → T (p z) → f z ≡ z) →
              cong f x≡y ≡
              trans (f≡id x px) (trans x≡y $ sym (f≡id y py)))
           (λ x px px′ f≡id → helper x (p x) px px′ (f≡id x))
      where
      helper :
        (x : A) (b : Bool) (px px′ : T b)
        (f≡id : T b → f x ≡ x) →
        cong f (refl x) ≡
        trans (f≡id px) (trans (refl x) $ sym (f≡id px′))
      helper x false px _ f≡id = ⊥-elim px
      helper x true  _  _ f≡id =
        cong f (refl x)                                 ≡⟨ cong-refl f ⟩
        refl (f x)                                      ≡⟨ sym $ trans-symʳ _ ⟩
        trans (f≡id _) (sym (f≡id _))                   ≡⟨ cong (trans (f≡id _)) $ sym $ trans-reflˡ _ ⟩∎
        trans (f≡id _) (trans (refl x) $ sym (f≡id _))  ∎
