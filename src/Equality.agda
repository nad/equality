------------------------------------------------------------------------
-- Two logically equivalent axiomatisations of equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality where

open import Logical-equivalence hiding (id; _∘_)
open import Prelude

------------------------------------------------------------------------
-- Reflexive relations

record Reflexive-relation a : Set (lsuc a) where
  infix 4 _≡_
  field

    -- "Equality".

    _≡_ : {A : Set a} → A → A → Set a

    -- Reflexivity.

    refl : ∀ {A} (x : A) → x ≡ x

-- Some definitions.

module Reflexive-relation′
         (reflexive : ∀ ℓ → Reflexive-relation ℓ) where

  private
    open module R {ℓ} = Reflexive-relation (reflexive ℓ) public

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

  Extensionality′ : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
  Extensionality′ A B =
    {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

  -- Extensionality for functions at certain levels.

  Extensionality : (a b : Level) → Set (lsuc (a ⊔ b))
  Extensionality a b =
    {A : Set a} → {B : A → Set b} → Extensionality′ A B

  -- Proofs of extensionality which behave well when applied to
  -- reflexivity.

  Well-behaved-extensionality :
    ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
  Well-behaved-extensionality A B =
    ∃ λ (ext : Extensionality′ A B) →
      ∀ f → ext (λ x → refl (f x)) ≡ refl f

------------------------------------------------------------------------
-- Abstract definition of equality based on the J rule

-- Parametrised by a reflexive relation.

record Equality-with-J
         a p (reflexive : ∀ ℓ → Reflexive-relation ℓ) :
         Set (lsuc (a ⊔ p)) where

  open Reflexive-relation′ reflexive

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
  {reflexive : ∀ ℓ → Reflexive-relation ℓ}
  (eq : ∀ {a p} → Equality-with-J a p reflexive)
  where

  private
    open Reflexive-relation′ reflexive public
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

  -- "Evaluation rules" for subst.

  subst-refl≡id : ∀ {a p} {A : Set a} (P : A → Set p) {x} →
                  subst P (refl x) ≡ id
  subst-refl≡id P = elim-refl (λ {u v} _ → P u → P v) (λ x p → p)

  subst-refl : ∀ {a p} {A : Set a} (P : A → Set p) {x} (p : P x) →
               subst P (refl x) p ≡ p
  subst-refl P p = cong (_$ p) (subst-refl≡id P)

  -- Singleton types are contractible.

  private

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
         a p (reflexive : ∀ ℓ → Reflexive-relation ℓ) :
         Set (lsuc (a ⊔ p)) where

  open Reflexive-relation′ reflexive

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
  {reflexive : ∀ ℓ → Reflexive-relation ℓ}
  (eq :  ∀ {a p} → Equality-with-substitutivity-and-contractibility
                     a p reflexive)
  where

  private
    open Reflexive-relation′ reflexive public
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

  infix  -1 finally _∎
  infixr -2 step-≡ _≡⟨⟩_

  _∎ : ∀ {a} {A : Set a} (x : A) → x ≡ x
  x ∎ = refl x

  -- It can be easier for Agda to type-check typical equational
  -- reasoning chains if the transitivity proof gets the equality
  -- arguments in the opposite order, because then the y argument is
  -- (perhaps more) known once the proof of x ≡ y is type-checked.
  --
  -- The idea behind this optimisation came up in discussions with Ulf
  -- Norell.

  step-≡ : ∀ {a} {A : Set a} x {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ = flip trans

  syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

  _≡⟨⟩_ : ∀ {a} {A : Set a} x {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

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
-- The two abstract definitions are logically equivalent

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

  open Equality-with-J′ eq public
  open Equality-with-substitutivity-and-contractibility′
         (J⇒subst+contr eq) public
    using ( sym; sym-refl
          ; trans; trans-refl-refl
          ; _∎; step-≡; _≡⟨⟩_; finally
          )

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

  abstract

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

  abstract

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

  -- A dependent variant of cong.

  dependent-cong :
    ∀ {a b} {A : Set a} {B : A → Set b}
    (f : (x : A) → B x) {x y} (x≡y : x ≡ y) →
    subst B x≡y (f x) ≡ f y
  dependent-cong {B = B} f = elim
    (λ {x y} (x≡y : x ≡ y) → subst B x≡y (f x) ≡ f y)
    (λ x → subst B (refl x) (f x)  ≡⟨ subst-refl _ _ ⟩∎
           f x                     ∎)

  abstract

    -- "Evaluation rule" for dependent-cong.

    dependent-cong-refl :
      ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) {x} →
      dependent-cong f (refl x) ≡ subst-refl B (f x)
    dependent-cong-refl {B = B} f {x} =
      elim (λ {x y} (x≡y : x ≡ y) → subst B x≡y (f x) ≡ f y)
           (λ x → subst-refl B (f x))
           (refl x)                                           ≡⟨ elim-refl _ _ ⟩∎
      subst-refl B (f x)                                      ∎

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

  inspect : ∀ {a} {A : Set a} (x : A) → Other-singleton x
  inspect x = x , refl x

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

  -- The K rule is logically equivalent to uniqueness of identity
  -- proofs (at least for certain combinations of levels).

  K⇔UIP : ∀ {ℓ} →
          K-rule ℓ ℓ ⇔ ({A : Set ℓ} → Uniqueness-of-identity-proofs A)
  K⇔UIP = record
    { from = λ UIP P r {x} x≡x → subst P (UIP (refl x) x≡x) (r x)
    ; to   = λ K {_} →
        elim (λ p → ∀ q → p ≡ q)
             (λ x → K (λ {x} p → refl x ≡ p) (λ x → refl (refl x)))
    }

  abstract

    -- Extensionality at given levels works at lower levels as well.

    lower-extensionality :
      ∀ {a} â {b} b̂ →
      Extensionality (a ⊔ â) (b ⊔ b̂) → Extensionality a b
    lower-extensionality â b̂ ext f≡g =
      cong (λ h → lower ∘ h ∘ lift) $
        ext {A = ↑ â _} {B = ↑ b̂ ∘ _} (cong lift ∘ f≡g ∘ lower)

    lower-extensionality₂ :
      ∀ {a} {A : Set a} {b} b̂ →
      ({B : A → Set (b ⊔ b̂)} → Extensionality′ A B) →
      ({B : A → Set  b     } → Extensionality′ A B)
    lower-extensionality₂ b̂ ext f≡g =
      cong (λ h → lower ∘ h) $
        ext {B = ↑ b̂ ∘ _} (cong lift ∘ f≡g)

    -- Extensionality for explicit function types works for implicit
    -- function types as well.

    implicit-extensionality :
      ∀ {a b} {A : Set a} {B : A → Set b} →
      Extensionality′ A B →
      {f g : {x : A} → B x} →
      (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g
    implicit-extensionality ext f≡g =
      cong (λ f {x} → f x) $ ext f≡g

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

    cong-proj₁-cong₂-, :
      ∀ {a b} {A : Set a} {B : Set b} {x y : A} {u v : B}
      (x≡y : x ≡ y) (u≡v : u ≡ v) →
      cong proj₁ (cong₂ _,_ x≡y u≡v) ≡ x≡y
    cong-proj₁-cong₂-, {x = x} {y} {u} {v} x≡y u≡v =
      cong proj₁ (trans (cong (flip _,_ u) x≡y) (cong (_,_ y) u≡v))  ≡⟨ cong-trans proj₁ _ _ ⟩

      trans (cong proj₁ (cong (flip _,_ u) x≡y))
            (cong proj₁ (cong (_,_ y) u≡v))                          ≡⟨ cong₂ trans (cong-∘ proj₁ (flip _,_ u) x≡y) (cong-∘ proj₁ (_,_ y) u≡v) ⟩

      trans (cong id x≡y) (cong (const y) u≡v)                       ≡⟨ cong₂ trans (sym $ cong-id x≡y) (cong-const u≡v) ⟩

      trans x≡y (refl y)                                             ≡⟨ trans-reflʳ x≡y ⟩∎

      x≡y                                                            ∎

    cong-proj₂-cong₂-, :
      ∀ {a b} {A : Set a} {B : Set b} {x y : A} {u v : B}
      (x≡y : x ≡ y) (u≡v : u ≡ v) →
      cong proj₂ (cong₂ _,_ x≡y u≡v) ≡ u≡v
    cong-proj₂-cong₂-, {x = x} {y} {u} {v} x≡y u≡v =
      cong proj₂ (trans (cong (flip _,_ u) x≡y) (cong (_,_ y) u≡v))  ≡⟨ cong-trans proj₂ _ _ ⟩

      trans (cong proj₂ (cong (flip _,_ u) x≡y))
            (cong proj₂ (cong (_,_ y) u≡v))                          ≡⟨ cong₂ trans (cong-∘ proj₂ (flip _,_ u) x≡y) (cong-∘ proj₂ (_,_ y) u≡v) ⟩

      trans (cong (const u) x≡y) (cong id u≡v)                       ≡⟨ cong₂ trans (cong-const x≡y) (sym $ cong-id u≡v) ⟩

      trans (refl u) u≡v                                             ≡⟨ trans-reflˡ u≡v ⟩∎

      u≡v                                                            ∎

    cong-sym : ∀ {a b} {A : Set a} {B : Set b} {x y : A}
               (f : A → B) (x≡y : x ≡ y) →
               cong f (sym x≡y) ≡ sym (cong f x≡y)
    cong-sym f = elim (λ x≡y → cong f (sym x≡y) ≡ sym (cong f x≡y))
                      (λ x → cong f (sym (refl x))  ≡⟨ cong (cong f) sym-refl ⟩
                             cong f (refl x)        ≡⟨ cong-refl f ⟩
                             refl (f x)             ≡⟨ sym sym-refl ⟩
                             sym (refl (f x))       ≡⟨ cong sym $ sym (cong-refl f {x = x}) ⟩∎
                             sym (cong f (refl x))  ∎)

    cong₂-reflˡ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                  (f : A → B → C) {x : A} {u v : B} {u≡v : u ≡ v} →
                  cong₂ f (refl x) u≡v ≡ cong (f x) u≡v
    cong₂-reflˡ f {x} {u} {u≡v = u≡v} =
      trans (cong (flip f u) (refl x)) (cong (f x) u≡v)  ≡⟨ cong₂ trans (cong-refl (flip f u)) (refl _) ⟩
      trans (refl (f x u)) (cong (f x) u≡v)              ≡⟨ trans-reflˡ _ ⟩∎
      cong (f x) u≡v                                     ∎

    cong₂-reflʳ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                  (f : A → B → C) {x y : A} {u : B} {x≡y : x ≡ y} →
                  cong₂ f x≡y (refl u) ≡ cong (flip f u) x≡y
    cong₂-reflʳ f {y = y} {u} {x≡y} =
      trans (cong (flip f u) x≡y) (cong (f y) (refl u))  ≡⟨ cong (trans _) (cong-refl (f y)) ⟩
      trans (cong (flip f u) x≡y) (refl (f y u))         ≡⟨ trans-reflʳ _ ⟩∎
      cong (flip f u) x≡y                                ∎

    cong₂-cong-cong :
      ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        {x₁ x₂} {eq : x₁ ≡ x₂}
      (f : A → B) (g : A → C) (h : B → C → D) →
      cong₂ h (cong f eq) (cong g eq) ≡
      cong (λ x → h (f x) (g x)) eq
    cong₂-cong-cong f g h = elim¹
      (λ eq → cong₂ h (cong f eq) (cong g eq) ≡
              cong (λ x → h (f x) (g x)) eq)
      (cong₂ h (cong f (refl _)) (cong g (refl _))  ≡⟨ cong₂ (cong₂ h) (cong-refl f) (cong-refl g) ⟩
       cong₂ h (refl _) (refl _)                    ≡⟨ cong₂-refl h ⟩
       refl _                                       ≡⟨ sym $ cong-refl (λ x → h (f x) (g x)) ⟩∎
       cong (λ x → h (f x) (g x)) (refl _)          ∎)
      _

    cong-≡id :
      ∀ {a b} {A : Set a} (B : A → Set b) {x} {y : B x} {f : B x → B x}
      (f≡id : f ≡ id) →
      cong (λ g → g (f y)) f≡id ≡
      cong (λ g → f (g y)) f≡id
    cong-≡id B = elim₁
      (λ {f} p → cong (λ g → g (f _)) p ≡ cong (λ g → f (g _)) p)
      (refl _)

    elim-∘ :
      ∀ {a p} {A : Set a} {x y : A}
      (P Q : ∀ {x y} → x ≡ y → Set p)
      (f : ∀ {x y} {x≡y : x ≡ y} → P x≡y → Q x≡y)
      (r : ∀ x → P (refl x)) {x≡y : x ≡ y} →
      f (elim P r x≡y) ≡ elim Q (f ∘ r) x≡y
    elim-∘ {x = x} P Q f r {x≡y} = elim¹
      (λ x≡y → f (elim P r x≡y) ≡
               elim Q (f ∘ r) x≡y)
      (f (elim P r (refl x))    ≡⟨ cong f $ elim-refl P _ ⟩
       f (r x)                  ≡⟨ sym $ elim-refl Q _ ⟩∎
       elim Q (f ∘ r) (refl x)  ∎)
      x≡y

    elim-cong :
      ∀ {a b p} {A : Set a} {B : Set b} {x y : A}
      (P : B → B → Set p) (f : A → B)
      (r : ∀ x → P x x) {x≡y : x ≡ y} →
      elim (λ {x y} _ → P x y) r (cong f x≡y) ≡
      elim (λ {x y} _ → P (f x) (f y)) (r ∘ f) x≡y
    elim-cong {x = x} P f r {x≡y} = elim¹
      (λ x≡y → elim (λ {x y} _ → P x y) r (cong f x≡y) ≡
               elim (λ {x y} _ → P (f x) (f y)) (r ∘ f) x≡y)
      (elim (λ {x y} _ → P x y) r (cong f (refl x))       ≡⟨ cong (elim (λ {x y} _ → P x y) _) $ cong-refl f ⟩
       elim (λ {x y} _ → P x y) r (refl (f x))            ≡⟨ elim-refl (λ {x y} _ → P x y) _ ⟩
       r (f x)                                            ≡⟨ sym $ elim-refl (λ {x y} _ → P (f x) (f y)) _ ⟩∎
       elim (λ {x y} _ → P (f x) (f y)) (r ∘ f) (refl x)  ∎)
      x≡y

  subst-const : ∀ {a p} {A : Set a} {x₁ x₂ : A} (x₁≡x₂ : x₁ ≡ x₂)
                  {P : Set p} {p} →
                subst (const P) x₁≡x₂ p ≡ p
  subst-const x₁≡x₂ {P = P} {p} =
    elim¹ (λ x₁≡x₂ → subst (const P) x₁≡x₂ p ≡ p)
          (subst-refl (const P) _)
          x₁≡x₂

  abstract

    subst-∘ : ∀ {a b p} {A : Set a} {B : Set b} {x y : A}
              (P : B → Set p) (f : A → B) (x≡y : x ≡ y) {p : P (f x)} →
              subst (P ∘ f) x≡y p ≡ subst P (cong f x≡y) p
    subst-∘ P f _ =
      sym $ cong (λ g → g _) $ elim-cong (λ u v → P u → P v) f _

    subst-↑ : ∀ {a p ℓ} {A : Set a} {x y}
              (P : A → Set p) {p : ↑ ℓ (P x)} {x≡y : x ≡ y} →
              subst (↑ ℓ ∘ P) x≡y p ≡ lift (subst P x≡y (lower p))
    subst-↑ {ℓ = ℓ} P {p} = elim¹
      (λ x≡y → subst (↑ ℓ ∘ P) x≡y p ≡ lift (subst P x≡y (lower p)))
      (subst (↑ ℓ ∘ P) (refl _) p         ≡⟨ subst-refl (↑ ℓ ∘ P) _ ⟩
       p                                  ≡⟨ cong lift $ sym $ subst-refl P _ ⟩∎
       lift (subst P (refl _) (lower p))  ∎)
      _

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

    -- "Computation rules" for subst-subst.

    subst-subst-reflˡ :
      ∀ {a p} {A : Set a} (P : A → Set p) {x y p} {x≡y : x ≡ y} →
      subst-subst P (refl x) x≡y p ≡
      cong₂ (flip (subst P)) (subst-refl P p) (sym $ trans-reflˡ x≡y)
    subst-subst-reflˡ P =
      cong (λ f → f _ _) $
        elim-refl (λ {x y} x≡y → ∀ {z} (y≡z : y ≡ z) p →
                     subst P y≡z (subst P x≡y p) ≡ _)
                  _

    subst-subst-refl-refl :
      ∀ {a p} {A : Set a} (P : A → Set p) {x p} →
      subst-subst P (refl x) (refl x) p ≡
      cong₂ (flip (subst P)) (subst-refl P p) (sym trans-refl-refl)
    subst-subst-refl-refl P {x} {p} =
      subst-subst P (refl x) (refl x) p                              ≡⟨ subst-subst-reflˡ _ ⟩

      cong₂ (flip (subst P)) (subst-refl P p)
                             (sym $ trans-reflˡ (refl x))            ≡⟨ cong (cong₂ (flip (subst P)) (subst-refl P p) ∘ sym) $
                                                                             elim-refl _ _ ⟩∎
      cong₂ (flip (subst P)) (subst-refl P p) (sym trans-refl-refl)  ∎

    -- The combinator trans is defined in terms of subst. It could
    -- have been defined in another way.

    subst-trans :
      ∀ {a} {A : Set a} {x y z : A} (x≡y : x ≡ y) {y≡z : y ≡ z} →
      subst (λ x → x ≡ z) (sym x≡y) y≡z ≡ trans x≡y y≡z
    subst-trans {y = y} {z} x≡y {y≡z} =
      elim₁ (λ x≡y → subst (λ x → x ≡ z) (sym x≡y) y≡z ≡
                     trans x≡y y≡z)
            (subst (λ x → x ≡ z) (sym (refl y)) y≡z  ≡⟨ cong (λ eq → subst (λ x → x ≡ z) eq y≡z) sym-refl ⟩
             subst (λ x → x ≡ z) (refl y) y≡z        ≡⟨ subst-refl (λ x → x ≡ z) y≡z ⟩
             y≡z                                     ≡⟨ sym $ trans-reflˡ y≡z ⟩∎
             trans (refl y) y≡z                      ∎)
            x≡y

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

    -- Some corollaries and variants.

    trans-[trans-sym]- : ∀ {a} {A : Set a} {a b c : A} →
                         (a≡b : a ≡ b) (c≡b : c ≡ b) →
                         trans (trans a≡b (sym c≡b)) c≡b ≡ a≡b
    trans-[trans-sym]- a≡b c≡b = subst-subst-sym (_≡_ _) c≡b a≡b

    trans-[trans]-sym : ∀ {a} {A : Set a} {a b c : A} →
                        (a≡b : a ≡ b) (b≡c : b ≡ c) →
                        trans (trans a≡b b≡c) (sym b≡c) ≡ a≡b
    trans-[trans]-sym a≡b b≡c =
      trans (trans a≡b b≡c)             (sym b≡c)  ≡⟨ sym $ cong (λ eq → trans (trans _ eq) (sym b≡c)) $ sym-sym _ ⟩
      trans (trans a≡b (sym (sym b≡c))) (sym b≡c)  ≡⟨ trans-[trans-sym]- _ _ ⟩∎
      a≡b                                          ∎

    trans--[trans-sym] : ∀ {a} {A : Set a} {a b c : A} →
                         (b≡a : b ≡ a) (b≡c : b ≡ c) →
                         trans b≡a (trans (sym b≡a) b≡c) ≡ b≡c
    trans--[trans-sym] b≡a b≡c =
      trans b≡a (trans (sym b≡a) b≡c)  ≡⟨ sym $ trans-assoc _ _ _ ⟩
      trans (trans b≡a (sym b≡a)) b≡c  ≡⟨ cong (flip trans _) $ trans-symʳ _ ⟩
      trans (refl _) b≡c               ≡⟨ trans-reflˡ _ ⟩∎
      b≡c                              ∎

    trans-sym-[trans] : ∀ {a} {A : Set a} {a b c : A} →
                        (a≡b : a ≡ b) (b≡c : b ≡ c) →
                        trans (sym a≡b) (trans a≡b b≡c) ≡ b≡c
    trans-sym-[trans] a≡b b≡c =
      trans (sym a≡b) (trans a≡b b≡c)              ≡⟨ cong (λ p → trans (sym _) (trans p _)) $ sym $ sym-sym _ ⟩
      trans (sym a≡b) (trans (sym (sym a≡b)) b≡c)  ≡⟨ trans--[trans-sym] _ _ ⟩∎
      b≡c                                          ∎

    -- The lemmas subst-refl and subst-const can cancel each other
    -- out.

    subst-refl-subst-const :
      ∀ {a p} {A : Set a} {x : A} {P : Set p} {p} →
      trans (sym $ subst-refl (λ _ → P) p) (subst-const (refl x)) ≡
      refl p
    subst-refl-subst-const {x = x} {P} {p} =
      trans (sym $ subst-refl (λ _ → P) p)
            (elim¹ (λ eq → subst (λ _ → P) eq p ≡ p)
                   (subst-refl (λ _ → P) _) _)        ≡⟨ cong (trans _) (elim¹-refl (λ eq → subst (λ _ → P) eq p ≡ p) _) ⟩
      trans (sym $ subst-refl (λ _ → P) p)
            (subst-refl (λ _ → P) _)                  ≡⟨ trans-symˡ _ ⟩∎
      refl _                                          ∎

    -- In non-dependent cases one can express dependent-cong using
    -- subst-const and cong.
    --
    -- This is (similar to) Lemma 2.3.8 in the HoTT book.

    dependent-cong-subst-const-cong :
      ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} (x≡y : x ≡ y) →
      dependent-cong f x≡y ≡
      (subst (const B) x≡y (f x)  ≡⟨ subst-const x≡y ⟩
       f x                        ≡⟨ cong f x≡y ⟩∎
       f y                        ∎)
    dependent-cong-subst-const-cong f = elim
      (λ {x y} x≡y → dependent-cong f x≡y ≡
                     trans (subst-const x≡y) (cong f x≡y))
      (λ x →
        dependent-cong f (refl x)                        ≡⟨ dependent-cong-refl f ⟩
        subst-refl (const _) (f x)                       ≡⟨ sym $ trans-reflʳ _ ⟩
        trans (subst-refl (const _) (f x)) (refl (f x))  ≡⟨ cong₂ trans
                                                                  (sym $ elim¹-refl _ _)
                                                                  (sym $ cong-refl f) ⟩∎
        trans (subst-const (refl x)) (cong f (refl x))   ∎)

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

  -- The uncurried form of Σ-≡,≡→≡ has an inverse, Σ-≡,≡←≡. (For a
  -- proof, see Bijection.Σ-≡,≡↔≡.)

  Σ-≡,≡←≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} →
            p₁ ≡ p₂ →
            ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
              subst B p (proj₂ p₁) ≡ proj₂ p₂
  Σ-≡,≡←≡ {A = A} {B} = elim
    (λ {p₁ p₂ : Σ A B} _ →
       ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) → subst B p (proj₂ p₁) ≡ proj₂ p₂)
    (λ p → refl _ , subst-refl B _)

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

    Σ-≡,≡→≡-refl-subst-refl :
      ∀ {a b} {A : Set a} {B : A → Set b} {x y} →
      Σ-≡,≡→≡ (refl x) (subst-refl B y) ≡ refl (x , y)
    Σ-≡,≡→≡-refl-subst-refl {B = B} {x} {y} =
      Σ-≡,≡→≡ (refl x) (subst-refl B y)                             ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩
      cong (_,_ x) (trans (sym $ subst-refl B y) (subst-refl B y))  ≡⟨ cong (cong _) (trans-symˡ _) ⟩
      cong (_,_ x) (refl y)                                         ≡⟨ cong-refl _ ⟩∎
      refl (x , y)                                                  ∎

    -- "Evaluation rule" for Σ-≡,≡←≡.

    Σ-≡,≡←≡-refl :
      ∀ {a b} {A : Set a} {B : A → Set b} {p : Σ A B} →
      Σ-≡,≡←≡ (refl p) ≡ (refl (proj₁ p) , subst-refl B (proj₂ p))
    Σ-≡,≡←≡-refl {A = A} {B} = elim-refl
      (λ {p₁ p₂ : Σ A B} _ →
         ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
           subst B p (proj₂ p₁) ≡ proj₂ p₂)
      _

    -- Proof transformation rules for Σ-≡,≡→≡.

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

    Σ-≡,≡→≡-cong :
      ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B}
      {q₁ q₂ : proj₁ p₁ ≡ proj₁ p₂}
      (q₁≡q₂ : q₁ ≡ q₂)
      {r₁ : subst B q₁ (proj₂ p₁) ≡ proj₂ p₂}
      {r₂ : subst B q₂ (proj₂ p₁) ≡ proj₂ p₂}
      (r₁≡r₂ : (subst B q₂ (proj₂ p₁)  ≡⟨ cong (flip (subst B) _) (sym q₁≡q₂) ⟩
                subst B q₁ (proj₂ p₁)  ≡⟨ r₁ ⟩∎
                proj₂ p₂               ∎)
                 ≡
               r₂) →
      Σ-≡,≡→≡ q₁ r₁ ≡ Σ-≡,≡→≡ q₂ r₂
    Σ-≡,≡→≡-cong {B = B} = elim
      (λ {q₁ q₂} q₁≡q₂ →
         ∀ {r₁ r₂}
         (r₁≡r₂ : trans (cong (flip (subst B) _) (sym q₁≡q₂)) r₁ ≡ r₂) →
         Σ-≡,≡→≡ q₁ r₁ ≡ Σ-≡,≡→≡ q₂ r₂)
      (λ q {r₁ r₂} r₁≡r₂ → cong (Σ-≡,≡→≡ q) (
         r₁                                                 ≡⟨ sym $ trans-reflˡ _ ⟩
         trans (refl (subst B q _)) r₁                      ≡⟨ cong (flip trans _) $ sym $ cong-refl _ ⟩
         trans (cong (flip (subst B) _) (refl q)) r₁        ≡⟨ cong (λ e → trans (cong (flip (subst B) _) e) _) $ sym sym-refl ⟩
         trans (cong (flip (subst B) _) (sym (refl q))) r₁  ≡⟨ r₁≡r₂ ⟩∎
         r₂                                                 ∎))

    trans-Σ-≡,≡→≡ :
      ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ p₃ : Σ A B} →
      (q₁₂ : proj₁ p₁ ≡ proj₁ p₂) (q₂₃ : proj₁ p₂ ≡ proj₁ p₃)
      (r₁₂ : subst B q₁₂ (proj₂ p₁) ≡ proj₂ p₂)
      (r₂₃ : subst B q₂₃ (proj₂ p₂) ≡ proj₂ p₃) →
      trans (Σ-≡,≡→≡ q₁₂ r₁₂) (Σ-≡,≡→≡ q₂₃ r₂₃) ≡
      Σ-≡,≡→≡ (trans q₁₂ q₂₃)
              (subst B (trans q₁₂ q₂₃) (proj₂ p₁)    ≡⟨ sym $ subst-subst _ _ _ _ ⟩
               subst B q₂₃ (subst B q₁₂ (proj₂ p₁))  ≡⟨ cong (subst _ _) r₁₂ ⟩
               subst B q₂₃ (proj₂ p₂)                ≡⟨ r₂₃ ⟩∎
               proj₂ p₃                              ∎)
    trans-Σ-≡,≡→≡ {B = B} q₁₂ q₂₃ r₁₂ r₂₃ = elim
      (λ {p₂₁ p₃₁} q₂₃ → ∀ {p₁₁} (q₁₂ : p₁₁ ≡ p₂₁)
         {p₁₂ p₂₂} (r₁₂ : subst B q₁₂ p₁₂ ≡ p₂₂)
         {p₃₂} (r₂₃ : subst B q₂₃ p₂₂ ≡ p₃₂) →
         trans (Σ-≡,≡→≡ q₁₂ r₁₂) (Σ-≡,≡→≡ q₂₃ r₂₃) ≡
         Σ-≡,≡→≡ (trans q₁₂ q₂₃)
                 (trans (sym $ subst-subst _ _ _ _)
                        (trans (cong (subst _ _) r₁₂) r₂₃)))
      (λ x → elim₁
         (λ q₁₂ →
          ∀ {p₁₂ p₂₂} (r₁₂ : subst B q₁₂ p₁₂ ≡ p₂₂)
            {p₃₂} (r₂₃ : subst B (refl _) p₂₂ ≡ p₃₂) →
            trans (Σ-≡,≡→≡ q₁₂ r₁₂) (Σ-≡,≡→≡ (refl _) r₂₃) ≡
            Σ-≡,≡→≡ (trans q₁₂ (refl _))
                    (trans (sym $ subst-subst _ _ _ _)
                           (trans (cong (subst _ _) r₁₂) r₂₃)))
         (λ {y} → elim¹
            (λ {p₂₂} r₁₂ →
             ∀ {p₃₂} (r₂₃ : subst B (refl _) p₂₂ ≡ p₃₂) →
               trans (Σ-≡,≡→≡ (refl _) r₁₂) (Σ-≡,≡→≡ (refl _) r₂₃) ≡
               Σ-≡,≡→≡ (trans (refl _) (refl _))
                       (trans (sym $ subst-subst _ _ _ _)
                              (trans (cong (subst _ _) r₁₂) r₂₃)))
            (elim¹
              (λ r₂₃ →
                 trans (Σ-≡,≡→≡ (refl _) (refl _))
                       (Σ-≡,≡→≡ (refl _) r₂₃) ≡
                 Σ-≡,≡→≡ (trans (refl _) (refl _))
                         (trans (sym $ subst-subst _ _ _ _)
                                (trans (cong (subst _ _) (refl _))
                                       r₂₃)))
              (let lemma₁ =
                     sym (subst-refl B (subst B (refl x) y))          ≡⟨⟩

                     sym (cong (λ f → f (subst B (refl x) y))
                               (subst-refl≡id B))                     ≡⟨ cong sym $ cong-≡id B _ ⟩

                     sym (cong (λ f → subst B (refl x) (f y))
                               (subst-refl≡id B))                     ≡⟨ cong sym $ sym $ cong-∘ _ _ _ ⟩∎

                     sym (cong (subst B (refl x)) (subst-refl B y))   ∎

                   lemma₂ =
                     sym (cong (subst B _) (subst-refl B _))          ≡⟨ sym $ trans-sym-[trans] _ _ ⟩

                     trans (sym $ cong (flip (subst B) _)
                                       trans-refl-refl)
                           (trans (cong (flip (subst B) _)
                                        trans-refl-refl)
                                  (sym (cong (subst B _)
                                             (subst-refl B _))))      ≡⟨ cong (flip trans _) $ sym $ cong-sym _ _ ⟩∎

                     trans (cong (flip (subst B) _)
                                 (sym trans-refl-refl))
                           (trans (cong (flip (subst B) _)
                                        trans-refl-refl)
                                  (sym (cong (subst B _)
                                             (subst-refl B _))))      ∎

                   lemma₃ =
                     trans (cong (flip (subst B) _) trans-refl-refl)
                           (sym (cong (subst B _) (subst-refl B _)))     ≡⟨ cong (λ e → trans (cong (flip (subst B) _) e)
                                                                                              (sym $ cong (subst B _) (subst-refl B _))) $
                                                                                 sym $ sym-sym _ ⟩
                     trans (cong (flip (subst B) _)
                                 (sym $ sym trans-refl-refl))
                           (sym (cong (subst B _) (subst-refl B _)))     ≡⟨ cong (flip trans _) $ cong-sym _ _ ⟩

                     trans (sym (cong (flip (subst B) _)
                                      (sym trans-refl-refl)))
                           (sym (cong (subst B _) (subst-refl B _)))     ≡⟨ sym $ sym-trans _ _ ⟩

                     sym (trans (cong (subst B _) (subst-refl B _))
                                (cong (flip (subst B) _)
                                      (sym trans-refl-refl)))            ≡⟨⟩

                     sym (cong₂ (flip (subst B)) (subst-refl B _)
                                                 (sym trans-refl-refl))  ≡⟨ cong sym $ sym $ subst-subst-refl-refl _ ⟩

                     sym (subst-subst _ _ _ _)                           ≡⟨ sym $ trans-reflʳ _ ⟩

                     trans (sym $ subst-subst _ _ _ _) (refl _)          ≡⟨ cong (trans (sym $ subst-subst _ _ _ _)) $ sym trans-refl-refl ⟩

                     trans (sym $ subst-subst _ _ _ _)
                           (trans (refl _) (refl _))                     ≡⟨ cong (λ x → trans (sym $ subst-subst _ _ _ _) (trans x (refl _))) $
                                                                                 sym $ cong-refl _ ⟩∎
                     trans (sym $ subst-subst _ _ _ _)
                           (trans (cong (subst _ _) (refl _)) (refl _))  ∎
               in
               trans (Σ-≡,≡→≡ (refl _) (refl _))
                     (Σ-≡,≡→≡ (refl _) (refl _))                          ≡⟨ cong₂ trans Σ-≡,≡→≡-refl-refl Σ-≡,≡→≡-refl-refl ⟩

               trans (cong (_ ,_) (sym (subst-refl B _)))
                     (cong (_ ,_) (sym (subst-refl B _)))                 ≡⟨ sym $ cong-trans _ _ _ ⟩

               cong (_ ,_) (trans (sym (subst-refl B _))
                                  (sym (subst-refl B _)))                 ≡⟨ cong (cong (_ ,_) ∘ trans _) lemma₁ ⟩

               cong (_ ,_)
                    (trans (sym (subst-refl B _))
                           (sym (cong (subst B _) (subst-refl B _))))     ≡⟨ sym $ Σ-≡,≡→≡-reflˡ _ ⟩

               Σ-≡,≡→≡ (refl _)
                       (sym (cong (subst B _) (subst-refl B _)))          ≡⟨ cong (Σ-≡,≡→≡ _) lemma₂ ⟩

               Σ-≡,≡→≡ (refl _)
                 (trans (cong (flip (subst B) _) (sym trans-refl-refl))
                    (trans (cong (flip (subst B) _) trans-refl-refl)
                       (sym (cong (subst B _) (subst-refl B _)))))        ≡⟨ sym $ Σ-≡,≡→≡-cong _ (refl _) ⟩

               Σ-≡,≡→≡ (trans (refl _) (refl _))
                       (trans (cong (flip (subst B) _) trans-refl-refl)
                              (sym (cong (subst B _) (subst-refl B _))))  ≡⟨ cong (Σ-≡,≡→≡ (trans (refl _) (refl _))) lemma₃ ⟩∎

               Σ-≡,≡→≡ (trans (refl _) (refl _))
                       (trans (sym $ subst-subst _ _ _ _)
                              (trans (cong (subst _ _) (refl _))
                                     (refl _)))                           ∎))))
      q₂₃ q₁₂ r₁₂ r₂₃

    Σ-≡,≡→≡-subst-const :
      ∀ {a b} {A : Set a} {B : Set b} {p₁ p₂ : A × B} →
      (p : proj₁ p₁ ≡ proj₁ p₂) (q : proj₂ p₁ ≡ proj₂ p₂) →
      Σ-≡,≡→≡ p (trans (subst-const p) q) ≡ cong₂ _,_ p q
    Σ-≡,≡→≡-subst-const {B = B} {_ , y₁} {_ , y₂} p q = elim
      (λ {x₁ y₁} (p : x₁ ≡ y₁) →
         Σ-≡,≡→≡ p (trans (subst-const _) q) ≡ cong₂ _,_ p q)
      (λ x →
         let lemma =
               trans (sym $ subst-refl (λ _ → B) y₁)
                     (trans (subst-const _) q)               ≡⟨ sym $ trans-assoc _ _ _ ⟩
               trans (trans (sym $ subst-refl (λ _ → B) y₁)
                            (subst-const _))
                     q                                       ≡⟨ cong₂ trans subst-refl-subst-const (refl _) ⟩
               trans (refl y₁) q                             ≡⟨ trans-reflˡ _ ⟩∎
               q                                             ∎ in

         Σ-≡,≡→≡ (refl x) (trans (subst-const _) q)           ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩
         cong (_,_ x) (trans (sym $ subst-refl (λ _ → B) y₁)
                             (trans (subst-const _) q))       ≡⟨ cong (cong (_,_ x)) lemma ⟩
         cong (_,_ x) q                                       ≡⟨ sym $ cong₂-reflˡ _,_ ⟩∎
         cong₂ _,_ (refl x) q                                 ∎)
      p

    -- Proof simplification rule for Σ-≡,≡←≡.

    proj₁-Σ-≡,≡←≡ :
      ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B}
      (p₁≡p₂ : p₁ ≡ p₂) →
      proj₁ (Σ-≡,≡←≡ p₁≡p₂) ≡ cong proj₁ p₁≡p₂
    proj₁-Σ-≡,≡←≡ = elim
      (λ p₁≡p₂ → proj₁ (Σ-≡,≡←≡ p₁≡p₂) ≡ cong proj₁ p₁≡p₂)
      (λ p →
         proj₁ (Σ-≡,≡←≡ (refl p))  ≡⟨ cong proj₁ $ Σ-≡,≡←≡-refl ⟩
         refl (proj₁ p)            ≡⟨ sym $ cong-refl proj₁ ⟩∎
         cong proj₁ (refl p)       ∎)

  -- A binary variant of subst.

  subst₂ : ∀ {a b p} {A : Set a} {B : A → Set b}
           (P : Σ A B → Set p) {x₁ x₂ y₁ y₂} →
           (x₁≡x₂ : x₁ ≡ x₂) → subst B x₁≡x₂ y₁ ≡ y₂ →
           P (x₁ , y₁) → P (x₂ , y₂)
  subst₂ P x₁≡x₂ y₁≡y₂ = subst P (Σ-≡,≡→≡ x₁≡x₂ y₁≡y₂)

  abstract

    -- "Evaluation rule" for subst₂.

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

    -- The subst function can be "pushed" inside non-dependent pairs.

    push-subst-, :
      ∀ {a b c} {A : Set a} {y z : A} {y≡z : y ≡ z}
      (B : A → Set b) (C : A → Set c) {p} →
      subst (λ x → B x × C x) y≡z p ≡
      (subst B y≡z (proj₁ p) , subst C y≡z (proj₂ p))
    push-subst-, {y≡z = y≡z} B C {x , y} =
      subst (λ x → B x × C x) y≡z (x , y)                           ≡⟨ push-subst-pair B (C ∘ proj₁) ⟩
      (subst B y≡z x , subst (C ∘ proj₁) (Σ-≡,≡→≡ y≡z (refl _)) y)  ≡⟨ cong (_,_ _) $ subst₂-proj₁ C ⟩∎
      (subst B y≡z x , subst C y≡z y)                               ∎

    -- The subst function can be "pushed" inside inj₁ and inj₂.

    push-subst-inj₁ :
      ∀ {a b c} {A : Set a} {y z : A} {y≡z : y ≡ z}
      (B : A → Set b) (C : A → Set c) {x} →
      subst (λ x → B x ⊎ C x) y≡z (inj₁ x) ≡ inj₁ (subst B y≡z x)
    push-subst-inj₁ {y≡z = y≡z} B C {x} = elim¹
      (λ y≡z → subst (λ x → B x ⊎ C x) y≡z (inj₁ x) ≡
               inj₁ (subst B y≡z x))
      (subst (λ x → B x ⊎ C x) (refl _) (inj₁ x)  ≡⟨ subst-refl (λ x → B x ⊎ C x) _ ⟩
       inj₁ x                                     ≡⟨ cong inj₁ $ sym $ subst-refl B _ ⟩∎
       inj₁ (subst B (refl _) x)                  ∎)
      y≡z

    push-subst-inj₂ :
      ∀ {a b c} {A : Set a} {y z : A} {y≡z : y ≡ z}
      (B : A → Set b) (C : A → Set c) {x} →
      subst (λ x → B x ⊎ C x) y≡z (inj₂ x) ≡ inj₂ (subst C y≡z x)
    push-subst-inj₂ {y≡z = y≡z} B C {x} = elim¹
      (λ y≡z → subst (λ x → B x ⊎ C x) y≡z (inj₂ x) ≡
               inj₂ (subst C y≡z x))
      (subst (λ x → B x ⊎ C x) (refl _) (inj₂ x)  ≡⟨ subst-refl (λ x → B x ⊎ C x) _ ⟩
       inj₂ x                                     ≡⟨ cong inj₂ $ sym $ subst-refl C _ ⟩∎
       inj₂ (subst C (refl _) x)                  ∎)
      y≡z

    -- The subst function can be "pushed" inside applications.

    push-subst-application :
      ∀ {a b c} {A : Set a} {x : A} {B : Set b} {y₁ y₂ : B}
      (y₁≡y₂ : y₁ ≡ y₂) (C : A → B → Set c) {f : (x : A) → C x y₁} →
      subst (C x) y₁≡y₂ (f x) ≡
      subst (λ y → (x : A) → C x y) y₁≡y₂ f x
    push-subst-application {x = x} y₁≡y₂ C {f} = elim¹
      (λ y₁≡y₂ → subst (C x) y₁≡y₂ (f x) ≡
                 subst (λ y → ∀ x → C x y) y₁≡y₂ f x)
      (subst (C x) (refl _) (f x)              ≡⟨ subst-refl (C x) _ ⟩
       f x                                     ≡⟨ cong (λ g → g x) $ sym $ subst-refl (λ y → ∀ x → C x y) _ ⟩∎
       subst (λ y → ∀ x → C x y) (refl _) f x  ∎)
      y₁≡y₂

    push-subst-implicit-application :
      ∀ {a b c} {A : Set a} {x : A} {B : Set b} {y₁ y₂ : B}
      (y₁≡y₂ : y₁ ≡ y₂) (C : A → B → Set c) {f : {x : A} → C x y₁} →
      subst (C x) y₁≡y₂ (f {x = x}) ≡
      subst (λ y → {x : A} → C x y) y₁≡y₂ f {x = x}
    push-subst-implicit-application {x = x} y₁≡y₂ C {f} =
      elim¹
        (λ y₁≡y₂ → subst (C x) y₁≡y₂ f ≡
                   subst (λ y → ∀ {x} → C x y) y₁≡y₂ f)
        (subst (C x) (refl _) f                  ≡⟨ subst-refl (C x) _ ⟩
         f                                       ≡⟨ cong (λ g → g {x = x}) $ sym $ subst-refl (λ y → ∀ {x} → C x y) _ ⟩∎
         subst (λ y → ∀ {x} → C x y) (refl _) f  ∎)
        y₁≡y₂

    -- Yet another equality rearrangement lemma.

    subst-→-domain :
      ∀ {a b c} {A : Set a} {x y : A}
      (B : A → Set b) {C : Set c} {f : B x → C}
      (x≡y : x ≡ y) →
      subst (λ x → B x → C) x≡y f ≡ f ∘ subst B (sym x≡y)
    subst-→-domain B {C} x≡y = elim
      (λ {x y} x≡y → (f : B x → C) →
                     subst (λ x → B x → C) x≡y f ≡
                     f ∘ subst B (sym x≡y))
      (λ x f →
         subst (λ x → B x → C) (refl x) f  ≡⟨ subst-refl (λ x → B x → _) _ ⟩
         f                                 ≡⟨ cong (f ∘_) $ sym $ subst-refl≡id _ ⟩
         f ∘ subst B (refl x)              ≡⟨ cong (λ p → f ∘ subst B p) $ sym sym-refl ⟩∎
         f ∘ subst B (sym (refl x))        ∎)
      x≡y _

    -- The following lemma is Proposition 2 from "Generalizations of
    -- Hedberg's Theorem" by Kraus, Escardó, Coquand and Altenkirch.

    subst-in-terms-of-trans-and-cong :
      ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y}
        {x≡y : x ≡ y} {fx≡gx : f x ≡ g x} →
      subst (λ z → f z ≡ g z) x≡y fx≡gx ≡
      trans (sym (cong f x≡y)) (trans fx≡gx (cong g x≡y))
    subst-in-terms-of-trans-and-cong {f = f} {g} = elim
      (λ {x y} x≡y →
           (fx≡gx : f x ≡ g x) →
           subst (λ z → f z ≡ g z) x≡y fx≡gx ≡
           trans (sym (cong f x≡y)) (trans fx≡gx (cong g x≡y)))
      (λ x fx≡gx →
           subst (λ z → f z ≡ g z) (refl x) fx≡gx                         ≡⟨ subst-refl _ _ ⟩
           fx≡gx                                                          ≡⟨ sym $ trans-reflˡ _ ⟩
           trans (refl (f x)) fx≡gx                                       ≡⟨ sym $ cong₂ trans sym-refl (trans-reflʳ _)  ⟩
           trans (sym (refl (f x))) (trans fx≡gx (refl (g x)))            ≡⟨ sym $ cong₂ (λ p q → trans (sym p) (trans _ q))
                                                                                         (cong-refl _) (cong-refl _) ⟩∎
           trans (sym (cong f (refl x))) (trans fx≡gx (cong g (refl x)))  ∎ )
      _
      _

    -- Some rearrangement lemmas for equalities between equalities.

    [trans≡]≡[≡trans-symʳ] :
      ∀ {a} {A : Set a} {a₁ a₂ a₃ : A}
      (p₁₂ : a₁ ≡ a₂) (p₁₃ : a₁ ≡ a₃) (p₂₃ : a₂ ≡ a₃) →
      (trans p₁₂ p₂₃ ≡ p₁₃)
        ≡
      (p₁₂ ≡ trans p₁₃ (sym p₂₃))
    [trans≡]≡[≡trans-symʳ] p₁₂ p₁₃ p₂₃ = elim
      (λ {a₂ a₃} p₂₃ →
         ∀ {a₁} (p₁₂ : a₁ ≡ a₂) (p₁₃ : a₁ ≡ a₃) →
         (trans p₁₂ p₂₃ ≡ p₁₃)
           ≡
         (p₁₂ ≡ trans p₁₃ (sym p₂₃)))
      (λ a₂₃ p₁₂ p₁₃ →
         trans p₁₂ (refl a₂₃) ≡ p₁₃        ≡⟨ cong₂ _≡_ (trans-reflʳ _) (sym $ trans-reflʳ _) ⟩
         p₁₂ ≡ trans p₁₃ (refl a₂₃)        ≡⟨ cong ((_ ≡_) ∘ trans _) (sym sym-refl) ⟩∎
         p₁₂ ≡ trans p₁₃ (sym (refl a₂₃))  ∎)
      p₂₃ p₁₂ p₁₃

    [trans≡]≡[≡trans-symˡ] :
      ∀ {a} {A : Set a} {a₁ a₂ a₃ : A}
      (p₁₂ : a₁ ≡ a₂) (p₁₃ : a₁ ≡ a₃) (p₂₃ : a₂ ≡ a₃) →
      (trans p₁₂ p₂₃ ≡ p₁₃)
        ≡
      (p₂₃ ≡ trans (sym p₁₂) p₁₃)
    [trans≡]≡[≡trans-symˡ] p₁₂ = elim
      (λ {a₁ a₂} p₁₂ →
         ∀ {a₃} (p₁₃ : a₁ ≡ a₃) (p₂₃ : a₂ ≡ a₃) →
         (trans p₁₂ p₂₃ ≡ p₁₃)
           ≡
         (p₂₃ ≡ trans (sym p₁₂) p₁₃))
      (λ a₁₂ p₁₃ p₂₃ →
         trans (refl a₁₂) p₂₃ ≡ p₁₃        ≡⟨ cong₂ _≡_ (trans-reflˡ _) (sym $ trans-reflˡ _) ⟩
         p₂₃ ≡ trans (refl a₁₂) p₁₃        ≡⟨ cong ((_ ≡_) ∘ flip trans _) (sym sym-refl) ⟩∎
         p₂₃ ≡ trans (sym (refl a₁₂)) p₁₃  ∎)
      p₁₂

    -- The following lemma is basically Theorem 2.11.5 from the HoTT
    -- book (the book's lemma gives an equivalence between equality
    -- types, rather than an equality between equality types).

    [subst≡]≡[trans≡trans] :
      ∀ {a} {A : Set a} {x y : A} {p : x ≡ y} {q : x ≡ x} {r : y ≡ y} →
      (subst (λ z → z ≡ z) p q ≡ r)
        ≡
      (trans q p ≡ trans p r)
    [subst≡]≡[trans≡trans] {p = p} {q} {r} = elim
      (λ {x y} p → {q : x ≡ x} {r : y ≡ y} →
                   (subst (λ z → z ≡ z) p q ≡ r)
                     ≡
                   (trans q p ≡ trans p r))
      (λ x {q r} →
         subst (λ z → z ≡ z) (refl x) q ≡ r   ≡⟨ cong (_≡ _) (subst-refl (λ z → z ≡ z) _) ⟩
         q ≡ r                                ≡⟨ sym $ cong₂ _≡_ (trans-reflʳ _) (trans-reflˡ _) ⟩∎
         trans q (refl x) ≡ trans (refl x) r  ∎)
      p

    -- "Evaluation rule" for [subst≡]≡[trans≡trans].

    [subst≡]≡[trans≡trans]-refl :
      ∀ {a} {A : Set a} {x : A} {q : x ≡ x} {r : x ≡ x} →
      [subst≡]≡[trans≡trans] {p = refl x} {q = q} {r = r} ≡
      trans (cong (_≡ r) (subst-refl (λ z → z ≡ z) q))
            (sym $ cong₂ _≡_ (trans-reflʳ q) (trans-reflˡ r))
    [subst≡]≡[trans≡trans]-refl {q = q} {r = r} =
      cong (λ f → f {q = q} {r = r}) $
        elim-refl (λ {x y} _ → {q : x ≡ x} {r : y ≡ y} → _) _

    -- Sometimes one can turn two ("modified") copies of a proof into
    -- one.

    trans-cong-cong :
      ∀ {a b} {A : Set a} {B : Set b} {x y : A}
      (f : A → A → B) (p : x ≡ y) →
      trans (cong (λ z → f z x) p)
            (cong (λ z → f y z) p) ≡
             cong (λ z → f z z) p
    trans-cong-cong f = elim
      (λ {x y} p → trans (cong (λ z → f z x) p)
                         (cong (λ z → f y z) p) ≡
                          cong (λ z → f z z) p)
      (λ x → trans (cong (λ z → f z x) (refl x))
                   (cong (λ z → f x z) (refl x))  ≡⟨ cong₂ trans (cong-refl _) (cong-refl _) ⟩

             trans (refl (f x x)) (refl (f x x))  ≡⟨ trans-refl-refl ⟩

             refl (f x x)                         ≡⟨ sym $ cong-refl (λ z → f z z) ⟩∎

             cong (λ z → f z z) (refl x)          ∎)

    -- If f and g agree on a decidable subset of their common domain, then
    -- cong f eq is equal to (modulo some uses of transitivity) cong g eq
    -- for proofs eq between elements in this subset.

    cong-respects-relevant-equality :
      ∀ {a b} {A : Set a} {B : Set b} {x y} {x≡y : x ≡ y} {f g : A → B}
      (p : A → Bool) (f≡g : ∀ x → T (p x) → f x ≡ g x)
      {px : T (p x)} {py : T (p y)} →
      trans (cong f x≡y) (f≡g y py) ≡ trans (f≡g x px) (cong g x≡y)
    cong-respects-relevant-equality {f = f} {g} p f≡g = elim
      (λ {x y} x≡y →
         {px : T (p x)} {py : T (p y)} →
         trans (cong f x≡y) (f≡g y py) ≡ trans (f≡g x px) (cong g x≡y))
      (λ x {px px′} →
         trans (cong f (refl x)) (f≡g x px′)  ≡⟨ cong (flip trans _) (cong-refl _) ⟩
         trans (refl (f x)) (f≡g x px′)       ≡⟨ trans-reflˡ _ ⟩
         f≡g x px′                            ≡⟨ cong (f≡g x) (T-irr (p x) px′ px) ⟩
         f≡g x px                             ≡⟨ sym $ trans-reflʳ _ ⟩
         trans (f≡g x px) (refl (g x))        ≡⟨ cong (trans _) (sym $ cong-refl _) ⟩∎
         trans (f≡g x px) (cong g (refl x))   ∎)
      _
      where
      T-irr : ∀ b → Proof-irrelevant (T b)
      T-irr true  _ _ = refl _
      T-irr false ()

    -- If f z evaluates to z for a decidable set of values which
    -- includes x and y, do we have
    --
    --   cong f x≡y ≡ x≡y
    --
    -- for any x≡y : x ≡ y? The equation above is not well-typed if f
    -- is a variable, but the approximation below can be proved.

    cong-roughly-id :
      ∀ {a} {A : Set a} (f : A → A) (p : A → Bool) {x y : A}
      (x≡y : x ≡ y) (px : T (p x)) (py : T (p y))
      (f≡id : ∀ z → T (p z) → f z ≡ z) →
      cong f x≡y ≡
      trans (f≡id x px) (trans x≡y $ sym (f≡id y py))
    cong-roughly-id f p {x} {y} x≡y px py f≡id =
      let lemma =
            trans (cong id x≡y) (sym (f≡id y py))  ≡⟨ cong-respects-relevant-equality p (λ x → sym ∘ f≡id x) ⟩∎
            trans (sym (f≡id x px)) (cong f x≡y)   ∎
      in
      cong f x≡y                                                 ≡⟨ sym $ subst (λ eq → eq → trans (f≡id x px)
                                                                                                   (trans (cong id x≡y) (sym (f≡id y py))) ≡
                                                                                             cong f x≡y)
                                                                                ([trans≡]≡[≡trans-symˡ] _ _ _) id lemma ⟩
      trans (f≡id x px) (trans (cong id x≡y) $ sym (f≡id y py))  ≡⟨ cong (λ eq → trans _ (trans eq _)) (sym $ cong-id _) ⟩∎
      trans (f≡id x px) (trans x≡y $ sym (f≡id y py))            ∎
