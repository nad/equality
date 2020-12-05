------------------------------------------------------------------------
-- Two logically equivalent axiomatisations of equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Equality where

open import Logical-equivalence hiding (id; _∘_)
open import Prelude

private
  variable
    ℓ                                      : Level
    A B C D                                : Type ℓ
    P                                      : A → Type ℓ
    a a₁ a₂ a₃ b c p u v x x₁ x₂ y y₁ y₂ z : A
    f g                                    : (x : A) → P x

------------------------------------------------------------------------
-- Reflexive relations

record Reflexive-relation a : Type (lsuc a) where
  no-eta-equality
  infix 4 _≡_
  field

    -- "Equality".

    _≡_ : {A : Type a} → A → A → Type a

    -- Reflexivity.

    refl : (x : A) → x ≡ x

-- Some definitions.

module Reflexive-relation′
         (reflexive : ∀ ℓ → Reflexive-relation ℓ) where

  private
    open module R {ℓ} = Reflexive-relation (reflexive ℓ) public

  -- Non-equality.

  infix 4 _≢_

  _≢_ : {A : Type a} → A → A → Type a
  x ≢ y = ¬ (x ≡ y)

  -- The property of having decidable equality.

  Decidable-equality : Type ℓ → Type ℓ
  Decidable-equality A = Decidable (_≡_ {A = A})

  -- A type is contractible if it is inhabited and all elements are
  -- equal.

  Contractible : Type ℓ → Type ℓ
  Contractible A = ∃ λ (x : A) → ∀ y → x ≡ y

  -- The property of being a proposition.

  Is-proposition : Type ℓ → Type ℓ
  Is-proposition A = (x y : A) → x ≡ y

  -- The property of being a set.

  Is-set : Type ℓ → Type ℓ
  Is-set A = {x y : A} → Is-proposition (x ≡ y)

  -- Uniqueness of identity proofs (for a specific universe level).

  Uniqueness-of-identity-proofs : ∀ ℓ → Type (lsuc ℓ)
  Uniqueness-of-identity-proofs ℓ = {A : Type ℓ} → Is-set A

  -- The K rule (without computational content).

  K-rule : ∀ a p → Type (lsuc (a ⊔ p))
  K-rule a p = {A : Type a} (P : {x : A} → x ≡ x → Type p) →
               (∀ x → P (refl x)) →
               ∀ {x} (x≡x : x ≡ x) → P x≡x

  -- Singleton x is a set which contains all elements which are equal
  -- to x.

  Singleton : {A : Type a} → A → Type a
  Singleton x = ∃ λ y → y ≡ x

  -- A variant of Singleton.

  Other-singleton : {A : Type a} → A → Type a
  Other-singleton x = ∃ λ y → x ≡ y

  -- The inspect idiom.

  inspect : (x : A) → Other-singleton x
  inspect x = x , refl x

  -- Extensionality for functions of a certain type.

  Extensionality′ : (A : Type a) → (A → Type b) → Type (a ⊔ b)
  Extensionality′ A B =
    {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

  -- Extensionality for functions at certain levels.
  --
  -- The definition is wrapped in a record type in order to avoid
  -- certain problems related to Agda's handling of implicit
  -- arguments.

  record Extensionality (a b : Level) : Type (lsuc (a ⊔ b)) where
    no-eta-equality
    field
      apply-ext : {A : Type a} {B : A → Type b} → Extensionality′ A B

  open Extensionality public

  -- Proofs of extensionality which behave well when applied to
  -- reflexivity.

  Well-behaved-extensionality :
    (A : Type a) → (A → Type b) → Type (a ⊔ b)
  Well-behaved-extensionality A B =
    ∃ λ (ext : Extensionality′ A B) →
      ∀ f → ext (λ x → refl (f x)) ≡ refl f

------------------------------------------------------------------------
-- Abstract definition of equality based on the J rule

-- Parametrised by a reflexive relation.

record Equality-with-J₀
         a p (reflexive : ∀ ℓ → Reflexive-relation ℓ) :
         Type (lsuc (a ⊔ p)) where

  open Reflexive-relation′ reflexive

  field

    -- The J rule.

    elim : ∀ {A : Type a} {x y}
           (P : {x y : A} → x ≡ y → Type p) →
           (∀ x → P (refl x)) →
           (x≡y : x ≡ y) → P x≡y

    -- The usual computational behaviour of the J rule.

    elim-refl : ∀ {A : Type a} {x}
                (P : {x y : A} → x ≡ y → Type p)
                (r : ∀ x → P (refl x)) →
                elim P r (refl x) ≡ r x

-- Extended variants of Reflexive-relation and Equality-with-J₀ with
-- some extra fields. These fields can be derived from
-- Equality-with-J₀ (see J₀⇒Equivalence-relation⁺ and J₀⇒J below), but
-- those derived definitions may not have the intended computational
-- behaviour (in particular, not when the paths of Cubical Agda are
-- used).

-- A variant of Reflexive-relation: equivalence relations with some
-- extra structure.

record Equivalence-relation⁺ a : Type (lsuc a) where
  no-eta-equality
  field
    reflexive-relation : Reflexive-relation a

  open Reflexive-relation reflexive-relation

  field

    -- Symmetry.

    sym      : {A : Type a} {x y : A} → x ≡ y → y ≡ x
    sym-refl : {A : Type a} {x : A} → sym (refl x) ≡ refl x

    -- Transitivity.

    trans           : {A : Type a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans-refl-refl : {A : Type a} {x : A} →
                      trans (refl x) (refl x) ≡ refl x

-- A variant of Equality-with-J₀.

record Equality-with-J
         a b (e⁺ : ∀ ℓ → Equivalence-relation⁺ ℓ) :
         Type (lsuc (a ⊔ b)) where
  no-eta-equality

  private
    open module R  {ℓ} = Equivalence-relation⁺ (e⁺ ℓ)
    open module R₀ {ℓ} = Reflexive-relation (reflexive-relation {ℓ})

  field
    equality-with-J₀ : Equality-with-J₀ a b (λ _ → reflexive-relation)

  open Equality-with-J₀ equality-with-J₀

  field

    -- Congruence.

    cong      : {A : Type a} {B : Type b} {x y : A}
                (f : A → B) → x ≡ y → f x ≡ f y
    cong-refl : {A : Type a} {B : Type b} {x : A} (f : A → B) →
                cong f (refl x) ≡ refl (f x)

    -- Substitutivity.

    subst      : {A : Type a} {x y : A} (P : A → Type b) →
                 x ≡ y → P x → P y
    subst-refl : ∀ {A : Type a} {x} (P : A → Type b) p →
                 subst P (refl x) p ≡ p

    -- A dependent variant of cong.

    dcong :
      ∀ {A : Type a} {P : A → Type b} {x y}
      (f : (x : A) → P x) (x≡y : x ≡ y) →
      subst P x≡y (f x) ≡ f y
    dcong-refl :
      ∀ {A : Type a} {P : A → Type b} {x} (f : (x : A) → P x) →
      dcong f (refl x) ≡ subst-refl _ _

-- Equivalence-relation⁺ can be derived from Equality-with-J₀.

J₀⇒Equivalence-relation⁺ :
  ∀ {ℓ reflexive} →
  Equality-with-J₀ ℓ ℓ reflexive →
  Equivalence-relation⁺ ℓ
J₀⇒Equivalence-relation⁺ {ℓ} {r} eq = record
  { reflexive-relation = r ℓ
  ; sym                = sym
  ; sym-refl           = sym-refl
  ; trans              = trans
  ; trans-refl-refl    = trans-refl-refl
  }
  where
  open Reflexive-relation (r ℓ)
  open Equality-with-J₀ eq

  cong : (f : A → B) → x ≡ y → f x ≡ f y
  cong f = elim (λ {u v} _ → f u ≡ f v) (λ x → refl (f x))

  subst : (P : A → Type ℓ) → x ≡ y → P x → P y
  subst P = elim (λ {u v} _ → P u → P v) (λ _ p → p)

  subst-refl : (P : A → Type ℓ) (p : P x) → subst P (refl x) p ≡ p
  subst-refl _ p = cong (_$ p) $ elim-refl _ _

  sym : x ≡ y → y ≡ x
  sym {x = x} x≡y = subst (λ z → x ≡ z → z ≡ x) x≡y id x≡y

  abstract

    sym-refl : sym (refl x) ≡ refl x
    sym-refl = cong (_$ _) $ subst-refl (λ z → _ ≡ z → z ≡ _) _

  trans : x ≡ y → y ≡ z → x ≡ z
  trans {x = x} = flip (subst (x ≡_))

  abstract

    trans-refl-refl : trans (refl x) (refl x) ≡ refl x
    trans-refl-refl = subst-refl _ _

-- Equality-with-J (for arbitrary universe levels) can be derived from
-- Equality-with-J₀ (for arbitrary universe levels).

J₀⇒J :
  ∀ {reflexive} →
  (eq : ∀ {a p} → Equality-with-J₀ a p reflexive) →
  ∀ {a p} → Equality-with-J a p (λ _ → J₀⇒Equivalence-relation⁺ eq)
J₀⇒J {r} eq {a} {b} = record
  { equality-with-J₀ = eq
  ; cong             = cong
  ; cong-refl        = cong-refl
  ; subst            = subst
  ; subst-refl       = subst-refl
  ; dcong            = dcong
  ; dcong-refl       = dcong-refl
  }
  where
  open module R {ℓ}     = Reflexive-relation (r ℓ)
  open module E {a} {b} = Equality-with-J₀ (eq {a} {b})

  cong : (f : A → B) → x ≡ y → f x ≡ f y
  cong f = elim (λ {u v} _ → f u ≡ f v) (λ x → refl (f x))

  abstract

    cong-refl : (f : A → B) → cong f (refl x) ≡ refl (f x)
    cong-refl _ = elim-refl _ _

  subst : (P : A → Type b) → x ≡ y → P x → P y
  subst P = elim (λ {u v} _ → P u → P v) (λ _ p → p)

  subst-refl≡id : (P : A → Type b) → subst P (refl x) ≡ id
  subst-refl≡id P = elim-refl (λ {u v} _ → P u → P v) (λ _ p → p)

  subst-refl : ∀ (P : A → Type b) p → subst P (refl x) p ≡ p
  subst-refl P p = cong (_$ p) (subst-refl≡id _)

  dcong : (f : (x : A) → P x) (x≡y : x ≡ y) →
          subst P x≡y (f x) ≡ f y
  dcong {A = A} {P = P} f x≡y = elim
    (λ {x y} (x≡y : x ≡ y) → (f : (x : A) → P x) →
       subst P x≡y (f x) ≡ f y)
    (λ _ _ → subst-refl _ _)
    x≡y
    f

  abstract

    dcong-refl : (f : (x : A) → P x) →
                 dcong f (refl x) ≡ subst-refl _ _
    dcong-refl f = cong (_$ f) $ elim-refl _ _

-- Some derived properties.

module Equality-with-J′
  {e⁺ : ∀ ℓ → Equivalence-relation⁺ ℓ}
  (eq : ∀ {a p} → Equality-with-J a p e⁺)
  where

  private
    open module E⁺ {ℓ}   = Equivalence-relation⁺ (e⁺ ℓ) public
    open module E  {a b} = Equality-with-J (eq {a} {b}) public
                             hiding (subst; subst-refl)
    open module E₀ {a p} = Equality-with-J₀ (equality-with-J₀ {a} {p})
                             public
  open Reflexive-relation′ (λ ℓ → reflexive-relation {ℓ}) public

  -- Substitutivity.

  subst : (P : A → Type p) → x ≡ y → P x → P y
  subst = E.subst

  subst-refl : (P : A → Type p) (p : P x) → subst P (refl x) p ≡ p
  subst-refl = E.subst-refl

  -- Singleton types are contractible.

  private

    irr : (p : Singleton x) → (x , refl x) ≡ p
    irr p =
      elim (λ {u v} u≡v → (v , refl v) ≡ (u , u≡v))
           (λ _ → refl _)
           (proj₂ p)

  singleton-contractible : (x : A) → Contractible (Singleton x)
  singleton-contractible x = ((x , refl x) , irr)

  abstract

    -- "Evaluation rule" for singleton-contractible.

    singleton-contractible-refl :
      (x : A) →
      proj₂ (singleton-contractible x) (x , refl x) ≡ refl (x , refl x)
    singleton-contractible-refl _ = elim-refl _ _

------------------------------------------------------------------------
-- Abstract definition of equality based on substitutivity and
-- contractibility of singleton types

record Equality-with-substitutivity-and-contractibility
         a p (reflexive : ∀ ℓ → Reflexive-relation ℓ) :
         Type (lsuc (a ⊔ p)) where
  no-eta-equality

  open Reflexive-relation′ reflexive

  field

    -- Substitutivity.

    subst : {A : Type a} {x y : A} (P : A → Type p) → x ≡ y → P x → P y

    -- The usual computational behaviour of substitutivity.

    subst-refl : {A : Type a} {x : A} (P : A → Type p) (p : P x) →
                 subst P (refl x) p ≡ p

    -- Singleton types are contractible.

    singleton-contractible :
      {A : Type a} (x : A) → Contractible (Singleton x)

-- Some derived properties.

module Equality-with-substitutivity-and-contractibility′
  {reflexive : ∀ ℓ → Reflexive-relation ℓ}
  (eq : ∀ {a p} → Equality-with-substitutivity-and-contractibility
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

    cong : (f : A → B) → x ≡ y → f x ≡ f y
    cong {x = x} f x≡y =
      subst (λ y → x ≡ y → f x ≡ f y) x≡y (λ _ → refl (f x)) x≡y

  -- Symmetry.

  sym : x ≡ y → y ≡ x
  sym {x = x} x≡y = subst (λ z → x ≡ z → z ≡ x) x≡y id x≡y

  abstract

    -- "Evaluation rule" for sym.

    sym-refl : sym (refl x) ≡ refl x
    sym-refl {x = x} =
      cong (λ f → f (refl x)) $
        subst-refl (λ z → x ≡ z → z ≡ x) _

  -- Transitivity.

  trans : x ≡ y → y ≡ z → x ≡ z
  trans {x = x} = flip (subst (_≡_ x))

  abstract

    -- "Evaluation rule" for trans.

    trans-refl-refl : trans (refl x) (refl x) ≡ refl x
    trans-refl-refl = subst-refl _ _

  abstract

    -- The J rule.

    elim : (P : {x y : A} → x ≡ y → Type p) →
           (∀ x → P (refl x)) →
           (x≡y : x ≡ y) → P x≡y
    elim {x = x} {y = y} P p x≡y =
      let lemma = proj₂ (singleton-contractible y) in
      subst (P ∘ proj₂)
            (trans (sym (lemma (y , refl y))) (lemma (x , x≡y)))
            (p y)

    -- Transitivity and symmetry sometimes cancel each other out.

    trans-sym : (x≡y : x ≡ y) → trans (sym x≡y) x≡y ≡ refl y
    trans-sym =
      elim (λ {x y} (x≡y : x ≡ y) → trans (sym x≡y) x≡y ≡ refl y)
           (λ _ → trans (cong (λ p → trans p _) sym-refl)
                        trans-refl-refl)

    -- "Evaluation rule" for elim.

    elim-refl : (P : {x y : A} → x ≡ y → Type p)
                (p : ∀ x → P (refl x)) →
                elim P p (refl x) ≡ p x
    elim-refl {x = x} _ _ =
      let lemma = proj₂ (singleton-contractible x) (x , refl x) in
      trans (cong (λ q → subst _ q _) (trans-sym lemma))
            (subst-refl _ _)

------------------------------------------------------------------------
-- The two abstract definitions are logically equivalent

J⇒subst+contr :
  ∀ {reflexive} →
  (∀ {a p} → Equality-with-J₀ a p reflexive) →
  ∀ {a p} → Equality-with-substitutivity-and-contractibility
              a p reflexive
J⇒subst+contr eq = record
  { subst                  = subst
  ; subst-refl             = subst-refl
  ; singleton-contractible = singleton-contractible
  }
  where open Equality-with-J′ (J₀⇒J eq)

subst+contr⇒J :
  ∀ {reflexive} →
  (∀ {a p} → Equality-with-substitutivity-and-contractibility
               a p reflexive) →
  ∀ {a p} → Equality-with-J₀ a p reflexive
subst+contr⇒J eq = record
  { elim      = elim
  ; elim-refl = elim-refl
  }
  where open Equality-with-substitutivity-and-contractibility′ eq

------------------------------------------------------------------------
-- Some derived definitions and properties

module Derived-definitions-and-properties
  {e⁺}
  (equality-with-J : ∀ {a p} → Equality-with-J a p e⁺)
  where

  -- This module reexports most of the definitions and properties
  -- introduced above.

  open Equality-with-J′ equality-with-J public

  private
    variable
      eq u≡v x≡y y≡z x₁≡x₂ : x ≡ y

  -- Equational reasoning combinators.

  infix  -1 finally _∎
  infixr -2 step-≡ _≡⟨⟩_

  _∎ : (x : A) → x ≡ x
  x ∎ = refl x

  -- It can be easier for Agda to type-check typical equational
  -- reasoning chains if the transitivity proof gets the equality
  -- arguments in the opposite order, because then the y argument is
  -- (perhaps more) known once the proof of x ≡ y is type-checked.
  --
  -- The idea behind this optimisation came up in discussions with Ulf
  -- Norell.

  step-≡ : ∀ x → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ = flip trans

  syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

  _≡⟨⟩_ : ∀ x → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  finally : (x y : A) → x ≡ y → x ≡ y
  finally _ _ x≡y = x≡y

  syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

  -- A minor variant of Christine Paulin-Mohring's version of the J
  -- rule.
  --
  -- This definition is based on Martin Hofmann's (see the addendum
  -- to Thomas Streicher's Habilitation thesis). Note that it is
  -- also very similar to the definition of
  -- Equality-with-substitutivity-and-contractibility.elim.

  elim₁ : (P : ∀ {x} → x ≡ y → Type p) →
          P (refl y) →
          (x≡y : x ≡ y) → P x≡y
  elim₁ {y = y} {x = x} P p x≡y =
    subst (P ∘ proj₂)
          (proj₂ (singleton-contractible y) (x , x≡y))
          p

  abstract

    -- "Evaluation rule" for elim₁.

    elim₁-refl : (P : ∀ {x} → x ≡ y → Type p) (p : P (refl y)) →
                 elim₁ P p (refl y) ≡ p
    elim₁-refl {y = y} P p =
      subst (P ∘ proj₂)
            (proj₂ (singleton-contractible y) (y , refl y))
            p                                                ≡⟨ cong (λ q → subst (P ∘ proj₂) q _) (singleton-contractible-refl _) ⟩

      subst (P ∘ proj₂) (refl (y , refl y)) p                ≡⟨ subst-refl _ _ ⟩∎

      p                                                      ∎

  -- A variant of singleton-contractible.

  private

    irr : (p : Other-singleton x) → (x , refl x) ≡ p
    irr p =
      elim (λ {u v} u≡v → (u , refl u) ≡ (v , u≡v))
           (λ _ → refl _)
           (proj₂ p)

  other-singleton-contractible :
    (x : A) → Contractible (Other-singleton x)
  other-singleton-contractible x = ((x , refl x) , irr)

  abstract

    -- "Evaluation rule" for other-singleton-contractible.

    other-singleton-contractible-refl :
      (x : A) →
      proj₂ (other-singleton-contractible x) (x , refl x) ≡
      refl (x , refl x)
    other-singleton-contractible-refl _ = elim-refl _ _

  -- Christine Paulin-Mohring's version of the J rule.

  elim¹ : (P : ∀ {y} → x ≡ y → Type p) →
          P (refl x) →
          (x≡y : x ≡ y) → P x≡y
  elim¹ {x = x} {y = y} P p x≡y =
    subst (P ∘ proj₂)
          (proj₂ (other-singleton-contractible x) (y , x≡y))
          p

  abstract

    -- "Evaluation rule" for elim¹.

    elim¹-refl : (P : ∀ {y} → x ≡ y → Type p) (p : P (refl x)) →
                 elim¹ P p (refl x) ≡ p
    elim¹-refl {x = x} P p =
      subst (P ∘ proj₂)
            (proj₂ (other-singleton-contractible x) (x , refl x)) p    ≡⟨ cong (λ q → subst (P ∘ proj₂) q _)
                                                                               (other-singleton-contractible-refl _) ⟩
      subst (P ∘ proj₂) (refl (x , refl x)) p                          ≡⟨ subst-refl _ _ ⟩∎
      p                                                                ∎

    -- Every conceivable alternative implementation of cong (for two
    -- specific types) is pointwise equal to cong.

    monomorphic-cong-canonical :
      (cong′ : {x y : A} (f : A → B) → x ≡ y → f x ≡ f y) →
      ({x : A} (f : A → B) → cong′ f (refl x) ≡ refl (f x)) →
      cong′ f x≡y ≡ cong f x≡y
    monomorphic-cong-canonical {f = f} cong′ cong′-refl = elim
      (λ x≡y → cong′ f x≡y ≡ cong f x≡y)
      (λ x →
         cong′ f (refl x)  ≡⟨ cong′-refl _ ⟩
         refl (f x)        ≡⟨ sym $ cong-refl _ ⟩∎
         cong f (refl x)   ∎)
      _

    -- Every conceivable alternative implementation of cong (for
    -- arbitrary types) is pointwise equal to cong.

    cong-canonical :
      (cong′ :
         ∀ {a b} {A : Type a} {B : Type b} {x y : A}
         (f : A → B) → x ≡ y → f x ≡ f y) →
      (∀ {a b} {A : Type a} {B : Type b} {x : A}
       (f : A → B) → cong′ f (refl x) ≡ refl (f x)) →
      cong′ f x≡y ≡ cong f x≡y
    cong-canonical cong′ cong′-refl =
      monomorphic-cong-canonical cong′ cong′-refl

  -- A generalisation of dcong.

  dcong′ :
    (f : (x : A) → x ≡ y → P x) (x≡y : x ≡ y) →
    subst P x≡y (f x x≡y) ≡ f y (refl y)
  dcong′ {y = y} {P = P} f x≡y = elim₁
    (λ {x} (x≡y : x ≡ y) →
       (f : ∀ x → x ≡ y → P x) →
       subst P x≡y (f x x≡y) ≡ f y (refl y))
    (λ f → subst P (refl y) (f y (refl y))  ≡⟨ subst-refl _ _ ⟩∎
           f y (refl y)                     ∎)
    x≡y f

  abstract

    -- "Evaluation rule" for dcong′.

    dcong′-refl :
      (f : (x : A) → x ≡ y → P x) →
      dcong′ f (refl y) ≡ subst-refl _ _
    dcong′-refl f = cong (_$ f) $ elim₁-refl _ _

  -- Binary congruence.

  cong₂ : (f : A → B → C) → x ≡ y → u ≡ v → f x u ≡ f y v
  cong₂ {x = x} {y = y} {u = u} {v = v} f x≡y u≡v =
    f x u  ≡⟨ cong (flip f u) x≡y ⟩
    f y u  ≡⟨ cong (f y)      u≡v ⟩∎
    f y v  ∎

  abstract

    -- "Evaluation rule" for cong₂.

    cong₂-refl : (f : A → B → C) →
                 cong₂ f (refl x) (refl y) ≡ refl (f x y)
    cong₂-refl {x = x} {y = y} f =
      trans (cong (flip f y) (refl x)) (cong (f x) (refl y))  ≡⟨ cong₂ trans (cong-refl _) (cong-refl _) ⟩
      trans (refl (f x y)) (refl (f x y))                     ≡⟨ trans-refl-refl ⟩∎
      refl (f x y)                                            ∎

  -- The K rule is logically equivalent to uniqueness of identity
  -- proofs (at least for certain combinations of levels).

  K⇔UIP : K-rule ℓ ℓ ⇔ Uniqueness-of-identity-proofs ℓ
  K⇔UIP = record
    { from = λ UIP P r {x} x≡x → subst P (UIP (refl x) x≡x) (r x)
    ; to   = λ K →
        elim (λ p → ∀ q → p ≡ q)
             (λ x → K (λ {x} p → refl x ≡ p) (λ x → refl (refl x)))
    }

  abstract

    -- Extensionality at given levels works at lower levels as well.

    lower-extensionality :
      ∀ â b̂ → Extensionality (a ⊔ â) (b ⊔ b̂) → Extensionality a b
    apply-ext (lower-extensionality â b̂ ext) f≡g =
      cong (λ h → lower ∘ h ∘ lift) $
        apply-ext ext
          {A = ↑ â _} {B = ↑ b̂ ∘ _} (cong lift ∘ f≡g ∘ lower)

  -- Extensionality for explicit function types works for implicit
  -- function types as well.

  implicit-extensionality :
    Extensionality a b →
    {A : Type a} {B : A → Type b} {f g : {x : A} → B x} →
    (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g
  implicit-extensionality ext f≡g =
    cong (λ f {x} → f x) $ apply-ext ext f≡g

  -- A bunch of lemmas that can be used to rearrange equalities.

  abstract

    trans-reflʳ : (x≡y : x ≡ y) → trans x≡y (refl y) ≡ x≡y
    trans-reflʳ =
      elim (λ {u v} u≡v → trans u≡v (refl v) ≡ u≡v)
           (λ _ → trans-refl-refl)

    trans-reflˡ : (x≡y : x ≡ y) → trans (refl x) x≡y ≡ x≡y
    trans-reflˡ =
      elim (λ {u v} u≡v → trans (refl u) u≡v ≡ u≡v)
           (λ _ → trans-refl-refl)

    trans-assoc : (x≡y : x ≡ y) (y≡z : y ≡ z) (z≡u : z ≡ u) →
                  trans (trans x≡y y≡z) z≡u ≡ trans x≡y (trans y≡z z≡u)
    trans-assoc =
      elim (λ x≡y → ∀ y≡z z≡u → trans (trans x≡y y≡z) z≡u ≡
                                trans x≡y (trans y≡z z≡u))
           (λ y y≡z z≡u →
              trans (trans (refl y) y≡z) z≡u ≡⟨ cong₂ trans (trans-reflˡ _) (refl _) ⟩
              trans y≡z z≡u                  ≡⟨ sym $ trans-reflˡ _ ⟩∎
              trans (refl y) (trans y≡z z≡u) ∎)

    sym-sym : (x≡y : x ≡ y) → sym (sym x≡y) ≡ x≡y
    sym-sym = elim (λ {u v} u≡v → sym (sym u≡v) ≡ u≡v)
                   (λ x → sym (sym (refl x))  ≡⟨ cong sym sym-refl ⟩
                          sym (refl x)        ≡⟨ sym-refl ⟩∎
                          refl x              ∎)

    sym-trans : (x≡y : x ≡ y) (y≡z : y ≡ z) →
                sym (trans x≡y y≡z) ≡ trans (sym y≡z) (sym x≡y)
    sym-trans =
      elim (λ x≡y → ∀ y≡z → sym (trans x≡y y≡z) ≡ trans (sym y≡z) (sym x≡y))
           (λ y y≡z → sym (trans (refl y) y≡z)        ≡⟨ cong sym (trans-reflˡ _) ⟩
                      sym y≡z                         ≡⟨ sym $ trans-reflʳ _ ⟩
                      trans (sym y≡z) (refl y)        ≡⟨ cong (trans (sym y≡z)) (sym sym-refl)  ⟩∎
                      trans (sym y≡z) (sym (refl y))  ∎)

    trans-symˡ : (p : x ≡ y) → trans (sym p) p ≡ refl y
    trans-symˡ =
      elim (λ p → trans (sym p) p ≡ refl _)
           (λ x → trans (sym (refl x)) (refl x)  ≡⟨ trans-reflʳ _ ⟩
                  sym (refl x)                   ≡⟨ sym-refl ⟩∎
                  refl x                         ∎)

    trans-symʳ : (p : x ≡ y) → trans p (sym p) ≡ refl _
    trans-symʳ =
      elim (λ p → trans p (sym p) ≡ refl _)
           (λ x → trans (refl x) (sym (refl x))  ≡⟨ trans-reflˡ _ ⟩
                  sym (refl x)                   ≡⟨ sym-refl ⟩∎
                  refl x                         ∎)

    cong-trans : (f : A → B) (x≡y : x ≡ y) (y≡z : y ≡ z) →
                 cong f (trans x≡y y≡z) ≡ trans (cong f x≡y) (cong f y≡z)
    cong-trans f =
      elim (λ x≡y → ∀ y≡z → cong f (trans x≡y y≡z) ≡
                            trans (cong f x≡y) (cong f y≡z))
           (λ y y≡z → cong f (trans (refl y) y≡z)           ≡⟨ cong (cong f) (trans-reflˡ _) ⟩
                      cong f y≡z                            ≡⟨ sym $ trans-reflˡ _ ⟩
                      trans (refl (f y)) (cong f y≡z)       ≡⟨ cong₂ trans (sym (cong-refl _)) (refl _) ⟩∎
                      trans (cong f (refl y)) (cong f y≡z)  ∎)

    cong-id : (x≡y : x ≡ y) → x≡y ≡ cong id x≡y
    cong-id = elim (λ u≡v → u≡v ≡ cong id u≡v)
                   (λ x → refl x            ≡⟨ sym (cong-refl _) ⟩∎
                          cong id (refl x)  ∎)

    cong-const : (x≡y : x ≡ y) → cong (const z) x≡y ≡ refl z
    cong-const {z = z} =
      elim (λ u≡v → cong (const z) u≡v ≡ refl z)
           (λ x → cong (const z) (refl x)  ≡⟨ cong-refl _ ⟩∎
                  refl z                   ∎)

    cong-∘ : (f : B → C) (g : A → B) (x≡y : x ≡ y) →
             cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y
    cong-∘ f g = elim (λ x≡y → cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y)
                      (λ x → cong f (cong g (refl x))  ≡⟨ cong (cong f) (cong-refl _) ⟩
                             cong f (refl (g x))       ≡⟨ cong-refl _ ⟩
                             refl (f (g x))            ≡⟨ sym (cong-refl _) ⟩∎
                             cong (f ∘ g) (refl x)     ∎)

    cong-uncurry-cong₂-, :
      {x≡y : x ≡ y} {u≡v : u ≡ v} →
      cong (uncurry f) (cong₂ _,_ x≡y u≡v) ≡ cong₂ f x≡y u≡v
    cong-uncurry-cong₂-, {y = y} {u = u} {f = f} {x≡y = x≡y} {u≡v} =
      cong (uncurry f)
           (trans (cong (flip _,_ u) x≡y) (cong (_,_ y) u≡v))  ≡⟨ cong-trans _ _ _ ⟩

      trans (cong (uncurry f) (cong (flip _,_ u) x≡y))
            (cong (uncurry f) (cong (_,_ y) u≡v))              ≡⟨ cong₂ trans (cong-∘ _ _ _) (cong-∘ _ _ _) ⟩∎

      trans (cong (flip f u) x≡y) (cong (f y) u≡v)             ∎

    cong-proj₁-cong₂-, :
      (x≡y : x ≡ y) (u≡v : u ≡ v) →
      cong proj₁ (cong₂ _,_ x≡y u≡v) ≡ x≡y
    cong-proj₁-cong₂-, {y = y} x≡y u≡v =
      cong proj₁ (cong₂ _,_ x≡y u≡v)            ≡⟨ cong-uncurry-cong₂-, ⟩
      cong₂ const x≡y u≡v                       ≡⟨⟩
      trans (cong id x≡y) (cong (const y) u≡v)  ≡⟨ cong₂ trans (sym $ cong-id _) (cong-const _) ⟩
      trans x≡y (refl y)                        ≡⟨ trans-reflʳ _ ⟩∎
      x≡y                                       ∎

    cong-proj₂-cong₂-, :
      (x≡y : x ≡ y) (u≡v : u ≡ v) →
      cong proj₂ (cong₂ _,_ x≡y u≡v) ≡ u≡v
    cong-proj₂-cong₂-, {u = u} x≡y u≡v =
      cong proj₂ (cong₂ _,_ x≡y u≡v)            ≡⟨ cong-uncurry-cong₂-, ⟩
      cong₂ (const id) x≡y u≡v                  ≡⟨⟩
      trans (cong (const u) x≡y) (cong id u≡v)  ≡⟨ cong₂ trans (cong-const _) (sym $ cong-id _) ⟩
      trans (refl u) u≡v                        ≡⟨ trans-reflˡ _ ⟩∎
      u≡v                                       ∎

    cong₂-reflˡ : {u≡v : u ≡ v}
                  (f : A → B → C) →
                  cong₂ f (refl x) u≡v ≡ cong (f x) u≡v
    cong₂-reflˡ {u = u} {x = x} {u≡v = u≡v} f =
      trans (cong (flip f u) (refl x)) (cong (f x) u≡v)  ≡⟨ cong₂ trans (cong-refl _) (refl _) ⟩
      trans (refl (f x u)) (cong (f x) u≡v)              ≡⟨ trans-reflˡ _ ⟩∎
      cong (f x) u≡v                                     ∎

    cong₂-reflʳ : (f : A → B → C) {x≡y : x ≡ y} →
                  cong₂ f x≡y (refl u) ≡ cong (flip f u) x≡y
    cong₂-reflʳ {y = y} {u = u} f {x≡y} =
      trans (cong (flip f u) x≡y) (cong (f y) (refl u))  ≡⟨ cong (trans _) (cong-refl _) ⟩
      trans (cong (flip f u) x≡y) (refl (f y u))         ≡⟨ trans-reflʳ _ ⟩∎
      cong (flip f u) x≡y                                ∎

    cong-sym : (f : A → B) (x≡y : x ≡ y) →
               cong f (sym x≡y) ≡ sym (cong f x≡y)
    cong-sym f = elim (λ x≡y → cong f (sym x≡y) ≡ sym (cong f x≡y))
                      (λ x → cong f (sym (refl x))  ≡⟨ cong (cong f) sym-refl ⟩
                             cong f (refl x)        ≡⟨ cong-refl _ ⟩
                             refl (f x)             ≡⟨ sym sym-refl ⟩
                             sym (refl (f x))       ≡⟨ cong sym $ sym (cong-refl _) ⟩∎
                             sym (cong f (refl x))  ∎)

    cong₂-sym :
      cong₂ f (sym x≡y) (sym u≡v) ≡ sym (cong₂ f x≡y u≡v)
    cong₂-sym {f = f} {x≡y = x≡y} {u≡v = u≡v} = elim¹
      (λ u≡v → cong₂ f (sym x≡y) (sym u≡v) ≡ sym (cong₂ f x≡y u≡v))
      (cong₂ f (sym x≡y) (sym (refl _))  ≡⟨ cong (cong₂ _ _) sym-refl ⟩
       cong₂ f (sym x≡y) (refl _)        ≡⟨ cong₂-reflʳ _ ⟩
       cong (flip f _) (sym x≡y)         ≡⟨ cong-sym _ _ ⟩
       sym (cong (flip f _) x≡y)         ≡⟨ cong sym $ sym $ cong₂-reflʳ _ ⟩∎
       sym (cong₂ f x≡y (refl _))        ∎)
      u≡v

    cong₂-∘ˡ :
      {f : B → C → D} {g : A → B} {x≡y : x ≡ y} {u≡v : u ≡ v} →
      cong₂ (f ∘ g) x≡y u≡v ≡ cong₂ f (cong g x≡y) u≡v
    cong₂-∘ˡ {y = y} {u = u} {f = f} {g = g} {x≡y = x≡y} {u≡v} =
      trans (cong (flip (f ∘ g) u) x≡y) (cong (f (g y)) u≡v)     ≡⟨ cong (flip trans _) $ sym $ cong-∘ _ _ _ ⟩∎
      trans (cong (flip f u) (cong g x≡y)) (cong (f (g y)) u≡v)  ∎

    cong₂-∘ʳ :
      {x≡y : x ≡ y} {u≡v : u ≡ v} →
      cong₂ (λ x → f x ∘ g) x≡y u≡v ≡ cong₂ f x≡y (cong g u≡v)
    cong₂-∘ʳ {y = y} {u = u} {f = f} {g = g} {x≡y = x≡y} {u≡v} =
      trans (cong (flip f (g u)) x≡y) (cong (f y ∘ g) u≡v)       ≡⟨ cong (trans _) $ sym $ cong-∘ _ _ _ ⟩∎
      trans (cong (flip f (g u)) x≡y) (cong (f y) (cong g u≡v))  ∎

    cong₂-cong-cong :
      (f : A → B) (g : A → C) (h : B → C → D) →
      cong₂ h (cong f eq) (cong g eq) ≡
      cong (λ x → h (f x) (g x)) eq
    cong₂-cong-cong f g h = elim¹
      (λ eq → cong₂ h (cong f eq) (cong g eq) ≡
              cong (λ x → h (f x) (g x)) eq)
      (cong₂ h (cong f (refl _)) (cong g (refl _))  ≡⟨ cong₂ (cong₂ h) (cong-refl _) (cong-refl _) ⟩
       cong₂ h (refl _) (refl _)                    ≡⟨ cong₂-refl h ⟩
       refl _                                       ≡⟨ sym $ cong-refl _ ⟩∎
       cong (λ x → h (f x) (g x)) (refl _)          ∎)
      _

    cong-≡id :
      {f : A → A}
      (f≡id : f ≡ id) →
      cong (λ g → g (f x)) f≡id ≡
      cong (λ g → f (g x)) f≡id
    cong-≡id = elim₁
      (λ {f} p → cong (λ g → g (f _)) p ≡ cong (λ g → f (g _)) p)
      (refl _)

    cong-≡id-≡-≡id :
      (f≡id : ∀ x → f x ≡ x) →
      cong f (f≡id x) ≡ f≡id (f x)
    cong-≡id-≡-≡id {f = f} {x = x} f≡id =
      cong f (f≡id x)                                             ≡⟨ elim¹
                                                                       (λ {y} (p : f x ≡ y) →
                                                                          cong f p ≡ trans (f≡id (f x)) (trans p (sym (f≡id y)))) (
          cong f (refl _)                                              ≡⟨ cong-refl _ ⟩
          refl _                                                       ≡⟨ sym $ trans-symʳ _ ⟩
          trans (f≡id (f x)) (sym (f≡id (f x)))                        ≡⟨ cong (trans (f≡id (f x))) $ sym $ trans-reflˡ _ ⟩∎
          trans (f≡id (f x)) (trans (refl _) (sym (f≡id (f x))))       ∎)
                                                                       (f≡id x)⟩
      trans (f≡id (f x)) (trans (f≡id x) (sym (f≡id x)))          ≡⟨ cong (trans (f≡id (f x))) $ trans-symʳ _ ⟩
      trans (f≡id (f x)) (refl _)                                 ≡⟨ trans-reflʳ _ ⟩
      f≡id (f x)                                                  ∎

    elim-∘ :
      (P Q : ∀ {x y} → x ≡ y → Type p)
      (f : ∀ {x y} {x≡y : x ≡ y} → P x≡y → Q x≡y)
      (r : ∀ x → P (refl x)) {x≡y : x ≡ y} →
      f (elim P r x≡y) ≡ elim Q (f ∘ r) x≡y
    elim-∘ {x = x} P Q f r {x≡y} = elim¹
      (λ x≡y → f (elim P r x≡y) ≡
               elim Q (f ∘ r) x≡y)
      (f (elim P r (refl x))    ≡⟨ cong f $ elim-refl _ _ ⟩
       f (r x)                  ≡⟨ sym $ elim-refl _ _ ⟩∎
       elim Q (f ∘ r) (refl x)  ∎)
      x≡y

    elim-cong :
      (P : B → B → Type p) (f : A → B)
      (r : ∀ x → P x x) {x≡y : x ≡ y} →
      elim (λ {x y} _ → P x y) r (cong f x≡y) ≡
      elim (λ {x y} _ → P (f x) (f y)) (r ∘ f) x≡y
    elim-cong {x = x} P f r {x≡y} = elim¹
      (λ x≡y → elim (λ {x y} _ → P x y) r (cong f x≡y) ≡
               elim (λ {x y} _ → P (f x) (f y)) (r ∘ f) x≡y)
      (elim (λ {x y} _ → P x y) r (cong f (refl x))       ≡⟨ cong (elim (λ {x y} _ → P x y) _) $ cong-refl _ ⟩
       elim (λ {x y} _ → P x y) r (refl (f x))            ≡⟨ elim-refl _ _ ⟩
       r (f x)                                            ≡⟨ sym $ elim-refl _ _ ⟩∎
       elim (λ {x y} _ → P (f x) (f y)) (r ∘ f) (refl x)  ∎)
      x≡y

  subst-const : ∀ (x₁≡x₂ : x₁ ≡ x₂) {b} →
                subst (const B) x₁≡x₂ b ≡ b
  subst-const {B = B} x₁≡x₂ {b} =
    elim¹ (λ x₁≡x₂ → subst (const B) x₁≡x₂ b ≡ b)
          (subst-refl _ _)
          x₁≡x₂

  abstract

    -- One can express sym in terms of subst.

    sym-subst : sym x≡y ≡ subst (λ z → x ≡ z → z ≡ x) x≡y id x≡y
    sym-subst = elim
      (λ {x} x≡y → sym x≡y ≡ subst (λ z → x ≡ z → z ≡ x) x≡y id x≡y)
      (λ x →
         sym (refl x)                                      ≡⟨ sym-refl ⟩
         refl x                                            ≡⟨ cong (_$ refl x) $ sym $ subst-refl _ _ ⟩∎
         subst (λ z → x ≡ z → z ≡ x) (refl x) id (refl x)  ∎)
      _

    -- One can express trans in terms of subst (in several ways).

    trans-subst :
      {x≡y : x ≡ y} {y≡z : y ≡ z} →
      trans x≡y y≡z ≡ subst (x ≡_) y≡z x≡y
    trans-subst {z = z} = elim
      (λ {x y} x≡y → (y≡z : y ≡ z) → trans x≡y y≡z ≡ subst (x ≡_) y≡z x≡y)
      (λ y → elim
         (λ {y} y≡z → trans (refl y) y≡z ≡ subst (y ≡_) y≡z (refl y))
         (λ x →
            trans (refl x) (refl x)         ≡⟨ trans-refl-refl ⟩
            refl x                          ≡⟨ sym $ subst-refl _ _ ⟩∎
            subst (x ≡_) (refl x) (refl x)  ∎))
      _
      _

    subst-trans :
      (x≡y : x ≡ y) {y≡z : y ≡ z} →
      subst (_≡ z) (sym x≡y) y≡z ≡ trans x≡y y≡z
    subst-trans {y = y} {z} x≡y {y≡z} =
      elim₁ (λ x≡y → subst (λ x → x ≡ z) (sym x≡y) y≡z ≡
                     trans x≡y y≡z)
            (subst (λ x → x ≡ z) (sym (refl y)) y≡z  ≡⟨ cong (λ eq → subst (λ x → x ≡ z) eq _) sym-refl ⟩
             subst (λ x → x ≡ z) (refl y) y≡z        ≡⟨ subst-refl _ _ ⟩
             y≡z                                     ≡⟨ sym $ trans-reflˡ _ ⟩∎
             trans (refl y) y≡z                      ∎)
            x≡y

    subst-trans-sym :
      {y≡x : y ≡ x} {y≡z : y ≡ z} →
      subst (_≡ z) y≡x y≡z ≡ trans (sym y≡x) y≡z
    subst-trans-sym {z = z} {y≡x = y≡x} {y≡z = y≡z} =
      subst (_≡ z) y≡x y≡z              ≡⟨ cong (flip (subst (_≡ z)) _) $ sym $ sym-sym _ ⟩
      subst (_≡ z) (sym (sym y≡x)) y≡z  ≡⟨ subst-trans _ ⟩∎
      trans (sym y≡x) y≡z               ∎

    -- One can express subst in terms of elim.

    subst-elim :
      subst P x≡y p ≡ elim (λ {u v} _ → P u → P v) (λ _ → id) x≡y p
    subst-elim {P = P} = elim
      (λ x≡y → ∀ p →
         subst P x≡y p ≡ elim (λ {u v} _ → P u → P v) (λ _ → id) x≡y p)
      (λ x p →
         subst P (refl x) p                                  ≡⟨ subst-refl _ _ ⟩
         p                                                   ≡⟨ cong (_$ p) $ sym $ elim-refl _ _ ⟩∎
         elim (λ {u v} _ → P u → P v) (λ _ → id) (refl x) p  ∎)
      _
      _

    subst-∘ : (P : B → Type p) (f : A → B) (x≡y : x ≡ y) {p : P (f x)} →
              subst (P ∘ f) x≡y p ≡ subst P (cong f x≡y) p
    subst-∘ P f _ {p} = elim¹
      (λ x≡y → subst (P ∘ f) x≡y p ≡ subst P (cong f x≡y) p)
      (subst (P ∘ f) (refl _) p     ≡⟨ subst-refl _ _ ⟩
       p                            ≡⟨ sym $ subst-refl _ _ ⟩
       subst P (refl _) p           ≡⟨ cong (flip (subst _) _) $ sym $ cong-refl _ ⟩∎
       subst P (cong f (refl _)) p  ∎)
      _

    subst-↑ : (P : A → Type p) {p : ↑ ℓ (P x)} →
              subst (↑ ℓ ∘ P) x≡y p ≡ lift (subst P x≡y (lower p))
    subst-↑ {ℓ = ℓ} P {p} = elim¹
      (λ x≡y → subst (↑ ℓ ∘ P) x≡y p ≡ lift (subst P x≡y (lower p)))
      (subst (↑ ℓ ∘ P) (refl _) p         ≡⟨ subst-refl _ _ ⟩
       p                                  ≡⟨ cong lift $ sym $ subst-refl _ _ ⟩∎
       lift (subst P (refl _) (lower p))  ∎)
      _

    -- A fusion law for subst.

    subst-subst :
      (P : A → Type p) (x≡y : x ≡ y) (y≡z : y ≡ z) (p : P x) →
      subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
    subst-subst P x≡y y≡z p =
      elim (λ {x y} x≡y → ∀ {z} (y≡z : y ≡ z) p →
              subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p)
           (λ x y≡z p →
              subst P y≡z (subst P (refl x) p)  ≡⟨ cong (subst P _) $ subst-refl _ _ ⟩
              subst P y≡z p                     ≡⟨ cong (λ q → subst P q _) (sym $ trans-reflˡ _) ⟩∎
              subst P (trans (refl x) y≡z) p    ∎)
           x≡y y≡z p

    -- "Computation rules" for subst-subst.

    subst-subst-reflˡ :
      ∀ (P : A → Type p) {p} →
      subst-subst P (refl x) x≡y p ≡
      cong₂ (flip (subst P)) (subst-refl _ _) (sym $ trans-reflˡ x≡y)
    subst-subst-reflˡ P =
      cong (λ f → f _ _) $
        elim-refl (λ {x y} x≡y → ∀ {z} (y≡z : y ≡ z) p →
                     subst P y≡z (subst P x≡y p) ≡ _)
                  _

    subst-subst-refl-refl :
      ∀ (P : A → Type p) {p} →
      subst-subst P (refl x) (refl x) p ≡
      cong₂ (flip (subst P)) (subst-refl _ _) (sym trans-refl-refl)
    subst-subst-refl-refl {x = x} P {p} =
      subst-subst P (refl x) (refl x) p                              ≡⟨ subst-subst-reflˡ _ ⟩

      cong₂ (flip (subst P)) (subst-refl _ _)
                             (sym $ trans-reflˡ (refl x))            ≡⟨ cong (cong₂ (flip (subst P)) (subst-refl _ _) ∘ sym) $
                                                                             elim-refl _ _ ⟩∎
      cong₂ (flip (subst P)) (subst-refl _ _) (sym trans-refl-refl)  ∎

    -- Substitutivity and symmetry sometimes cancel each other out.

    subst-subst-sym :
      (P : A → Type p) (x≡y : x ≡ y) (p : P y) →
      subst P x≡y (subst P (sym x≡y) p) ≡ p
    subst-subst-sym P =
      elim¹
        (λ x≡y → ∀ p → subst P x≡y (subst P (sym x≡y) p) ≡ p)
        (λ p →
           subst P (refl _) (subst P (sym (refl _)) p)  ≡⟨ subst-refl _ _ ⟩
           subst P (sym (refl _)) p                     ≡⟨ cong (flip (subst P) _) sym-refl ⟩
           subst P (refl _) p                           ≡⟨ subst-refl _ _ ⟩∎
           p                                            ∎)

    subst-sym-subst :
      (P : A → Type p) {x≡y : x ≡ y} {p : P x} →
      subst P (sym x≡y) (subst P x≡y p) ≡ p
    subst-sym-subst P {x≡y = x≡y} {p = p} =
      elim¹
        (λ x≡y → ∀ p → subst P (sym x≡y) (subst P x≡y p) ≡ p)
        (λ p →
           subst P (sym (refl _)) (subst P (refl _) p)  ≡⟨ cong (flip (subst P) _) sym-refl ⟩
           subst P (refl _) (subst P (refl _) p)        ≡⟨ subst-refl _ _ ⟩
           subst P (refl _) p                           ≡⟨ subst-refl _ _ ⟩∎
           p                                            ∎)
        x≡y p

    -- Some "computation rules".

    subst-subst-sym-refl :
      (P : A → Type p) {p : P x} →
      subst-subst-sym P (refl x) p ≡
      trans (subst-refl _ _)
        (trans (cong (flip (subst P) _) sym-refl)
           (subst-refl _ _))
    subst-subst-sym-refl P {p = p} =
      cong (_$ _) $
      elim¹-refl
        (λ x≡y → ∀ p → subst P x≡y (subst P (sym x≡y) p) ≡ p)
        _

    subst-sym-subst-refl :
      (P : A → Type p) {p : P x} →
      subst-sym-subst P {x≡y = refl x} {p = p} ≡
      trans (cong (flip (subst P) _) sym-refl)
         (trans (subst-refl _ _) (subst-refl _ _))
    subst-sym-subst-refl P =
      cong (_$ _) $
      elim¹-refl
        (λ x≡y → ∀ p → subst P (sym x≡y) (subst P x≡y p) ≡ p)
        _

    -- Some corollaries and variants.

    trans-[trans-sym]- : (a≡b : a ≡ b) (c≡b : c ≡ b) →
                         trans (trans a≡b (sym c≡b)) c≡b ≡ a≡b
    trans-[trans-sym]- a≡b c≡b =
      trans (trans a≡b (sym c≡b)) c≡b                ≡⟨ trans-subst ⟩
      subst (_ ≡_) c≡b (trans a≡b (sym c≡b))         ≡⟨ cong (subst _ _) trans-subst ⟩
      subst (_ ≡_) c≡b (subst (_ ≡_) (sym c≡b) a≡b)  ≡⟨ subst-subst-sym _ _ _ ⟩∎
      a≡b                                            ∎

    trans-[trans]-sym : (a≡b : a ≡ b) (b≡c : b ≡ c) →
                        trans (trans a≡b b≡c) (sym b≡c) ≡ a≡b
    trans-[trans]-sym a≡b b≡c =
      trans (trans a≡b b≡c)             (sym b≡c)  ≡⟨ sym $ cong (λ eq → trans (trans _ eq) (sym b≡c)) $ sym-sym _ ⟩
      trans (trans a≡b (sym (sym b≡c))) (sym b≡c)  ≡⟨ trans-[trans-sym]- _ _ ⟩∎
      a≡b                                          ∎

    trans--[trans-sym] : (b≡a : b ≡ a) (b≡c : b ≡ c) →
                         trans b≡a (trans (sym b≡a) b≡c) ≡ b≡c
    trans--[trans-sym] b≡a b≡c =
      trans b≡a (trans (sym b≡a) b≡c)  ≡⟨ sym $ trans-assoc _ _ _ ⟩
      trans (trans b≡a (sym b≡a)) b≡c  ≡⟨ cong (flip trans _) $ trans-symʳ _ ⟩
      trans (refl _) b≡c               ≡⟨ trans-reflˡ _ ⟩∎
      b≡c                              ∎

    trans-sym-[trans] : (a≡b : a ≡ b) (b≡c : b ≡ c) →
                        trans (sym a≡b) (trans a≡b b≡c) ≡ b≡c
    trans-sym-[trans] a≡b b≡c =
      trans (sym a≡b) (trans a≡b b≡c)              ≡⟨ cong (λ p → trans (sym _) (trans p _)) $ sym $ sym-sym _ ⟩
      trans (sym a≡b) (trans (sym (sym a≡b)) b≡c)  ≡⟨ trans--[trans-sym] _ _ ⟩∎
      b≡c                                          ∎

    -- The lemmas subst-refl and subst-const can cancel each other
    -- out.

    subst-refl-subst-const :
      trans (sym $ subst-refl (λ _ → B) b) (subst-const (refl x)) ≡
      refl b
    subst-refl-subst-const {b = b} {x = x} =
      trans (sym $ subst-refl _ _)
            (elim¹ (λ eq → subst (λ _ → _) eq b ≡ b)
                   (subst-refl _ _)
                   (refl _))                          ≡⟨ cong (trans _) (elim¹-refl _ _) ⟩
      trans (sym $ subst-refl _ _) (subst-refl _ _)   ≡⟨ trans-symˡ _ ⟩∎
      refl _                                          ∎

    -- In non-dependent cases one can express dcong using subst-const
    -- and cong.
    --
    -- This is (similar to) Lemma 2.3.8 in the HoTT book.

    dcong-subst-const-cong :
      (f : A → B) (x≡y : x ≡ y) →
      dcong f x≡y ≡
      (subst (const B) x≡y (f x)  ≡⟨ subst-const _ ⟩
       f x                        ≡⟨ cong f x≡y ⟩∎
       f y                        ∎)
    dcong-subst-const-cong f = elim
      (λ {x y} x≡y → dcong f x≡y ≡
                     trans (subst-const x≡y) (cong f x≡y))
      (λ x →
        dcong f (refl x)                         ≡⟨ dcong-refl _ ⟩
        subst-refl _ _                           ≡⟨ sym $ trans-reflʳ _ ⟩
        trans (subst-refl _ _) (refl (f x))      ≡⟨ cong₂ trans
                                                          (sym $ elim¹-refl _ _)
                                                          (sym $ cong-refl _) ⟩∎
        trans (subst-const _) (cong f (refl x))  ∎)

    -- A corollary.

    dcong≡→cong≡ :
      {x≡y : x ≡ y} {fx≡fy : f x ≡ f y} →
      dcong f x≡y ≡ trans (subst-const _) fx≡fy →
      cong f x≡y ≡ fx≡fy
    dcong≡→cong≡ {f = f} {x≡y = x≡y} {fx≡fy} hyp =
      cong f x≡y                                                        ≡⟨ sym $ trans-sym-[trans] _ _ ⟩
      trans (sym $ subst-const _) (trans (subst-const _) $ cong f x≡y)  ≡⟨ cong (trans (sym $ subst-const _)) $ sym $
                                                                           dcong-subst-const-cong _ _ ⟩
      trans (sym $ subst-const _) (dcong f x≡y)                         ≡⟨ cong (trans (sym $ subst-const _)) hyp ⟩
      trans (sym $ subst-const _) (trans (subst-const _) fx≡fy)         ≡⟨ trans-sym-[trans] _ _ ⟩∎
      fx≡fy                                                             ∎

    -- A kind of symmetry for "dependent paths".

    dsym :
      {x≡y : x ≡ y} {P : A → Type p} {p : P x} {q : P y} →
      subst P x≡y p ≡ q → subst P (sym x≡y) q ≡ p
    dsym {x≡y = x≡y} {P = P} p≡q = elim
      (λ {x y} x≡y →
         ∀ {p : P x} {q : P y} →
         subst P x≡y p ≡ q →
         subst P (sym x≡y) q ≡ p)
      (λ _ {p q} p≡q →
         subst P (sym (refl _)) q  ≡⟨ cong (flip (subst P) _) sym-refl ⟩
         subst P (refl _) q        ≡⟨ subst-refl _ _ ⟩
         q                         ≡⟨ sym p≡q ⟩
         subst P (refl _) p        ≡⟨ subst-refl _ _ ⟩∎
         p                         ∎)
      x≡y
      p≡q

    -- A "computation rule" for dsym.

    dsym-subst-refl :
      {P : A → Type p} {p : P x} →
      dsym (subst-refl P p) ≡
      trans (cong (flip (subst P) _) sym-refl) (subst-refl _ _)
    dsym-subst-refl {P = P} =
      dsym (subst-refl _ _)                                      ≡⟨ cong (λ f → f (subst-refl _ _)) $
                                                                    elim-refl
                                                                      (λ {x y} x≡y →
                                                                         ∀ {p : P x} {q : P y} →
                                                                         subst P x≡y p ≡ q →
                                                                         subst P (sym x≡y) q ≡ p)
                                                                      _ ⟩
      trans (cong (flip (subst P) _) sym-refl)
        (trans (subst-refl _ _)
           (trans (sym (subst-refl P _)) (subst-refl _ _)))      ≡⟨ cong (trans (cong (flip (subst P) _) sym-refl)) $ trans--[trans-sym] _ _ ⟩∎

      trans (cong (flip (subst P) _) sym-refl) (subst-refl _ _)  ∎

    -- A kind of transitivity for "dependent paths".
    --
    -- This lemma is suggested in the HoTT book (first edition,
    -- Exercise 6.1).

    dtrans :
      {x≡y : x ≡ y} {y≡z : y ≡ z}
      (P : A → Type p) {p : P x} {q : P y} {r : P z} →
      subst P x≡y p ≡ q →
      subst P y≡z q ≡ r →
      subst P (trans x≡y y≡z) p ≡ r
    dtrans {x≡y = x≡y} {y≡z = y≡z} P {p = p} {q = q} {r = r} p≡q q≡r =
      subst P (trans x≡y y≡z) p    ≡⟨ sym $ subst-subst _ _ _ _ ⟩
      subst P y≡z (subst P x≡y p)  ≡⟨ cong (subst P y≡z) p≡q ⟩
      subst P y≡z q                ≡⟨ q≡r ⟩∎
      r                            ∎

    -- "Computation rules" for dtrans.

    dtrans-reflˡ :
      {x≡y : x ≡ y} {y≡z : y ≡ z}
      {P : A → Type p} {p : P x} {r : P z}
      {p≡r : subst P y≡z (subst P x≡y p) ≡ r} →
      dtrans P (refl _) p≡r ≡
      trans (sym $ subst-subst _ _ _ _) p≡r
    dtrans-reflˡ {y≡z = y≡z} {P = P} {p≡r = p≡r} =
      trans (sym $ subst-subst _ _ _ _)
        (trans (cong (subst P y≡z) (refl _)) p≡r)             ≡⟨ cong (trans (sym $ subst-subst _ _ _ _) ∘ flip trans _) $ cong-refl _ ⟩

      trans (sym $ subst-subst _ _ _ _) (trans (refl _) p≡r)  ≡⟨ cong (trans (sym $ subst-subst _ _ _ _)) $ trans-reflˡ _ ⟩∎

      trans (sym $ subst-subst _ _ _ _) p≡r                   ∎

    dtrans-reflʳ :
      {x≡y : x ≡ y} {y≡z : y ≡ z}
      {P : A → Type p} {p : P x} {q : P y}
      {p≡q : subst P x≡y p ≡ q} →
      dtrans P p≡q (refl (subst P y≡z q)) ≡
      trans (sym $ subst-subst _ _ _ _) (cong (subst P y≡z) p≡q)
    dtrans-reflʳ {x≡y = x≡y} {y≡z = y≡z} {P = P} {p≡q = p≡q} =
      trans (sym $ subst-subst _ _ _ _)
        (trans (cong (subst P y≡z) p≡q) (refl _))                 ≡⟨ cong (trans _) $ trans-reflʳ _ ⟩∎

      trans (sym $ subst-subst _ _ _ _) (cong (subst P y≡z) p≡q)  ∎

    dtrans-subst-reflˡ :
      {x≡y : x ≡ y} {P : A → Type p} {p : P x} {q : P y}
      {p≡q : subst P x≡y p ≡ q} →
      dtrans P (subst-refl _ _) p≡q ≡
      trans (cong (flip (subst P) _) (trans-reflˡ _)) p≡q
    dtrans-subst-reflˡ {x≡y = x≡y} {P = P} {p≡q = p≡q} =
      trans (sym $ subst-subst _ _ _ _)
        (trans (cong (subst P x≡y) (subst-refl _ _)) p≡q)              ≡⟨ cong (λ eq → trans (sym eq)
                                                                                         (trans (cong (subst P x≡y) (subst-refl _ _)) _)) $
                                                                          subst-subst-reflˡ _ ⟩
      trans (sym $ trans (cong (subst P _) (subst-refl _ _))
                     (cong (flip (subst P) _) (sym $ trans-reflˡ _)))
        (trans (cong (subst P _) (subst-refl _ _)) p≡q)                ≡⟨ cong (flip trans _) $ sym-trans _ _ ⟩

      trans (trans
               (sym $ cong (flip (subst P) _) (sym $ trans-reflˡ _))
               (sym $ cong (subst P _) (subst-refl _ _)))
        (trans (cong (subst P _) (subst-refl _ _)) p≡q)                ≡⟨ trans-assoc _ _ _ ⟩

      trans (sym $ cong (flip (subst P) _) (sym $ trans-reflˡ _))
        (trans (sym $ cong (subst P _) (subst-refl _ _))
           (trans (cong (subst P _) (subst-refl _ _)) p≡q))            ≡⟨ cong (trans _) $ trans-sym-[trans] _ _ ⟩

      trans (sym $ cong (flip (subst P) _) (sym $ trans-reflˡ _)) p≡q  ≡⟨ cong (flip trans _ ∘ sym) $ cong-sym _ _ ⟩

      trans (sym $ sym $ cong (flip (subst P) _) (trans-reflˡ _)) p≡q  ≡⟨ cong (flip trans _) $ sym-sym _ ⟩∎

      trans (cong (flip (subst P) _) (trans-reflˡ _)) p≡q              ∎

    dtrans-subst-reflʳ :
      {x≡y : x ≡ y} {P : A → Type p} {p : P x} {q : P y}
      {p≡q : subst P x≡y p ≡ q} →
      dtrans P p≡q (subst-refl _ _) ≡
      trans (cong (flip (subst P) _) (trans-reflʳ _)) p≡q
    dtrans-subst-reflʳ {x≡y = x≡y} {P = P} {p = p} {p≡q = p≡q} = elim¹
      (λ x≡y → ∀ {q} (p≡q : subst P x≡y p ≡ q) →
               dtrans P p≡q (subst-refl _ _) ≡
               trans (cong (flip (subst P) _) (trans-reflʳ _)) p≡q)
      (λ p≡q →
         trans (sym $ subst-subst _ _ _ _)
           (trans (cong (subst P (refl _)) p≡q) (subst-refl _ _))         ≡⟨ cong (λ eq → trans (sym eq) (trans (cong (subst P (refl _)) _)
                                                                                                            (subst-refl _ _))) $
                                                                             subst-subst-refl-refl _ ⟩
         trans (sym $ cong₂ (flip (subst P)) (subst-refl _ _) $
                        sym trans-refl-refl)
           (trans (cong (subst P (refl _)) p≡q) (subst-refl _ _))         ≡⟨⟩

         trans (sym $ trans (cong (subst P _) (subst-refl _ _))
                        (cong (flip (subst P) _) (sym trans-refl-refl)))
           (trans (cong (subst P (refl _)) p≡q) (subst-refl _ _))         ≡⟨ cong (flip trans _) $ sym-trans _ _ ⟩

         trans (trans (sym $ cong (flip (subst P) _)
                               (sym trans-refl-refl))
                  (sym $ cong (subst P _) (subst-refl _ _)))
           (trans (cong (subst P (refl _)) p≡q) (subst-refl _ _))         ≡⟨ lemma₁ p≡q ⟩

         trans (cong (flip (subst P) _) trans-refl-refl) p≡q              ≡⟨ cong (λ eq → trans (cong (flip (subst P) _) eq) _) $ sym $
                                                                             elim-refl _ _ ⟩∎
         trans (cong (flip (subst P) _) (trans-reflʳ _)) p≡q              ∎)
      x≡y
      p≡q
      where
      lemma₂ :
        cong (subst P (refl _)) (subst-refl P p) ≡
        cong id (subst-refl P (subst P (refl _) p))
      lemma₂ =
        cong (subst P (refl _)) (subst-refl P p)     ≡⟨ cong-≡id-≡-≡id (subst-refl P) ⟩
        subst-refl P (subst P (refl _) p)            ≡⟨ cong-id _ ⟩∎
        cong id (subst-refl P (subst P (refl _) p))  ∎

      lemma₁ : ∀ {q} (p≡q : subst P (refl _) p ≡ q) → _
      lemma₁ = elim¹
        (λ p≡q →
           trans (trans (sym $ cong (flip (subst P) _)
                                (sym trans-refl-refl))
                   (sym $ cong (subst P (refl _)) (subst-refl _ _)))
            (trans (cong (subst P (refl _)) p≡q) (subst-refl _ _)) ≡
          trans (cong (flip (subst P) _) trans-refl-refl) p≡q)
        (trans (trans (sym $ cong (flip (subst P) _)
                               (sym trans-refl-refl))
                  (sym $ cong (subst P (refl _)) (subst-refl _ _)))
           (trans (cong (subst P (refl _)) (refl _)) (subst-refl _ _))  ≡⟨ cong (λ eq → trans (trans (sym $ cong (flip (subst P) _)
                                                                                                              (sym trans-refl-refl))
                                                                                                 (sym $ cong (subst P _) (subst-refl _ _)))
                                                                                          (trans eq (subst-refl _ _))) $
                                                                           cong-refl (subst P (refl _)) ⟩
         trans (trans (sym $ cong (flip (subst P) _)
                               (sym trans-refl-refl))
                  (sym $ cong (subst P (refl _)) (subst-refl _ _)))
           (trans (refl _) (subst-refl _ _))                            ≡⟨ cong (trans _) $ trans-reflˡ _ ⟩

         trans (trans (sym $ cong (flip (subst P) _)
                               (sym trans-refl-refl))
                  (sym $ cong (subst P (refl _)) (subst-refl _ _)))
           (subst-refl _ _)                                             ≡⟨ cong (λ eq → trans (trans (sym $ cong (flip (subst P) _) _) (sym eq))
                                                                                                 (subst-refl _ _))
                                                                           lemma₂ ⟩
         trans (trans (sym $ cong (flip (subst P) _)
                               (sym trans-refl-refl))
                  (sym $ cong id (subst-refl _ _)))
           (subst-refl _ _)                                             ≡⟨ cong (λ eq → trans (trans (sym $ cong (flip (subst P) _)
                                                                                                              (sym trans-refl-refl)) (sym eq))
                                                                                                 (subst-refl _ _)) $ sym $
                                                                           cong-id _ ⟩
         trans (trans (sym $ cong (flip (subst P) _)
                               (sym trans-refl-refl))
                  (sym $ subst-refl _ _))
           (subst-refl _ _)                                             ≡⟨ trans-[trans-sym]- _ _ ⟩

         sym (cong (flip (subst P) _) (sym trans-refl-refl))            ≡⟨ cong sym $ cong-sym _ _ ⟩

         sym (sym (cong (flip (subst P) _) trans-refl-refl))            ≡⟨ sym-sym _ ⟩

         cong (flip (subst P) _) trans-refl-refl                        ≡⟨ sym $ trans-reflʳ _ ⟩∎

         trans (cong (flip (subst P) _) trans-refl-refl) (refl _)       ∎)

    -- A lemma relating dcong, trans and dtrans.
    --
    -- This lemma is suggested in the HoTT book (first edition,
    -- Exercise 6.1).

    dcong-trans :
      {f : (x : A) → P x} {x≡y : x ≡ y} {y≡z : y ≡ z} →
      dcong f (trans x≡y y≡z) ≡ dtrans P (dcong f x≡y) (dcong f y≡z)
    dcong-trans {P = P} {f = f} {x≡y = x≡y} {y≡z = y≡z} = elim₁
      (λ x≡y → dcong f (trans x≡y y≡z) ≡ dtrans P (dcong f x≡y) (dcong f y≡z))
      (dcong f (trans (refl _) y≡z)                                   ≡⟨ elim₁ (λ {p} eq → dcong f p ≡
                                                                                           trans (cong (flip (subst P) _) eq) (dcong f y≡z)) (
           dcong f y≡z                                                     ≡⟨ sym $ trans-reflˡ _ ⟩
           trans (refl _) (dcong f y≡z)                                    ≡⟨ cong (flip trans _) $ sym $ cong-refl _ ⟩∎
           trans (cong (flip (subst P) _) (refl _)) (dcong f y≡z)          ∎)
                                                                           (trans-reflˡ _) ⟩
       trans (cong (flip (subst P) _) (trans-reflˡ _)) (dcong f y≡z)  ≡⟨ sym dtrans-subst-reflˡ ⟩
       dtrans P (subst-refl _ _) (dcong f y≡z)                        ≡⟨ cong (λ eq → dtrans P eq (dcong f y≡z)) $ sym $ dcong-refl _ ⟩∎
       dtrans P (dcong f (refl _)) (dcong f y≡z)                      ∎)
      x≡y

  -- An equality between pairs can be proved using a pair of
  -- equalities.

  Σ-≡,≡→≡ : {B : A → Type b} {p₁ p₂ : Σ A B} →
            (p : proj₁ p₁ ≡ proj₁ p₂) →
            subst B p (proj₂ p₁) ≡ proj₂ p₂ →
            p₁ ≡ p₂
  Σ-≡,≡→≡ {B = B} p q = elim
    (λ {x₁ y₁} (p : x₁ ≡ y₁) → ∀ {x₂ y₂} →
       subst B p x₂ ≡ y₂ → (x₁ , x₂) ≡ (y₁ , y₂))
    (λ z₁ {x₂} {y₂} x₂≡y₂ → cong (_,_ z₁) (
       x₂                    ≡⟨ sym $ subst-refl _ _ ⟩
       subst B (refl z₁) x₂  ≡⟨ x₂≡y₂ ⟩∎
       y₂                    ∎))
    p q

  -- The uncurried form of Σ-≡,≡→≡ has an inverse, Σ-≡,≡←≡. (For a
  -- proof, see Bijection.Σ-≡,≡↔≡.)

  Σ-≡,≡←≡ : {B : A → Type b} {p₁ p₂ : Σ A B} →
            p₁ ≡ p₂ →
            ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
              subst B p (proj₂ p₁) ≡ proj₂ p₂
  Σ-≡,≡←≡ {A = A} {B = B} = elim
    (λ {p₁ p₂ : Σ A B} _ →
       ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) → subst B p (proj₂ p₁) ≡ proj₂ p₂)
    (λ p → refl _ , subst-refl _ _)

  abstract

    -- "Evaluation rules" for Σ-≡,≡→≡.

    Σ-≡,≡→≡-reflˡ :
      ∀ {B : A → Type b} {y₁ y₂} →
      (y₁≡y₂ : subst B (refl x) y₁ ≡ y₂) →
      Σ-≡,≡→≡ (refl x) y₁≡y₂ ≡
      cong (x ,_) (trans (sym $ subst-refl _ _) y₁≡y₂)
    Σ-≡,≡→≡-reflˡ {B = B} y₁≡y₂ =
      cong (λ f → f y₁≡y₂) $
        elim-refl (λ {x₁ y₁} (p : x₁ ≡ y₁) → ∀ {x₂ y₂} →
                     subst B p x₂ ≡ y₂ → (x₁ , x₂) ≡ (y₁ , y₂))
                  _

    Σ-≡,≡→≡-refl-refl :
      ∀ {B : A → Type b} {y} →
      Σ-≡,≡→≡ (refl x) (refl (subst B (refl x) y)) ≡
      cong (x ,_) (sym (subst-refl _ _))
    Σ-≡,≡→≡-refl-refl {x = x} =
      Σ-≡,≡→≡ (refl x) (refl _)                            ≡⟨ Σ-≡,≡→≡-reflˡ (refl _) ⟩
      cong (x ,_) (trans (sym $ subst-refl _ _) (refl _))  ≡⟨ cong (cong (x ,_)) (trans-reflʳ _) ⟩∎
      cong (x ,_) (sym (subst-refl _ _))                   ∎

    Σ-≡,≡→≡-refl-subst-refl :
      {B : A → Type b} {p : Σ A B} →
      Σ-≡,≡→≡ (refl _) (subst-refl _ _) ≡ refl p
    Σ-≡,≡→≡-refl-subst-refl =
      Σ-≡,≡→≡ (refl _) (subst-refl _ _)                            ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩
      cong (_ ,_) (trans (sym $ subst-refl _ _) (subst-refl _ _))  ≡⟨ cong (cong _) (trans-symˡ _) ⟩
      cong (_ ,_) (refl _)                                         ≡⟨ cong-refl _ ⟩∎
      refl _                                                       ∎

    Σ-≡,≡→≡-refl-subst-const :
      {p : A × B} →
      Σ-≡,≡→≡ (refl _) (subst-const _) ≡ refl p
    Σ-≡,≡→≡-refl-subst-const =
      Σ-≡,≡→≡ (refl _) (subst-const _)                            ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩
      cong (_ ,_) (trans (sym $ subst-refl _ _) (subst-const _))  ≡⟨ cong (cong _) subst-refl-subst-const ⟩
      cong (_ ,_) (refl _)                                        ≡⟨ cong-refl _ ⟩∎
      refl _                                                      ∎

    -- "Evaluation rule" for Σ-≡,≡←≡.

    Σ-≡,≡←≡-refl :
      {B : A → Type b} {p : Σ A B} →
      Σ-≡,≡←≡ (refl p) ≡ (refl _ , subst-refl _ _)
    Σ-≡,≡←≡-refl = elim-refl _ _

    -- Proof transformation rules for Σ-≡,≡→≡.

    proj₁-Σ-≡,≡→≡ :
      ∀ {B : A → Type b} {y₁ y₂}
      (x₁≡x₂ : x₁ ≡ x₂) (y₁≡y₂ : subst B x₁≡x₂ y₁ ≡ y₂) →
      cong proj₁ (Σ-≡,≡→≡ x₁≡x₂ y₁≡y₂) ≡ x₁≡x₂
    proj₁-Σ-≡,≡→≡ {B = B} {y₁ = y₁} x₁≡x₂ y₁≡y₂ = elim¹
      (λ x₁≡x₂ → ∀ {y₂} (y₁≡y₂ : subst B x₁≡x₂ y₁ ≡ y₂) →
         cong proj₁ (Σ-≡,≡→≡ x₁≡x₂ y₁≡y₂) ≡ x₁≡x₂)
      (λ y₁≡y₂ →
         cong proj₁ (Σ-≡,≡→≡ (refl _) y₁≡y₂)                             ≡⟨ cong (cong proj₁) $ Σ-≡,≡→≡-reflˡ _ ⟩
         cong proj₁ (cong (_,_ _) (trans (sym $ subst-refl _ _) y₁≡y₂))  ≡⟨ cong-∘ _ _ _ ⟩
         cong (const _) (trans (sym $ subst-refl _ _) y₁≡y₂)             ≡⟨ cong-const _ ⟩∎
         refl _                                                          ∎)
      x₁≡x₂ y₁≡y₂

    Σ-≡,≡→≡-cong :
      {B : A → Type b} {p₁ p₂ : Σ A B}
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
      {B : A → Type b} {p₁ p₂ p₃ : Σ A B} →
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
                     sym (cong (subst B _) (subst-refl _ _))          ≡⟨ sym $ trans-sym-[trans] _ _ ⟩

                     trans (sym $ cong (flip (subst B) _)
                                       trans-refl-refl)
                           (trans (cong (flip (subst B) _)
                                        trans-refl-refl)
                                  (sym (cong (subst B _)
                                             (subst-refl _ _))))      ≡⟨ cong (flip trans _) $ sym $ cong-sym _ _ ⟩∎

                     trans (cong (flip (subst B) _)
                                 (sym trans-refl-refl))
                           (trans (cong (flip (subst B) _)
                                        trans-refl-refl)
                                  (sym (cong (subst B _)
                                             (subst-refl _ _))))      ∎

                   lemma₂ =
                     trans (cong (flip (subst B) _) trans-refl-refl)
                           (sym (cong (subst B _) (subst-refl _ _)))     ≡⟨ cong (λ e → trans (cong (flip (subst B) _) e)
                                                                                              (sym $ cong (subst B _) (subst-refl _ _))) $
                                                                                 sym $ sym-sym _ ⟩
                     trans (cong (flip (subst B) _)
                                 (sym $ sym trans-refl-refl))
                           (sym (cong (subst B _) (subst-refl _ _)))     ≡⟨ cong (flip trans _) $ cong-sym _ _ ⟩

                     trans (sym (cong (flip (subst B) _)
                                      (sym trans-refl-refl)))
                           (sym (cong (subst B _) (subst-refl _ _)))     ≡⟨ sym $ sym-trans _ _ ⟩

                     sym (trans (cong (subst B _) (subst-refl _ _))
                                (cong (flip (subst B) _)
                                      (sym trans-refl-refl)))            ≡⟨⟩

                     sym (cong₂ (flip (subst B)) (subst-refl _ _)
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

               trans (cong (_ ,_) (sym (subst-refl _ _)))
                     (cong (_ ,_) (sym (subst-refl B _)))                 ≡⟨ sym $ cong-trans _ _ _ ⟩

               cong (_ ,_) (trans (sym (subst-refl _ _))
                                  (sym (subst-refl _ _)))                 ≡⟨ cong (cong (_ ,_) ∘ trans (sym (subst-refl _ _)) ∘ sym) $ sym $
                                                                                  cong-≡id-≡-≡id (subst-refl B) ⟩
               cong (_ ,_)
                    (trans (sym (subst-refl _ _))
                           (sym (cong (subst B _) (subst-refl _ _))))     ≡⟨ sym $ Σ-≡,≡→≡-reflˡ _ ⟩

               Σ-≡,≡→≡ (refl _)
                       (sym (cong (subst B _) (subst-refl _ _)))          ≡⟨ cong (Σ-≡,≡→≡ _) lemma₁ ⟩

               Σ-≡,≡→≡ (refl _)
                 (trans (cong (flip (subst B) _) (sym trans-refl-refl))
                    (trans (cong (flip (subst B) _) trans-refl-refl)
                       (sym (cong (subst B _) (subst-refl _ _)))))        ≡⟨ sym $ Σ-≡,≡→≡-cong _ (refl _) ⟩

               Σ-≡,≡→≡ (trans (refl _) (refl _))
                       (trans (cong (flip (subst B) _) trans-refl-refl)
                              (sym (cong (subst B _) (subst-refl _ _))))  ≡⟨ cong (Σ-≡,≡→≡ (trans (refl _) (refl _))) lemma₂ ⟩∎

               Σ-≡,≡→≡ (trans (refl _) (refl _))
                       (trans (sym $ subst-subst _ _ _ _)
                              (trans (cong (subst _ _) (refl _))
                                     (refl _)))                           ∎))))
      q₂₃ q₁₂ r₁₂ r₂₃

    Σ-≡,≡→≡-subst-const :
      {p₁ p₂ : A × B} →
      (p : proj₁ p₁ ≡ proj₁ p₂) (q : proj₂ p₁ ≡ proj₂ p₂) →
      Σ-≡,≡→≡ p (trans (subst-const _) q) ≡ cong₂ _,_ p q
    Σ-≡,≡→≡-subst-const p q = elim
      (λ {x₁ y₁} (p : x₁ ≡ y₁) →
         Σ-≡,≡→≡ p (trans (subst-const _) q) ≡ cong₂ _,_ p q)
      (λ x →
         let lemma =
               trans (sym $ subst-refl _ _) (trans (subst-const _) q)  ≡⟨ sym $ trans-assoc _ _ _ ⟩
               trans (trans (sym $ subst-refl _ _) (subst-const _)) q  ≡⟨ cong₂ trans subst-refl-subst-const (refl _) ⟩
               trans (refl _) q                                        ≡⟨ trans-reflˡ _ ⟩∎
               q                                                       ∎ in

         Σ-≡,≡→≡ (refl x) (trans (subst-const _) q)     ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩
         cong (x ,_) (trans (sym $ subst-refl _ _)
                            (trans (subst-const _) q))  ≡⟨ cong (cong (x ,_)) lemma ⟩
         cong (x ,_) q                                  ≡⟨ sym $ cong₂-reflˡ _,_ ⟩∎
         cong₂ _,_ (refl x) q                           ∎)
      p

    Σ-≡,≡→≡-subst-const-refl :
      Σ-≡,≡→≡ x₁≡x₂ (subst-const _) ≡ cong₂ _,_ x₁≡x₂ (refl y)
    Σ-≡,≡→≡-subst-const-refl {x₁≡x₂ = x₁≡x₂} {y = y} =
      Σ-≡,≡→≡ x₁≡x₂ (subst-const _)                   ≡⟨ cong (Σ-≡,≡→≡ x₁≡x₂) $ sym $ trans-reflʳ _ ⟩
      Σ-≡,≡→≡ x₁≡x₂ (trans (subst-const _) (refl _))  ≡⟨ Σ-≡,≡→≡-subst-const _ _ ⟩∎
      cong₂ _,_ x₁≡x₂ (refl y)                        ∎

    -- Proof simplification rule for Σ-≡,≡←≡.

    proj₁-Σ-≡,≡←≡ :
      {B : A → Type b} {p₁ p₂ : Σ A B}
      (p₁≡p₂ : p₁ ≡ p₂) →
      proj₁ (Σ-≡,≡←≡ p₁≡p₂) ≡ cong proj₁ p₁≡p₂
    proj₁-Σ-≡,≡←≡ = elim
      (λ p₁≡p₂ → proj₁ (Σ-≡,≡←≡ p₁≡p₂) ≡ cong proj₁ p₁≡p₂)
      (λ p →
         proj₁ (Σ-≡,≡←≡ (refl p))  ≡⟨ cong proj₁ $ Σ-≡,≡←≡-refl ⟩
         refl (proj₁ p)            ≡⟨ sym $ cong-refl _ ⟩∎
         cong proj₁ (refl p)       ∎)

  -- A binary variant of subst.

  subst₂ : ∀ {B : A → Type b} (P : Σ A B → Type p) {x₁ x₂ y₁ y₂} →
           (x₁≡x₂ : x₁ ≡ x₂) → subst B x₁≡x₂ y₁ ≡ y₂ →
           P (x₁ , y₁) → P (x₂ , y₂)
  subst₂ P x₁≡x₂ y₁≡y₂ = subst P (Σ-≡,≡→≡ x₁≡x₂ y₁≡y₂)

  abstract

    -- "Evaluation rule" for subst₂.

    subst₂-refl-refl :
      ∀ {B : A → Type b} (P : Σ A B → Type p) {y p} →
      subst₂ P (refl _) (refl _) p ≡
      subst (curry P x) (sym $ subst-refl B y) p
    subst₂-refl-refl {x = x} P {p = p} =
      subst P (Σ-≡,≡→≡ (refl _) (refl _)) p           ≡⟨ cong (λ eq₁ → subst P eq₁ _) Σ-≡,≡→≡-refl-refl ⟩
      subst P (cong (x ,_) (sym (subst-refl _ _))) p  ≡⟨ sym $ subst-∘ _ _ _ ⟩∎
      subst (curry P x) (sym $ subst-refl _ _) p      ∎

    -- The subst function can be "pushed" inside pairs.

    push-subst-pair :
      ∀ (B : A → Type b) (C : Σ A B → Type c) {p} →
      subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
      (subst B y≡z (proj₁ p) , subst₂ C y≡z (refl _) (proj₂ p))
    push-subst-pair {y≡z = y≡z} B C {p} = elim¹
      (λ y≡z →
         subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
         (subst B y≡z (proj₁ p) , subst₂ C y≡z (refl _) (proj₂ p)))
      (subst (λ x → Σ (B x) (curry C x)) (refl _) p  ≡⟨ subst-refl _ _ ⟩
       p                                             ≡⟨ Σ-≡,≡→≡ (sym (subst-refl _ _)) (sym (subst₂-refl-refl _)) ⟩∎
       (subst B (refl _) (proj₁ p) ,
        subst₂ C (refl _) (refl _) (proj₂ p))        ∎)
      y≡z

    -- A proof transformation rule for push-subst-pair.

    proj₁-push-subst-pair-refl :
      ∀ {A : Type a} {y : A} (B : A → Type b) (C : Σ A B → Type c) {p} →
      cong proj₁ (push-subst-pair {y≡z = refl y} B C {p = p}) ≡
      trans (cong proj₁ (subst-refl _ _)) (sym $ subst-refl _ _)
    proj₁-push-subst-pair-refl B C =
      cong proj₁ (push-subst-pair _ _)                                   ≡⟨ cong (cong proj₁) $
                                                                            elim¹-refl
                                                                              (λ y≡z →
                                                                                 subst (λ x → Σ (B x) (curry C x)) y≡z _ ≡
                                                                                 (subst B y≡z _ , subst₂ C y≡z (refl _) _))
                                                                              _ ⟩
      cong proj₁
        (trans (subst-refl _ _)
           (Σ-≡,≡→≡ (sym $ subst-refl _ _) (sym (subst₂-refl-refl _))))  ≡⟨ cong-trans _ _ _ ⟩

      trans (cong proj₁ (subst-refl _ _))
        (cong proj₁
           (Σ-≡,≡→≡ (sym $ subst-refl _ _) (sym (subst₂-refl-refl _))))  ≡⟨ cong (trans _) $
                                                                            proj₁-Σ-≡,≡→≡ _ _ ⟩∎
      trans (cong proj₁ (subst-refl _ _)) (sym $ subst-refl _ _)         ∎

    -- Corollaries of push-subst-pair.

    push-subst-pair′ :
      ∀ (B : A → Type b) (C : Σ A B → Type c) {p p₁} →
      (p₁≡p₁ : subst B y≡z (proj₁ p) ≡ p₁) →
      subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
      (p₁ , subst₂ C y≡z p₁≡p₁ (proj₂ p))
    push-subst-pair′ {y≡z = y≡z} B C {p} =
      elim¹ (λ {p₁} p₁≡p₁ →
               subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
               (p₁ , subst₂ C y≡z p₁≡p₁ (proj₂ p)))
            (push-subst-pair _ _)

    push-subst-pair-× :
      ∀ {y≡z : y ≡ z} (B : Type b) (C : A × B → Type c) {p} →
      subst (λ x → Σ B (curry C x)) y≡z p ≡
      (proj₁ p , subst (λ x → C (x , proj₁ p)) y≡z (proj₂ p))
    push-subst-pair-× {y≡z = y≡z} B C {p} =
      subst (λ x → Σ B (curry C x)) y≡z p                       ≡⟨ push-subst-pair′ _ C (subst-const _) ⟩
      (proj₁ p , subst₂ C y≡z (subst-const _) (proj₂ p))        ≡⟨ cong (_ ,_) $
                                                                   elim¹
                                                                     (λ y≡z → subst₂ C y≡z (subst-const y≡z) (proj₂ p) ≡
                                                                              subst (λ x → C (x , proj₁ p)) y≡z (proj₂ p))
                                                                     (
          subst₂ C (refl _) (subst-const _) (proj₂ p)                 ≡⟨⟩
          subst C (Σ-≡,≡→≡ (refl _) (subst-const _)) (proj₂ p)        ≡⟨ cong (λ eq → subst C eq _) Σ-≡,≡→≡-refl-subst-const ⟩
          subst C (refl _) (proj₂ p)                                  ≡⟨ subst-refl _ _ ⟩
          proj₂ p                                                     ≡⟨ sym $ subst-refl _ _ ⟩∎
          subst (λ x → C (x , _)) (refl _) (proj₂ p)                  ∎)
                                                                     y≡z ⟩
      (proj₁ p , subst (λ x → C (x , _)) y≡z (proj₂ p))         ∎

    -- A proof simplification rule for subst₂.

    subst₂-proj₁ :
      ∀ {B : A → Type b} {y₁ y₂}
        {x₁≡x₂ : x₁ ≡ x₂} {y₁≡y₂ : subst B x₁≡x₂ y₁ ≡ y₂}
      (P : A → Type p) {p} →
      subst₂ {B = B} (P ∘ proj₁) x₁≡x₂ y₁≡y₂ p ≡ subst P x₁≡x₂ p
    subst₂-proj₁ {x₁≡x₂ = x₁≡x₂} {y₁≡y₂} P {p} =
      subst₂ (P ∘ proj₁) x₁≡x₂ y₁≡y₂ p              ≡⟨ subst-∘ _ _ _ ⟩
      subst P (cong proj₁ (Σ-≡,≡→≡ x₁≡x₂ y₁≡y₂)) p  ≡⟨ cong (λ eq → subst P eq _) (proj₁-Σ-≡,≡→≡ _ _) ⟩∎
      subst P x₁≡x₂ p                               ∎

    -- The subst function can be "pushed" inside non-dependent pairs.

    push-subst-, :
      ∀ (B : A → Type b) (C : A → Type c) {p} →
      subst (λ x → B x × C x) y≡z p ≡
      (subst B y≡z (proj₁ p) , subst C y≡z (proj₂ p))
    push-subst-, {y≡z = y≡z} B C {x , y} =
      subst (λ x → B x × C x) y≡z (x , y)                           ≡⟨ push-subst-pair _ _ ⟩
      (subst B y≡z x , subst (C ∘ proj₁) (Σ-≡,≡→≡ y≡z (refl _)) y)  ≡⟨ cong (_,_ _) $ subst₂-proj₁ _ ⟩∎
      (subst B y≡z x , subst C y≡z y)                               ∎

    -- A proof transformation rule for push-subst-,.

    proj₁-push-subst-,-refl :
      ∀ {A : Type a} {y : A} (B : A → Type b) (C : A → Type c) {p} →
      cong proj₁ (push-subst-, {y≡z = refl y} B C {p = p}) ≡
      trans (cong proj₁ (subst-refl _ _)) (sym $ subst-refl _ _)
    proj₁-push-subst-,-refl _ _ =
      cong proj₁ (trans (push-subst-pair _ _)
                    (cong (_,_ _) $ subst₂-proj₁ _))              ≡⟨ cong-trans _ _ _ ⟩

      trans (cong proj₁ (push-subst-pair _ _))
        (cong proj₁ (cong (_,_ _) $ subst₂-proj₁ _))              ≡⟨ cong (trans _) $
                                                                     cong-∘ _ _ _ ⟩
      trans (cong proj₁ (push-subst-pair _ _))
        (cong (const _) $ subst₂-proj₁ _)                         ≡⟨ trans (cong (trans _) (cong-const _)) $
                                                                     trans-reflʳ _ ⟩

      cong proj₁ (push-subst-pair _ _)                            ≡⟨ proj₁-push-subst-pair-refl _ _ ⟩∎

      trans (cong proj₁ (subst-refl _ _)) (sym $ subst-refl _ _)  ∎

    -- The subst function can be "pushed" inside inj₁ and inj₂.

    push-subst-inj₁ :
      ∀ (B : A → Type b) (C : A → Type c) {x} →
      subst (λ x → B x ⊎ C x) y≡z (inj₁ x) ≡ inj₁ (subst B y≡z x)
    push-subst-inj₁ {y≡z = y≡z} B C {x} = elim¹
      (λ y≡z → subst (λ x → B x ⊎ C x) y≡z (inj₁ x) ≡
               inj₁ (subst B y≡z x))
      (subst (λ x → B x ⊎ C x) (refl _) (inj₁ x)  ≡⟨ subst-refl _ _ ⟩
       inj₁ x                                     ≡⟨ cong inj₁ $ sym $ subst-refl _ _ ⟩∎
       inj₁ (subst B (refl _) x)                  ∎)
      y≡z

    push-subst-inj₂ :
      ∀ (B : A → Type b) (C : A → Type c) {x} →
      subst (λ x → B x ⊎ C x) y≡z (inj₂ x) ≡ inj₂ (subst C y≡z x)
    push-subst-inj₂ {y≡z = y≡z} B C {x} = elim¹
      (λ y≡z → subst (λ x → B x ⊎ C x) y≡z (inj₂ x) ≡
               inj₂ (subst C y≡z x))
      (subst (λ x → B x ⊎ C x) (refl _) (inj₂ x)  ≡⟨ subst-refl _ _ ⟩
       inj₂ x                                     ≡⟨ cong inj₂ $ sym $ subst-refl _ _ ⟩∎
       inj₂ (subst C (refl _) x)                  ∎)
      y≡z

    -- The subst function can be "pushed" inside applications.

    push-subst-application :
      {B : A → Type b}
      (x₁≡x₂ : x₁ ≡ x₂) (C : (x : A) → B x → Type c)
      {f : (x : A) → B x} {g : (y : B x₁) → C x₁ y} →
      subst (λ x → C x (f x)) x₁≡x₂ (g (f x₁)) ≡
      subst (λ x → (y : B x) → C x y) x₁≡x₂ g (f x₂)
    push-subst-application {x₁ = x₁} x₁≡x₂ C {f} {g} = elim¹
      (λ {x₂} x₁≡x₂ →
         subst (λ x → C x (f x)) x₁≡x₂ (g (f x₁)) ≡
         subst (λ x → ∀ y → C x y) x₁≡x₂ g (f x₂))
      (subst (λ x → C x (f x)) (refl _) (g (f x₁))  ≡⟨ subst-refl _ _ ⟩
       g (f x₁)                                     ≡⟨ cong (_$ f x₁) $ sym $ subst-refl _ _ ⟩∎
       subst (λ x → ∀ y → C x y) (refl _) g (f x₁)  ∎)
      x₁≡x₂

    push-subst-implicit-application :
      {B : A → Type b}
      (x₁≡x₂ : x₁ ≡ x₂) (C : (x : A) → B x → Type c)
      {f : (x : A) → B x} {g : {y : B x₁} → C x₁ y} →
      subst (λ x → C x (f x)) x₁≡x₂ (g {y = f x₁}) ≡
      subst (λ x → {y : B x} → C x y) x₁≡x₂ g {y = f x₂}
    push-subst-implicit-application {x₁ = x₁} x₁≡x₂ C {f} {g} = elim¹
      (λ {x₂} x₁≡x₂ →
         subst (λ x → C x (f x)) x₁≡x₂ (g {y = f x₁}) ≡
         subst (λ x → ∀ {y} → C x y) x₁≡x₂ g {y = f x₂})
      (subst (λ x → C x (f x)) (refl _) (g {y = f x₁})    ≡⟨ subst-refl _ _ ⟩
       g {y = f x₁}                                       ≡⟨ cong (λ g → g {y = f x₁}) $ sym $ subst-refl (λ x → ∀ {y} → C x y) _ ⟩∎
       subst (λ x → ∀ {y} → C x y) (refl _) g {y = f x₁}  ∎)
      x₁≡x₂

    subst-∀-sym :
      ∀ {B : A → Type b} {y : B x₁}
        {C : (x : A) → B x → Type c} {f : (y : B x₂) → C x₂ y}
        {x₁≡x₂ : x₁ ≡ x₂} →
      subst (λ x → (y : B x) → C x y) (sym x₁≡x₂) f y ≡
      subst (uncurry C) (sym $ Σ-≡,≡→≡ x₁≡x₂ (refl _))
        (f (subst B x₁≡x₂ y))
    subst-∀-sym {B = B} {C = C} {x₁≡x₂ = x₁≡x₂} = elim
      (λ {x₁ x₂} x₁≡x₂ →
         {y : B x₁} (f : (y : B x₂) → C x₂ y) →
         subst (λ x → (y : B x) → C x y) (sym x₁≡x₂) f y ≡
         subst (uncurry C) (sym $ Σ-≡,≡→≡ x₁≡x₂ (refl _))
           (f (subst B x₁≡x₂ y)))
      (λ x {y} f →
         let lemma =
               cong (x ,_) (subst-refl B y)              ≡⟨ cong (cong (x ,_)) $ sym $ sym-sym _ ⟩
               cong (x ,_) (sym $ sym $ subst-refl B y)  ≡⟨ cong-sym _ _ ⟩
               sym $ cong (x ,_) (sym $ subst-refl B y)  ≡⟨ cong sym $ sym Σ-≡,≡→≡-refl-refl ⟩∎
               sym $ Σ-≡,≡→≡ (refl x) (refl _)           ∎
         in
         subst (λ x → (y : B x) → C x y) (sym (refl x)) f y     ≡⟨ cong (λ eq → subst (λ x → (y : B x) → C x y) eq _ _) sym-refl ⟩

         subst (λ x → (y : B x) → C x y) (refl x) f y           ≡⟨ cong (_$ y) $ subst-refl _ _ ⟩

         f y                                                    ≡⟨ sym $ dcong f _ ⟩

         subst (C x) (subst-refl B _) (f (subst B (refl x) y))  ≡⟨ subst-∘ _ _ _ ⟩

         subst (uncurry C) (cong (x ,_) (subst-refl B y))
           (f (subst B (refl x) y))                             ≡⟨ cong (λ eq → subst (uncurry C) eq (f (subst B (refl x) y))) lemma ⟩∎

         subst (uncurry C) (sym $ Σ-≡,≡→≡ (refl x) (refl _))
           (f (subst B (refl x) y))                             ∎)
      x₁≡x₂ _

    subst-∀ :
      ∀ {B : A → Type b} {y : B x₂}
        {C : (x : A) → B x → Type c} {f : (y : B x₁) → C x₁ y}
        {x₁≡x₂ : x₁ ≡ x₂} →
      subst (λ x → (y : B x) → C x y) x₁≡x₂ f y ≡
      subst (uncurry C) (sym $ Σ-≡,≡→≡ (sym x₁≡x₂) (refl _))
        (f (subst B (sym x₁≡x₂) y))
    subst-∀ {B = B} {y = y} {C = C} {f = f} {x₁≡x₂ = x₁≡x₂} =
      subst (λ x → (y : B x) → C x y) x₁≡x₂ f y               ≡⟨ cong (λ eq → subst (λ x → (y : B x) → C x y) eq _ _) $ sym $ sym-sym _ ⟩
      subst (λ x → (y : B x) → C x y) (sym (sym x₁≡x₂)) f y   ≡⟨ subst-∀-sym ⟩∎
      subst (uncurry C) (sym $ Σ-≡,≡→≡ (sym x₁≡x₂) (refl _))
        (f (subst B (sym x₁≡x₂) y))                           ∎

    subst-→ :
      {B : A → Type b} {y : B x₂} {C : A → Type c} {f : B x₁ → C x₁} →
      subst (λ x → B x → C x) x₁≡x₂ f y ≡
      subst C x₁≡x₂ (f (subst B (sym x₁≡x₂) y))
    subst-→ {x₁≡x₂ = x₁≡x₂} {B = B} {y = y} {C} {f} =
      subst (λ x → B x → C x) x₁≡x₂ f y                          ≡⟨ cong (λ eq → subst (λ x → B x → C x) eq f y) $ sym $
                                                                      sym-sym _ ⟩
      subst (λ x → B x → C x) (sym $ sym x₁≡x₂) f y              ≡⟨ subst-∀-sym ⟩

      subst (C ∘ proj₁) (sym $ Σ-≡,≡→≡ (sym x₁≡x₂) (refl _))
        (f (subst B (sym x₁≡x₂) y))                              ≡⟨ subst-∘ _ _ _ ⟩

      subst C (cong proj₁ $ sym $ Σ-≡,≡→≡ (sym x₁≡x₂) (refl _))
        (f (subst B (sym x₁≡x₂) y))                              ≡⟨ cong (λ eq → subst C eq (f (subst B (sym x₁≡x₂) y))) $
                                                                      cong-sym _ _ ⟩
      subst C (sym $ cong proj₁ $ Σ-≡,≡→≡ (sym x₁≡x₂) (refl _))
        (f (subst B (sym x₁≡x₂) y))                              ≡⟨ cong (λ eq → subst C (sym eq) (f (subst B (sym x₁≡x₂) y))) $
                                                                      proj₁-Σ-≡,≡→≡ _ _ ⟩
      subst C (sym $ sym x₁≡x₂) (f (subst B (sym x₁≡x₂) y))      ≡⟨ cong (λ eq → subst C eq (f (subst B (sym x₁≡x₂) y))) $
                                                                      sym-sym _ ⟩∎
      subst C x₁≡x₂ (f (subst B (sym x₁≡x₂) y))                  ∎

    subst-→-domain :
      (B : A → Type b) {f : B x → C} (x≡y : x ≡ y) {u : B y} →
      subst (λ x → B x → C) x≡y f u ≡ f (subst B (sym x≡y) u)
    subst-→-domain {C = C} B x≡y {u = u} = elim₁
      (λ {x} x≡y → (f : B x → C) →
                   subst (λ x → B x → C) x≡y f u ≡
                   f (subst B (sym x≡y) u))
      (λ f →
         subst (λ x → B x → C) (refl _) f u  ≡⟨ cong (_$ u) $ subst-refl _ _ ⟩
         f u                                 ≡⟨ cong f $ sym $ subst-refl _ _ ⟩
         f (subst B (refl _) u)              ≡⟨ cong (λ p → f (subst B p u)) $ sym sym-refl ⟩∎
         f (subst B (sym (refl _)) u)        ∎)
      x≡y _

    -- A "computation rule".

    subst-→-domain-refl :
      {B : A → Type b} {f : B x → C} {u : B x} →
      subst-→-domain B {f = f} (refl x) {u = u} ≡
      trans (cong (_$ u) (subst-refl _ _))
        (trans (cong f (sym (subst-refl _ _)))
           (cong (f ∘ flip (subst B) u) (sym sym-refl)))
    subst-→-domain-refl {C = C} {B = B} {u = u} =
      cong (_$ _) $
      elim₁-refl
        (λ {x} x≡y → (f : B x → C) →
                     subst (λ x → B x → C) x≡y f u ≡
                     f (subst B (sym x≡y) u))
        _

    -- The following lemma is Proposition 2 from "Generalizations of
    -- Hedberg's Theorem" by Kraus, Escardó, Coquand and Altenkirch.

    subst-in-terms-of-trans-and-cong :
      {x≡y : x ≡ y} {fx≡gx : f x ≡ g x} →
      subst (λ z → f z ≡ g z) x≡y fx≡gx ≡
      trans (sym (cong f x≡y)) (trans fx≡gx (cong g x≡y))
    subst-in-terms-of-trans-and-cong {f = f} {g = g} = elim
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

    -- Sometimes cong can be "pushed" inside subst. The following
    -- lemma provides one example.

    cong-subst :
      {B : A → Type b} {C : A → Type c}
      {f : ∀ {x} → B x → C x} {g h : (x : A) → B x}
      (eq₁ : x ≡ y) (eq₂ : g x ≡ h x) →
      cong f (subst (λ x → g x ≡ h x) eq₁ eq₂) ≡
      subst (λ x → f (g x) ≡ f (h x)) eq₁ (cong f eq₂)
    cong-subst {f = f} {g} {h} = elim₁
      (λ eq₁ → ∀ eq₂ →
         cong f (subst (λ x → g x ≡ h x) eq₁ eq₂) ≡
         subst (λ x → f (g x) ≡ f (h x)) eq₁ (cong f eq₂))
      (λ eq₂ →
         cong f (subst (λ x → g x ≡ h x) (refl _) eq₂)          ≡⟨ cong (cong f) $ subst-refl _ _ ⟩
         cong f eq₂                                             ≡⟨ sym $ subst-refl _ _ ⟩∎
         subst (λ x → f (g x) ≡ f (h x)) (refl _) (cong f eq₂)  ∎)

    -- Some rearrangement lemmas for equalities between equalities.

    [trans≡]≡[≡trans-symʳ] :
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
      {p : x ≡ y} {q : x ≡ x} {r : y ≡ y} →
      (subst (λ z → z ≡ z) p q ≡ r)
        ≡
      (trans q p ≡ trans p r)
    [subst≡]≡[trans≡trans] {p = p} {q} {r} = elim
      (λ {x y} p → {q : x ≡ x} {r : y ≡ y} →
                   (subst (λ z → z ≡ z) p q ≡ r)
                     ≡
                   (trans q p ≡ trans p r))
      (λ x {q r} →
         subst (λ z → z ≡ z) (refl x) q ≡ r   ≡⟨ cong (_≡ _) (subst-refl _ _) ⟩
         q ≡ r                                ≡⟨ sym $ cong₂ _≡_ (trans-reflʳ _) (trans-reflˡ _) ⟩∎
         trans q (refl x) ≡ trans (refl x) r  ∎)
      p

    -- "Evaluation rule" for [subst≡]≡[trans≡trans].

    [subst≡]≡[trans≡trans]-refl :
      {q r : x ≡ x} →
      [subst≡]≡[trans≡trans] {p = refl x} ≡
      trans (cong (_≡ r) (subst-refl (λ z → z ≡ z) q))
            (sym $ cong₂ _≡_ (trans-reflʳ q) (trans-reflˡ r))
    [subst≡]≡[trans≡trans]-refl {q = q} {r = r} =
      cong (λ f → f {q = q} {r = r}) $
        elim-refl
          (λ {x y} p → {q : x ≡ x} {r : y ≡ y} → _ ≡ (trans _ p ≡ _))
          _

    -- The proof trans is commutative when one of the arguments is f x for
    -- a function f : (x : A) → x ≡ x.

    trans-sometimes-commutative :
      {p : x ≡ x} (f : (x : A) → x ≡ x) →
      trans (f x) p ≡ trans p (f x)
    trans-sometimes-commutative {x = x} {p = p} f =
      trans (f x) p  ≡⟨ subst id [subst≡]≡[trans≡trans] lemma ⟩∎
      trans p (f x)  ∎
      where
      lemma =
        subst (λ z → z ≡ z) p (f x)  ≡⟨ dcong f p ⟩∎
        f x                          ∎

    -- Sometimes one can turn two ("modified") copies of a proof into
    -- one.

    trans-cong-cong :
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

             refl (f x x)                         ≡⟨ sym $ cong-refl _ ⟩∎

             cong (λ z → f z z) (refl x)          ∎)

    -- If f and g agree on a decidable subset of their common domain, then
    -- cong f eq is equal to (modulo some uses of transitivity) cong g eq
    -- for proofs eq between elements in this subset.

    cong-respects-relevant-equality :
      {f g : A → B}
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
      T-irr : (b : Bool) → Is-proposition (T b)
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
      (f : A → A) (p : A → Bool)
      (x≡y : x ≡ y) (px : T (p x)) (py : T (p y))
      (f≡id : ∀ z → T (p z) → f z ≡ z) →
      cong f x≡y ≡
      trans (f≡id x px) (trans x≡y $ sym (f≡id y py))
    cong-roughly-id {x = x} {y = y} f p x≡y px py f≡id =
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
