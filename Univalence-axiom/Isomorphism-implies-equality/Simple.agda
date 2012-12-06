------------------------------------------------------------------------
-- A class of algebraic structures, based on non-recursive simple
-- types, satisfies the property that isomorphic instances of a
-- structure are equal (assuming univalence)
------------------------------------------------------------------------

-- In fact, isomorphism and equality are basically the same thing, and
-- the main theorem can be instantiated with several different
-- "universes", not only the one based on simple types.

-- This module has been developed in collaboration with Thierry
-- Coquand.

{-# OPTIONS --without-K #-}

open import Equality

module Univalence-axiom.Isomorphism-implies-equality.Simple
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection hiding (id; _∘_; inverse)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence using (_⇔_; module _⇔_)
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Preimage eq
open import Prelude as P hiding (id)
open import Univalence-axiom eq
open import Weak-equivalence eq using (_≈_; module _≈_; ↔⇒≈)

------------------------------------------------------------------------
-- Universes with some extra stuff

record Universe : Set₂ where
  field
    -- Codes for something.
    U : Set₁

    -- Interpretation of codes.
    El : U → Set → Set

    -- A predicate.
    Is-isomorphism : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set

    -- A property.
    isomorphism↔subst :
      (univ : Univalence (# 0)) →
      Univalence (# 1) →
      ∀ {B C} (B↔C : B ↔ C) → Is-set C →
      ∀ a {x y} →
      Is-isomorphism B↔C a x y ↔
      (subst (El a) (≈⇒≡ univ $ ↔⇒≈ B↔C) x ≡ y)

------------------------------------------------------------------------
-- A universe-indexed family of classes of structures

module Class (Univ : Universe) where

  open Universe Univ

  -- Codes for structures.

  Code : Set₁
  Code =
    -- A code.
    Σ U λ a →

    -- A proposition.
    (A : SET (# 0)) → El a (Type A) → Σ Set λ P →
      -- The proposition should be propositional (assuming
      -- extensionality).
      Extensionality (# 0) (# 0) → Propositional P

  -- Interpretation of the codes. The elements of "Instance a" are
  -- instances of the structure encoded by a.

  Instance : Code → Set₁
  Instance (a , P) =
    -- A carrier set.
    Σ (SET (# 0)) λ A →

    -- An element.
    Σ (El a (Type A)) λ x →

    -- The element should satisfy the proposition.
    proj₁ (P A x)

  -- The carrier set.

  Carrier : ∀ a → Instance a → Set
  Carrier _ I = Type (proj₁ I)

  -- The "element".

  element : ∀ a (I : Instance a) → El (proj₁ a) (Carrier a I)
  element _ I = proj₁ (proj₂ I)

  abstract

    -- One can prove that two instances of a structure are equal by
    -- proving that the carrier sets and "elements" (suitably
    -- transported) are equal (assuming extensionality).

    instances-equal↔ :
      Extensionality (# 0) (# 0) →
      ∀ a {I₁ I₂} →
      (I₁ ≡ I₂) ↔
      ∃ λ (C-eq : Carrier a I₁ ≡ Carrier a I₂) →
        subst (El (proj₁ a)) C-eq (element a I₁) ≡ element a I₂
    instances-equal↔ ext (a , P)
                     {(C₁ , s₁) , e₁ , p₁} {(C₂ , s₂) , e₂ , p₂} =

      (((C₁ , s₁) , e₁ , p₁) ≡ ((C₂ , s₂) , e₂ , p₂))         ↝⟨ inverse Σ-≡,≡↔≡ ⟩

      (∃ λ (C-eq : (C₁ , s₁) ≡ (C₂ , s₂)) →
         subst (λ A → Σ (El a (Type A)) λ x → proj₁ (P A x))
               C-eq (e₁ , p₁) ≡
         (e₂ , p₂))                                           ↝⟨ ∃-cong (λ C-eq → ≡⇒↝ _ $ cong (λ eq → eq ≡ _) $
                                                                    push-subst-pair (λ A → El a (Type A))
                                                                                    (λ { (A , x) → proj₁ (P A x) })) ⟩
      (∃ λ (C-eq : (C₁ , s₁) ≡ (C₂ , s₂)) →
         (subst (λ A → El a (Type A)) C-eq e₁ ,
          subst (λ { (A , x) → proj₁ (P A x) })
                (Σ-≡,≡→≡ C-eq (refl _)) p₁) ≡
         (e₂ , p₂))                                           ↝⟨ ∃-cong (λ C-eq → inverse $ ignore-propositional-component (proj₂ (P _ _) ext)) ⟩

      (∃ λ (C-eq : (C₁ , s₁) ≡ (C₂ , s₂)) →
         subst (λ A → El a (Type A)) C-eq e₁ ≡ e₂)            ↝⟨ inverse $
                                                                   Σ-cong (ignore-propositional-component (H-level-propositional ext 2)) (λ C-eq →
                                                                          ≡⇒↝ _ $ cong (λ e → e ≡ e₂) $ sym (

                                                          subst (λ A → El a (Type A)) (Σ-≡,≡→≡ C-eq _) e₁  ≡⟨ subst-∘ (El a) Type _ ⟩
                                                          subst (El a) (cong Type $ Σ-≡,≡→≡ C-eq _) e₁     ≡⟨ cong (λ eq → subst (El a) eq _) $
                                                                                                                    proj₁-Σ-≡,≡→≡ C-eq _ ⟩∎
                                                          subst (El a) C-eq e₁                              ∎)) ⟩

      (∃ λ (C-eq : C₁ ≡ C₂) → subst (El a) C-eq e₁ ≡ e₂)      □

  -- Structure isomorphisms.

  Isomorphic : ∀ a → Instance a → Instance a → Set
  Isomorphic (a , _) ((A₁ , _) , x₁ , _) ((A₂ , _) , x₂ , _) =
    Σ (A₁ ↔ A₂) λ A₁↔A₂ → Is-isomorphism A₁↔A₂ a x₁ x₂

  abstract

    -- The type of isomorphisms between two instances of a structure
    -- is isomorphic to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is isomorphic to equality.

    isomorphic↔equal :
      Univalence (# 0) →
      Univalence (# 1) →
      ∀ a {I₁ I₂} → Isomorphic a I₁ I₂ ↔ (I₁ ≡ I₂)
    isomorphic↔equal univ univ₁ a {I₁} {I₂} =

      Isomorphic a I₁ I₂                                               ↝⟨ ∃-cong (λ C-eq → isomorphism↔subst univ univ₁ C-eq
                                                                                             (proj₂ $ proj₁ I₂) (proj₁ a)) ⟩
      (∃ λ (C-eq : Carrier a I₁ ↔ Carrier a I₂) →
         subst (El (proj₁ a)) (≈⇒≡ univ $ ↔⇒≈ C-eq) (element a I₁) ≡
         element a I₂)                                                 ↝⟨ inverse $
                                                                            Σ-cong (≡≈↔ univ ext is-set) (λ C-eq → ≡⇒↝ _ $ sym $
                                                                              cong (λ eq → subst (El (proj₁ a)) eq (element a I₁) ≡ element a I₂)
                                                                                   (_≈_.left-inverse-of (≡≈↔ univ ext is-set) C-eq)) ⟩
      (∃ λ (C-eq : Carrier a I₁ ≡ Carrier a I₂) →
         subst (El (proj₁ a)) C-eq (element a I₁) ≡ element a I₂)      ↝⟨ inverse $ instances-equal↔ ext a ⟩□

      (I₁ ≡ I₂)                                                        □

      where
      -- Extensionality follows from univalence.
      ext : Extensionality (# 0) (# 0)
      ext = dependent-extensionality univ₁ (λ _ → univ)

      is-set : Is-set (Carrier a I₁)
      is-set = proj₂ (proj₁ I₁)

    -- The type of (lifted) isomorphisms between two instances of a
    -- structure is equal to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is equal to equality.

    isomorphic≡equal :
      Univalence (# 0) →
      Univalence (# 1) →
      ∀ a {I₁ I₂} → ↑ _ (Isomorphic a I₁ I₂) ≡ (I₁ ≡ I₂)
    isomorphic≡equal univ univ₁ a {I₁} {I₂} =
      ≈⇒≡ univ₁ $ ↔⇒≈ (
        ↑ _ (Isomorphic a I₁ I₂)  ↝⟨ ↑↔ ⟩
        Isomorphic a I₁ I₂        ↝⟨ isomorphic↔equal univ univ₁ a ⟩□
        (I₁ ≡ I₂)                 □)

------------------------------------------------------------------------
-- A universe of non-recursive, simple types

-- Codes for types.
--
-- Note that the argument to k is assumed to be a set.

infixr 20 _⊗_
infixr 15 _⊕_
infixr 10 _⇾_

data U : Set₁ where
  id          : U
  k           : SET (# 0) → U
  _⇾_ _⊕_ _⊗_ : U → U → U

-- Interpretation of types.

El : U → Set → Set
El id      B = B
El (k A)   B = Type A
El (a ⇾ b) B = El a B → El b B
El (a ⊕ b) B = El a B ⊎ El b B
El (a ⊗ b) B = El a B × El b B

-- El a preserves equivalences.

cast : ∀ a {B C} → B ⇔ C → El a B ⇔ El a C
cast id      B⇔C = B⇔C
cast (k A)   B⇔C = Equivalence.id
cast (a ⇾ b) B⇔C = →-cong-⇔ (cast a B⇔C) (cast b B⇔C)
cast (a ⊕ b) B⇔C = cast a B⇔C ⊎-cong cast b B⇔C
cast (a ⊗ b) B⇔C = cast a B⇔C ×-cong cast b B⇔C

abstract

  -- The cast function respects identities (assuming extensionality).

  cast-id : Extensionality (# 0) (# 0) →
            ∀ a {B} → cast a (Equivalence.id {A = B}) ≡ Equivalence.id
  cast-id ext id      = refl _
  cast-id ext (k A)   = refl _
  cast-id ext (a ⇾ b) = cong₂ →-cong-⇔ (cast-id ext a) (cast-id ext b)
  cast-id ext (a ⊗ b) = cong₂ _×-cong_ (cast-id ext a) (cast-id ext b)
  cast-id ext (a ⊕ b) =
    cast a Equivalence.id ⊎-cong cast b Equivalence.id       ≡⟨ cong₂ _⊎-cong_ (cast-id ext a) (cast-id ext b) ⟩
    record { to = [ inj₁ , inj₂ ]; from = [ inj₁ , inj₂ ] }  ≡⟨ cong₂ (λ f g → record { to = f; from = g })
                                                                      (ext [ refl ∘ inj₁ , refl ∘ inj₂ ])
                                                                      (ext [ refl ∘ inj₁ , refl ∘ inj₂ ]) ⟩∎
    Equivalence.id                                           ∎

-- El a also preserves bijections (assuming extensionality).

cast↔ : Extensionality (# 0) (# 0) →
        ∀ a {B C} → B ↔ C → El a B ↔ El a C
cast↔ ext a {B} {C} B↔C = record
  { surjection = record
    { equivalence      = cast a B⇔C
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  B⇔C = _↔_.equivalence B↔C

  cst : ∀ a → El a B ↔ El a C
  cst id      = B↔C
  cst (k A)   = Bijection.id
  cst (a ⇾ b) = →-cong ext (cst a) (cst b)
  cst (a ⊕ b) = cst a ⊎-cong cst b
  cst (a ⊗ b) = cst a ×-cong cst b

  abstract

    -- The projection _↔_.equivalence is homomorphic with respect to
    -- cast a/cst a

    casts-related :
      ∀ a → cast a (_↔_.equivalence B↔C) ≡ _↔_.equivalence (cst a)
    casts-related id      = refl _
    casts-related (k A)   = refl _
    casts-related (a ⇾ b) = cong₂ →-cong-⇔ (casts-related a)
                                           (casts-related b)
    casts-related (a ⊕ b) = cong₂ _⊎-cong_ (casts-related a)
                                           (casts-related b)
    casts-related (a ⊗ b) = cong₂ _×-cong_ (casts-related a)
                                           (casts-related b)

    to∘from : ∀ x → _⇔_.to (cast a B⇔C) (_⇔_.from (cast a B⇔C) x) ≡ x
    to∘from x =
      _⇔_.to (cast a B⇔C) (_⇔_.from (cast a B⇔C) x)  ≡⟨ cong₂ (λ f g → f (g x)) (cong _⇔_.to $ casts-related a)
                                                                                (cong _⇔_.from $ casts-related a) ⟩
      _↔_.to (cst a) (_↔_.from (cst a) x)            ≡⟨ _↔_.right-inverse-of (cst a) x ⟩∎
      x                                              ∎

    from∘to : ∀ x → _⇔_.from (cast a B⇔C) (_⇔_.to (cast a B⇔C) x) ≡ x
    from∘to x =
      _⇔_.from (cast a B⇔C) (_⇔_.to (cast a B⇔C) x)  ≡⟨ cong₂ (λ f g → f (g x)) (cong _⇔_.from $ casts-related a)
                                                                                (cong _⇔_.to $ casts-related a) ⟩
      _↔_.from (cst a) (_↔_.to (cst a) x)            ≡⟨ _↔_.left-inverse-of (cst a) x ⟩∎
      x                                              ∎

abstract

  -- El a preserves Is-set (assuming extensionality).

  El-preserves-Is-set :
    Extensionality (# 0) (# 0) →
    ∀ a {B} → Is-set B → Is-set (El a B)

  El-preserves-Is-set ext id B-set = B-set

  El-preserves-Is-set ext (k A) B-set = proj₂ A

  El-preserves-Is-set ext (a ⇾ b) B-set =
    Π-closure ext 2 λ _ → El-preserves-Is-set ext b B-set

  El-preserves-Is-set ext (a ⊕ b) B-set =
    ⊎-closure 0 (El-preserves-Is-set ext a B-set)
                (El-preserves-Is-set ext b B-set)

  El-preserves-Is-set ext (a ⊗ b) B-set =
    ×-closure 2 (El-preserves-Is-set ext a B-set)
                (El-preserves-Is-set ext b B-set)

-- The property of being an isomorphism between two elements.

Is-isomorphism : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set

Is-isomorphism B↔C id = λ x y → _↔_.to B↔C x ≡ y

Is-isomorphism B↔C (k A) = λ x y → x ≡ y

Is-isomorphism B↔C (a ⇾ b) = λ f g →
  ∀ {x y} → Is-isomorphism B↔C a x y → Is-isomorphism B↔C b (f x) (g y)

Is-isomorphism B↔C (a ⊕ b) =
  Is-isomorphism B↔C a ⊎-rel Is-isomorphism B↔C b

Is-isomorphism B↔C (a ⊗ b) = λ { (x , u) (y , v) →
  Is-isomorphism B↔C a x y × Is-isomorphism B↔C b u v }

-- Another definition of "being an isomorphism".

Is-isomorphism′ : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set
Is-isomorphism′ B↔C a x y = _⇔_.to (cast a (_↔_.equivalence B↔C)) x ≡ y

abstract

  -- Both definitions of "being an isomorphism" are propositional,
  -- assuming extensionality and that one of the underlying types is a
  -- set.

  Is-isomorphism′-propositional :
     Extensionality (# 0) (# 0) →
     ∀ {B C} (B↔C : B ↔ C) → Is-set C →
     ∀ a {x y} → Propositional (Is-isomorphism′ B↔C a x y)
  Is-isomorphism′-propositional ext B↔C C-set a =
    El-preserves-Is-set ext a C-set _ _

  Is-isomorphism-propositional :
     Extensionality (# 0) (# 0) →
     ∀ {B C} (B↔C : B ↔ C) → Is-set C →
     ∀ a {x y} →
     Propositional (Is-isomorphism B↔C a x y)

  Is-isomorphism-propositional ext B↔C C-set id = C-set _ _

  Is-isomorphism-propositional ext B↔C C-set (k A) = proj₂ A _ _

  Is-isomorphism-propositional ext B↔C C-set (a ⇾ b) =
    implicit-Π-closure ext 1 λ _ →
    implicit-Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Is-isomorphism-propositional ext B↔C C-set b

  Is-isomorphism-propositional ext B↔C C-set (a ⊕ b) {x} {y} with x | y
  ... | inj₁ _ | inj₁ _ = Is-isomorphism-propositional ext B↔C C-set a
  ... | inj₂ _ | inj₂ _ = Is-isomorphism-propositional ext B↔C C-set b
  ... | inj₁ _ | inj₂ _ = ⊥-propositional
  ... | inj₂ _ | inj₁ _ = ⊥-propositional

  Is-isomorphism-propositional ext B↔C C-set (a ⊗ b) =
    ×-closure 1 (Is-isomorphism-propositional ext B↔C C-set a)
                (Is-isomorphism-propositional ext B↔C C-set b)

  -- The two definitions of "being an isomorphism" are equivalent
  -- (assuming extensionality).

  isomorphism-definitions-equivalent :
    (ext : Extensionality (# 0) (# 0)) →
    ∀ {B C} (B↔C : B ↔ C) a {x y} →
    Is-isomorphism B↔C a x y ⇔ Is-isomorphism′ B↔C a x y
  isomorphism-definitions-equivalent ext B↔C = λ a →
    record { to = to a; from = from a }
    where

    mutual

      to : ∀ a {x y} →
           Is-isomorphism B↔C a x y → Is-isomorphism′ B↔C a x y

      to id iso = iso

      to (k A) iso = iso

      to (a ⇾ b) {f} {g} iso = ext λ x →
        let B⇔C = _↔_.equivalence B↔C in

        _⇔_.to (cast b B⇔C) (f (_⇔_.from (cast a B⇔C) x))  ≡⟨ to b (iso (from a (refl _))) ⟩
        g (_⇔_.to (cast a B⇔C) (_⇔_.from (cast a B⇔C) x))  ≡⟨ cong g $ _↔_.right-inverse-of (cast↔ ext a B↔C) x ⟩∎
        g x                                                ∎

      to (a ⊕ b) {inj₁ x} {inj₁ y} iso = cong inj₁ $ to a iso
      to (a ⊕ b) {inj₂ x} {inj₂ y} iso = cong inj₂ $ to b iso
      to (a ⊕ b) {inj₁ x} {inj₂ y} ()
      to (a ⊕ b) {inj₂ x} {inj₁ y} ()

      to (a ⊗ b) (iso-a , iso-b) = cong₂ _,_ (to a iso-a) (to b iso-b)

      from : ∀ a {x y} →
             Is-isomorphism′ B↔C a x y → Is-isomorphism B↔C a x y

      from id iso = iso

      from (k A) iso = iso

      from (a ⇾ b) {f} {g} iso = λ {x y} x≅y → from b (
        let B⇔C = _↔_.equivalence B↔C in

        _⇔_.to (cast b B⇔C) (f x)                          ≡⟨ cong (_⇔_.to (cast b B⇔C) ∘ f) $ sym $
                                                                   _↔_.to-from (cast↔ ext a B↔C) $ to a x≅y ⟩
        _⇔_.to (cast b B⇔C) (f (_⇔_.from (cast a B⇔C) y))  ≡⟨ cong (λ f → f y) iso ⟩∎
        g y                                                ∎)

      from (a ⊕ b) {inj₁ x} {inj₁ y} iso = from a (⊎.cancel-inj₁ iso)
      from (a ⊕ b) {inj₂ x} {inj₂ y} iso = from b (⊎.cancel-inj₂ iso)
      from (a ⊕ b) {inj₁ x} {inj₂ y} iso = ⊎.inj₁≢inj₂ iso
      from (a ⊕ b) {inj₂ x} {inj₁ y} iso = ⊎.inj₁≢inj₂ (sym iso)

      from (a ⊗ b) iso =
        from a (cong proj₁ iso) , from b (cong proj₂ iso)

  -- If we add the assumption that one of the underlying types is a
  -- set, then the two definitions of "being an isomorphism" are
  -- "isomorphic" (in bijective correspondence).

  isomorphism-definitions-isomorphic :
    (ext : Extensionality (# 0) (# 0)) →
    ∀ {B C} (B↔C : B ↔ C) → Is-set C →
    ∀ a {x y} →
    Is-isomorphism B↔C a x y ↔ Is-isomorphism′ B↔C a x y
  isomorphism-definitions-isomorphic ext B↔C C-set = λ a → record
    { surjection = record
      { equivalence      = isomorphism-definitions-equivalent ext B↔C a
      ; right-inverse-of = λ _ →
          _⇔_.to propositional⇔irrelevant
                 (Is-isomorphism′-propositional ext B↔C C-set a) _ _
      }
    ; left-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant
               (Is-isomorphism-propositional ext B↔C C-set a) _ _
    }

  -- "Being an isomorphism between two elements" is isomorphic to "the
  -- isomorphism transports one element to the other" (assuming
  -- extensionality and univalence, and that one of the underlying
  -- types is a set).

  isomorphism↔subst :
    (ext : Extensionality (# 0) (# 0))
    (univ : Univalence (# 0)) →
    ∀ {B C} (B↔C : B ↔ C) → Is-set C →
    ∀ a {x y} →
    Is-isomorphism B↔C a x y ↔ (subst (El a) (≈⇒≡ univ $ ↔⇒≈ B↔C) x ≡ y)
  isomorphism↔subst ext univ B↔C C-set a {x} {y} =
    Is-isomorphism  B↔C a x y                  ↝⟨ isomorphism-definitions-isomorphic ext B↔C C-set a ⟩
    Is-isomorphism′ B↔C a x y                  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ y) $
                                                    subst-unique (El a)
                                                                 (λ A≈B → _⇔_.to (cast a (_≈_.equivalence A≈B)))
                                                                 (λ x → cong (λ f → _⇔_.to f x) $ cast-id ext a)
                                                                 univ (↔⇒≈ B↔C) x ⟩□
    (subst (El a) (≈⇒≡ univ $ ↔⇒≈ B↔C) x ≡ y)  □

-- The universe above is a "universe with some extra stuff".

simple : Universe
simple = record
  { U                 = U
  ; El                = El
  ; Is-isomorphism    = Is-isomorphism
  ; isomorphism↔subst = λ univ univ₁ →
      isomorphism↔subst (dependent-extensionality univ₁ (λ _ → univ))
                        univ
  }

-- Let us use this universe in the examples below.

open Class simple

------------------------------------------------------------------------
-- An example: monoids

monoid : Code
monoid =
  -- Binary operation.
  (id ⇾ id ⇾ id) ⊗

  -- Identity.
  id ,

  λ { (_ , M-set) (_∙_ , e) →

       -- Left and right identity laws.
      ((∀ x → e ∙ x ≡ x) ×
       (∀ x → x ∙ e ≡ x) ×

       -- Associativity.
       (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z)) ,

       -- The laws are propositional (assuming extensionality).
      λ ext →
        ×-closure 1  (Π-closure ext 1 λ _ →
                      M-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      M-set _ _)
                     (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      M-set _ _)) }

-- The interpretation of the code is reasonable.

Instance-monoid :
  Instance monoid ≡
  Σ (SET (# 0)) λ { (M , _) →
  Σ ((M → M → M) × M) λ { (_∙_ , e) →
  (∀ x → e ∙ x ≡ x) ×
  (∀ x → x ∙ e ≡ x) ×
  (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z) } }
Instance-monoid = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-monoid :
  ∀ {M₁ M₁-set _∙₁_ e₁ laws₁ M₂ M₂-set _∙₂_ e₂ laws₂} →
  Isomorphic monoid ((M₁ , M₁-set) , (_∙₁_ , e₁) , laws₁)
                    ((M₂ , M₂-set) , (_∙₂_ , e₂) , laws₂) ≡
  Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
  (∀ {x y} → to x ≡ y → ∀ {u v} → to u ≡ v → to (x ∙₁ u) ≡ y ∙₂ v) ×
  to e₁ ≡ e₂
Isomorphic-monoid = refl _

------------------------------------------------------------------------
-- An example: fields

-- Fields are defined in two ways:
--
-- * With the multiplicative inverse introduced using a law.
--
-- * With the multiplicative inverse introduced as a partial
--   operation.
--
-- Note that the latter definition implies that one can decide if an
-- element is distinct from zero.

module Field-law where

  -- Fields.
  --
  -- Note that "field" is a reserved word in Agda.

  field′ : Code
  field′ =
    -- Addition.
    (id ⇾ id ⇾ id) ⊗

    -- Zero.
    id ⊗

    -- Multiplication.
    (id ⇾ id ⇾ id) ⊗

    -- One.
    id ⊗

    -- Minus. (Division is introduced using a law.)
    (id ⇾ id) ,

    λ { (_ , F-set) (_+_ , 0# , _*_ , 1# , -_) →

         -- Associativity.
        ((∀ x y z → x + (y + z) ≡ (x + y) + z) ×
         (∀ x y z → x * (y * z) ≡ (x * y) * z) ×

         -- Commutativity.
         (∀ x y → x + y ≡ y + x) ×
         (∀ x y → x * y ≡ y * x) ×

         -- Distributivity.
         (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×

         -- Identity laws.
         (∀ x → x + 0# ≡ x) ×
         (∀ x → x * 1# ≡ x) ×

         -- Zero and one are distinct.
         0# ≢ 1# ×

         -- Inverse laws. The multiplicative inverse law is
         -- "computational" and propositional at the same time (because
         -- inverses are unique).
         (∀ x → x + (- x) ≡ 0#) ×
         (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#)) ,

        λ ext → [inhabited⇒+]⇒+ 0
          λ { (_ , *-assoc , _ , *-comm , _ , _ , *-id , _) →
            ×-closure 1  (Π-closure ext 1 λ _ →
                          Π-closure ext 1 λ _ →
                          Π-closure ext 1 λ _ →
                          F-set _ _)
            (×-closure 1 (Π-closure ext 1 λ _ →
                          Π-closure ext 1 λ _ →
                          Π-closure ext 1 λ _ →
                          F-set _ _)
            (×-closure 1 (Π-closure ext 1 λ _ →
                          Π-closure ext 1 λ _ →
                          F-set _ _)
            (×-closure 1 (Π-closure ext 1 λ _ →
                          Π-closure ext 1 λ _ →
                          F-set _ _)
            (×-closure 1 (Π-closure ext 1 λ _ →
                          Π-closure ext 1 λ _ →
                          Π-closure ext 1 λ _ →
                          F-set _ _)
            (×-closure 1 (Π-closure ext 1 λ _ →
                          F-set _ _)
            (×-closure 1 (Π-closure ext 1 λ _ →
                          F-set _ _)
            (×-closure 1 (Π-closure ext 1 λ _ →
                          ⊥-propositional)
            (×-closure 1 (Π-closure ext 1 λ _ →
                          F-set _ _)
                         (Π-closure ext 1 λ x →
                          Π-closure ext 1 λ _ →
                          [inhabited⇒+]⇒+ 0 λ { (x⁻¹ , xx⁻¹≡1) →
                            let lemma : ∀ y → y ≡ x⁻¹ * (x * y)
                                lemma y =
                                  y              ≡⟨ sym $ *-id _ ⟩
                                  y * 1#         ≡⟨ *-comm _ _ ⟩
                                  1# * y         ≡⟨ cong (λ x → x * y) $ sym xx⁻¹≡1 ⟩
                                  (x * x⁻¹) * y  ≡⟨ cong (λ x → x * y) $ *-comm _ _ ⟩
                                  (x⁻¹ * x) * y  ≡⟨ sym $ *-assoc _ _ _ ⟩∎
                                  x⁻¹ * (x * y)  ∎
                            in

                            injection⁻¹-propositional
                              (record { to        = _*_ x
                                      ; injective = λ {y₁ y₂} xy₁≡xy₂ →
                                          y₁              ≡⟨ lemma y₁ ⟩
                                          x⁻¹ * (x * y₁)  ≡⟨ cong (_*_ x⁻¹) xy₁≡xy₂ ⟩
                                          x⁻¹ * (x * y₂)  ≡⟨ sym $ lemma y₂ ⟩∎
                                          y₂              ∎
                                      })
                              F-set 1# } ))))))))) } }

  -- The interpretation of the code is reasonable.

  Instance-field′ :
    Instance field′ ≡
    Σ (SET (# 0)) λ { (F , _) →
    Σ ((F → F → F) × F × (F → F → F) × F × (F → F))
      λ { (_+_ , 0# , _*_ , 1# , -_) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
    (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
    (∀ x y → x + y ≡ y + x) ×
    (∀ x y → x * y ≡ y * x) ×
    (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
    (∀ x → x + 0# ≡ x) ×
    (∀ x → x * 1# ≡ x) ×
    0# ≢ 1# ×
    (∀ x → x + (- x) ≡ 0#) ×
    (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#) } }
  Instance-field′ = refl _

  -- Note that we do get a multiplicative inverse, even though it is
  -- introduced using a propositional law.

  multiplicative-inverse :
    (F : Instance field′) →
    let 0#  = proj₁ (proj₂ (proj₁ (proj₂ F)))
        _*_ = proj₁ (proj₂ (proj₂ (proj₁ (proj₂ F))))
        1#  = proj₁ (proj₂ (proj₂ (proj₂ (proj₁ (proj₂ F))))) in
    Σ ((x : Carrier field′ F) → x ≢ 0# → Carrier field′ F) λ *-inv →
      ∀ x (x≢0 : x ≢ 0#) → x * *-inv x x≢0 ≡ 1#
  multiplicative-inverse
    (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , *-inv) =
    (λ x x≢0 → proj₁ (*-inv x x≢0)) ,
    (λ x x≢0 → proj₂ (*-inv x x≢0))

  -- The notion of isomorphism that we get for fields is reasonable.

  Isomorphic-field′ :
    ∀ {F₁ F₁-set _+₁_ 0₁ _*₁_ 1₁ -₁_ laws₁
       F₂ F₂-set _+₂_ 0₂ _*₂_ 1₂ -₂_ laws₂} →
    Isomorphic field′
               ((F₁ , F₁-set) , (_+₁_ , 0₁ , _*₁_ , 1₁ , -₁_) , laws₁)
               ((F₂ , F₂-set) , (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_) , laws₂) ≡
    Σ (F₁ ↔ F₂) λ F₁↔F₂ → let open _↔_ F₁↔F₂ in
    (∀ {x y} → to x ≡ y → ∀ {u v} → to u ≡ v → to (x +₁ u) ≡ y +₂ v) ×
    to 0₁ ≡ 0₂ ×
    (∀ {x y} → to x ≡ y → ∀ {u v} → to u ≡ v → to (x *₁ u) ≡ y *₂ v) ×
    to 1₁ ≡ 1₂ ×
    (∀ {x y} → to x ≡ y → to (-₁ x) ≡ -₂ y)
  Isomorphic-field′ = refl _

  -- Note that field isomorphisms are homomorphic also with respect to
  -- the multiplicative inverse operator.

  homomorphic-with-respect-to-multiplicative-inverse :
    ∀ {F₁ F₂} (iso : Isomorphic field′ F₁ F₂) →
    let open _↔_ (proj₁ iso) in
    ∀ {x y} → to x ≡ y → ∀ {x≢0 y≢0} →
    to (proj₁ (multiplicative-inverse F₁) x x≢0) ≡
    proj₁ (multiplicative-inverse F₂) y y≢0
  homomorphic-with-respect-to-multiplicative-inverse
    {_ , (_ , _ , _*₁_ , 1₁ , _) ,
     _ , _ , _ , _ , _ , _ , _ , _ , _ , *⁻¹₁}
    {_ , (_ , _ , _*₂_ , 1₂ , _) ,
     _ , *₂-assoc , _ , *₂-comm , _ , _ , *1₂ , _ , _ , *⁻¹₂}
    (F₁↔F₂ , _ , _ , *-homo , 1-homo , _)
    {x} {y} to-x≡y {x≢0} {y≢0} =

      to (inv₁ x x≢0)                       ≡⟨ sym $ *1₂ _ ⟩
      to (inv₁ x x≢0) *₂ 1₂                 ≡⟨ cong (_*₂_ _) $ sym $ proj₂ (*⁻¹₂ y y≢0) ⟩
      to (inv₁ x x≢0) *₂ (y *₂ inv₂ y y≢0)  ≡⟨ *₂-assoc _ _ _ ⟩
      (to (inv₁ x x≢0) *₂ y) *₂ inv₂ y y≢0  ≡⟨ cong (λ z → z *₂ _) lemma ⟩
      1₂ *₂ inv₂ y y≢0                      ≡⟨ *₂-comm _ _ ⟩
      inv₂ y y≢0 *₂ 1₂                      ≡⟨ *1₂ _ ⟩∎
      inv₂ y y≢0                            ∎

    where
    open _↔_ F₁↔F₂

    inv₁ = λ x x≢0 → proj₁ (*⁻¹₁ x x≢0)
    inv₂ = λ x x≢0 → proj₁ (*⁻¹₂ x x≢0)

    lemma =
      to (inv₁ x x≢0) *₂ y  ≡⟨ *₂-comm _ _ ⟩
      y *₂ to (inv₁ x x≢0)  ≡⟨ sym $ *-homo to-x≡y (refl _) ⟩
      to (x *₁ inv₁ x x≢0)  ≡⟨ cong to $ proj₂ (*⁻¹₁ x x≢0) ⟩
      to 1₁                 ≡⟨ 1-homo ⟩∎
      1₂                    ∎

module Field-partial where

  private

    ⊤-set : Is-set ⊤
    ⊤-set = mono (≤-step (≤-step ≤-refl)) ⊤-contractible

  -- Fields.

  field′ : Code
  field′ =
    -- Addition.
    (id ⇾ id ⇾ id) ⊗

    -- Zero.
    id ⊗

    -- Multiplication.
    (id ⇾ id ⇾ id) ⊗

    -- One.
    id ⊗

    -- Minus.
    (id ⇾ id) ⊗

    -- Multiplicative inverse (a partial operation).
    (id ⇾ k (⊤ , ⊤-set) ⊕ id) ,

    λ { (_ , F-set) (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →

         -- Associativity.
        ((∀ x y z → x + (y + z) ≡ (x + y) + z) ×
         (∀ x y z → x * (y * z) ≡ (x * y) * z) ×

         -- Commutativity.
         (∀ x y → x + y ≡ y + x) ×
         (∀ x y → x * y ≡ y * x) ×

         -- Distributivity.
         (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×

         -- Identity laws.
         (∀ x → x + 0# ≡ x) ×
         (∀ x → x * 1# ≡ x) ×

         -- Zero and one are distinct.
         0# ≢ 1# ×

         -- Inverse laws.
         (∀ x → x + (- x) ≡ 0#) ×
         0# ⁻¹ ≡ inj₁ tt ×
         (∀ x → x ≢ 0# → ⊎-map P.id (_*_ x) (x ⁻¹) ≡ inj₂ 1#)) ,

        λ ext →
          ×-closure 1  (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        ⊥-propositional)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (⊎-closure 0 ⊤-set F-set _ _)
                       (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        ⊎-closure 0 ⊤-set F-set _ _)))))))))) }

  -- The interpretation of the code is reasonable.

  Instance-field′ :
    Instance field′ ≡
    Σ (SET (# 0)) λ { (F , _) →
    Σ ((F → F → F) × F × (F → F → F) × F × (F → F) × (F → ⊤ ⊎ F))
      λ { (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
    (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
    (∀ x y → x + y ≡ y + x) ×
    (∀ x y → x * y ≡ y * x) ×
    (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
    (∀ x → x + 0# ≡ x) ×
    (∀ x → x * 1# ≡ x) ×
    0# ≢ 1# ×
    (∀ x → x + (- x) ≡ 0#) ×
    0# ⁻¹ ≡ inj₁ tt ×
    (∀ x → x ≢ 0# → ⊎-map P.id (_*_ x) (x ⁻¹) ≡ inj₂ 1#) } }
  Instance-field′ = refl _

  -- The notion of isomorphism that we get is also reasonable.

  Isomorphic-field′ :
    ∀ {F₁ F₁-set _+₁_ 0₁ _*₁_ 1₁ -₁_ _⁻¹₁ laws₁
       F₂ F₂-set _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ laws₂} →
    Isomorphic field′
      ((F₁ , F₁-set) , (_+₁_ , 0₁ , _*₁_ , 1₁ , -₁_ , _⁻¹₁) , laws₁)
      ((F₂ , F₂-set) , (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂) , laws₂) ≡
    Σ (F₁ ↔ F₂) λ F₁↔F₂ → let open _↔_ F₁↔F₂ in
    (∀ {x y} → to x ≡ y → ∀ {u v} → to u ≡ v → to (x +₁ u) ≡ y +₂ v) ×
    to 0₁ ≡ 0₂ ×
    (∀ {x y} → to x ≡ y → ∀ {u v} → to u ≡ v → to (x *₁ u) ≡ y *₂ v) ×
    to 1₁ ≡ 1₂ ×
    (∀ {x y} → to x ≡ y → to (-₁ x) ≡ -₂ y) ×
    (∀ {x y} → to x ≡ y →
       ((λ _ _ → tt ≡ tt) ⊎-rel (λ u v → to u ≡ v)) (x ⁻¹₁) (y ⁻¹₂))
  Isomorphic-field′ = refl _

  -- Note that a property of this kind of field is that one can decide
  -- if an element is distinct from zero.

  distinct-from-zero? :
    (F : Instance field′) → let 0# = proj₁ (proj₂ (proj₁ (proj₂ F))) in
    (x : Carrier field′ F) → Dec (x ≢ 0#)
  distinct-from-zero?
    (_ , (_ , 0# , _*_ , 1# , _ , _⁻¹) ,
     (_ , _ , _ , _ , _ , _ , _ , _ , _ , 0⁻¹ , *⁻¹))
    x
    with inspect (x ⁻¹)
  ... | inj₁ tt with-≡ eq = inj₂ λ x≢0# →
    ⊎.inj₁≢inj₂ (inj₁ tt                       ≡⟨⟩
                 ⊎-map P.id (_*_ x) (inj₁ tt)  ≡⟨ cong (⊎-map P.id (_*_ x)) $ sym eq ⟩
                 ⊎-map P.id (_*_ x) (x ⁻¹)     ≡⟨ *⁻¹ x x≢0# ⟩∎
                 inj₂ 1#                       ∎)
  ... | inj₂ x⁻¹ with-≡ eq = inj₁ λ x≡0# →
    ⊎.inj₁≢inj₂ (inj₁ tt   ≡⟨ sym 0⁻¹ ⟩
                 0# ⁻¹     ≡⟨ cong _⁻¹ $ sym x≡0# ⟩
                 x ⁻¹      ≡⟨ eq ⟩∎
                 inj₂ x⁻¹  ∎)

------------------------------------------------------------------------
-- An example: vector spaces

open Field-law

-- Vector spaces over a particular field.

vector-space : Instance field′ → Code
vector-space (F , (_+F_ , _ , _*F_ , 1F , _) , _) =
  -- Addition.
  (id ⇾ id ⇾ id) ⊗

  -- Scalar multiplication.
  (k F ⇾ id ⇾ id) ⊗

  -- Zero vector.
  id ⊗

  -- Additive inverse.
  (id ⇾ id) ,

  λ { (_ , V-set) (_+_ , _*_ , 0V , -_) →

       -- Associativity.
      ((∀ u v w → u + (v + w) ≡ (u + v) + w) ×
       (∀ x y v → x * (y * v) ≡ (x *F y) * v) ×

       -- Commutativity.
       (∀ u v → u + v ≡ v + u) ×

       -- Distributivity.
       (∀ x u v → x * (u + v) ≡ (x * u) + (x * v)) ×
       (∀ x y v → (x +F y) * v ≡ (x * v) + (y * v)) ×

       -- Identity laws.
       (∀ v → v + 0V ≡ v) ×
       (∀ v → 1F * v ≡ v) ×

       -- Inverse law.
       (∀ v → v + (- v) ≡ 0V)) ,

      λ ext →
        ×-closure 1  (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      V-set _ _)
                     (Π-closure ext 1 λ _ →
                      V-set _ _))))))) }

-- The interpretation of the code is reasonable.

Instance-vector-space :
  ∀ {F F-set _+F_ 0F _*F_ 1F -F_ laws} →
  Instance (vector-space
              ((F , F-set) , (_+F_ , 0F , _*F_ , 1F , -F_) , laws)) ≡
  Σ (SET (# 0)) λ { (V , _) →
  Σ ((V → V → V) × (F → V → V) × V × (V → V))
    λ { (_+_ , _*_ , 0V , -_) →
  (∀ u v w → u + (v + w) ≡ (u + v) + w) ×
  (∀ x y v → x * (y * v) ≡ (x *F y) * v) ×
  (∀ u v → u + v ≡ v + u) ×
  (∀ x u v → x * (u + v) ≡ (x * u) + (x * v)) ×
  (∀ x y v → (x +F y) * v ≡ (x * v) + (y * v)) ×
  (∀ v → v + 0V ≡ v) ×
  (∀ v → 1F * v ≡ v) ×
  (∀ v → v + (- v) ≡ 0V) } }
Instance-vector-space = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-vector-space :
  ∀ {F V₁ V₁-set _+₁_ _*₁_ 0₁ -₁_ laws₁
       V₂ V₂-set _+₂_ _*₂_ 0₂ -₂_ laws₂} →
  Isomorphic (vector-space F)
             ((V₁ , V₁-set) , (_+₁_ , _*₁_ , 0₁ , -₁_) , laws₁)
             ((V₂ , V₂-set) , (_+₂_ , _*₂_ , 0₂ , -₂_) , laws₂) ≡
  Σ (V₁ ↔ V₂) λ V₁↔V₂ → let open _↔_ V₁↔V₂ in
  (∀ {a b} → to a ≡ b → ∀ {u v} → to u ≡ v → to (a +₁ u) ≡ b +₂ v) ×
  (∀ {x y} →    x ≡ y → ∀ {u v} → to u ≡ v → to (x *₁ u) ≡ y *₂ v) ×
  to 0₁ ≡ 0₂ ×
  (∀ {u v} → to u ≡ v → to (-₁ u) ≡ -₂ v)
Isomorphic-vector-space = refl _
