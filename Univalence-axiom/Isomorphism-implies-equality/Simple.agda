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

open import Bijection eq as Bijection
  hiding (id; _∘_; inverse; _↔⟨_⟩_; finally-↔)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence using (_⇔_; module _⇔_)
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Preimage eq
open import Prelude as P hiding (id)
open import Univalence-axiom eq
open import Weak-equivalence eq hiding (id; _∘_; inverse)

------------------------------------------------------------------------
-- Universes with some extra stuff

-- A record packing up some assumptions.

record Assumptions : Set₃ where
  field

    -- Univalence at three different levels.

    univ  : Univalence (# 0)
    univ₁ : Univalence (# 1)
    univ₂ : Univalence (# 2)

  abstract

    -- Extensionality.

    ext : Extensionality (# 0) (# 0)
    ext = dependent-extensionality univ₁ (λ _ → univ)

    ext₁ : Extensionality (# 1) (# 1)
    ext₁ = dependent-extensionality univ₂ (λ _ → univ₁)

-- Universes with some extra stuff.

record Universe : Set₃ where
  field

    -- Codes for something.

    U : Set₂

    -- Interpretation of codes.

    El : U → Set₁ → Set₁

    -- A predicate, possibly specifying what it means for a bijection
    -- to be an isomorphism between two elements.

    Is-isomorphism : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁

    -- El a preserves equivalences.

    cast : ∀ a {B C} → B ⇔ C → El a B ⇔ El a C

    -- The cast function respects identities (assuming univalence).

    cast-id :
      Assumptions →
      ∀ a {B} → cast a (Equivalence.id {A = B}) ≡ Equivalence.id

  -- An alternative definition of Is-isomorphism.

  Is-isomorphism′ : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁
  Is-isomorphism′ B↔C a x y =
    _⇔_.to (cast a (_↔_.equivalence B↔C)) x ≡ y

  field

    -- Is-isomorphism and Is-isomorphism′ are isomorphic (assuming
    -- univalence and that one of the underlying types is a set).

    isomorphism-definitions-isomorphic :
      Assumptions →
      ∀ {B C} (B↔C : B ↔ C) → Is-set C →
      ∀ a {x y} →
      Is-isomorphism B↔C a x y ↔ Is-isomorphism′ B↔C a x y

  -- Another alternative definition of Is-isomorphism, defined using
  -- univalence.

  Is-isomorphism″ : Assumptions →
                    ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁
  Is-isomorphism″ ass B↔C a x y =
    subst (El a) (≈⇒≡ univ₁ $ ↔⇒≈ B↔C) x ≡ y
    where open Assumptions ass

  abstract

    -- Every element is isomorphic to itself, transported along the
    -- isomorphism.

    isomorphic-to-itself :
      (ass : Assumptions) → let open Assumptions ass in
      ∀ {B C} (B↔C : B ↔ C) a x →
      Is-isomorphism′ B↔C a x (subst (El a) (≈⇒≡ univ₁ $ ↔⇒≈ B↔C) x)
    isomorphic-to-itself ass B↔C a x =
      subst-unique
        (El a)
        (λ A≈B → _⇔_.to (cast a (_≈_.equivalence A≈B)))
        (λ x → cong (λ f → _⇔_.to f x) $ cast-id ass a)
        univ₁ (↔⇒≈ B↔C) x
      where open Assumptions ass

    -- Is-isomorphism and Is-isomorphism″ are isomorphic (assuming
    -- univalence and that one of the underlying types is a set).

    isomorphism-definitions-isomorphic₂ :
      (ass : Assumptions) →
      ∀ {B C} (B↔C : B ↔ C) → Is-set C →
      ∀ a {x y} →
      Is-isomorphism B↔C a x y ↔ Is-isomorphism″ ass B↔C a x y
    isomorphism-definitions-isomorphic₂ ass B↔C C-set a {x} {y} =
      Is-isomorphism      B↔C a x y  ↝⟨ isomorphism-definitions-isomorphic ass B↔C C-set a ⟩
      Is-isomorphism′     B↔C a x y  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ y) $ isomorphic-to-itself ass B↔C a x ⟩□
      Is-isomorphism″ ass B↔C a x y  □

------------------------------------------------------------------------
-- A universe-indexed family of classes of structures

module Class (Univ : Universe) where

  open Universe Univ

  -- Codes for structures.

  Code : Set₂
  Code =
    -- A code.
    Σ U λ a →

    -- A proposition.
    (A : SET (# 1)) → El a (Type A) → Σ Set₁ λ P →
      -- The proposition should be propositional (assuming
      -- extensionality).
      Extensionality (# 1) (# 1) → Propositional P

  -- Interpretation of the codes. The elements of "Instance a" are
  -- instances of the structure encoded by a.

  Instance : Code → Set₂
  Instance (a , P) =
    -- A carrier set.
    Σ (SET (# 1)) λ A →

    -- An element.
    Σ (El a (Type A)) λ x →

    -- The element should satisfy the proposition.
    proj₁ (P A x)

  -- The carrier set.

  Carrier : ∀ a → Instance a → Set₁
  Carrier _ I = Type (proj₁ I)

  -- The "element".

  element : ∀ a (I : Instance a) → El (proj₁ a) (Carrier a I)
  element _ I = proj₁ (proj₂ I)

  abstract

    -- One can prove that two instances of a structure are equal by
    -- proving that the carrier sets and "elements" (suitably
    -- transported) are equal (assuming extensionality).

    instances-equal↔ :
      Extensionality (# 1) (# 1) →
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

  Isomorphic : ∀ a → Instance a → Instance a → Set₁
  Isomorphic (a , _) ((A₁ , _) , x₁ , _) ((A₂ , _) , x₂ , _) =
    Σ (A₁ ↔ A₂) λ A₁↔A₂ → Is-isomorphism A₁↔A₂ a x₁ x₂

  abstract

    -- The type of isomorphisms between two instances of a structure
    -- is isomorphic to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is isomorphic to equality.

    isomorphic↔equal :
      Assumptions →
      ∀ a {I₁ I₂} → Isomorphic a I₁ I₂ ↔ (I₁ ≡ I₂)
    isomorphic↔equal ass a {I₁} {I₂} =

      (∃ λ (C-eq : Carrier a I₁ ↔ Carrier a I₂) →
         Is-isomorphism C-eq (proj₁ a) (element a I₁) (element a I₂))  ↝⟨ ∃-cong (λ C-eq → isomorphism-definitions-isomorphic₂
                                                                                             ass C-eq I₂-set (proj₁ a)) ⟩
      (∃ λ (C-eq : Carrier a I₁ ↔ Carrier a I₂) →
         subst (El (proj₁ a)) (≈⇒≡ univ₁ $ ↔⇒≈ C-eq) (element a I₁) ≡
         element a I₂)                                                 ↝⟨ inverse $
                                                                            Σ-cong (≡≈↔ univ₁ ext₁ I₁-set) (λ C-eq → ≡⇒↝ _ $ sym $
                                                                              cong (λ eq → subst (El (proj₁ a)) eq (element a I₁) ≡
                                                                                           element a I₂)
                                                                                   (_≈_.left-inverse-of (≡≈↔ univ₁ ext₁ I₁-set) C-eq)) ⟩
      (∃ λ (C-eq : Carrier a I₁ ≡ Carrier a I₂) →
         subst (El (proj₁ a)) C-eq (element a I₁) ≡ element a I₂)      ↝⟨ inverse $ instances-equal↔ ext₁ a ⟩□

      (I₁ ≡ I₂)                                                        □

      where
      open Assumptions ass

      I₁-set : Is-set (Carrier a I₁)
      I₁-set = proj₂ (proj₁ I₁)

      I₂-set : Is-set (Carrier a I₂)
      I₂-set = proj₂ (proj₁ I₂)

    -- The type of (lifted) isomorphisms between two instances of a
    -- structure is equal to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is equal to equality.

    isomorphic≡equal :
      Assumptions →
      ∀ a {I₁ I₂} → ↑ (# 2) (Isomorphic a I₁ I₂) ≡ (I₁ ≡ I₂)
    isomorphic≡equal ass a {I₁} {I₂} =
      ≈⇒≡ univ₂ $ ↔⇒≈ (
        ↑ _ (Isomorphic a I₁ I₂)  ↝⟨ ↑↔ ⟩
        Isomorphic a I₁ I₂        ↝⟨ isomorphic↔equal ass a ⟩□
        (I₁ ≡ I₂)                 □)
      where open Assumptions ass

------------------------------------------------------------------------
-- A universe of non-recursive, simple types

-- Codes for types.
--
-- Note that the argument to k is assumed to be a set.

infixr 20 _⊗_
infixr 15 _⊕_
infixr 10 _⇾_

data U : Set₂ where
  id set      : U
  k           : SET (# 1) → U
  _⇾_ _⊕_ _⊗_ : U → U → U

-- Interpretation of types.

El : U → Set₁ → Set₁
El id      B = B
El set     B = SET (# 0)
El (k A)   B = Type A
El (a ⇾ b) B = El a B → El b B
El (a ⊕ b) B = El a B ⊎ El b B
El (a ⊗ b) B = El a B × El b B

-- El a preserves equivalences.

cast : ∀ a {B C} → B ⇔ C → El a B ⇔ El a C
cast id      B⇔C = B⇔C
cast set     B⇔C = Equivalence.id
cast (k A)   B⇔C = Equivalence.id
cast (a ⇾ b) B⇔C = →-cong-⇔ (cast a B⇔C) (cast b B⇔C)
cast (a ⊕ b) B⇔C = cast a B⇔C ⊎-cong cast b B⇔C
cast (a ⊗ b) B⇔C = cast a B⇔C ×-cong cast b B⇔C

abstract

  -- The cast function respects identities (assuming extensionality).

  cast-id : Extensionality (# 1) (# 1) →
            ∀ a {B} → cast a (Equivalence.id {A = B}) ≡ Equivalence.id
  cast-id ext id      = refl _
  cast-id ext set     = refl _
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
--
-- Note that the equivalence component of cast↔ ext a B↔C is
-- cast a (_↔_.equivalence B↔C); this property is used below.

cast↔ : Extensionality (# 1) (# 1) →
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
  cst set     = Bijection.id
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
    casts-related set     = refl _
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

-- The property of being an isomorphism between two elements.

Is-isomorphism : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁

Is-isomorphism B↔C id = λ x y → _↔_.to B↔C x ≡ y

Is-isomorphism B↔C set = λ X Y → ↑ _ (Type X ↔ Type Y)

Is-isomorphism B↔C (k A) = λ x y → x ≡ y

Is-isomorphism B↔C (a ⇾ b) = λ f g →
  ∀ x y → Is-isomorphism B↔C a x y → Is-isomorphism B↔C b (f x) (g y)

Is-isomorphism B↔C (a ⊕ b) =
  Is-isomorphism B↔C a ⊎-rel Is-isomorphism B↔C b

Is-isomorphism B↔C (a ⊗ b) = λ { (x , u) (y , v) →
  Is-isomorphism B↔C a x y × Is-isomorphism B↔C b u v }

-- Another definition of "being an isomorphism".

Is-isomorphism′ : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁
Is-isomorphism′ B↔C a x y = _⇔_.to (cast a (_↔_.equivalence B↔C)) x ≡ y

abstract

  -- The two definitions of "being an isomorphism" are "isomorphic"
  -- (in bijective correspondence), assuming univalence.

  isomorphism-definitions-isomorphic :
    Assumptions →
    ∀ {B C} (B↔C : B ↔ C) a {x y} →
    Is-isomorphism B↔C a x y ↔ Is-isomorphism′ B↔C a x y

  isomorphism-definitions-isomorphic ass B↔C id = Bijection.id

  isomorphism-definitions-isomorphic ass B↔C set {X , X-set} {Y , Y-set} =
    ↑ _ (X ↔ Y)                  ↝⟨ ↑↔ ⟩
    (X ↔ Y)                      ↝⟨ ↔↔≈ (lower-extensionality _ _ ext₁) X-set ⟩
    (X ≈ Y)                      ↔⟨ inverse $ ≡≈≈ univ ⟩
    (X ≡ Y)                      ↝⟨ ignore-propositional-component (H-level-propositional (lower-extensionality _ _ ext₁) 2) ⟩□
    ((X , X-set) ≡ (Y , Y-set))  □
    where open Assumptions ass

  isomorphism-definitions-isomorphic ass B↔C (k A) = Bijection.id

  isomorphism-definitions-isomorphic ass B↔C (a ⇾ b) {f} {g} =
    let B⇔C = _↔_.equivalence B↔C in

    (∀ x y → Is-isomorphism B↔C a x y →
             Is-isomorphism B↔C b (f x) (g y))                     ↔⟨ ∀-preserves ext₁ (λ _ → ∀-preserves ext₁ λ _ → ↔⇒≈ $
                                                                        →-cong ext₁ (isomorphism-definitions-isomorphic ass B↔C a)
                                                                                    (isomorphism-definitions-isomorphic ass B↔C b)) ⟩
    (∀ x y → to (cast a B⇔C) x ≡ y → to (cast b B⇔C) (f x) ≡ g y)  ↔⟨ inverse $ ∀-preserves ext₁ (λ x →
                                                                        ↔⇒≈ $ ∀-intro ext₁ (λ y → to (cast b B⇔C) (f x) ≡ g y)) ⟩
    (∀ x → to (cast b B⇔C) (f x) ≡ g (to (cast a B⇔C) x))          ↔⟨ extensionality-isomorphism ext₁ ⟩

    (to (cast b B⇔C) ∘ f ≡ g ∘ to (cast a B⇔C))                    ↝⟨ ≡⇒↝ _ $ cong (λ h → to (cast b B⇔C) ∘ f ∘ h ≡ g ∘ to (cast a B⇔C)) $
                                                                        sym $ ext₁ $ _↔_.left-inverse-of (cast↔ ext₁ a B↔C) ⟩
    (to (cast b B⇔C) ∘ f ∘ from (cast a B⇔C) ∘ to (cast a B⇔C) ≡
     g ∘ to (cast a B⇔C))                                          ↔⟨ ≈-≡ $ weq _ $ precomposition-is-weak-equivalence univ₁ $
                                                                        ↔⇒≈ $ cast↔ ext₁ a B↔C ⟩□
    (to (cast b B⇔C) ∘ f ∘ from (cast a B⇔C) ≡ g)                  □

    where
    open _⇔_
    open Assumptions ass

  isomorphism-definitions-isomorphic ass B↔C (a ⊕ b) {inj₁ x} {inj₁ y} =
    let B⇔C = _↔_.equivalence B↔C in

    Is-isomorphism B↔C a x y                 ↝⟨ isomorphism-definitions-isomorphic ass B↔C a ⟩
    (_⇔_.to (cast a B⇔C) x ≡ y)              ↝⟨ ≡↔inj₁≡inj₁ ⟩□
    (inj₁ (_⇔_.to (cast a B⇔C) x) ≡ inj₁ y)  □

  isomorphism-definitions-isomorphic ass B↔C (a ⊕ b) {inj₂ x} {inj₂ y} =
    let B⇔C = _↔_.equivalence B↔C in

    Is-isomorphism B↔C b x y                 ↝⟨ isomorphism-definitions-isomorphic ass B↔C b ⟩
    (_⇔_.to (cast b B⇔C) x ≡ y)              ↝⟨ ≡↔inj₂≡inj₂ ⟩□
    (inj₂ (_⇔_.to (cast b B⇔C) x) ≡ inj₂ y)  □

  isomorphism-definitions-isomorphic ass B↔C (a ⊕ b) {inj₁ x} {inj₂ y} =
    ⊥                  ↝⟨ ⊥↔uninhabited ⊎.inj₁≢inj₂ ⟩□
    (inj₁ _ ≡ inj₂ _)  □

  isomorphism-definitions-isomorphic ass B↔C (a ⊕ b) {inj₂ x} {inj₁ y} =
    ⊥                  ↝⟨ ⊥↔uninhabited (⊎.inj₁≢inj₂ ∘ sym) ⟩□
    (inj₂ _ ≡ inj₁ _)  □

  isomorphism-definitions-isomorphic ass B↔C (a ⊗ b) {x , u} {y , v} =
    let B⇔C = _↔_.equivalence B↔C in

    Is-isomorphism  B↔C a x y × Is-isomorphism  B↔C b u v        ↝⟨ isomorphism-definitions-isomorphic ass B↔C a ×-cong
                                                                    isomorphism-definitions-isomorphic ass B↔C b ⟩
    Is-isomorphism′ B↔C a x y × Is-isomorphism′ B↔C b u v        ↝⟨ ≡×≡↔≡ ⟩□

    ((_⇔_.to (cast a B⇔C) x , _⇔_.to (cast b B⇔C) u) ≡ (y , v))  □

-- The universe above is a "universe with some extra stuff".

simple : Universe
simple = record
  { U                                  = U
  ; El                                 = El
  ; Is-isomorphism                     = Is-isomorphism
  ; cast                               = cast
  ; cast-id                            = λ ass → cast-id (ext₁ ass)
  ; isomorphism-definitions-isomorphic = λ ass B↔C _ →
      isomorphism-definitions-isomorphic ass B↔C
  }
  where open Assumptions

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
  Σ (SET (# 1)) λ { (M , _) →
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
  (∀ x y → to x ≡ y → ∀ u v → to u ≡ v → to (x ∙₁ u) ≡ y ∙₂ v) ×
  to e₁ ≡ e₂
Isomorphic-monoid = refl _

------------------------------------------------------------------------
-- An example: discrete fields

-- Discrete fields.

discrete-field : Code
discrete-field =
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
  (id ⇾ k (↑ _ ⊤ , ⊤-set) ⊕ id) ,

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
       (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
       (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#)) ,

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
        (×-closure 1 (Π-closure (lower-extensionality (# 0) (# 1) ext) 1 λ _ →
                      ⊥-propositional)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      F-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      F-set _ _)
                     (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      F-set _ _)))))))))) }
  where
  ⊤-set : Is-set (↑ (# 1) ⊤)
  ⊤-set = ↑-closure 2 (mono (≤-step (≤-step ≤-refl)) ⊤-contractible)

-- The interpretation of the code is reasonable.

Instance-discrete-field :
  Instance discrete-field ≡
  Σ (SET (# 1)) λ { (F , _) →
  Σ ((F → F → F) × F × (F → F → F) × F × (F → F) × (F → ↑ (# 1) ⊤ ⊎ F))
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
  (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
  (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) } }
Instance-discrete-field = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-discrete-field :
  ∀ {F₁ F₁-set _+₁_ 0₁ _*₁_ 1₁ -₁_ _⁻¹₁ laws₁
     F₂ F₂-set _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ laws₂} →
  Isomorphic discrete-field
    ((F₁ , F₁-set) , (_+₁_ , 0₁ , _*₁_ , 1₁ , -₁_ , _⁻¹₁) , laws₁)
    ((F₂ , F₂-set) , (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂) , laws₂) ≡
  Σ (F₁ ↔ F₂) λ F₁↔F₂ → let open _↔_ F₁↔F₂ in
  (∀ x y → to x ≡ y → ∀ u v → to u ≡ v → to (x +₁ u) ≡ y +₂ v) ×
  to 0₁ ≡ 0₂ ×
  (∀ x y → to x ≡ y → ∀ u v → to u ≡ v → to (x *₁ u) ≡ y *₂ v) ×
  to 1₁ ≡ 1₂ ×
  (∀ x y → to x ≡ y → to (-₁ x) ≡ -₂ y) ×
  (∀ x y → to x ≡ y →
     ((λ _ _ → lift tt ≡ lift tt) ⊎-rel (λ u v → to u ≡ v))
       (x ⁻¹₁) (y ⁻¹₂))
Isomorphic-discrete-field = refl _

------------------------------------------------------------------------
-- An example: vector spaces over discrete fields

-- Vector spaces over a particular discrete field.

vector-space : Instance discrete-field → Code
vector-space (F , (_+F_ , _ , _*F_ , 1F , _ , _) , _) =
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
  ∀ {F F-set _+F_ 0F _*F_ 1F -F_ _⁻¹F laws} →
  Instance (vector-space
    ((F , F-set) , (_+F_ , 0F , _*F_ , 1F , -F_ , _⁻¹F) , laws)) ≡
  Σ (SET (# 1)) λ { (V , _) →
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
  (∀ a b → to a ≡ b → ∀ u v → to u ≡ v → to (a +₁ u) ≡ b +₂ v) ×
  (∀ x y →    x ≡ y → ∀ u v → to u ≡ v → to (x *₁ u) ≡ y *₂ v) ×
  to 0₁ ≡ 0₂ ×
  (∀ u v → to u ≡ v → to (-₁ u) ≡ -₂ v)
Isomorphic-vector-space = refl _
