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

open import Bijection eq
  hiding (id; inverse; _↔⟨_⟩_; finally-↔) renaming (_∘_ to _∘B_)
open Derived-definitions-and-properties eq
  renaming (lower-extensionality to lower-ext)
open import Equality.Decision-procedures eq
open import Equivalence using (_⇔_; module _⇔_)
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Preimage eq
open import Prelude as P hiding (id)
open import Univalence-axiom eq
open import Weak-equivalence eq as Weak hiding (id; _∘_; inverse)

------------------------------------------------------------------------
-- Universes with some extra stuff

-- A record type packing up some assumptions.

record Assumptions : Set₃ where
  field

    -- Univalence at three different levels.

    univ  : Univalence (# 0)
    univ₁ : Univalence (# 1)
    univ₂ : Univalence (# 2)

  abstract

    -- Extensionality.

    ext : Extensionality (# 1) (# 1)
    ext = dependent-extensionality univ₂ (λ _ → univ₁)

-- Universes with some extra stuff.

record Universe : Set₃ where
  field

    -- Codes for something.

    U : Set₂

    -- Interpretation of codes.

    El : U → Set₁ → Set₁

    -- A predicate, possibly specifying what it means for a weak
    -- equivalence to be an isomorphism between two elements.

    Is-isomorphism : ∀ {B C} → B ≈ C → ∀ a → El a B → El a C → Set₁

    -- El a, seen as a predicate, respects weak equivalences (assuming
    -- univalence).

    resp : Assumptions → ∀ a {B C} → B ≈ C → El a B → El a C

    -- The resp function respects identities (assuming univalence).

    resp-id : (ass : Assumptions) →
              ∀ a {B} (x : El a B) → resp ass a Weak.id x ≡ x

  -- An alternative definition of Is-isomorphism, (possibly) defined
  -- using univalence.

  Is-isomorphism′ : Assumptions →
                    ∀ {B C} → B ≈ C → ∀ a → El a B → El a C → Set₁
  Is-isomorphism′ ass B≈C a x y = resp ass a B≈C x ≡ y

  field

    -- Is-isomorphism and Is-isomorphism′ are isomorphic (assuming
    -- univalence).

    isomorphism-definitions-isomorphic :
      (ass : Assumptions) →
      ∀ {B C} (B≈C : B ≈ C) a {x y} →
      Is-isomorphism B≈C a x y ↔ Is-isomorphism′ ass B≈C a x y

  -- Another alternative definition of Is-isomorphism, defined using
  -- univalence.

  Is-isomorphism″ : Assumptions →
                    ∀ {B C} → B ≈ C → ∀ a → El a B → El a C → Set₁
  Is-isomorphism″ ass B≈C a x y = subst (El a) (≈⇒≡ univ₁ B≈C) x ≡ y
    where open Assumptions ass

  abstract

    -- Every element is isomorphic to itself, transported along the
    -- isomorphism.

    isomorphic-to-itself :
      (ass : Assumptions) → let open Assumptions ass in
      ∀ {B C} (B≈C : B ≈ C) a x →
      Is-isomorphism′ ass B≈C a x (subst (El a) (≈⇒≡ univ₁ B≈C) x)
    isomorphic-to-itself ass B≈C a x =
      subst-unique (El a) (resp ass a) (resp-id ass a) univ₁ B≈C x
      where open Assumptions ass

    -- Is-isomorphism and Is-isomorphism″ are isomorphic (assuming
    -- univalence).

    isomorphism-definitions-isomorphic₂ :
      (ass : Assumptions) →
      ∀ {B C} (B≈C : B ≈ C) a {x y} →
      Is-isomorphism B≈C a x y ↔ Is-isomorphism″ ass B≈C a x y
    isomorphism-definitions-isomorphic₂ ass B≈C a {x} {y} =
      Is-isomorphism      B≈C a x y  ↝⟨ isomorphism-definitions-isomorphic ass B≈C a ⟩
      Is-isomorphism′ ass B≈C a x y  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ y) $ isomorphic-to-itself ass B≈C a x ⟩□
      Is-isomorphism″ ass B≈C a x y  □

------------------------------------------------------------------------
-- A universe-indexed family of classes of structures

module Class (Univ : Universe) where

  open Universe Univ

  -- Codes for structures.

  Code : Set₃
  Code =
    -- A code.
    Σ U λ a →

    -- A proposition.
    (C : Set₁) → El a C → Σ Set₁ λ P →
      -- The proposition should be propositional (assuming
      -- univalence).
      Assumptions → Propositional P

  -- Interpretation of the codes. The elements of "Instance c" are
  -- instances of the structure encoded by c.

  Instance : Code → Set₂
  Instance (a , P) =
    -- A carrier type.
    Σ Set₁ λ C →

    -- An element.
    Σ (El a C) λ x →

    -- The element should satisfy the proposition.
    proj₁ (P C x)

  -- The carrier type.

  Carrier : ∀ c → Instance c → Set₁
  Carrier _ I = proj₁ I

  -- The "element".

  element : ∀ c (I : Instance c) → El (proj₁ c) (Carrier c I)
  element _ I = proj₁ (proj₂ I)

  abstract

    -- One can prove that two instances of a structure are equal by
    -- proving that the carrier types and "elements" (suitably
    -- transported) are equal (assuming univalence).

    instances-equal↔ :
      Assumptions →
      ∀ c {I₁ I₂} →
      (I₁ ≡ I₂) ↔
      ∃ λ (C-eq : Carrier c I₁ ≡ Carrier c I₂) →
        subst (El (proj₁ c)) C-eq (element c I₁) ≡ element c I₂
    instances-equal↔ ass (a , P) {C₁ , x₁ , p₁} {C₂ , x₂ , p₂} =

      ((C₁ , x₁ , p₁) ≡ (C₂ , x₂ , p₂))                   ↔⟨ inverse $ ≈-≡ $ ↔⇒≈ Σ-assoc ⟩

      (((C₁ , x₁) , p₁) ≡ ((C₂ , x₂) , p₂))               ↝⟨ inverse $ ignore-propositional-component (proj₂ (P C₂ x₂) ass) ⟩

      ((C₁ , x₁) ≡ (C₂ , x₂))                             ↝⟨ inverse Σ-≡,≡↔≡ ⟩□

      (∃ λ (C-eq : C₁ ≡ C₂) → subst (El a) C-eq x₁ ≡ x₂)  □

  -- Structure isomorphisms.

  Isomorphic : ∀ c → Instance c → Instance c → Set₁
  Isomorphic (a , _) (C₁ , x₁ , _) (C₂ , x₂ , _) =
    Σ (C₁ ≈ C₂) λ C₁≈C₂ → Is-isomorphism C₁≈C₂ a x₁ x₂

  abstract

    -- The type of isomorphisms between two instances of a structure
    -- is isomorphic to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is isomorphic to equality.

    isomorphic↔equal :
      Assumptions →
      ∀ c {I₁ I₂} → Isomorphic c I₁ I₂ ↔ (I₁ ≡ I₂)
    isomorphic↔equal ass c {I₁} {I₂} =

      (∃ λ (C-eq : Carrier c I₁ ≈ Carrier c I₂) →
         Is-isomorphism C-eq (proj₁ c) (element c I₁) (element c I₂))  ↝⟨ ∃-cong (λ C-eq → isomorphism-definitions-isomorphic₂
                                                                                             ass C-eq (proj₁ c)) ⟩
      (∃ λ (C-eq : Carrier c I₁ ≈ Carrier c I₂) →
         subst (El (proj₁ c)) (≈⇒≡ univ₁ C-eq) (element c I₁) ≡
         element c I₂)                                                 ↝⟨ inverse $
                                                                            Σ-cong (≡≈≈ univ₁) (λ C-eq → ≡⇒↝ _ $ sym $
                                                                              cong (λ eq → subst (El (proj₁ c)) eq (element c I₁) ≡
                                                                                           element c I₂)
                                                                                   (_≈_.left-inverse-of (≡≈≈ univ₁) C-eq)) ⟩
      (∃ λ (C-eq : Carrier c I₁ ≡ Carrier c I₂) →
         subst (El (proj₁ c)) C-eq (element c I₁) ≡ element c I₂)      ↝⟨ inverse $ instances-equal↔ ass c ⟩□

      (I₁ ≡ I₂)                                                        □

      where open Assumptions ass

    -- The type of (lifted) isomorphisms between two instances of a
    -- structure is equal to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is equal to equality.

    isomorphic≡equal :
      Assumptions →
      ∀ c {I₁ I₂} → ↑ (# 2) (Isomorphic c I₁ I₂) ≡ (I₁ ≡ I₂)
    isomorphic≡equal ass c {I₁} {I₂} =
      ≈⇒≡ univ₂ $ ↔⇒≈ (
        ↑ _ (Isomorphic c I₁ I₂)  ↝⟨ ↑↔ ⟩
        Isomorphic c I₁ I₂        ↝⟨ isomorphic↔equal ass c ⟩□
        (I₁ ≡ I₂)                 □)
      where open Assumptions ass

------------------------------------------------------------------------
-- A universe of non-recursive, simple types

-- Codes for types.

infixr 20 _⊗_
infixr 15 _⊕_
infixr 10 _⇾_

data U : Set₂ where
  id set      : U
  k           : Set₁ → U
  _⇾_ _⊕_ _⊗_ : U → U → U

-- Interpretation of types.

El : U → Set₁ → Set₁
El id      B = B
El set     B = Set
El (k A)   B = A
El (a ⇾ b) B = El a B → El b B
El (a ⊕ b) B = El a B ⊎ El b B
El (a ⊗ b) B = El a B × El b B

-- El a preserves weak equivalences (assuming extensionality).

cast : Extensionality (# 1) (# 1) →
       ∀ a {B C} → B ≈ C → El a B ≈ El a C
cast ext id      B≈C = B≈C
cast ext set     B≈C = Weak.id
cast ext (k A)   B≈C = Weak.id
cast ext (a ⇾ b) B≈C = →-cong ext (cast ext a B≈C) (cast ext b B≈C)
cast ext (a ⊕ b) B≈C = cast ext a B≈C ⊎-cong cast ext b B≈C
cast ext (a ⊗ b) B≈C = cast ext a B≈C ×-cong cast ext b B≈C

abstract

  -- The cast function respects identities (assuming extensionality).

  cast-id : (ext : Extensionality (# 1) (# 1)) →
            ∀ a {B} → cast ext a (Weak.id {A = B}) ≡ Weak.id
  cast-id ext id      = refl _
  cast-id ext set     = refl _
  cast-id ext (k A)   = refl _
  cast-id ext (a ⇾ b) = lift-equality ext $ cong _≈_.to $
                          cong₂ (→-cong ext) (cast-id ext a) (cast-id ext b)
  cast-id ext (a ⊗ b) = lift-equality ext $ cong _≈_.to $
                          cong₂ _×-cong_ (cast-id ext a) (cast-id ext b)
  cast-id ext (a ⊕ b) =
    cast ext a Weak.id ⊎-cong cast ext b Weak.id  ≡⟨ cong₂ _⊎-cong_ (cast-id ext a) (cast-id ext b) ⟩
    weq [ inj₁ , inj₂ ] _                         ≡⟨ lift-equality ext (ext [ refl ∘ inj₁ , refl ∘ inj₂ ]) ⟩∎
    Weak.id                                       ∎

-- The property of being an isomorphism between two elements.

Is-isomorphism : ∀ {B C} → B ≈ C → ∀ a → El a B → El a C → Set₁
Is-isomorphism B≈C id      = λ x y → _≈_.to B≈C x ≡ y
Is-isomorphism B≈C set     = λ X Y → ↑ _ (X ≈ Y)
Is-isomorphism B≈C (k A)   = λ x y → x ≡ y
Is-isomorphism B≈C (a ⇾ b) = Is-isomorphism B≈C a →-rel
                             Is-isomorphism B≈C b
Is-isomorphism B≈C (a ⊕ b) = Is-isomorphism B≈C a ⊎-rel
                             Is-isomorphism B≈C b
Is-isomorphism B≈C (a ⊗ b) = Is-isomorphism B≈C a ×-rel
                             Is-isomorphism B≈C b

-- Another definition of "being an isomorphism" (defined using
-- extensionality).

Is-isomorphism′ : Extensionality (# 1) (# 1) →
                  ∀ {B C} → B ≈ C → ∀ a → El a B → El a C → Set₁
Is-isomorphism′ ext B≈C a x y = _≈_.to (cast ext a B≈C) x ≡ y

abstract

  -- The two definitions of "being an isomorphism" are "isomorphic"
  -- (in bijective correspondence), assuming univalence.

  isomorphism-definitions-isomorphic :
    (ass : Assumptions) → let open Assumptions ass in
    ∀ {B C} (B≈C : B ≈ C) a {x y} →
    Is-isomorphism B≈C a x y ↔ Is-isomorphism′ ext B≈C a x y

  isomorphism-definitions-isomorphic ass B≈C id {x} {y} =

    (_≈_.to B≈C x ≡ y)  □

  isomorphism-definitions-isomorphic ass B≈C set {X} {Y} =

    ↑ _ (X ≈ Y)  ↝⟨ ↑↔ ⟩

    (X ≈ Y)      ↔⟨ inverse $ ≡≈≈ univ ⟩

    (X ≡ Y)      □

    where open Assumptions ass

  isomorphism-definitions-isomorphic ass B≈C (k A) {x} {y} =

    (x ≡ y) □

  isomorphism-definitions-isomorphic ass B≈C (a ⇾ b) {f} {g} =

    (∀ x y → Is-isomorphism B≈C a x y →
             Is-isomorphism B≈C b (f x) (g y))                     ↔⟨ ∀-preserves ext (λ _ → ∀-preserves ext λ _ → ↔⇒≈ $
                                                                        →-cong ext (isomorphism-definitions-isomorphic ass B≈C a)
                                                                                   (isomorphism-definitions-isomorphic ass B≈C b)) ⟩
    (∀ x y → to (cast ext a B≈C) x ≡ y →
             to (cast ext b B≈C) (f x) ≡ g y)                      ↔⟨ inverse $ ∀-preserves ext (λ x →
                                                                        ↔⇒≈ $ ∀-intro ext (λ y _ → to (cast ext b B≈C) (f x) ≡ g y)) ⟩
    (∀ x → to (cast ext b B≈C) (f x) ≡ g (to (cast ext a B≈C) x))  ↔⟨ extensionality-isomorphism ext ⟩

    (to (cast ext b B≈C) ∘ f ≡ g ∘ to (cast ext a B≈C))            ↝⟨ inverse $ ∘from≡↔≡∘to ext (cast ext a B≈C) ⟩□

    (to (cast ext b B≈C) ∘ f ∘ from (cast ext a B≈C) ≡ g)          □

    where
    open _≈_
    open Assumptions ass

  isomorphism-definitions-isomorphic ass B≈C (a ⊕ b) {inj₁ x} {inj₁ y} =

    Is-isomorphism B≈C a x y                 ↝⟨ isomorphism-definitions-isomorphic ass B≈C a ⟩

    (to (cast ext a B≈C) x ≡ y)              ↝⟨ ≡↔inj₁≡inj₁ ⟩□

    (inj₁ (to (cast ext a B≈C) x) ≡ inj₁ y)  □

    where
    open _≈_
    open Assumptions ass

  isomorphism-definitions-isomorphic ass B≈C (a ⊕ b) {inj₂ x} {inj₂ y} =

    Is-isomorphism B≈C b x y                 ↝⟨ isomorphism-definitions-isomorphic ass B≈C b ⟩

    (to (cast ext b B≈C) x ≡ y)              ↝⟨ ≡↔inj₂≡inj₂ ⟩□

    (inj₂ (to (cast ext b B≈C) x) ≡ inj₂ y)  □

    where
    open _≈_
    open Assumptions ass

  isomorphism-definitions-isomorphic ass B≈C (a ⊕ b) {inj₁ x} {inj₂ y} =

    ⊥                  ↝⟨ ⊥↔uninhabited ⊎.inj₁≢inj₂ ⟩□

    (inj₁ _ ≡ inj₂ _)  □

  isomorphism-definitions-isomorphic ass B≈C (a ⊕ b) {inj₂ x} {inj₁ y} =

    ⊥                  ↝⟨ ⊥↔uninhabited (⊎.inj₁≢inj₂ ∘ sym) ⟩□

    (inj₂ _ ≡ inj₁ _)  □

  isomorphism-definitions-isomorphic ass B≈C (a ⊗ b) {x , u} {y , v} =

    Is-isomorphism  B≈C a x y × Is-isomorphism  B≈C b u v        ↝⟨ isomorphism-definitions-isomorphic ass B≈C a ×-cong
                                                                    isomorphism-definitions-isomorphic ass B≈C b ⟩
    (to (cast ext a B≈C) x ≡ y × to (cast ext b B≈C) u ≡ v)      ↝⟨ ≡×≡↔≡ ⟩□

    ((to (cast ext a B≈C) x , to (cast ext b B≈C) u) ≡ (y , v))  □

    where
    open _≈_
    open Assumptions ass

-- The universe above is a "universe with some extra stuff".

simple : Universe
simple = record
  { U              = U
  ; El             = El
  ; Is-isomorphism = Is-isomorphism
  ; resp           = λ ass a → _≈_.to ∘ cast (ext ass) a
  ; resp-id        = λ ass a x →
                       cong (λ f → _≈_.to f x) $ cast-id (ext ass) a
  ; isomorphism-definitions-isomorphic =
      isomorphism-definitions-isomorphic
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

  λ { M (_∙_ , e) →

       -- The carrier type is a set.
      (Is-set M ×

       -- Left and right identity laws.
       (∀ x → e ∙ x ≡ x) ×
       (∀ x → x ∙ e ≡ x) ×

       -- Associativity.
       (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z)) ,

       -- The laws are propositional (assuming extensionality).
      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (M-set , _) →
          ×-closure 1  (H-level-propositional ext 2)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        M-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        M-set _ _)
                       (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        M-set _ _))) }}

-- The interpretation of the code is reasonable.

Instance-monoid :

  Instance monoid
    ≡
  Σ Set₁ λ M →
  Σ ((M → M → M) × M) λ { (_∙_ , e) →
  Is-set M ×
  (∀ x → e ∙ x ≡ x) ×
  (∀ x → x ∙ e ≡ x) ×
  (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z) }

Instance-monoid = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-monoid :
  ∀ {M₁ _∙₁_ e₁ laws₁ M₂ _∙₂_ e₂ laws₂} →

  Isomorphic monoid (M₁ , (_∙₁_ , e₁) , laws₁)
                    (M₂ , (_∙₂_ , e₂) , laws₂)
    ≡
  Σ (M₁ ≈ M₂) λ M₁≈M₂ → let open _≈_ M₁≈M₂ in
  (∀ x y → to x ≡ y → ∀ u v → to u ≡ v → to (x ∙₁ u) ≡ y ∙₂ v) ×
  to e₁ ≡ e₂

Isomorphic-monoid = refl _

-- Note that this definition of isomorphism is isomorphic to a more
-- standard one (assuming extensionality).

Isomorphism-monoid-isomorphic-to-standard :
  Extensionality (# 1) (# 1) →
  ∀ {M₁ _∙₁_ e₁ laws₁ M₂ _∙₂_ e₂ laws₂} →

  Isomorphic monoid (M₁ , (_∙₁_ , e₁) , laws₁)
                    (M₂ , (_∙₂_ , e₂) , laws₂)
    ↔
  Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
  (∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y) ×
  to e₁ ≡ e₂

Isomorphism-monoid-isomorphic-to-standard ext
  {M₁} {_∙₁_} {e₁} {laws₁} {M₂} {_∙₂_} {e₂} =

  (Σ (M₁ ≈ M₂) λ M₁≈M₂ → let open _≈_ M₁≈M₂ in
   (∀ x y → to x ≡ y → ∀ u v → to u ≡ v → to (x ∙₁ u) ≡ y ∙₂ v) ×
   to e₁ ≡ e₂)                                                     ↝⟨ inverse $ Σ-cong (↔↔≈ ext (proj₁ laws₁)) (λ _ → _ □) ⟩

  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
   (∀ x y → to x ≡ y → ∀ u v → to u ≡ v → to (x ∙₁ u) ≡ y ∙₂ v) ×
   to e₁ ≡ e₂)                                                     ↔⟨ inverse $ ∃-cong (λ _ →
                                                                        (∀-preserves ext λ _ → ↔⇒≈ $ ∀-intro ext λ _ _ → _) ×-cong (_ □)) ⟩
  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
   (∀ x u v → to u ≡ v → to (x ∙₁ u) ≡ to x ∙₂ v) ×
   to e₁ ≡ e₂)                                                     ↔⟨ inverse $ ∃-cong (λ _ →
                                                                        (∀-preserves ext λ _ → ∀-preserves ext λ _ → ↔⇒≈ $ ∀-intro ext λ _ _ → _)
                                                                          ×-cong
                                                                        (_ □)) ⟩□
  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
   (∀ x u → to (x ∙₁ u) ≡ to x ∙₂ to u) ×
   to e₁ ≡ e₂)                                                     □

------------------------------------------------------------------------
-- An example: discrete fields

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
  (id ⇾ k (↑ _ ⊤) ⊕ id) ,

  λ { F (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →

       -- The carrier type is a set.
      (Is-set F ×

       -- Associativity.
       (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
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

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (F-set , _) →
          ×-closure 1  (H-level-propositional ext 2)
          (×-closure 1 (Π-closure ext 1 λ _ →
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
          (×-closure 1 (Π-closure (lower-ext (# 0) (# 1) ext) 1 λ _ →
                        ⊥-propositional)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        F-set _ _)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _)
                       (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _))))))))))) }}

-- The interpretation of the code is reasonable.

Instance-discrete-field :

  Instance discrete-field
    ≡
  Σ Set₁ λ F →
  Σ ((F → F → F) × F × (F → F → F) × F × (F → F) × (F → ↑ _ ⊤ ⊎ F))
    λ { (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →
  Is-set F ×
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
  (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) }

Instance-discrete-field = refl _

-- nLab defines a discrete field as a commutative ring satisfying the
-- property that "an element is invertible xor it equals zero"
-- (http://ncatlab.org/nlab/show/field). This definition of discrete
-- fields is isomorphic to the one given above (assuming
-- extensionality).

Instance-discrete-field-isomorphic-to-standard :
  Extensionality (# 1) (# 1) →

  Instance discrete-field
    ↔
  Σ Set₁ λ F →
  Σ ((F → F → F) × F × (F → F → F) × F × (F → F))
    λ { (_+_ , 0# , _*_ , 1# , -_) →
  Is-set F ×
  (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
  (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
  (∀ x y → x + y ≡ y + x) ×
  (∀ x y → x * y ≡ y * x) ×
  (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
  (∀ x → x + 0# ≡ x) ×
  (∀ x → x * 1# ≡ x) ×
  (∀ x → x + (- x) ≡ 0#) ×
  (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#)) }

Instance-discrete-field-isomorphic-to-standard ext = ∃-cong λ F →
  (Σ ((F → F → F) × F × (F → F → F) × F × (F → F) × (F → ↑ _ ⊤ ⊎ F))
      λ { (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →
          Is-set F ×
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
          (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#)})                        ↝⟨ Σ-cong (lemma₁ _ _ _ _ _ _) (λ _ →
                                                                                   lemma₂ _ _ _ _ _ _ _ _ _ _ _) ⟩
  (Σ (((F → F → F) × F × (F → F → F) × F × (F → F)) × (F → ↑ _ ⊤ ⊎ F))
     λ { ((_+_ , 0# , _*_ , 1# , -_) , _⁻¹) →
         The-rest F _+_ 0# _*_ 1# -_ ×
         0# ≢ 1# ×
         (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
         (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) })                        ↝⟨ inverse Σ-assoc ⟩

  (Σ ((F → F → F) × F × (F → F → F) × F × (F → F))
     λ { (_+_ , 0# , _*_ , 1# , -_) →
         Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
         The-rest F _+_ 0# _*_ 1# -_ ×
         0# ≢ 1# ×
         (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
         (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) })                        ↝⟨ ∃-cong (λ _ → ∃-comm) ⟩

  (Σ ((F → F → F) × F × (F → F → F) × F × (F → F))
     λ { (_+_ , 0# , _*_ , 1# , -_) →
         The-rest F _+_ 0# _*_ 1# -_ ×
         Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
         0# ≢ 1# ×
         (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
         (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) })                        ↝⟨ ∃-cong (λ { (_+_ , 0# , _*_ , 1# , -_) →
                                                                                       ∃-cong (main-lemma _+_ 0# _*_ 1# -_) }) ⟩

  (Σ ((F → F → F) × F × (F → F → F) × F × (F → F))
     λ { (_+_ , 0# , _*_ , 1# , -_) →
         The-rest F _+_ 0# _*_ 1# -_ ×
         (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#)) })                   ↝⟨ ∃-cong (λ _ → inverse $ ×-assoc ∘B ×-assoc ∘B ×-assoc ∘B
                                                                                                   ×-assoc ∘B ×-assoc ∘B ×-assoc ∘B
                                                                                                   ×-assoc ∘B ×-assoc) ⟩□
  (Σ ((F → F → F) × F × (F → F → F) × F × (F → F))
    λ { (_+_ , 0# , _*_ , 1# , -_) →
        Is-set F ×
        (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
        (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
        (∀ x y → x + y ≡ y + x) ×
        (∀ x y → x * y ≡ y * x) ×
        (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
        (∀ x → x + 0# ≡ x) ×
        (∀ x → x * 1# ≡ x) ×
        (∀ x → x + (- x) ≡ 0#) ×
        (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#)) })                    □
  where
  The-rest :
    (F : Set₁) → (F → F → F) → F → (F → F → F) → F → (F → F) → Set₁
  The-rest F _+_ 0# _*_ 1# -_ = (((((((
    Is-set F ×
    (∀ x y z → x + (y + z) ≡ (x + y) + z)) ×
    (∀ x y z → x * (y * z) ≡ (x * y) * z)) ×
    (∀ x y → x + y ≡ y + x)) ×
    (∀ x y → x * y ≡ y * x)) ×
    (∀ x y z → x * (y + z) ≡ (x * y) + (x * z))) ×
    (∀ x → x + 0# ≡ x)) ×
    (∀ x → x * 1# ≡ x)) ×
    (∀ x → x + (- x) ≡ 0#)

  main-lemma :
    ∀ {F} _+_ 0# _*_ 1# -_ →
    The-rest F _+_ 0# _*_ 1# -_ →

    (Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
       0# ≢ 1# ×
       (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
       (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#))
      ↔
    (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#))

  main-lemma {F} _+_ 0# _*_ 1# -_
    ((((((((F-set , +-assoc) , _) , +-comm) , *-comm) ,
            *+) , +0) , *1) , +-) = record
    { surjection = record
      { equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of = from∘to
    }
    where
    0* : 0# ≢ 1# → ∀ x → 0# * x ≡ 0#
    0* 0≢1 x =
      0# * x                ≡⟨ sym $ +0 _ ⟩
      (0# * x) + 0#         ≡⟨ cong (_+_ _) $ sym $ +- _ ⟩
      (0# * x) + (x + - x)  ≡⟨ +-assoc _ _ _ ⟩
      ((0# * x) + x) + - x  ≡⟨ cong (λ y → y + _) lemma ⟩
      x + - x               ≡⟨ +- x ⟩∎
      0#                    ∎
      where
      lemma =
        (0# * x) + x         ≡⟨ cong (_+_ _) $ sym $ *1 _ ⟩
        (0# * x) + (x * 1#)  ≡⟨ cong (λ y → y + (x * 1#)) $ *-comm _ _ ⟩
        (x * 0#) + (x * 1#)  ≡⟨ sym $ *+ _ _ _ ⟩
        x * (0# + 1#)        ≡⟨ cong (_*_ _) $ +-comm _ _ ⟩
        x * (1# + 0#)        ≡⟨ cong (_*_ _) $ +0 _ ⟩
        x * 1#               ≡⟨ *1 _ ⟩∎
        x                    ∎

    01-lemma : 0# ≢ 1# → ∀ x y → x ≡ 0# → x * y ≡ 1# → ⊥
    01-lemma 0≢1 x y x≡0 xy≡1 = 0≢1 (
      0#      ≡⟨ sym $ 0* 0≢1 _ ⟩
      0# * y  ≡⟨ cong (λ x → x * _) $ sym x≡0 ⟩
      x * y   ≡⟨ xy≡1 ⟩∎
      1#      ∎)

    To   = ∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#)
    From = Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
           0# ≢ 1# ×
           (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
           (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#)

    to′ : (f : From) → ∀ x y → proj₁ f x ≡ y →
          (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#)
    to′ (_⁻¹ , 0≢1 , ⁻¹0 , ⁻¹1) x (inj₁ _) x⁻¹≡₁ =
      inj₂ ((λ { (y , xy≡1) → 01-lemma 0≢1 x y (⁻¹0 x (x⁻¹≡₁)) xy≡1 }) ,
            ⁻¹0 x (x⁻¹≡₁))
    to′ (_⁻¹ , 0≢1 , ⁻¹0 , ⁻¹1) x (inj₂ y) x⁻¹≡y =
      inj₁ ((y , ⁻¹1 x y x⁻¹≡y) , λ x≡0 →
            01-lemma 0≢1 x y x≡0 (⁻¹1 x y x⁻¹≡y))

    to : From → To
    to f x = to′ f x (proj₁ f x) (refl _)

    drop-prop : ∀ {x} → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#) → ↑ _ ⊤ ⊎ F
    drop-prop = [ inj₂ ∘ proj₁ ∘ proj₁ , const (inj₁ _) ]

    from : To → From
    from _⁻¹ = drop-prop ∘ _⁻¹ ,
               [ (λ { (_ , 1≢0) → 1≢0 ∘ sym })
               , (λ { (∄y→1y≡1 , _) → const (∄y→1y≡1 (1# , *1 _)) })
               ] (1# ⁻¹) ,
               lemma₁ , lemma₂
      where
      lemma₁ : ∀ x → drop-prop (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#
      lemma₁ x x⁻¹≡₁ with x ⁻¹
      ... | inj₁ _         = ⊥-elim $ ⊎.inj₁≢inj₂ (sym x⁻¹≡₁)
      ... | inj₂ (_ , x≡0) = x≡0

      lemma₂ : ∀ x y → drop-prop (x ⁻¹) ≡ inj₂ y → x * y ≡ 1#
      lemma₂ x y x⁻¹≡y with x ⁻¹
      ... | inj₂ _                  = ⊥-elim $ ⊎.inj₁≢inj₂ x⁻¹≡y
      ... | inj₁ ((y′ , xy′≡1) , _) =
        subst (λ y → x * y ≡ 1#) (⊎.cancel-inj₂ x⁻¹≡y) xy′≡1

    to∘from : ∀ _⁻¹ → to (from _⁻¹) ≡ _⁻¹
    to∘from _⁻¹ = ext λ x → lemma x (x ⁻¹) (refl _)
      where
      lemma : ∀ x y (eq : drop-prop (x ⁻¹) ≡ drop-prop y) →
              to′ (from _⁻¹) x (drop-prop y) eq ≡ y
      lemma _ (inj₁ _) _ = cong inj₁ $
        Σ-≡,≡→≡ (Σ-≡,≡→≡ (refl _)
                   (_⇔_.to propositional⇔irrelevant (F-set _ _) _ _))
          (_⇔_.to propositional⇔irrelevant
                  (¬-propositional (lower-ext (# 0) _ ext)) _ _)
      lemma _ (inj₂ _) _ = cong inj₂ $
        _⇔_.to propositional⇔irrelevant
               (×-closure 1 (¬-propositional (lower-ext (# 0) _ ext))
                            (F-set _ _)) _ _

    from∘to : ∀ f → from (to f) ≡ f
    from∘to f = Σ-≡,≡→≡ (ext λ x → lemma x _ (refl _))
      (_⇔_.to propositional⇔irrelevant
                (×-closure 1  (¬-propositional (lower-ext (# 0) _ ext))
                 (×-closure 1 (Π-closure ext 1 λ _ →
                               Π-closure ext 1 λ _ →
                               F-set _ _)
                              (Π-closure ext 1 λ _ →
                               Π-closure ext 1 λ _ →
                               Π-closure ext 1 λ _ →
                               F-set _ _)))
                _ _)
      where
      lemma : ∀ x y x⁻¹≡y → drop-prop (to′ f x y x⁻¹≡y) ≡ proj₁ f x
      lemma x (inj₁ _) x⁻¹≡₁ = sym x⁻¹≡₁
      lemma x (inj₂ y) x⁻¹≡y = sym x⁻¹≡y

  lemma₁ : (A B C D E F : Set₁) →
           (A × B × C × D × E × F) ↔ ((A × B × C × D × E) × F)
  lemma₁ A B C D E F =
    (A × B × C × D × E × F)          ↝⟨ ×-assoc ∘B ×-assoc ∘B ×-assoc ∘B ×-assoc ⟩
    (((((A × B) × C) × D) × E) × F)  ↝⟨ inverse (×-assoc ∘B ×-assoc ∘B ×-assoc) ×-cong (_ □) ⟩□
    ((A × B × C × D × E) × F)        □

  lemma₂ : (A B C D E F G H I J K : Set₁) →
           (A × B × C × D × E × F × G × H × I × J × K) ↔
           (((((((((A × B) × C) × D) × E) × F) × G) × H) × J) × I × K)
  lemma₂ A B C D E F G H I J K =
    (A × B × C × D × E × F × G × H × I × J × K)                  ↝⟨ ×-assoc ∘B ×-assoc ∘B ×-assoc ∘B ×-assoc ∘B ×-assoc ∘B ×-assoc ∘B ×-assoc ⟩
    ((((((((A × B) × C) × D) × E) × F) × G) × H) × I × J × K)    ↝⟨ (_ □) ×-cong ×-assoc ⟩
    ((((((((A × B) × C) × D) × E) × F) × G) × H) × (I × J) × K)  ↝⟨ (_ □) ×-cong (×-comm ×-cong (_ □)) ⟩
    ((((((((A × B) × C) × D) × E) × F) × G) × H) × (J × I) × K)  ↝⟨ (_ □) ×-cong inverse ×-assoc ⟩
    ((((((((A × B) × C) × D) × E) × F) × G) × H) × J × I × K)    ↝⟨ ×-assoc ⟩□
    (((((((((A × B) × C) × D) × E) × F) × G) × H) × J) × I × K)  □

-- The notion of isomorphism that we get is reasonable.

Isomorphic-discrete-field :
  ∀ {F₁ _+₁_ 0₁ _*₁_ 1₁ -₁_ _⁻¹₁ laws₁
     F₂ _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ laws₂} →

  Isomorphic discrete-field
             (F₁ , (_+₁_ , 0₁ , _*₁_ , 1₁ , -₁_ , _⁻¹₁) , laws₁)
             (F₂ , (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂) , laws₂)
    ≡
  Σ (F₁ ≈ F₂) λ F₁≈F₂ → let open _≈_ F₁≈F₂ in
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

  λ { V (_+_ , _*_ , 0V , -_) →

       -- The carrier type is a set.
      (Is-set V ×

       -- Associativity.
       (∀ u v w → u + (v + w) ≡ (u + v) + w) ×
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

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (V-set , _) →
          ×-closure 1  (H-level-propositional ext 2)
          (×-closure 1 (Π-closure ext 1 λ _ →
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
                        V-set _ _)))))))) }}

-- The interpretation of the code is reasonable.

Instance-vector-space :
  ∀ {F _+F_ 0F _*F_ 1F -F_ _⁻¹F laws} →

  Instance (vector-space
              (F , (_+F_ , 0F , _*F_ , 1F , -F_ , _⁻¹F) , laws))
    ≡
  Σ Set₁ λ V →
  Σ ((V → V → V) × (F → V → V) × V × (V → V))
    λ { (_+_ , _*_ , 0V , -_) →
  Is-set V ×
  (∀ u v w → u + (v + w) ≡ (u + v) + w) ×
  (∀ x y v → x * (y * v) ≡ (x *F y) * v) ×
  (∀ u v → u + v ≡ v + u) ×
  (∀ x u v → x * (u + v) ≡ (x * u) + (x * v)) ×
  (∀ x y v → (x +F y) * v ≡ (x * v) + (y * v)) ×
  (∀ v → v + 0V ≡ v) ×
  (∀ v → 1F * v ≡ v) ×
  (∀ v → v + (- v) ≡ 0V) }

Instance-vector-space = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-vector-space :
  ∀ {F V₁ _+₁_ _*₁_ 0₁ -₁_ laws₁
       V₂ _+₂_ _*₂_ 0₂ -₂_ laws₂} →

  Isomorphic (vector-space F)
             (V₁ , (_+₁_ , _*₁_ , 0₁ , -₁_) , laws₁)
             (V₂ , (_+₂_ , _*₂_ , 0₂ , -₂_) , laws₂)
    ≡
  Σ (V₁ ≈ V₂) λ V₁≈V₂ → let open _≈_ V₁≈V₂ in
  (∀ a b → to a ≡ b → ∀ u v → to u ≡ v → to (a +₁ u) ≡ b +₂ v) ×
  (∀ x y →    x ≡ y → ∀ u v → to u ≡ v → to (x *₁ u) ≡ y *₂ v) ×
  to 0₁ ≡ 0₂ ×
  (∀ u v → to u ≡ v → to (-₁ u) ≡ -₂ v)

Isomorphic-vector-space = refl _

------------------------------------------------------------------------
-- An example: posets

poset : Code
poset =
  -- The ordering relation.
  (id ⇾ id ⇾ set) ,

  λ P _≤_ →

     -- The carrier type is a set.
    (Is-set P ×

     -- The ordering relation is (pointwise) propositional.
     (∀ x y → Propositional (x ≤ y)) ×

     -- Reflexivity.
     (∀ x → x ≤ x) ×

     -- Transitivity.
     (∀ x y z → x ≤ y → y ≤ z → x ≤ z) ×

     -- Antisymmetry.
     (∀ x y → x ≤ y → y ≤ x → x ≡ y)) ,

    λ ass → let open Assumptions ass in
      [inhabited⇒+]⇒+ 0 λ { (P-set , ≤-prop , _) →
        ×-closure 1  (H-level-propositional ext 2)
        (×-closure 1 (Π-closure ext                     1 λ _ →
                      Π-closure (lower-ext (# 0) _ ext) 1 λ _ →
                      H-level-propositional (lower-ext _ _ ext) 1)
        (×-closure 1 (Π-closure (lower-ext (# 0) _ ext) 1 λ _ →
                      ≤-prop _ _)
        (×-closure 1 (Π-closure ext                     1 λ _ →
                      Π-closure ext                     1 λ _ →
                      Π-closure (lower-ext (# 0) _ ext) 1 λ _ →
                      Π-closure (lower-ext _ _ ext)     1 λ _ →
                      Π-closure (lower-ext _ _ ext)     1 λ _ →
                      ≤-prop _ _)
                     (Π-closure ext                     1 λ _ →
                      Π-closure ext                     1 λ _ →
                      Π-closure (lower-ext _ (# 0) ext) 1 λ _ →
                      Π-closure (lower-ext _ (# 0) ext) 1 λ _ →
                      P-set _ _)))) }

-- The interpretation of the code is reasonable. (Except, perhaps,
-- that the carrier type lives in Set₁ but the codomain of the
-- ordering relation is Set. In the corresponding example in
-- Univalence-axiom.Isomorphism-implies-equality.Simple.Variant the
-- carrier type lives in Set.)

Instance-poset :

  Instance poset
    ≡
  Σ Set₁ λ P →
  Σ (P → P → Set) λ _≤_ →
  Is-set P ×
  (∀ x y → Propositional (x ≤ y)) ×
  (∀ x → x ≤ x) ×
  (∀ x y z → x ≤ y → y ≤ z → x ≤ z) ×
  (∀ x y → x ≤ y → y ≤ x → x ≡ y)

Instance-poset = refl _

-- The notion of isomorphism that we get is also reasonable. It is the
-- usual notion of "order isomorphism", with two (main) differences:
--
-- * Weak equivalences are used instead of bijections. However, weak
--   equivalences and bijections coincide for sets (assuming
--   extensionality).
--
-- * We use weak equivalence, (a ≤₁ c) ≈ (b ≤₂ d), instead of "iff",
--   (a ≤₁ c) ⇔ (b ≤₂ d). However, the ordering relation is pointwise
--   propositional, so these two expressions are equal (assuming
--   extensionality).

Isomorphic-poset :
  ∀ {P₁ _≤₁_ laws₁ P₂ _≤₂_ laws₂} →

  Isomorphic poset (P₁ , _≤₁_ , laws₁) (P₂ , _≤₂_ , laws₂)
    ≡
  Σ (P₁ ≈ P₂) λ P₁≈P₂ → let open _≈_ P₁≈P₂ in
  ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≈ (b ≤₂ d))

Isomorphic-poset = refl _

-- We can prove that the notion of isomorphism is isomorphic to the
-- usual notion of order isomorphism (assuming extensionality).

Isomorphism-poset-isomorphic-to-order-isomorphism :
  Extensionality (# 1) (# 1) →
  ∀ {P₁ _≤₁_ laws₁ P₂ _≤₂_ laws₂} →

  Isomorphic poset (P₁ , _≤₁_ , laws₁) (P₂ , _≤₂_ , laws₂)
    ↔
  Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
  ∀ x y → (x ≤₁ y) ⇔ (to x ≤₂ to y)

Isomorphism-poset-isomorphic-to-order-isomorphism ext
  {P₁} {_≤₁_} {laws₁} {P₂} {_≤₂_} {laws₂} =

  (Σ (P₁ ≈ P₂) λ P₁≈P₂ → let open _≈_ P₁≈P₂ in
   ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≈ (b ≤₂ d)))  ↝⟨ inverse $ Σ-cong (↔↔≈ ext (proj₁ laws₁)) (λ _ → _ □) ⟩

  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≈ (b ≤₂ d)))  ↔⟨ inverse $ ∃-cong (λ _ → ∀-preserves ext λ _ → ↔⇒≈ $
                                                                          ∀-intro ext λ _ _ → _) ⟩
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≈ (to a ≤₂ d)))                ↔⟨ inverse $ ∃-cong (λ _ → ∀-preserves ext λ _ → ∀-preserves ext λ _ → ↔⇒≈ $
                                                                          ∀-intro ext λ _ _ → _) ⟩
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a c → ↑ _ ((a ≤₁ c) ≈ (to a ≤₂ to c)))                          ↔⟨ ∃-cong (λ _ → ∀-preserves ext λ _ → ∀-preserves ext λ _ → ↔⇒≈
                                                                          ↑↔) ⟩
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a c → (a ≤₁ c) ≈ (to a ≤₂ to c))                                ↔⟨ inverse $ ∃-cong (λ _ →
                                                                          ∀-preserves ext λ _ → ∀-preserves (lower-ext (# 0) _ ext) λ _ → ↔⇒≈ $
                                                                            ⇔↔≈ (lower-ext _ _ ext) (proj₁ (proj₂ laws₁) _ _)
                                                                                                    (proj₁ (proj₂ laws₂) _ _)) ⟩□
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a c → (a ≤₁ c) ⇔ (to a ≤₂ to c))                                □

------------------------------------------------------------------------
-- An example: sets equipped with fixpoint operators

set-with-fixpoint-operator : Code
set-with-fixpoint-operator =
  (id ⇾ id) ⇾ id ,

  λ F fix →

     -- The carrier type is a set.
    (Is-set F ×

     -- The fixpoint operator property.
     (∀ f → f (fix f) ≡ fix f)) ,

    λ ass → let open Assumptions ass in
      [inhabited⇒+]⇒+ 0 λ { (F-set , _) →
        ×-closure 1 (H-level-propositional ext 2)
                    (Π-closure ext 1 λ _ →
                     F-set _ _) }

-- The usual unfolding lemmas.

Instance-set-with-fixpoint-operator :

  Instance set-with-fixpoint-operator
    ≡
  Σ Set₁ λ F →
  Σ ((F → F) → F) λ fix →
  Is-set F ×
  (∀ f → f (fix f) ≡ fix f)

Instance-set-with-fixpoint-operator = refl _

Isomorphic-set-with-fixpoint-operator :
  ∀ {F₁ fix₁ laws₁ F₂ fix₂ laws₂} →

  Isomorphic set-with-fixpoint-operator
             (F₁ , fix₁ , laws₁) (F₂ , fix₂ , laws₂)
    ≡
  Σ (F₁ ≈ F₂) λ F₁≈F₂ → let open _≈_ F₁≈F₂ in
  ∀ f g → (∀ x y → to x ≡ y → to (f x) ≡ g y) → to (fix₁ f) ≡ fix₂ g

Isomorphic-set-with-fixpoint-operator = refl _
