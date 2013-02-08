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
  hiding (id; _∘_; inverse; _↔⟨_⟩_; finally-↔)
open import Category eq
open Derived-definitions-and-properties eq
  renaming (lower-extensionality to lower-ext)
open import Equality.Decision-procedures eq
open import Equivalence using (_⇔_; module _⇔_)
open import Function-universe eq hiding (id) renaming (_∘_ to _⊚_)
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

  -- Parameters.

  field

    -- Codes for something.

    U : Set₂

    -- Interpretation of codes.

    El : U → Set₁ → Set₁

    -- El a, seen as a predicate, respects weak equivalences.

    resp : ∀ a {B C} → B ≃ C → El a B → El a C

    -- The resp function respects identities (assuming univalence).

    resp-id : Assumptions → ∀ a {B} (x : El a B) → resp a Weak.id x ≡ x

  -- Derived definitions.

  -- A predicate that specifies what it means for a weak equivalence
  -- to be an isomorphism between two elements.

  Is-isomorphism : ∀ a {B C} → B ≃ C → El a B → El a C → Set₁
  Is-isomorphism a B≃C x y = resp a B≃C x ≡ y

  -- An alternative definition of Is-isomorphism, defined using
  -- univalence.

  Is-isomorphism′ : Assumptions →
                    ∀ a {B C} → B ≃ C → El a B → El a C → Set₁
  Is-isomorphism′ ass a B≃C x y = subst (El a) (≃⇒≡ univ₁ B≃C) x ≡ y
    where open Assumptions ass

  abstract

    -- Every element is isomorphic to itself, transported along the
    -- isomorphism.

    isomorphic-to-itself :
      (ass : Assumptions) → let open Assumptions ass in
      ∀ a {B C} (B≃C : B ≃ C) x →
      Is-isomorphism a B≃C x (subst (El a) (≃⇒≡ univ₁ B≃C) x)
    isomorphic-to-itself ass a B≃C x =
      subst-unique (El a) (resp a) (resp-id ass a) univ₁ B≃C x
      where open Assumptions ass

    -- Is-isomorphism and Is-isomorphism′ are isomorphic (assuming
    -- univalence).

    isomorphism-definitions-isomorphic :
      (ass : Assumptions) →
      ∀ a {B C} (B≃C : B ≃ C) {x y} →
      Is-isomorphism a B≃C x y ↔ Is-isomorphism′ ass a B≃C x y
    isomorphism-definitions-isomorphic ass a B≃C {x} {y} =
      Is-isomorphism      a B≃C x y  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ y) $ isomorphic-to-itself ass a B≃C x ⟩□
      Is-isomorphism′ ass a B≃C x y  □

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
      Assumptions → Is-proposition P

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
      ∀ c {I J} →
      (I ≡ J) ↔
      ∃ λ (C-eq : Carrier c I ≡ Carrier c J) →
        subst (El (proj₁ c)) C-eq (element c I) ≡ element c J
    instances-equal↔ ass (a , P) {C , x , p} {D , y , q} =

      ((C , x , p) ≡ (D , y , q))                     ↔⟨ inverse $ ≃-≡ $ ↔⇒≃ Σ-assoc ⟩

      (((C , x) , p) ≡ ((D , y) , q))                 ↝⟨ inverse $ ignore-propositional-component (proj₂ (P D y) ass) ⟩

      ((C , x) ≡ (D , y))                             ↝⟨ inverse Σ-≡,≡↔≡ ⟩□

      (∃ λ (C-eq : C ≡ D) → subst (El a) C-eq x ≡ y)  □

  -- Structure isomorphisms.

  Isomorphic : ∀ c → Instance c → Instance c → Set₁
  Isomorphic (a , _) (C₁ , x₁ , _) (C₂ , x₂ , _) =
    Σ (C₁ ≃ C₂) λ C₁≃C₂ → Is-isomorphism a C₁≃C₂ x₁ x₂

  abstract

    -- The type of isomorphisms between two instances of a structure
    -- is isomorphic to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is isomorphic to equality.

    isomorphic↔equal :
      Assumptions →
      ∀ c {I J} → Isomorphic c I J ↔ (I ≡ J)
    isomorphic↔equal ass (a , P) {C , x , p} {D , y , q} =

      (∃ λ (C-eq : C ≃ D) → Is-isomorphism a C-eq x y)            ↝⟨ ∃-cong (λ C-eq → isomorphism-definitions-isomorphic ass a C-eq) ⟩

      (∃ λ (C-eq : C ≃ D) → subst (El a) (≃⇒≡ univ₁ C-eq) x ≡ y)  ↝⟨ inverse $
                                                                       Σ-cong (≡≃≃ univ₁) (λ C-eq → ≡⇒↝ _ $ sym $
                                                                         cong (λ eq → subst (El a) eq x ≡ y)
                                                                              (_≃_.left-inverse-of (≡≃≃ univ₁) C-eq)) ⟩
      (∃ λ (C-eq : C ≡ D) → subst (El a) C-eq x ≡ y)              ↝⟨ inverse $ instances-equal↔ ass c ⟩□

      (I ≡ J)                                                     □

      where
      open Assumptions ass

      c : Code
      c = a , P

      I : Instance c
      I = C , x , p

      J : Instance c
      J = D , y , q

    -- The type of (lifted) isomorphisms between two instances of a
    -- structure is equal to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is equal to equality.

    isomorphic≡equal :
      Assumptions →
      ∀ c {I J} → ↑ (# 2) (Isomorphic c I J) ≡ (I ≡ J)
    isomorphic≡equal ass c {I} {J} =
      ≃⇒≡ univ₂ $ ↔⇒≃ (
        ↑ _ (Isomorphic c I J)  ↝⟨ ↑↔ ⟩
        Isomorphic c I J        ↝⟨ isomorphic↔equal ass c ⟩□
        (I ≡ J)                 □)
      where open Assumptions ass

------------------------------------------------------------------------
-- An aside: A limited variant of Class.isomorphic↔equal can be proved
-- by using the "Abstract SIP Theorem" (see the HoTT Book)

-- "Standard notions of structure".

record Standard-notion-of-structure
         {x₁ x₂} ℓ₁ ℓ₂ (X : Precategory x₁ x₂) :
         Set (x₁ ⊔ x₂ ⊔ lsuc (ℓ₁ ⊔ ℓ₂)) where
  open Precategory X renaming (id to ⟨id⟩)

  field
    P               : Obj → Set ℓ₁
    P-set           : ∀ A → Is-set (P A)
    H               : ∀ {X Y} (p : P X) (q : P Y) → Hom X Y → Set ℓ₂
    H-prop          : ∀ {X Y} {p : P X} {q : P Y}
                      (f : Hom X Y) → Is-proposition (H p q f)
    H-id            : ∀ {X} {p : P X} → H p p ⟨id⟩
    H-∘             : ∀ {X Y Z} {p : P X} {q : P Y} {r : P Z} {f g} →
                      H p q f → H q r g → H p r (f ∙ g)
    H-antisymmetric : ∀ {X} (p q : P X) →
                      H p q ⟨id⟩ → H q p ⟨id⟩ → p ≡ q

  abstract

    -- Two Str morphisms (see below) of equal type are equal if their
    -- first components are equal.

    lift-equality-Str : {X Y : ∃ P} {f g : ∃ (H (proj₂ X) (proj₂ Y))} →
                        proj₁ f ≡ proj₁ g → f ≡ g
    lift-equality-Str eq =
      Σ-≡,≡→≡ eq (_⇔_.to propositional⇔irrelevant (H-prop _) _ _)

  -- A derived precategory.

  Str : Precategory (x₁ ⊔ ℓ₁) (x₂ ⊔ ℓ₂)
  Str = record { precategory =
    ∃ P ,
    (λ { (X , p) (Y , q) →
         ∃ (H p q) ,
         Σ-closure 2 Hom-is-set (λ f → mono₁ 1 (H-prop f)) }) ,
    (⟨id⟩ , H-id) ,
    (λ { (f , hf) (g , hg) → f ∙ g , H-∘ hf hg }) ,
    lift-equality-Str left-identity ,
    lift-equality-Str right-identity ,
    lift-equality-Str assoc }

-- The statement of the Abstract SIP Theorem.
--
-- I (NAD) have not seen a formalisation of the theorem, and I am not
-- 100% certain that the statement below is correct. For instance, I
-- have made the theorem universe-polymorphic, but I am not sure if
-- the statement of the theorem (in the draft of the HoTT Book that I
-- looked at) is supposed to be read universe-polymorphically.

Abstract-SIP-Theorem :
  (x₁ x₂ ℓ₁ ℓ₂ : Level) → Set (lsuc (x₁ ⊔ x₂ ⊔ ℓ₁ ⊔ ℓ₂))
Abstract-SIP-Theorem x₁ x₂ ℓ₁ ℓ₂ =
  (X : Category x₁ x₂) →
  (S : Standard-notion-of-structure ℓ₁ ℓ₂ (Category.precategory X)) →
  ∀ {X Y} → Is-weak-equivalence
              (Precategory.≡→≅ (Standard-notion-of-structure.Str S)
                               {X} {Y})

-- The "Abstract SIP Theorem", as stated above, can be used to prove a
-- limited variant of Class.isomorphic↔equal.

isomorphic↔equal-is-corollary :
  Abstract-SIP-Theorem (# 2) (# 1) (# 1) (# 1) →
  (Univ : Universe) → let open Universe Univ in
  (∀ a {B C D} (f : C ≃ D) (g : B ≃ C) →
     resp a (f ⊚ g) ≡ resp a f ∘ resp a g) →
  (∀ a {B C x y} (f : B ≃ C) →
     resp a f x ≡ y → resp a (inverse f) y ≡ x) →
  (∀ a {B} → Is-set B → Is-set (El a B)) →
  Assumptions →
  ∀ c {I J} →
  Is-set (proj₁ I) → Is-set (proj₁ J) →
  Class.Isomorphic Univ c I J ↔ (I ≡ J)
isomorphic↔equal-is-corollary
  sip Univ resp-∘ resp-⁻¹ El-set ass
  (a , P) {C , x , p} {D , y , q} C-set D-set =

  Isomorphic (a , P) (C , x , p) (D , y , q)  ↝⟨ (let ≃≃≅ = ≃≃≅-Set (# 1) ext Cs Ds in
                                                  Σ-cong ≃≃≅ (λ C≃D →
                                                    let C≃D′ = _≃_.from ≃≃≅ (_≃_.to ≃≃≅ C≃D) in
                                                    Is-isomorphism a C≃D  x y  ↝⟨ ≡⇒↝ _ $ cong (λ eq → Is-isomorphism a eq x y) $ sym $
                                                                                    _≃_.left-inverse-of ≃≃≅ C≃D ⟩
                                                    Is-isomorphism a C≃D′ x y  □)) ⟩
  ∃ (H {X = Cs} {Y = Ds} x y)                 ↝⟨ inverse ×-right-identity ⟩
  ∃ (H {X = Cs} {Y = Ds} x y) × ⊤             ↝⟨ ∃-cong (λ I≅J → inverse $ contractible↔⊤ $ propositional⇒inhabited⇒contractible
                                                                   (Precategory.Is-isomorphism-propositional Str I≅J)
                                                                   (Str-homs-are-isos I≅J)) ⟩
  ((Cs , x) ≅-Str (Ds , y))                   ↔⟨ inverse $ weq _ (sip X≅ S {X = Cs , x} {Y = Ds , y}) ⟩
  ((Cs , x) ≡ (Ds , y))                       ↔⟨ ≃-≡ $ ↔⇒≃ (Σ-assoc ⊚ ∃-cong (λ _ → ×-comm) ⊚ inverse Σ-assoc) ⟩
  (((C , x) , C-set) ≡ ((D , y) , D-set))     ↝⟨ inverse $ ignore-propositional-component (H-level-propositional ext 2) ⟩
  ((C , x) ≡ (D , y))                         ↝⟨ ignore-propositional-component (proj₂ (P D y) ass) ⟩
  (((C , x) , p) ≡ ((D , y) , q))             ↔⟨ ≃-≡ $ ↔⇒≃ Σ-assoc ⟩□
  ((C , x , p) ≡ (D , y , q))                 □

  where
  open Assumptions ass
  open Universe Univ
  open Class Univ using (Isomorphic)

  -- Some abbreviations.

  X : Category (# 2) (# 1)
  X = category-Set (# 1) ext univ₁

  open Category X using (_≅_)

  Cs : Category.Obj X
  Cs = C , C-set

  Ds : Category.Obj X
  Ds = D , D-set

  ≅⇒≃ : (C D : Category.Obj X) → C ≅ D → Type C ≃ Type D
  ≅⇒≃ C D = _≃_.from (≃≃≅-Set (# 1) ext C D)

  -- The underlying category.

  X≅ : Category (# 2) (# 1)
  X≅ = category-Set-≅ (# 1) ext univ₁

  -- The "standard notion of structure" that the theorem is
  -- instantiated with.

  S : Standard-notion-of-structure (# 1) (# 1) (Category.precategory X≅)
  S = record
    { P               = El a ∘ Type
    ; P-set           = El-set a ∘ proj₂
    ; H               = λ {C D} x y C≅D →
                          Is-isomorphism a (≅⇒≃ C D C≅D) x y
    ; H-prop          = λ {_ C} _ → El-set a (proj₂ C) _ _
    ; H-id            = λ {C x} →
                          resp a (≅⇒≃ C C (Category.id X≅ {X = C})) x  ≡⟨ cong (λ eq → resp a eq x) $ Weak.lift-equality ext (refl _) ⟩
                          resp a Weak.id x                             ≡⟨ resp-id ass a x ⟩∎
                          x                                            ∎
    ; H-∘             = λ {B C D x y z B≅C C≅D} x≅y y≅z →
                          resp a (≅⇒≃ B D (Category._∙_ X≅ B≅C C≅D)) x   ≡⟨ cong (λ eq → resp a eq x) $ Weak.lift-equality ext (refl _) ⟩
                          resp a (≅⇒≃ C D C≅D ⊚ ≅⇒≃ B C B≅C) x           ≡⟨ cong (λ h → h x) $ resp-∘ a (≅⇒≃ C D C≅D) (≅⇒≃ B C B≅C) ⟩
                          resp a (≅⇒≃ C D C≅D) (resp a (≅⇒≃ B C B≅C) x)  ≡⟨ cong (resp a (≅⇒≃ C D C≅D)) x≅y ⟩
                          resp a (≅⇒≃ C D C≅D) y                         ≡⟨ y≅z ⟩∎
                          z                                              ∎
    ; H-antisymmetric = λ {C} x y x≡y _ →
                          x                                            ≡⟨ sym $ resp-id ass a x ⟩
                          resp a Weak.id x                             ≡⟨ cong (λ eq → resp a eq x) $ Weak.lift-equality ext (refl _) ⟩
                          resp a (≅⇒≃ C C (Category.id X≅ {X = C})) x  ≡⟨ x≡y ⟩∎
                          y                                            ∎
    }

  open Standard-notion-of-structure S using (H; Str; lift-equality-Str)
  open Precategory Str using () renaming (_≅_ to _≅-Str_)

  abstract

    -- Every Str morphism is an isomorphism.

    Str-homs-are-isos :
      ∀ {C D x y} (f : ∃ (H {X = C} {Y = D} x y)) →
      Precategory.Is-isomorphism Str {X = C , x} {Y = D , y} f
    Str-homs-are-isos {C} {D} {x} {y} (C≅D , x≅y) =

      (D≅C ,
       (resp a (≅⇒≃ D C D≅C) y            ≡⟨ cong (λ eq → resp a eq y) $ Weak.lift-equality ext (refl _) ⟩
        resp a (inverse $ ≅⇒≃ C D C≅D) y  ≡⟨ resp-⁻¹ a (≅⇒≃ C D C≅D) x≅y ⟩∎
        x                                 ∎)) ,

      lift-equality-Str {X = C , x} {Y = C , x} (
        C≅D ∙≅ D≅C   ≡⟨ _≃_.from (≡≃≡¹ {X = C} {Y = C}) (_¹⁻¹ {X = C} {Y = D} C≅D) ⟩∎
        id≅ {X = C}  ∎) ,

      lift-equality-Str {X = D , y} {Y = D , y} (
        D≅C ∙≅ C≅D   ≡⟨ _≃_.from (≡≃≡¹ {X = D} {Y = D}) (_⁻¹¹ {X = C} {Y = D} C≅D) ⟩∎
        id≅ {X = D}  ∎)

      where
      open Category X using (_⁻¹≅; _∙≅_; id≅; _¹⁻¹; _⁻¹¹; ≡≃≡¹)

      D≅C : D ≅ C
      D≅C = _⁻¹≅ {X = C} {Y = D} C≅D

------------------------------------------------------------------------
-- A universe of non-recursive, simple types

-- Codes for types.

infixr 20 _⊗_
infixr 15 _⊕_
infixr 10 _⇾_

data U : Set₂ where
  id set      : U
  k           : Set₁ → U
  _⇾_ _⊗_ _⊕_ : U → U → U

-- Interpretation of types.

El : U → Set₁ → Set₁
El id      B = B
El set     B = Set
El (k A)   B = A
El (a ⇾ b) B = El a B → El b B
El (a ⊗ b) B = El a B × El b B
El (a ⊕ b) B = El a B ⊎ El b B

-- El a preserves equivalences.

cast : ∀ a {B C} → B ⇔ C → El a B ⇔ El a C
cast id      B≃C = B≃C
cast set     B≃C = Equivalence.id
cast (k A)   B≃C = Equivalence.id
cast (a ⇾ b) B≃C = →-cong-⇔ (cast a B≃C) (cast b B≃C)
cast (a ⊗ b) B≃C = cast a B≃C ×-cong cast b B≃C
cast (a ⊕ b) B≃C = cast a B≃C ⊎-cong cast b B≃C

-- El a respects weak equivalences.

resp : ∀ a {B C} → B ≃ C → El a B → El a C
resp a B≃C = _⇔_.to (cast a (_≃_.equivalence B≃C))

resp⁻¹ : ∀ a {B C} → B ≃ C → El a C → El a B
resp⁻¹ a B≃C = _⇔_.from (cast a (_≃_.equivalence B≃C))

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
    cast a Equivalence.id ⊎-cong cast b Equivalence.id  ≡⟨ cong₂ _⊎-cong_ (cast-id ext a) (cast-id ext b) ⟩
    Equivalence.id ⊎-cong Equivalence.id                ≡⟨ cong₂ (λ f g → record { to = f; from = g })
                                                                 (ext [ refl ∘ inj₁ , refl ∘ inj₂ ])
                                                                 (ext [ refl ∘ inj₁ , refl ∘ inj₂ ]) ⟩∎
    Equivalence.id                                      ∎

  -- The following two properties are not used below.

  -- The cast function respects composition (assuming extensionality).

  cast-∘ : Extensionality (# 1) (# 1) →
           ∀ a {B C D} (f : C ⇔ D) (g : B ⇔ C) →
           cast a (f ⊚ g) ≡ cast a f ⊚ cast a g
  cast-∘ ext id      f g = refl _
  cast-∘ ext set     f g = refl _
  cast-∘ ext (k A)   f g = refl _
  cast-∘ ext (a ⇾ b) f g = cong₂ →-cong-⇔ (cast-∘ ext a f g) (cast-∘ ext b f g)
  cast-∘ ext (a ⊗ b) f g = cong₂ _×-cong_ (cast-∘ ext a f g) (cast-∘ ext b f g)
  cast-∘ ext (a ⊕ b) f g =
    cast a (f ⊚ g) ⊎-cong cast b (f ⊚ g)                     ≡⟨ cong₂ _⊎-cong_ (cast-∘ ext a f g) (cast-∘ ext b f g) ⟩
    cast a f ⊚ cast a g ⊎-cong cast b f ⊚ cast b g           ≡⟨ cong₂ (λ f g → record { to = f; from = g })
                                                                      (ext [ (λ _ → refl _) , (λ _ → refl _) ])
                                                                      (ext [ (λ _ → refl _) , (λ _ → refl _) ]) ⟩∎
    (cast a f ⊎-cong cast b f) ⊚ (cast a g ⊎-cong cast b g)  ∎

  -- The cast function respects inverses.

  cast-⁻¹ : ∀ a {B C} (f : B ⇔ C) →
            cast a (inverse f) ≡ inverse (cast a f)
  cast-⁻¹ id      f = refl _
  cast-⁻¹ set     f = refl _
  cast-⁻¹ (k A)   f = refl _
  cast-⁻¹ (a ⇾ b) f = cong₂ →-cong-⇔ (cast-⁻¹ a f) (cast-⁻¹ b f)
  cast-⁻¹ (a ⊗ b) f = cong₂ _×-cong_ (cast-⁻¹ a f) (cast-⁻¹ b f)
  cast-⁻¹ (a ⊕ b) f = cong₂ _⊎-cong_ (cast-⁻¹ a f) (cast-⁻¹ b f)

-- The universe above is a "universe with some extra stuff".

simple : Universe
simple = record
  { U       = U
  ; El      = El
  ; resp    = resp
  ; resp-id = λ ass a x → cong (λ eq → _⇔_.to eq x) $
                            cast-id (Assumptions.ext ass) a
  }

-- Let us use this universe below.

open Universe simple using (Is-isomorphism)
open Class simple

-- An alternative definition of "being an isomorphism".
--
-- This definition is in bijective correspondence with Is-isomorphism
-- (see below).

Is-isomorphism′ : ∀ a {B C} → B ≃ C → El a B → El a C → Set₁
Is-isomorphism′ id      B≃C = λ x y → _≃_.to B≃C x ≡ y
Is-isomorphism′ set     B≃C = λ X Y → ↑ _ (X ≃ Y)
Is-isomorphism′ (k A)   B≃C = λ x y → x ≡ y
Is-isomorphism′ (a ⇾ b) B≃C = Is-isomorphism′ a B≃C →-rel
                              Is-isomorphism′ b B≃C
Is-isomorphism′ (a ⊗ b) B≃C = Is-isomorphism′ a B≃C ×-rel
                              Is-isomorphism′ b B≃C
Is-isomorphism′ (a ⊕ b) B≃C = Is-isomorphism′ a B≃C ⊎-rel
                              Is-isomorphism′ b B≃C

-- An alternative definition of Isomorphic, using Is-isomorphism′
-- instead of Is-isomorphism.

Isomorphic′ : ∀ c → Instance c → Instance c → Set₁
Isomorphic′ (a , _) (C₁ , x₁ , _) (C₂ , x₂ , _) =
  Σ (C₁ ≃ C₂) λ C₁≃C₂ → Is-isomorphism′ a C₁≃C₂ x₁ x₂

-- El a preserves weak equivalences (assuming extensionality).
--
-- Note that _≃_.equivalence (cast≃ ext a B≃C) is (definitionally)
-- equal to cast a (_≃_.equivalence B≃C); this property is used below.

cast≃ : Extensionality (# 1) (# 1) →
        ∀ a {B C} → B ≃ C → El a B ≃ El a C
cast≃ ext a {B} {C} B≃C = ↔⇒≃ record
  { surjection = record
    { equivalence      = cast a B⇔C
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  B⇔C = _≃_.equivalence B≃C

  cst : ∀ a → El a B ≃ El a C
  cst id      = B≃C
  cst set     = Weak.id
  cst (k A)   = Weak.id
  cst (a ⇾ b) = →-cong ext (cst a) (cst b)
  cst (a ⊗ b) = cst a ×-cong cst b
  cst (a ⊕ b) = cst a ⊎-cong cst b

  abstract

    -- The projection _≃_.equivalence is homomorphic with respect to
    -- cast a/cst a.

    casts-related :
      ∀ a → cast a (_≃_.equivalence B≃C) ≡ _≃_.equivalence (cst a)
    casts-related id      = refl _
    casts-related set     = refl _
    casts-related (k A)   = refl _
    casts-related (a ⇾ b) = cong₂ →-cong-⇔ (casts-related a)
                                           (casts-related b)
    casts-related (a ⊗ b) = cong₂ _×-cong_ (casts-related a)
                                           (casts-related b)
    casts-related (a ⊕ b) = cong₂ _⊎-cong_ (casts-related a)
                                           (casts-related b)

    to∘from : ∀ x → _⇔_.to (cast a B⇔C) (_⇔_.from (cast a B⇔C) x) ≡ x
    to∘from x =
      _⇔_.to (cast a B⇔C) (_⇔_.from (cast a B⇔C) x)  ≡⟨ cong₂ (λ f g → f (g x)) (cong _⇔_.to $ casts-related a)
                                                                                (cong _⇔_.from $ casts-related a) ⟩
      _≃_.to (cst a) (_≃_.from (cst a) x)            ≡⟨ _≃_.right-inverse-of (cst a) x ⟩∎
      x                                              ∎

    from∘to : ∀ x → _⇔_.from (cast a B⇔C) (_⇔_.to (cast a B⇔C) x) ≡ x
    from∘to x =
      _⇔_.from (cast a B⇔C) (_⇔_.to (cast a B⇔C) x)  ≡⟨ cong₂ (λ f g → f (g x)) (cong _⇔_.from $ casts-related a)
                                                                                (cong _⇔_.to $ casts-related a) ⟩
      _≃_.from (cst a) (_≃_.to (cst a) x)            ≡⟨ _≃_.left-inverse-of (cst a) x ⟩∎
      x                                              ∎

abstract

  -- The two definitions of "being an isomorphism" are "isomorphic"
  -- (in bijective correspondence), assuming univalence.

  isomorphism-definitions-isomorphic :
    Assumptions →
    ∀ a {B C} (B≃C : B ≃ C) {x y} →
    Is-isomorphism a B≃C x y ↔ Is-isomorphism′ a B≃C x y

  isomorphism-definitions-isomorphic ass id B≃C {x} {y} =

    (_≃_.to B≃C x ≡ y)  □

  isomorphism-definitions-isomorphic ass set B≃C {X} {Y} =

    (X ≡ Y)      ↔⟨ ≡≃≃ univ ⟩

    (X ≃ Y)      ↝⟨ inverse ↑↔ ⟩□

    ↑ _ (X ≃ Y)  □

    where open Assumptions ass

  isomorphism-definitions-isomorphic ass (k A) B≃C {x} {y} =

    (x ≡ y) □

  isomorphism-definitions-isomorphic ass (a ⇾ b) B≃C {f} {g} =

    (resp b B≃C ∘ f ∘ resp⁻¹ a B≃C ≡ g)                  ↝⟨ ∘from≡↔≡∘to ext (cast≃ ext a B≃C) ⟩

    (resp b B≃C ∘ f ≡ g ∘ resp a B≃C)                    ↔⟨ inverse $ extensionality-isomorphism ext ⟩

    (∀ x → resp b B≃C (f x) ≡ g (resp a B≃C x))          ↔⟨ ∀-preserves ext (λ x → ↔⇒≃ $
                                                              ∀-intro ext (λ y _ → resp b B≃C (f x) ≡ g y)) ⟩
    (∀ x y → resp a B≃C x ≡ y → resp b B≃C (f x) ≡ g y)  ↔⟨ ∀-preserves ext (λ _ → ∀-preserves ext λ _ → ↔⇒≃ $
                                                              →-cong ext (isomorphism-definitions-isomorphic ass a B≃C)
                                                                         (isomorphism-definitions-isomorphic ass b B≃C)) ⟩□
    (∀ x y → Is-isomorphism′ a B≃C x y →
             Is-isomorphism′ b B≃C (f x) (g y))          □

    where open Assumptions ass

  isomorphism-definitions-isomorphic ass (a ⊗ b) B≃C {x , u} {y , v} =

    ((resp a B≃C x , resp b B≃C u) ≡ (y , v))              ↝⟨ inverse ≡×≡↔≡ ⟩

    (resp a B≃C x ≡ y × resp b B≃C u ≡ v)                  ↝⟨ isomorphism-definitions-isomorphic ass a B≃C ×-cong
                                                              isomorphism-definitions-isomorphic ass b B≃C ⟩□
    Is-isomorphism′ a B≃C x y × Is-isomorphism′ b B≃C u v  □

    where open Assumptions ass

  isomorphism-definitions-isomorphic ass (a ⊕ b) B≃C {inj₁ x} {inj₁ y} =

    (inj₁ (resp a B≃C x) ≡ inj₁ y)  ↝⟨ inverse ≡↔inj₁≡inj₁ ⟩

    (resp a B≃C x ≡ y)              ↝⟨ isomorphism-definitions-isomorphic ass a B≃C ⟩□

    Is-isomorphism′ a B≃C x y       □

    where open Assumptions ass

  isomorphism-definitions-isomorphic ass (a ⊕ b) B≃C {inj₂ x} {inj₂ y} =

    (inj₂ (resp b B≃C x) ≡ inj₂ y)  ↝⟨ inverse ≡↔inj₂≡inj₂ ⟩

    (resp b B≃C x ≡ y)              ↝⟨ isomorphism-definitions-isomorphic ass b B≃C ⟩□

    Is-isomorphism′ b B≃C x y       □

    where open Assumptions ass

  isomorphism-definitions-isomorphic ass (a ⊕ b) B≃C {inj₁ x} {inj₂ y} =

    (inj₁ _ ≡ inj₂ _)  ↝⟨ inverse $ ⊥↔uninhabited ⊎.inj₁≢inj₂ ⟩□

    ⊥                  □

  isomorphism-definitions-isomorphic ass (a ⊕ b) B≃C {inj₂ x} {inj₁ y} =

    (inj₂ _ ≡ inj₁ _)  ↝⟨ inverse $ ⊥↔uninhabited (⊎.inj₁≢inj₂ ∘ sym) ⟩□

    ⊥                  □

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
  Σ (M₁ ≃ M₂) λ M₁≃M₂ → let open _≃_ M₁≃M₂ in
  ((λ x y → to (from x ∙₁ from y)) , to e₁) ≡ (_∙₂_ , e₂)

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

  (Σ (M₁ ≃ M₂) λ M₁≃M₂ → let open _≃_ M₁≃M₂ in
   ((λ x y → to (from x ∙₁ from y)) , to e₁) ≡ (_∙₂_ , e₂))  ↝⟨ inverse $ Σ-cong (↔↔≃ ext (proj₁ laws₁)) (λ _ → _ □) ⟩

  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
   ((λ x y → to (from x ∙₁ from y)) , to e₁) ≡ (_∙₂_ , e₂))  ↝⟨ inverse $ ∃-cong (λ _ → ≡×≡↔≡) ⟩

  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
   (λ x y → to (from x ∙₁ from y)) ≡ _∙₂_ ×
   to e₁ ≡ e₂)                                               ↔⟨ inverse $ ∃-cong (λ _ → extensionality-isomorphism ext ×-cong (_ □)) ⟩

  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
   (∀ x → (λ y → to (from x ∙₁ from y)) ≡ _∙₂_ x) ×
   to e₁ ≡ e₂)                                               ↔⟨ inverse $ ∃-cong (λ _ →
                                                                  ∀-preserves ext (λ _ → extensionality-isomorphism ext)
                                                                    ×-cong
                                                                  (_ □)) ⟩
  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
   (∀ x y → to (from x ∙₁ from y) ≡ x ∙₂ y) ×
   to e₁ ≡ e₂)                                               ↔⟨ inverse $ ∃-cong (λ M₁↔M₂ →
                                                                  Π-preserves ext (↔⇒≃ M₁↔M₂) (λ x → Π-preserves ext (↔⇒≃ M₁↔M₂) (λ y →
                                                                      ≡⇒≃ $ sym $ cong₂ (λ u v → _↔_.to M₁↔M₂ (u ∙₁ v) ≡
                                                                                                 _↔_.to M₁↔M₂ x ∙₂ _↔_.to M₁↔M₂ y)
                                                                                        (_↔_.left-inverse-of M₁↔M₂ x)
                                                                                        (_↔_.left-inverse-of M₁↔M₂ y)))
                                                                    ×-cong
                                                                  (_ □)) ⟩□
  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ M₁↔M₂ in
   (∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y) ×
   to e₁ ≡ e₂)                                               □

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
         (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#)) })                   ↝⟨ ∃-cong (λ _ → inverse $ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚
                                                                                                   ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚
                                                                                                   ×-assoc ⊚ ×-assoc) ⟩□
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
    (A × B × C × D × E × F)          ↝⟨ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⟩
    (((((A × B) × C) × D) × E) × F)  ↝⟨ inverse (×-assoc ⊚ ×-assoc ⊚ ×-assoc) ×-cong (_ □) ⟩□
    ((A × B × C × D × E) × F)        □

  lemma₂ : (A B C D E F G H I J K : Set₁) →
           (A × B × C × D × E × F × G × H × I × J × K) ↔
           (((((((((A × B) × C) × D) × E) × F) × G) × H) × J) × I × K)
  lemma₂ A B C D E F G H I J K =
    (A × B × C × D × E × F × G × H × I × J × K)                  ↝⟨ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⟩
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
  Σ (F₁ ≃ F₂) λ F₁≃F₂ → let open _≃_ F₁≃F₂ in
  ((λ x y → to (from x +₁ from y)) ,
   to 0₁ ,
   (λ x y → to (from x *₁ from y)) ,
   to 1₁ ,
   (λ x → to (-₁ from x)) ,
   (λ x → ⊎-map P.id to (from x ⁻¹₁))) ≡
  (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂)

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
  Σ (V₁ ≃ V₂) λ V₁≃V₂ → let open _≃_ V₁≃V₂ in
  ((λ u v → to (from u +₁ from v)) ,
   (λ x v → to (x *₁ from v)) ,
   to 0₁ ,
   (λ x → to (-₁ from x))) ≡
  (_+₂_ , _*₂_ , 0₂ , -₂_)

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
     (∀ x y → Is-proposition (x ≤ y)) ×

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
  (∀ x y → Is-proposition (x ≤ y)) ×
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
-- * We use equality, (λ a b → from a ≤₁ from b) ≡ _≤₂_, instead of
--   "iff", ∀ a b → (a ≤₁ b) ⇔ (to a ≤₂ to b). However, the ordering
--   relation is pointwise propositional, so these two expressions are
--   equal (assuming univalence).

Isomorphic-poset :
  ∀ {P₁ _≤₁_ laws₁ P₂ _≤₂_ laws₂} →

  Isomorphic poset (P₁ , _≤₁_ , laws₁) (P₂ , _≤₂_ , laws₂)
    ≡
  Σ (P₁ ≃ P₂) λ P₁≃P₂ → let open _≃_ P₁≃P₂ in
  (λ a b → from a ≤₁ from b) ≡ _≤₂_

Isomorphic-poset = refl _

-- We can prove that the notion of isomorphism is isomorphic to the
-- usual notion of order isomorphism (assuming univalence).

Isomorphism-poset-isomorphic-to-order-isomorphism :
  Assumptions →
  ∀ {P₁ _≤₁_ laws₁ P₂ _≤₂_ laws₂} →

  Isomorphic poset (P₁ , _≤₁_ , laws₁) (P₂ , _≤₂_ , laws₂)
    ↔
  Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
  ∀ x y → (x ≤₁ y) ⇔ (to x ≤₂ to y)

Isomorphism-poset-isomorphic-to-order-isomorphism ass
  {P₁} {_≤₁_} {laws₁} {P₂} {_≤₂_} {laws₂} =

  (Σ (P₁ ≃ P₂) λ P₁≃P₂ → let open _≃_ P₁≃P₂ in
   (λ a b → from a ≤₁ from b) ≡ _≤₂_)           ↝⟨ inverse $ Σ-cong (↔↔≃ ext (proj₁ laws₁)) (λ _ → _ □) ⟩

  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   (λ a b → from a ≤₁ from b) ≡ _≤₂_)           ↔⟨ inverse $ ∃-cong (λ _ → extensionality-isomorphism ext) ⟩

  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   (∀ a → (λ b → from a ≤₁ from b) ≡ _≤₂_ a))   ↔⟨ inverse $ ∃-cong (λ _ → ∀-preserves ext λ _ → extensionality-isomorphism ext) ⟩

  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   (∀ a b → (from a ≤₁ from b) ≡ (a ≤₂ b)))     ↔⟨ inverse $ ∃-cong (λ P₁↔P₂ →
                                                     Π-preserves ext (↔⇒≃ P₁↔P₂) λ a → Π-preserves ext (↔⇒≃ P₁↔P₂) λ b →
                                                         ≡⇒≃ $ sym $ cong₂ (λ x y → (x ≤₁ y) ≡ (_↔_.to P₁↔P₂ a ≤₂ _↔_.to P₁↔P₂ b))
                                                                           (_↔_.left-inverse-of P₁↔P₂ a)
                                                                           (_↔_.left-inverse-of P₁↔P₂ b)) ⟩
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   (∀ a b → (a ≤₁ b) ≡ (to a ≤₂ to b)))         ↔⟨ ∃-cong (λ _ → ∀-preserves ext λ _ → ∀-preserves ext λ _ → ≡≃≃ univ) ⟩

  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   (∀ a b → (a ≤₁ b) ≃ (to a ≤₂ to b)))         ↔⟨ inverse $ ∃-cong (λ _ → ∀-preserves ext λ _ → ∀-preserves (lower-ext (# 0) _ ext) λ _ → ↔⇒≃ $
                                                     ⇔↔≃ (lower-ext _ _ ext) (proj₁ (proj₂ laws₁) _ _)
                                                                             (proj₁ (proj₂ laws₂) _ _)) ⟩□
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   (∀ a b → (a ≤₁ b) ⇔ (to a ≤₂ to b)))         □

  where open Assumptions ass

-- If we define isomorphism using Is-isomorphism′ instead of
-- Is-isomorphism, then the previous property can be proved without
-- using univalence (but still extensionality).

Isomorphism′-poset-isomorphic-to-order-isomorphism :
  Extensionality (# 1) (# 1) →
  ∀ {P₁ _≤₁_ laws₁ P₂ _≤₂_ laws₂} →

  Isomorphic′ poset (P₁ , _≤₁_ , laws₁) (P₂ , _≤₂_ , laws₂)
    ↔
  Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
  ∀ x y → (x ≤₁ y) ⇔ (to x ≤₂ to y)

Isomorphism′-poset-isomorphic-to-order-isomorphism ext
  {P₁} {_≤₁_} {laws₁} {P₂} {_≤₂_} {laws₂} =

  (Σ (P₁ ≃ P₂) λ P₁≃P₂ → let open _≃_ P₁≃P₂ in
   ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≃ (b ≤₂ d)))  ↝⟨ inverse $ Σ-cong (↔↔≃ ext (proj₁ laws₁)) (λ _ → _ □) ⟩

  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≃ (b ≤₂ d)))  ↔⟨ inverse $ ∃-cong (λ _ → ∀-preserves ext λ _ → ↔⇒≃ $
                                                                          ∀-intro ext λ _ _ → _) ⟩
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≃ (to a ≤₂ d)))                ↔⟨ inverse $ ∃-cong (λ _ → ∀-preserves ext λ _ → ∀-preserves ext λ _ → ↔⇒≃ $
                                                                          ∀-intro ext λ _ _ → _) ⟩
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a c → ↑ _ ((a ≤₁ c) ≃ (to a ≤₂ to c)))                          ↔⟨ ∃-cong (λ _ → ∀-preserves ext λ _ → ∀-preserves ext λ _ → ↔⇒≃
                                                                          ↑↔) ⟩
  (Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ P₁↔P₂ in
   ∀ a c → (a ≤₁ c) ≃ (to a ≤₂ to c))                                ↔⟨ inverse $ ∃-cong (λ _ →
                                                                          ∀-preserves ext λ _ → ∀-preserves (lower-ext (# 0) _ ext) λ _ → ↔⇒≃ $
                                                                            ⇔↔≃ (lower-ext _ _ ext) (proj₁ (proj₂ laws₁) _ _)
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
  Σ (F₁ ≃ F₂) λ F₁≃F₂ → let open _≃_ F₁≃F₂ in
  (λ f → to (fix₁ (λ x → from (f (to x))))) ≡ fix₂

Isomorphic-set-with-fixpoint-operator = refl _
