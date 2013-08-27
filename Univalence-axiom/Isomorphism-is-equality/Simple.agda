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

module Univalence-axiom.Isomorphism-is-equality.Simple
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq
  hiding (id; _∘_; inverse; _↔⟨_⟩_; finally-↔)
open import Category eq
open Derived-definitions-and-properties eq
  renaming (lower-extensionality to lower-ext)
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq hiding (id; _∘_; inverse)
open import Function-universe eq hiding (id) renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
open import Injection eq hiding (id; _∘_)
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Preimage eq
open import Prelude as P hiding (id)
open import Univalence-axiom eq

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

    -- El a, seen as a predicate, respects equivalences.

    resp : ∀ a {B C} → B ≃ C → El a B → El a C

    -- The resp function respects identities (assuming univalence).

    resp-id : Assumptions → ∀ a {B} (x : El a B) → resp a Eq.id x ≡ x

  -- Derived definitions.

  -- A predicate that specifies what it means for an equivalence to be
  -- an isomorphism between two elements.

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

    equality-pair-lemma :
      Assumptions →
      ∀ c {I J : Instance c} →
      (I ≡ J) ↔
      ∃ λ (C-eq : Carrier c I ≡ Carrier c J) →
        subst (El (proj₁ c)) C-eq (element c I) ≡ element c J
    equality-pair-lemma ass (a , P) {C , x , p} {D , y , q} =

      ((C , x , p) ≡ (D , y , q))                     ↔⟨ inverse $ ≃-≡ $ ↔⇒≃ Σ-assoc ⟩

      (((C , x) , p) ≡ ((D , y) , q))                 ↝⟨ inverse $ ignore-propositional-component (proj₂ (P D y) ass) ⟩

      ((C , x) ≡ (D , y))                             ↝⟨ inverse Σ-≡,≡↔≡ ⟩□

      (∃ λ (C-eq : C ≡ D) → subst (El a) C-eq x ≡ y)  □

  -- Structure isomorphisms.

  Isomorphic : ∀ c → Instance c → Instance c → Set₁
  Isomorphic (a , _) (C₁ , x₁ , _) (C₂ , x₂ , _) =
    Σ (C₁ ≃ C₂) λ C₁≃C₂ → Is-isomorphism a C₁≃C₂ x₁ x₂

  -- The type of isomorphisms between two instances of a structure
  -- is isomorphic to the type of equalities between the same
  -- instances (assuming univalence).
  --
  -- In short, isomorphism is isomorphic to equality.

  isomorphism-is-equality :
    Assumptions →
    ∀ c {I J} → Isomorphic c I J ↔ (I ≡ J)
  isomorphism-is-equality ass (a , P) {C , x , p} {D , y , q} =

    (∃ λ (C-eq : C ≃ D) → Is-isomorphism a C-eq x y)            ↝⟨ ∃-cong (λ C-eq → isomorphism-definitions-isomorphic ass a C-eq) ⟩

    (∃ λ (C-eq : C ≃ D) → subst (El a) (≃⇒≡ univ₁ C-eq) x ≡ y)  ↝⟨ inverse $
                                                                     Σ-cong (≡≃≃ univ₁) (λ C-eq → ≡⇒↝ _ $ sym $
                                                                       cong (λ eq → subst (El a) eq x ≡ y)
                                                                            (_≃_.left-inverse-of (≡≃≃ univ₁) C-eq)) ⟩
    (∃ λ (C-eq : C ≡ D) → subst (El a) C-eq x ≡ y)              ↝⟨ inverse $ equality-pair-lemma ass c ⟩□

    (I ≡ J)                                                     □

    where
    open Assumptions ass

    c : Code
    c = a , P

    I : Instance c
    I = C , x , p

    J : Instance c
    J = D , y , q

  abstract

    -- The first part of the from component of the preceding lemma is
    -- extensionally equal to a simple function. (The codomain of the
    -- second part is propositional whenever El (proj₁ c) applied to
    -- either carrier type is a set.)

    proj₁-from-isomorphism-is-equality :
      ∀ ass c {I J} (I≡J : I ≡ J) →
      proj₁ (_↔_.from (isomorphism-is-equality ass c) I≡J) ≡
      ≡⇒≃ (cong proj₁ I≡J)
    proj₁-from-isomorphism-is-equality ass _ I≡J =
      cong ≡⇒≃ (
        proj₁ (Σ-≡,≡←≡ (proj₁ (Σ-≡,≡←≡
          (cong (λ { (x , (y , z)) → (x , y) , z }) I≡J))))       ≡⟨ cong (proj₁ ∘ Σ-≡,≡←≡) $ proj₁-Σ-≡,≡←≡ _ ⟩
        proj₁ (Σ-≡,≡←≡ (cong proj₁
          (cong (λ { (x , (y , z)) → (x , y) , z }) I≡J)))        ≡⟨ cong (proj₁ ∘ Σ-≡,≡←≡) $ cong-∘ proj₁ (λ { (x , (y , z)) → (x , y) , z }) _ ⟩
        proj₁ (Σ-≡,≡←≡ (cong (λ { (x , (y , z)) → x , y }) I≡J))  ≡⟨ proj₁-Σ-≡,≡←≡ _ ⟩
        cong proj₁ (cong (λ { (x , (y , z)) → x , y }) I≡J)       ≡⟨ cong-∘ proj₁ (λ { (x , (y , z)) → x , y }) _ ⟩∎
        cong proj₁ I≡J                                            ∎)

    -- The type of (lifted) isomorphisms between two instances of a
    -- structure is equal to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is equal to equality.

    isomorphic≡≡ :
      Assumptions →
      ∀ c {I J} → ↑ (# 2) (Isomorphic c I J) ≡ (I ≡ J)
    isomorphic≡≡ ass c {I} {J} =
      ≃⇒≡ univ₂ $ ↔⇒≃ (
        ↑ _ (Isomorphic c I J)  ↝⟨ ↑↔ ⟩
        Isomorphic c I J        ↝⟨ isomorphism-is-equality ass c ⟩□
        (I ≡ J)                 □)
      where open Assumptions ass

------------------------------------------------------------------------
-- An aside: A slightly restricted variant of
-- Class.isomorphism-is-equality can be proved by using Aczel and
-- Shulman's "Abstract SIP Theorem", as found in one draft of the HoTT
-- Book

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
  ∀ {X Y} → Is-equivalence
              (Precategory.≡→≅ (Standard-notion-of-structure.Str S)
                               {X} {Y})

-- The "Abstract SIP Theorem", as stated above, can be used to prove a
-- slightly restricted variant of Class.isomorphism-is-equality.

isomorphism-is-equality-is-corollary :
  Abstract-SIP-Theorem (# 2) (# 1) (# 1) (# 1) →
  (Univ : Universe) → let open Universe Univ in
  (∀ a {B} → Is-set B → Is-set (El a B)) →  -- Extra assumption.
  Assumptions →
  ∀ c {I J} →
  Is-set (proj₁ I) → Is-set (proj₁ J) →     -- Extra assumptions.
  Class.Isomorphic Univ c I J ↔ (I ≡ J)
isomorphism-is-equality-is-corollary sip Univ El-set ass
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
  ((Cs , x) ≅-Str (Ds , y))                   ↔⟨ inverse ⟨ _ , sip X≅ S {X = Cs , x} {Y = Ds , y} ⟩ ⟩
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
                          resp a (≅⇒≃ C C (Category.id X≅ {X = C})) x  ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
                          resp a Eq.id x                               ≡⟨ resp-id ass a x ⟩∎
                          x                                            ∎
    ; H-∘             = λ {B C D x y z B≅C C≅D} x≅y y≅z →
                          resp a (≅⇒≃ B D (Category._∙_ X≅ B≅C C≅D)) x   ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
                          resp a (≅⇒≃ C D C≅D ⊚ ≅⇒≃ B C B≅C) x           ≡⟨ resp-preserves-compositions (El a) (resp a) (resp-id ass a)
                                                                                                        univ₁ ext (≅⇒≃ B C B≅C) (≅⇒≃ C D C≅D) x ⟩
                          resp a (≅⇒≃ C D C≅D) (resp a (≅⇒≃ B C B≅C) x)  ≡⟨ cong (resp a (≅⇒≃ C D C≅D)) x≅y ⟩
                          resp a (≅⇒≃ C D C≅D) y                         ≡⟨ y≅z ⟩∎
                          z                                              ∎
    ; H-antisymmetric = λ {C} x y x≡y _ →
                          x                                            ≡⟨ sym $ resp-id ass a x ⟩
                          resp a Eq.id x                               ≡⟨ cong (λ eq → resp a eq x) $ Eq.lift-equality ext (refl _) ⟩
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
       (resp a (≅⇒≃ D C D≅C) y            ≡⟨ cong (λ eq → resp a eq y) $ Eq.lift-equality ext (refl _) ⟩
        resp a (inverse $ ≅⇒≃ C D C≅D) y  ≡⟨ resp-preserves-inverses (El a) (resp a) (resp-id ass a) univ₁ ext (≅⇒≃ C D C≅D) _ _ x≅y ⟩∎
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

-- El a preserves logical equivalences.

cast : ∀ a {B C} → B ⇔ C → El a B ⇔ El a C
cast id      B≃C = B≃C
cast set     B≃C = Logical-equivalence.id
cast (k A)   B≃C = Logical-equivalence.id
cast (a ⇾ b) B≃C = →-cong-⇔ (cast a B≃C) (cast b B≃C)
cast (a ⊗ b) B≃C = cast a B≃C ×-cong cast b B≃C
cast (a ⊕ b) B≃C = cast a B≃C ⊎-cong cast b B≃C

-- El a respects equivalences.

resp : ∀ a {B C} → B ≃ C → El a B → El a C
resp a B≃C = _⇔_.to (cast a (_≃_.equivalence B≃C))

resp⁻¹ : ∀ a {B C} → B ≃ C → El a C → El a B
resp⁻¹ a B≃C = _⇔_.from (cast a (_≃_.equivalence B≃C))

abstract

  -- The cast function respects identities (assuming extensionality).

  cast-id : Extensionality (# 1) (# 1) →
            ∀ a {B} → cast a (Logical-equivalence.id {A = B}) ≡
                      Logical-equivalence.id
  cast-id ext id      = refl _
  cast-id ext set     = refl _
  cast-id ext (k A)   = refl _
  cast-id ext (a ⇾ b) = cong₂ →-cong-⇔ (cast-id ext a) (cast-id ext b)
  cast-id ext (a ⊗ b) = cong₂ _×-cong_ (cast-id ext a) (cast-id ext b)
  cast-id ext (a ⊕ b) =
    cast a Logical-equivalence.id ⊎-cong cast b Logical-equivalence.id  ≡⟨ cong₂ _⊎-cong_ (cast-id ext a) (cast-id ext b) ⟩
    Logical-equivalence.id ⊎-cong Logical-equivalence.id                ≡⟨ cong₂ (λ f g → record { to = f; from = g })
                                                                                 (ext [ refl ∘ inj₁ , refl ∘ inj₂ ])
                                                                                 (ext [ refl ∘ inj₁ , refl ∘ inj₂ ]) ⟩∎
    Logical-equivalence.id                                              ∎

  resp-id : Extensionality (# 1) (# 1) →
            ∀ a {B} x → resp a (Eq.id {A = B}) x ≡ x
  resp-id ext a x = cong (λ eq → _⇔_.to eq x) $ cast-id ext a

-- The universe above is a "universe with some extra stuff".

simple : Universe
simple = record
  { U       = U
  ; El      = El
  ; resp    = resp
  ; resp-id = resp-id ∘ Assumptions.ext
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

-- El a preserves equivalences (assuming extensionality).
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
  cst set     = Eq.id
  cst (k A)   = Eq.id
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

private

  equivalence-cast≃ :
    (ext : Extensionality (# 1) (# 1)) →
    ∀ a {B C} (B≃C : B ≃ C) →
    _≃_.equivalence (cast≃ ext a B≃C) ≡ cast a (_≃_.equivalence B≃C)
  equivalence-cast≃ _ _ _ = refl _

-- Alternative, shorter definition of cast≃, based on univalence.
--
-- This proof does not (at the time of writing) have the property that
-- _≃_.equivalence (cast≃′ ass a B≃C) is definitionally equal to
-- cast a (_≃_.equivalence B≃C).

cast≃′ : Assumptions → ∀ a {B C} → B ≃ C → El a B ≃ El a C
cast≃′ ass a B≃C =
  ⟨ resp a B≃C
  , resp-is-equivalence (El a) (resp a) (resp-id ext a) univ₁ B≃C
  ⟩
  where open Assumptions ass

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

private

  -- Some lemmas used below.

  0* :
    {F : Set₁}
    (_+_ : F → F → F)
    (0# : F)
    (_*_ : F → F → F)
    (1# : F)
    (-_ : F → F) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) →
    (∀ x y → x + y ≡ y + x) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) →
    (∀ x → x + 0# ≡ x) →
    (∀ x → x * 1# ≡ x) →
    (∀ x → x + (- x) ≡ 0#) →
    ∀ x → 0# * x ≡ 0#
  0* _+_ 0# _*_ 1# -_ +-assoc +-comm *-comm *+ +0 *1 +- x =
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

  dec-lemma₁ :
    {F : Set₁}
    (_+_ : F → F → F)
    (0# : F)
    (-_ : F → F) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) →
    (∀ x y → x + y ≡ y + x) →
    (∀ x → x + 0# ≡ x) →
    (∀ x → x + (- x) ≡ 0#) →
    (∀ x → Dec (x ≡ 0#)) →
    Decidable (_≡_ {A = F})
  dec-lemma₁ _+_ 0# -_ +-assoc +-comm +0 +- dec-0 x y =
    ⊎-map (λ x-y≡0 → x              ≡⟨ sym $ +0 _ ⟩
                     x + 0#         ≡⟨ cong (_+_ _) $ sym $ +- _ ⟩
                     x + (y + - y)  ≡⟨ cong (_+_ _) $ +-comm _ _ ⟩
                     x + (- y + y)  ≡⟨ +-assoc _ _ _ ⟩
                     (x + - y) + y  ≡⟨ cong (λ x → x + _) x-y≡0 ⟩
                     0# + y         ≡⟨ +-comm _ _ ⟩
                     y + 0#         ≡⟨ +0 _ ⟩∎
                     y              ∎)
          (λ x-y≢0 x≡y → x-y≢0 (x + - y  ≡⟨ cong (_+_ _ ∘ -_) $ sym x≡y ⟩
                                x + - x  ≡⟨ +- _ ⟩∎
                                0#       ∎))
          (dec-0 (x + - y))

  dec-lemma₂ :
    {F : Set₁}
    (_+_ : F → F → F)
    (0# : F)
    (_*_ : F → F → F)
    (1# : F)
    (-_ : F → F) →
    (_⁻¹ : F → ↑ (# 1) ⊤ ⊎ F) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) →
    (∀ x y → x + y ≡ y + x) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) →
    (∀ x → x + 0# ≡ x) →
    (∀ x → x * 1# ≡ x) →
    (∀ x → x + (- x) ≡ 0#) →
    0# ≢ 1# →
    (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) →
    (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) →
    Decidable (_≡_ {A = F})
  dec-lemma₂ _+_ 0# _*_ 1# -_ _⁻¹ +-assoc +-comm *-comm
             *+ +0 *1 +- 0≢1 ⁻¹₁ ⁻¹₂ =
    dec-lemma₁ _+_ 0# -_ +-assoc +-comm +0 +- dec-0
    where
    dec-0 : ∀ z → Dec (z ≡ 0#)
    dec-0 z with z ⁻¹ | ⁻¹₁ z | ⁻¹₂ z
    ... | inj₁ _   | hyp | _   = inj₁ (hyp (refl _))
    ... | inj₂ z⁻¹ | _   | hyp = inj₂ (λ z≡0 →
      0≢1 (0#        ≡⟨ sym $ 0* _+_ 0# _*_ 1# -_ +-assoc +-comm *-comm *+ +0 *1 +- _ ⟩
           0# * z⁻¹  ≡⟨ cong (λ x → x * _) $ sym z≡0 ⟩
           z * z⁻¹   ≡⟨ hyp z⁻¹ (refl _) ⟩∎
           1#        ∎))

  dec-lemma₃ :
    {F : Set₁}
    (_+_ : F → F → F)
    (0# : F)
    (-_ : F → F) →
    (_*_ : F → F → F)
    (1# : F) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) →
    (∀ x y z → x * (y * z) ≡ (x * y) * z) →
    (∀ x y → x + y ≡ y + x) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x → x + 0# ≡ x) →
    (∀ x → x * 1# ≡ x) →
    (∀ x → x + (- x) ≡ 0#) →
    (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#)) →
    Decidable (_≡_ {A = F})
  dec-lemma₃ _+_ 0# -_ _*_ 1# +-assoc *-assoc +-comm *-comm +0 *1 +-
             inv-xor =
    dec-lemma₁ _+_ 0# -_ +-assoc +-comm +0 +-
               (λ x → [ inj₂ ∘ proj₂ , inj₁ ∘ proj₂ ] (inv-xor x))

  *-injective :
    {F : Set₁}
    (_*_ : F → F → F)
    (1# : F) →
    (∀ x y z → x * (y * z) ≡ (x * y) * z) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x → x * 1# ≡ x) →
    ∀ x → ∃ (λ y → x * y ≡ 1#) → Injective (_*_ x)
  *-injective _*_ 1# *-assoc *-comm *1 x (x⁻¹ , xx⁻¹≡1)
             {y₁} {y₂} xy₁≡xy₂ =
    y₁              ≡⟨ lemma y₁ ⟩
    x⁻¹ * (x * y₁)  ≡⟨ cong (_*_ x⁻¹) xy₁≡xy₂ ⟩
    x⁻¹ * (x * y₂)  ≡⟨ sym $ lemma y₂ ⟩∎
    y₂              ∎
    where
    lemma : ∀ y → y ≡ x⁻¹ * (x * y)
    lemma y =
      y              ≡⟨ sym $ *1 _ ⟩
      y * 1#         ≡⟨ *-comm _ _ ⟩
      1# * y         ≡⟨ cong (λ x → x * y) $ sym xx⁻¹≡1 ⟩
      (x * x⁻¹) * y  ≡⟨ cong (λ x → x * y) $ *-comm _ _ ⟩
      (x⁻¹ * x) * y  ≡⟨ sym $ *-assoc _ _ _ ⟩∎
      x⁻¹ * (x * y)  ∎

  inverse-propositional :
    {F : Set₁}
    (_*_ : F → F → F)
    (1# : F) →
    (∀ x y z → x * (y * z) ≡ (x * y) * z) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x → x * 1# ≡ x) →
    Is-set F →
    ∀ x → Is-proposition (∃ λ y → x * y ≡ 1#)
  inverse-propositional _*_ 1# *-assoc *-comm *1 F-set x =
    [inhabited⇒+]⇒+ 0 λ { inv →
    injection⁻¹-propositional
      (record { to        = _*_ x
              ; injective = *-injective _*_ 1# *-assoc *-comm *1 x inv
              })
      F-set 1# }

  proposition-lemma₁ :
    Extensionality (# 1) (# 1) →
    {F : Set₁}
    (0# : F)
    (_*_ : F → F → F)
    (1# : F) →
    (∀ x y z → x * (y * z) ≡ (x * y) * z) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x → x * 1# ≡ x) →
    Is-proposition (((x y : F) → x ≡ y ⊎ x ≢ y) ×
                    (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#))
  proposition-lemma₁ ext 0# _*_ 1# *-assoc *-comm *1 =
    [inhabited⇒+]⇒+ 0 λ { (dec , _) →
    let F-set = decidable⇒set dec in
    ×-closure 1 (Π-closure ext 1 λ _ →
                 Π-closure ext 1 λ _ →
                 Dec-closure-propositional (lower-ext (# 0) _ ext)
                                           (F-set _ _))
                (Π-closure ext 1 λ x →
                 Π-closure ext 1 λ _ →
                 inverse-propositional _*_ 1# *-assoc *-comm *1
                                       F-set x) }

  proposition-lemma₂ :
    Extensionality (# 1) (# 1) →
    {F : Set₁}
    (_+_ : F → F → F)
    (0# : F)
    (-_ : F → F) →
    (_*_ : F → F → F)
    (1# : F) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) →
    (∀ x y z → x * (y * z) ≡ (x * y) * z) →
    (∀ x y → x + y ≡ y + x) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x → x + 0# ≡ x) →
    (∀ x → x * 1# ≡ x) →
    (∀ x → x + (- x) ≡ 0#) →
    Is-proposition (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#))
  proposition-lemma₂ ext _+_ 0# -_ _*_ 1# +-assoc *-assoc +-comm *-comm
                     +0 *1 +- =
    [inhabited⇒+]⇒+ 0 λ inv-xor →
    let F-set = decidable⇒set $
                  dec-lemma₃ _+_ 0# -_ _*_ 1# +-assoc *-assoc
                             +-comm *-comm +0 *1 +- inv-xor in
    Π-closure ext 1 λ x →
    Xor-closure-propositional (lower-ext (# 0) _ ext)
      (inverse-propositional _*_ 1# *-assoc *-comm *1 F-set x)
      (F-set _ _)

  proposition-lemma₃ :
    Extensionality (# 1) (# 1) →
    {F : Set₁}
    (_+_ : F → F → F)
    (0# : F)
    (_*_ : F → F → F)
    (1# : F) →
    (-_ : F → F) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) →
    (∀ x y z → x * (y * z) ≡ (x * y) * z) →
    (∀ x y → x + y ≡ y + x) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) →
    (∀ x → x + 0# ≡ x) →
    (∀ x → x * 1# ≡ x) →
    (∀ x → x + (- x) ≡ 0#) →
    0# ≢ 1# →
    Is-proposition (Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
                      (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
                      (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#))
  proposition-lemma₃ ext {F} _+_ 0# _*_ 1# -_ +-assoc *-assoc
                     +-comm *-comm *+ +0 *1 +- 0≢1 =
    _⇔_.from propositional⇔irrelevant irr
    where
    irr : ∀ x y → x ≡ y
    irr (inv , inv₁ , inv₂) (inv′ , inv₁′ , inv₂′) =
      _↔_.to (ignore-propositional-component
                (×-closure 1 (Π-closure ext 1 λ _ →
                              Π-closure ext 1 λ _ →
                              F-set _ _)
                             (Π-closure ext 1 λ _ →
                              Π-closure ext 1 λ _ →
                              Π-closure ext 1 λ _ →
                              F-set _ _)))
             (ext inv≡inv′)
      where
      F-set : Is-set F
      F-set = decidable⇒set $
        dec-lemma₂ _+_ 0# _*_ 1# -_ inv +-assoc +-comm
                   *-comm *+ +0 *1 +- 0≢1 inv₁ inv₂

      01-lemma : ∀ x y → x ≡ 0# → x * y ≡ 1# → ⊥
      01-lemma x y x≡0 xy≡1 = 0≢1 (
        0#      ≡⟨ sym $ 0* _+_ 0# _*_ 1# -_ +-assoc +-comm *-comm *+ +0 *1 +- _ ⟩
        0# * y  ≡⟨ cong (λ x → x * _) $ sym x≡0 ⟩
        x * y   ≡⟨ xy≡1 ⟩∎
        1#      ∎)

      inv≡inv′ : ∀ x → inv x ≡ inv′ x
      inv≡inv′ x with inv  x | inv₁  x | inv₂  x
                    | inv′ x | inv₁′ x | inv₂′ x
      ... | inj₁ _   | _ | _   | inj₁ _    | _    | _ = refl _
      ... | inj₂ x⁻¹ | _ | hyp | inj₁ _    | hyp′ | _ = ⊥-elim $ 01-lemma x x⁻¹ (hyp′ (refl _)) (hyp x⁻¹ (refl _))
      ... | inj₁ _   | hyp | _ | inj₂ x⁻¹  | _ | hyp′ = ⊥-elim $ 01-lemma x x⁻¹ (hyp (refl _)) (hyp′ x⁻¹ (refl _))
      ... | inj₂ x⁻¹ | _ | hyp | inj₂ x⁻¹′ | _ | hyp′ =
        cong inj₂ $ *-injective _*_ 1# *-assoc *-comm *1 x
                                (x⁻¹ , hyp x⁻¹ (refl _))
          (x * x⁻¹   ≡⟨ hyp x⁻¹ (refl _) ⟩
           1#        ≡⟨ sym $ hyp′ x⁻¹′ (refl _) ⟩∎
           x * x⁻¹′  ∎)

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
  (id ⇾ k (↑ _ ⊤) ⊕ id) ,

  λ { F (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →

      (-- Associativity.
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

       -- Additive inverse law.
       (∀ x → x + (- x) ≡ 0#) ×

       -- Zero and one are distinct.
       0# ≢ 1# ×

       -- Multiplicative inverse laws.
       (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
       (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#)) ,

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (+-assoc , _ , +-comm , *-comm , *+ , +0 ,
                               *1 , +- , 0≢1 , ⁻¹₁ , ⁻¹₂) →
          let F-set : Is-set F
              F-set = decidable⇒set $
                        dec-lemma₂ _+_ 0# _*_ 1# -_ _⁻¹ +-assoc +-comm
                                   *-comm *+ +0 *1 +- 0≢1 ⁻¹₁ ⁻¹₂
          in
          ×-closure  1 (Π-closure ext 1 λ _ →
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
                        F-set _ _)
          (×-closure 1 (Π-closure (lower-ext (# 0) (# 1) ext) 1 λ _ →
                        ⊥-propositional)
          (×-closure 1 (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _)
                       (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        F-set _ _)))))))))) }}

-- The interpretation of the code is reasonable.

Instance-discrete-field :

  Instance discrete-field
    ≡
  Σ Set₁ λ F →
  Σ ((F → F → F) × F × (F → F → F) × F × (F → F) × (F → ↑ _ ⊤ ⊎ F))
    λ { (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →
  (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
  (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
  (∀ x y → x + y ≡ y + x) ×
  (∀ x y → x * y ≡ y * x) ×
  (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
  (∀ x → x + 0# ≡ x) ×
  (∀ x → x * 1# ≡ x) ×
  (∀ x → x + (- x) ≡ 0#) ×
  0# ≢ 1# ×
  (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
  (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) }

Instance-discrete-field = refl _

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

-- The definitions of discrete field introduced below do not have an
-- inverse operator in their signature, so the derived notion of
-- isomorphism is perhaps not obviously identical to the one above.
-- However, the two notions of isomorphism are isomorphic (assuming
-- extensionality).

Isomorphic-discrete-field-isomorphic-to-one-without-⁻¹ :
  Extensionality (# 1) (# 1) →
  ∀ {F₁ _+₁_ 0₁ _*₁_ 1₁ -₁_ _⁻¹₁ laws₁
     F₂ _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ laws₂} →

  Isomorphic discrete-field
             (F₁ , (_+₁_ , 0₁ , _*₁_ , 1₁ , -₁_ , _⁻¹₁) , laws₁)
             (F₂ , (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂) , laws₂)
    ↔
  Σ (F₁ ≃ F₂) λ F₁≃F₂ → let open _≃_ F₁≃F₂ in
  ((λ x y → to (from x +₁ from y)) ,
   to 0₁ ,
   (λ x y → to (from x *₁ from y)) ,
   to 1₁ ,
   (λ x → to (-₁ from x))) ≡
  (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_)

Isomorphic-discrete-field-isomorphic-to-one-without-⁻¹ ext
  {F₁} {_+₁_} {0₁} {_*₁_} {1₁} { -₁_} {_⁻¹₁}
  {_ , _ , _ , _ , _ , _ , _ , _ , _ , ⁻¹₁₁ , ⁻¹₁₂}
  {F₂} {_+₂_} {0₂} {_*₂_} {1₂} { -₂_} {_⁻¹₂}
  {+₂-assoc , *₂-assoc , +₂-comm , *₂-comm , *₂+₂ , +₂0₂ , *₂1₂ , +₂-₂ ,
   0₂≢1₂ , ⁻¹₂₁ , ⁻¹₂₂} =

  ∃-cong λ F₁≃F₂ → let open _≃_ F₁≃F₂ in

  (((λ x y → to (from x +₁ from y)) ,
    to 0₁ ,
    (λ x y → to (from x *₁ from y)) ,
    to 1₁ ,
    (λ x → to (-₁ from x)) ,
    (λ x → ⊎-map P.id to (from x ⁻¹₁))) ≡
   (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂))                  ↝⟨ inverse (≡×≡↔≡ ⊚ ((_ □) ×-cong
                                                                      ≡×≡↔≡ ⊚ ((_ □) ×-cong
                                                                      ≡×≡↔≡ ⊚ ((_ □) ×-cong
                                                                      ≡×≡↔≡ ⊚ ((_ □) ×-cong
                                                                      ≡×≡↔≡))))) ⟩
  ((λ x y → to (from x +₁ from y)) ≡ _+₂_ ×
   to 0₁ ≡ 0₂ ×
   (λ x y → to (from x *₁ from y)) ≡ _*₂_ ×
   to 1₁ ≡ 1₂ ×
   (λ x → to (-₁ from x)) ≡ -₂_ ×
   (λ x → ⊎-map P.id to (from x ⁻¹₁)) ≡ _⁻¹₂)             ↝⟨ (∃-cong λ _ →
                                                              ∃-cong λ 0-homo →
                                                              ∃-cong λ *-homo →
                                                              ∃-cong λ 1-homo →
                                                              ∃-cong λ _ →
                                                              contractible↔⊤ $ propositional⇒inhabited⇒contractible
                                                                (⁻¹-set _ _)
                                                                (⁻¹-homo F₁≃F₂ 0-homo *-homo 1-homo)) ⟩
  ((λ x y → to (from x +₁ from y)) ≡ _+₂_ ×
   to 0₁ ≡ 0₂ ×
   (λ x y → to (from x *₁ from y)) ≡ _*₂_ ×
   to 1₁ ≡ 1₂ ×
   (λ x → to (-₁ from x)) ≡ -₂_ ×
   ⊤)                                                     ↝⟨ (_ □) ×-cong (_ □) ×-cong (_ □) ×-cong (_ □) ×-cong ×-right-identity ⟩

  ((λ x y → to (from x +₁ from y)) ≡ _+₂_ ×
   to 0₁ ≡ 0₂ ×
   (λ x y → to (from x *₁ from y)) ≡ _*₂_ ×
   to 1₁ ≡ 1₂ ×
   (λ x → to (-₁ from x)) ≡ -₂_)                          ↝⟨ ≡×≡↔≡ ⊚ ((_ □) ×-cong
                                                             ≡×≡↔≡ ⊚ ((_ □) ×-cong
                                                             ≡×≡↔≡ ⊚ ((_ □) ×-cong
                                                             ≡×≡↔≡))) ⟩
  (((λ x y → to (from x +₁ from y)) ,
    to 0₁ ,
    (λ x y → to (from x *₁ from y)) ,
    to 1₁ ,
    (λ x → to (-₁ from x))) ≡
   (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_))                         □

  where
  ⁻¹-set : Is-set (F₂ → ↑ _ ⊤ ⊎ F₂)
  ⁻¹-set =
    Π-closure ext 2 λ _ →
    ⊎-closure 0 (↑-closure 2 (mono (≤-step (≤-step ≤-refl))
                           ⊤-contractible))
                (decidable⇒set $
                   dec-lemma₂ _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ +₂-assoc +₂-comm
                              *₂-comm *₂+₂ +₂0₂ *₂1₂ +₂-₂ 0₂≢1₂
                              ⁻¹₂₁ ⁻¹₂₂)

  ⁻¹-homo :
    (F₁≃F₂ : F₁ ≃ F₂) → let open _≃_ F₁≃F₂ in
    to 0₁ ≡ 0₂ →
    (λ x y → to (from x *₁ from y)) ≡ _*₂_ →
    to 1₁ ≡ 1₂ →
    (λ x → ⊎-map P.id to (from x ⁻¹₁)) ≡ _⁻¹₂
  ⁻¹-homo F₁≃F₂ 0-homo *-homo 1-homo =
    cong proj₁ $
    _⇔_.to propositional⇔irrelevant
           (proposition-lemma₃ ext _+₂_ 0₂ _*₂_ 1₂ -₂_
                               +₂-assoc *₂-assoc +₂-comm *₂-comm
                               *₂+₂ +₂0₂ *₂1₂ +₂-₂ 0₂≢1₂)
           ( (λ x → ⊎-map P.id to (from x ⁻¹₁))
           , (λ x x⁻¹₁≡₁ →
                let lemma =
                      from x ⁻¹₁                                    ≡⟨ [_,_] {C = λ z → z ≡ ⊎-map P.id from (⊎-map P.id to z)}
                                                                             (λ _ → refl _)
                                                                             (λ _ → cong inj₂ $ sym $ left-inverse-of _)
                                                                             (from x ⁻¹₁) ⟩
                      ⊎-map P.id from (⊎-map P.id to (from x ⁻¹₁))  ≡⟨ cong (⊎-map P.id from) x⁻¹₁≡₁ ⟩∎
                      inj₁ (lift tt)                                ∎
                in
                x            ≡⟨ sym $ right-inverse-of x ⟩
                to (from x)  ≡⟨ cong to (⁻¹₁₁ (from x) lemma) ⟩
                to 0₁        ≡⟨ 0-homo ⟩∎
                0₂           ∎)
           , (λ x y x⁻¹₁≡y →
                let lemma =
                      from x ⁻¹₁                                    ≡⟨ [_,_] {C = λ z → z ≡ ⊎-map P.id from (⊎-map P.id to z)}
                                                                             (λ _ → refl _)
                                                                             (λ _ → cong inj₂ $ sym $ left-inverse-of _)
                                                                             (from x ⁻¹₁) ⟩
                      ⊎-map P.id from (⊎-map P.id to (from x ⁻¹₁))  ≡⟨ cong (⊎-map P.id from) x⁻¹₁≡y ⟩∎
                      inj₂ (from y)                                 ∎
                in
                x *₂ y                 ≡⟨ sym $ cong (λ _*_ → x * y) *-homo ⟩
                to (from x *₁ from y)  ≡⟨ cong to $ ⁻¹₁₂ (from x) (from y) lemma ⟩
                to 1₁                  ≡⟨ 1-homo ⟩∎
                1₂                     ∎)
           )
           (_⁻¹₂ , ⁻¹₂₁ , ⁻¹₂₂)
    where open _≃_ F₁≃F₂

-- In "Varieties of Constructive Mathematics" Bridges and Richman
-- define a discrete field as a commutative ring with 1, decidable
-- equality, and satisfying the property that non-zero elements are
-- invertible. What follows is—assuming that I interpreted the
-- informal definition correctly—an encoding of this definition,
-- restricted so that the discrete fields are non-trivial, and using
-- equality as the equality relation, and denial inequality as the
-- inequality relation.

discrete-field-à-la-Bridges-and-Richman : Code
discrete-field-à-la-Bridges-and-Richman =
  -- Addition.
  (id ⇾ id ⇾ id) ⊗

  -- Zero.
  id ⊗

  -- Multiplication.
  (id ⇾ id ⇾ id) ⊗

  -- One.
  id ⊗

  -- Minus.
  (id ⇾ id) ,

  λ { F (_+_ , 0# , _*_ , 1# , -_) →

      (-- Associativity.
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

       -- Additive inverse law.
       (∀ x → x + (- x) ≡ 0#) ×

       -- Zero and one are distinct.
       0# ≢ 1# ×

       -- Decidable equality.
       ((x y : F) → x ≡ y ⊎ x ≢ y) ×

       -- Non-zero elements are invertible.
       (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#)) ,

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (_ , *-assoc , _ , *-comm , _ , _ , *1 ,
                               _ , _ , dec , _) →
          let F-set : Is-set F
              F-set = decidable⇒set dec
          in
          ×-closure  1 (Π-closure ext 1 λ _ →
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
                        F-set _ _)
          (×-closure 1 (Π-closure (lower-ext (# 0) (# 1) ext) 1 λ _ →
                        ⊥-propositional)
          (proposition-lemma₁ ext 0# _*_ 1# *-assoc *-comm *1))))))))) }}

-- The two discrete field definitions above are isomorphic (assuming
-- extensionality).

Instance-discrete-field-isomorphic-to-Bridges-and-Richman's :
  Extensionality (# 1) (# 1) →

  Instance discrete-field
    ↔
  Instance discrete-field-à-la-Bridges-and-Richman

Instance-discrete-field-isomorphic-to-Bridges-and-Richman's ext =
  ∃-cong λ F →

  (Σ ((F → F → F) × F × (F → F → F) × F × (F → F) × (F → ↑ _ ⊤ ⊎ F))
      λ { (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →
          (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
          (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
          (∀ x y → x + y ≡ y + x) ×
          (∀ x y → x * y ≡ y * x) ×
          (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
          (∀ x → x + 0# ≡ x) ×
          (∀ x → x * 1# ≡ x) ×
          (∀ x → x + (- x) ≡ 0#) ×
          0# ≢ 1# ×
          (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
          (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#)})                      ↝⟨ lemma₁ _ _ _ _ _ _ _ ⟩

  (Σ ((F → F → F) × F × (F → F → F) × F × (F → F))
      λ { (_+_ , 0# , _*_ , 1# , -_) →
          Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
          (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
          (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
          (∀ x y → x + y ≡ y + x) ×
          (∀ x y → x * y ≡ y * x) ×
          (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
          (∀ x → x + 0# ≡ x) ×
          (∀ x → x * 1# ≡ x) ×
          (∀ x → x + (- x) ≡ 0#) ×
          0# ≢ 1# ×
          (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
          (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#)})                      ↝⟨ ∃-cong (λ _ → lemma₂ _ _ _ _ _ _ _ _ _ _ _) ⟩

  (Σ (((F → F → F) × F × (F → F → F) × F × (F → F)))
     λ { (_+_ , 0# , _*_ , 1# , -_) →
         (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
         (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
         (∀ x y → x + y ≡ y + x) ×
         (∀ x y → x * y ≡ y * x) ×
         (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
         (∀ x → x + 0# ≡ x) ×
         (∀ x → x * 1# ≡ x) ×
         (∀ x → x + (- x) ≡ 0#) ×
         0# ≢ 1# ×
         Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
         (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
         (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) })                      ↝⟨ (∃-cong λ { (_+_ , 0# , _*_ , 1# , -_) →
                                                                          ∃-cong λ +-assoc →
                                                                          ∃-cong λ *-assoc →
                                                                          ∃-cong λ +-comm →
                                                                          ∃-cong λ *-comm →
                                                                          ∃-cong λ *+ →
                                                                          ∃-cong λ +0 →
                                                                          ∃-cong λ *1 →
                                                                          ∃-cong λ +- →
                                                                          ∃-cong λ 0≢1 →
                                                                          main-lemma F _+_ 0# _*_ 1# -_
                                                                                     +-assoc *-assoc +-comm *-comm *+ +0 *1 +- 0≢1 }) ⟩□
  (Σ ((F → F → F) × F × (F → F → F) × F × (F → F))
     λ { (_+_ , 0# , _*_ , 1# , -_) →
         (∀ x y z → x + (y + z) ≡ (x + y) + z) ×
         (∀ x y z → x * (y * z) ≡ (x * y) * z) ×
         (∀ x y → x + y ≡ y + x) ×
         (∀ x y → x * y ≡ y * x) ×
         (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) ×
         (∀ x → x + 0# ≡ x) ×
         (∀ x → x * 1# ≡ x) ×
         (∀ x → x + (- x) ≡ 0#) ×
         0# ≢ 1# ×
         ((x y : F) → x ≡ y ⊎ x ≢ y) ×
         (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#) })                       □

  where
  main-lemma :
    (F : Set₁)
    (_+_ : F → F → F)
    (0# : F)
    (_*_ : F → F → F)
    (1# : F)
    (-_ : F → F) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) →
    (∀ x y z → x * (y * z) ≡ (x * y) * z) →
    (∀ x y → x + y ≡ y + x) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) →
    (∀ x → x + 0# ≡ x) →
    (∀ x → x * 1# ≡ x) →
    (∀ x → x + (- x) ≡ 0#) →
    0# ≢ 1# →

    (Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
     (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
     (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#))
      ↔
    (((x y : F) → x ≡ y ⊎ x ≢ y) ×
     (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#))

  main-lemma F _+_ 0# _*_ 1# -_
             +-assoc *-assoc +-comm *-comm *+ +0 *1 +- 0≢1 =
    _≃_.bijection $
    _↔_.to (⇔↔≃ ext (proposition-lemma₃ ext _+_ 0# _*_ 1# -_
                                        +-assoc *-assoc +-comm *-comm
                                        *+ +0 *1 +- 0≢1)
                    (proposition-lemma₁ ext 0# _*_ 1# *-assoc *-comm *1))
           (record { to = to; from = from })
    where
    To   = (((x y : F) → x ≡ y ⊎ x ≢ y) ×
            (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#))
    From = Σ (F → ↑ _ ⊤ ⊎ F) λ _⁻¹ →
           (∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#) ×
           (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#)

    to : From → To
    to (_⁻¹ , ⁻¹₁ , ⁻¹₂) = (dec , inv)
      where
      dec : Decidable (_≡_ {A = F})
      dec = dec-lemma₂ _+_ 0# _*_ 1# -_ _⁻¹ +-assoc +-comm *-comm *+
                       +0 *1 +- 0≢1 ⁻¹₁ ⁻¹₂

      inv : ∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#
      inv x x≢0 with x ⁻¹ | ⁻¹₁ x | ⁻¹₂ x
      ... | inj₁ _ | hyp | _   = ⊥-elim $ x≢0 (hyp (refl _))
      ... | inj₂ y | _   | hyp = y , hyp y (refl _)

    from : To → From
    from (dec , inv) = (_⁻¹ , ⁻¹₁ , ⁻¹₂)
      where
      _⁻¹ : F → ↑ _ ⊤ ⊎ F
      x ⁻¹ = ⊎-map (λ _ → _) (proj₁ ∘ inv x) (dec x 0#)

      ⁻¹₁ : ∀ x → x ⁻¹ ≡ inj₁ (lift tt) → x ≡ 0#
      ⁻¹₁ x x⁻¹≡₁ with dec x 0#
      ... | inj₁ x≡0 = x≡0
      ... | inj₂ x≢0 = ⊥-elim $ ⊎.inj₁≢inj₂ (sym x⁻¹≡₁)

      ⁻¹₂ : ∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#
      ⁻¹₂ x y x⁻¹≡y with dec x 0#
      ... | inj₁ x≡0 = ⊥-elim $ ⊎.inj₁≢inj₂ x⁻¹≡y
      ... | inj₂ x≢0 =
        x * y                  ≡⟨ cong (_*_ _) $ sym $ ⊎.cancel-inj₂ x⁻¹≡y ⟩
        x * proj₁ (inv x x≢0)  ≡⟨ proj₂ (inv x x≢0) ⟩∎
        1#                     ∎

  lemma₁ : (A B C D E F : Set₁) (G : A × B × C × D × E × F → Set₁) →
           Σ (A × B × C × D × E × F) G ↔
           Σ (A × B × C × D × E) λ { (a , b , c , d , e) →
             Σ F λ f → G (a , b , c , d , e , f) }
  lemma₁ A B C D E F G =
    Σ (A × B × C × D × E × F) G                       ↝⟨ Σ-cong (×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc) (λ _ → _ □) ⟩
    (Σ (((((A × B) × C) × D) × E) × F)
       λ { (((((a , b) , c) , d) , e) , f) →
           G (a , b , c , d , e , f) })               ↝⟨ inverse Σ-assoc ⟩
    (Σ ((((A × B) × C) × D) × E)
       λ { ((((a , b) , c) , d) , e) →
           Σ F λ f → G (a , b , c , d , e , f) })     ↝⟨ Σ-cong (inverse (×-assoc ⊚ ×-assoc ⊚ ×-assoc)) (λ _ → _ □) ⟩□
    (Σ (A × B × C × D × E) λ { (a , b , c , d , e) →
      Σ F λ f → G (a , b , c , d , e , f) })          □

  lemma₂ : (A B C D E F G H I J : Set₁) (K : A → Set₁) →
           (Σ A λ x → B × C × D × E × F × G × H × I × J × K x) ↔
           (B × C × D × E × F × G × H × I × J × Σ A K)
  lemma₂ A B C D E F G H I J K =
    (Σ A λ x → B × C × D × E × F × G × H × I × J × K x)                  ↝⟨ ∃-cong (λ _ → ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚
                                                                                          ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc) ⟩
    (Σ A λ x → ((((((((B × C) × D) × E) × F) × G) × H) × I) × J) × K x)  ↝⟨ ∃-comm ⟩
    (((((((((B × C) × D) × E) × F) × G) × H) × I) × J) × Σ A K)          ↝⟨ inverse (×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚
                                                                                     ×-assoc ⊚ ×-assoc ⊚ ×-assoc ⊚ ×-assoc) ⟩□
    (B × C × D × E × F × G × H × I × J × Σ A K)                          □

-- nLab defines a discrete field as a commutative ring satisfying the
-- property that "an element is invertible xor it equals zero"
-- (http://ncatlab.org/nlab/show/field). This definition can also be
-- encoded in our framework (assuming that I interpreted the informal
-- definitions correctly).

discrete-field-à-la-nLab : Code
discrete-field-à-la-nLab =
  -- Addition.
  (id ⇾ id ⇾ id) ⊗

  -- Zero.
  id ⊗

  -- Multiplication.
  (id ⇾ id ⇾ id) ⊗

  -- One.
  id ⊗

  -- Minus.
  (id ⇾ id) ,

  λ { F (_+_ , 0# , _*_ , 1# , -_) →

      (-- Associativity.
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

       -- Additive inverse law.
       (∀ x → x + (- x) ≡ 0#) ×

       -- An element is invertible xor it equals zero.
       (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#))) ,

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (+-assoc , *-assoc , +-comm , *-comm , _ ,
                               +0 , *1 , +- , inv-xor) →
          let F-set : Is-set F
              F-set = decidable⇒set $
                        dec-lemma₃ _+_ 0# -_ _*_ 1# +-assoc *-assoc
                                   +-comm *-comm +0 *1 +- inv-xor
          in
          ×-closure  1 (Π-closure ext 1 λ _ →
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
                        F-set _ _)
          (proposition-lemma₂ ext _+_ 0# -_ _*_ 1#
                              +-assoc *-assoc +-comm *-comm
                              +0 *1 +-)))))))) }}

-- nLab's definition of discrete fields is isomorphic to Bridges and
-- Richman's (assuming extensionality, and assuming that I interpreted
-- the informal definitions correctly).

nLab's-isomorphic-to-Bridges-and-Richman's :
  Extensionality (# 1) (# 1) →

  Instance discrete-field-à-la-nLab
    ↔
  Instance discrete-field-à-la-Bridges-and-Richman

nLab's-isomorphic-to-Bridges-and-Richman's ext =
  ∃-cong λ F →
  ∃-cong λ { (_+_ , 0# , _*_ , 1# , -_) →
  ∃-cong λ +-assoc →
  ∃-cong λ *-assoc →
  ∃-cong λ +-comm →
  ∃-cong λ *-comm →
  ∃-cong λ *+ →
  ∃-cong λ +0 →
  ∃-cong λ *1 →
  ∃-cong λ +- →
  main-lemma F _+_ 0# _*_ 1# -_
             +-assoc *-assoc +-comm *-comm *+ +0 *1 +- }
  where
  main-lemma :
    (F : Set₁)
    (_+_ : F → F → F)
    (0# : F)
    (_*_ : F → F → F)
    (1# : F)
    (-_ : F → F) →
    (∀ x y z → x + (y + z) ≡ (x + y) + z) →
    (∀ x y z → x * (y * z) ≡ (x * y) * z) →
    (∀ x y → x + y ≡ y + x) →
    (∀ x y → x * y ≡ y * x) →
    (∀ x y z → x * (y + z) ≡ (x * y) + (x * z)) →
    (∀ x → x + 0# ≡ x) →
    (∀ x → x * 1# ≡ x) →
    (∀ x → x + (- x) ≡ 0#) →

   (∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#))
     ↔
   (0# ≢ 1# ×
    ((x y : F) → x ≡ y ⊎ x ≢ y) ×
    (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#))
  main-lemma F _+_ 0# _*_ 1# -_
             +-assoc *-assoc +-comm *-comm *+ +0 *1 +- =
    _≃_.bijection $
    _↔_.to (⇔↔≃ ext (proposition-lemma₂ ext _+_ 0# -_ _*_ 1#
                                        +-assoc *-assoc +-comm *-comm
                                        +0 *1 +-)
                    (×-closure 1
                       (¬-propositional (lower-ext (# 0) _ ext))
                       (proposition-lemma₁ ext 0# _*_ 1# *-assoc
                                           *-comm *1)))
           (record { to = to; from = from })
    where
    To   = 0# ≢ 1# ×
           ((x y : F) → x ≡ y ⊎ x ≢ y) ×
           (∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#)
    From = ∀ x → (∃ λ y → x * y ≡ 1#) Xor (x ≡ 0#)

    to : From → To
    to inv-xor = (0≢1 , dec , inv)
      where
      0≢1 : 0# ≢ 1#
      0≢1 0≡1 =
        [ (λ { (_        , 1≢0) → 1≢0 (sym 0≡1) })
        , (λ { (∄y[1y≡1] , _)   → ∄y[1y≡1] (1# , *1 1#) })
        ] (inv-xor 1#)

      dec : Decidable (_≡_ {A = F})
      dec = dec-lemma₃ _+_ 0# -_ _*_ 1# +-assoc *-assoc +-comm *-comm
                       +0 *1 +- inv-xor

      inv : ∀ x → x ≢ 0# → ∃ λ y → x * y ≡ 1#
      inv x x≢0 =
        [ proj₁
        , (λ { (_ , x≡0) → ⊥-elim (x≢0 x≡0) })
        ] (inv-xor x)

    from : To → From
    from (0≢1 , dec , inv) x =
      [ (λ x≡0 → inj₂ ( (λ { (y , xy≡1) → 0≢1 (0#      ≡⟨ sym $ 0* _+_ 0# _*_ 1# -_ +-assoc +-comm *-comm *+ +0 *1 +- y ⟩
                                               0# * y  ≡⟨ cong (λ x → x * y) $ sym x≡0 ⟩
                                               x * y   ≡⟨ xy≡1 ⟩∎
                                               1#      ∎) })
                      , x≡0
                      ))
      , (λ x≢0 → inj₁ (inv x x≢0 , x≢0))
      ] (dec x 0#)

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
-- Univalence-axiom.Isomorphism-is-equality.Simple.Variant the carrier
-- type lives in Set.)

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
-- * Equivalences are used instead of bijections. However,
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

-- The notion of isomorphism that we get if we use Is-isomorphism′
-- instead of Is-isomorphism is also reasonable.

Isomorphic′-poset :
  ∀ {C₁ _≤₁_ laws₁ C₂ _≤₂_ laws₂} →

  Isomorphic′ poset (C₁ , _≤₁_ , laws₁) (C₂ , _≤₂_ , laws₂)
    ≡
  Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
  ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≃ (b ≤₂ d))

Isomorphic′-poset = refl _

-- If we had defined isomorphism using Is-isomorphism′ instead of
-- Is-isomorphism, then we could have proved
-- Isomorphism-poset-isomorphic-to-order-isomorphism without assuming
-- univalence, but instead assuming extensionality.

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
