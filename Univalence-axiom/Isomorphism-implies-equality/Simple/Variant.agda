------------------------------------------------------------------------
-- A class of algebraic structures, based on non-recursive simple
-- types, satisfies the property that isomorphic instances of a
-- structure are equal (assuming univalence)
------------------------------------------------------------------------

-- In fact, isomorphism and equality are basically the same thing, and
-- the main theorem can be instantiated with several different
-- "universes", not only the one based on simple types.

-- This module is very similar to
-- Univalence-axiom.Isomorphism-implies-equality.Simple, but the
-- definitions of isomorphism used below are perhaps closer to the
-- "standard" ones. Carrier types also live in Set rather than Set₁
-- (at the cost of quite a bit of lifting).

-- This module has been developed in collaboration with Thierry
-- Coquand.

{-# OPTIONS --without-K #-}

open import Equality

module Univalence-axiom.Isomorphism-implies-equality.Simple.Variant
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq hiding (id; _∘_; inverse; _↔⟨_⟩_; finally-↔)
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

    ext₀ : Extensionality (# 0) (# 0)
    ext₀ = dependent-extensionality univ₁ (λ _ → univ)

-- Universes with some extra stuff.

record Universe : Set₃ where
  field

    -- Codes for something.

    U : Set₁

    -- Interpretation of codes.

    El : U → Set → Set₁

    -- A predicate, possibly specifying what it means for a bijection
    -- to be an isomorphism between two elements.

    Is-isomorphism : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁

    -- El a, seen as a predicate, respects weak equivalences (assuming
    -- univalence).

    resp : Assumptions → ∀ a {B C} → B ≈ C → El a B → El a C

    -- The resp function respects identities (assuming univalence).

    resp-id : (ass : Assumptions) →
              ∀ a {B} (x : El a B) → resp ass a Weak.id x ≡ x

  -- An alternative definition of Is-isomorphism, (possibly) defined
  -- using univalence.

  Is-isomorphism′ : Assumptions →
                    ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁
  Is-isomorphism′ ass B↔C a x y = resp ass a (↔⇒≈ B↔C) x ≡ y

  field

    -- Is-isomorphism and Is-isomorphism′ are isomorphic (assuming
    -- univalence).

    isomorphism-definitions-isomorphic :
      (ass : Assumptions) →
      ∀ {B C} (B↔C : B ↔ C) a {x y} →
      Is-isomorphism B↔C a x y ↔ Is-isomorphism′ ass B↔C a x y

  -- Another alternative definition of Is-isomorphism, defined using
  -- univalence.

  Is-isomorphism″ : Assumptions →
                    ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁
  Is-isomorphism″ ass B↔C a x y =
    subst (El a) (≈⇒≡ univ (↔⇒≈ B↔C)) x ≡ y
    where open Assumptions ass

  abstract

    -- Every element is isomorphic to itself, transported along the
    -- isomorphism.

    isomorphic-to-itself :
      (ass : Assumptions) → let open Assumptions ass in
      ∀ {B C} (B↔C : B ↔ C) a x →
      Is-isomorphism′ ass B↔C a x (subst (El a) (≈⇒≡ univ (↔⇒≈ B↔C)) x)
    isomorphic-to-itself ass B↔C a x =
      subst-unique (El a) (resp ass a) (resp-id ass a) univ (↔⇒≈ B↔C) x
      where open Assumptions ass

    -- Is-isomorphism and Is-isomorphism″ are isomorphic (assuming
    -- univalence).

    isomorphism-definitions-isomorphic₂ :
      (ass : Assumptions) →
      ∀ {B C} (B↔C : B ↔ C) a {x y} →
      Is-isomorphism B↔C a x y ↔ Is-isomorphism″ ass B↔C a x y
    isomorphism-definitions-isomorphic₂ ass B↔C a {x} {y} =
      Is-isomorphism      B↔C a x y  ↝⟨ isomorphism-definitions-isomorphic ass B↔C a ⟩
      Is-isomorphism′ ass B↔C a x y  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ y) $ isomorphic-to-itself ass B↔C a x ⟩□
      Is-isomorphism″ ass B↔C a x y  □

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
    (C : SET (# 0)) → El a (Type C) → Σ Set₁ λ P →
      -- The proposition should be propositional (assuming
      -- univalence).
      Assumptions → Propositional P

  -- Interpretation of the codes. The elements of "Instance a" are
  -- instances of the structure encoded by a.

  Instance : Code → Set₁
  Instance (a , P) =
    -- A carrier set.
    Σ (SET (# 0)) λ C →

    -- An element.
    Σ (El a (Type C)) λ x →

    -- The element should satisfy the proposition.
    proj₁ (P C x)

  -- The carrier type.

  Carrier : ∀ a → Instance a → Set
  Carrier _ I = Type (proj₁ I)

  -- The "element".

  element : ∀ a (I : Instance a) → El (proj₁ a) (Carrier a I)
  element _ I = proj₁ (proj₂ I)

  abstract

    -- One can prove that two instances of a structure are equal by
    -- proving that the carrier types and "elements" (suitably
    -- transported) are equal (assuming univalence).

    instances-equal↔ :
      Assumptions →
      ∀ a {I₁ I₂} →
      (I₁ ≡ I₂) ↔
      ∃ λ (C-eq : Carrier a I₁ ≡ Carrier a I₂) →
        subst (El (proj₁ a)) C-eq (element a I₁) ≡ element a I₂
    instances-equal↔ ass (a , P)
                     {(C₁ , S₁) , x₁ , p₁} {(C₂ , S₂) , x₂ , p₂} =

      (((C₁ , S₁) , x₁ , p₁) ≡ ((C₂ , S₂) , x₂ , p₂))      ↔⟨ inverse $ ≈-≡ $ ↔⇒≈ bij ⟩

      (((C₁ , x₁) , (S₁ , p₁)) ≡ ((C₂ , x₂) , (S₂ , p₂)))  ↝⟨ inverse $ ignore-propositional-component prop ⟩

      ((C₁ , x₁) ≡ (C₂ , x₂))                              ↝⟨ inverse Σ-≡,≡↔≡ ⟩

      (∃ λ (C-eq : C₁ ≡ C₂) → subst (El a) C-eq x₁ ≡ x₂)   □

      where
      bij : Instance (a , P) ↔
            Σ (Σ Set (El a)) λ { (C , x) →
            Σ (Is-set C) λ S → proj₁ (P (C , S) x) }
      bij =
        (Σ (Σ Set Is-set) λ { (C , S) →
           Σ (El a C) λ x → proj₁ (P (C , S) x) })    ↝⟨ inverse Σ-assoc ⟩

        (Σ Set λ C → Σ (Is-set C) λ S →
           Σ (El a C) λ x → proj₁ (P (C , S) x))      ↝⟨ ∃-cong (λ _ → ∃-comm) ⟩

        (Σ Set λ C → Σ (El a C) λ x →
           Σ (Is-set C) λ S → proj₁ (P (C , S) x))    ↝⟨ Σ-assoc ⟩□

        (Σ (Σ Set (El a)) λ { (C , x) →
           Σ (Is-set C) λ S → proj₁ (P (C , S) x) })  □

      prop : Propositional (Σ (Is-set C₂) λ S₂ → proj₁ (P (C₂ , S₂) x₂))
      prop =
        Σ-closure 1
          (H-level-propositional (Assumptions.ext₀ ass) 2)
          (λ S₂ → proj₂ (P (C₂ , S₂) x₂) ass)

  -- Structure isomorphisms.

  Isomorphic : ∀ a → Instance a → Instance a → Set₁
  Isomorphic (a , _) ((C₁ , _) , x₁ , _) ((C₂ , _) , x₂ , _) =
    Σ (C₁ ↔ C₂) λ C₁↔C₂ → Is-isomorphism C₁↔C₂ a x₁ x₂

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
                                                                                             ass C-eq (proj₁ a)) ⟩
      (∃ λ (C-eq : Carrier a I₁ ↔ Carrier a I₂) →
         subst (El (proj₁ a)) (≈⇒≡ univ (↔⇒≈ C-eq)) (element a I₁) ≡
         element a I₂)                                                 ↝⟨ Σ-cong (↔↔≈ ext₀ (proj₂ (proj₁ I₁))) (λ _ → _ □) ⟩

      (∃ λ (C-eq : Carrier a I₁ ≈ Carrier a I₂) →
         subst (El (proj₁ a)) (≈⇒≡ univ C-eq) (element a I₁) ≡
         element a I₂)                                                 ↝⟨ inverse $
                                                                            Σ-cong (≡≈≈ univ) (λ C-eq → ≡⇒↝ _ $ sym $
                                                                              cong (λ eq → subst (El (proj₁ a)) eq (element a I₁) ≡
                                                                                           element a I₂)
                                                                                   (_≈_.left-inverse-of (≡≈≈ univ) C-eq)) ⟩
      (∃ λ (C-eq : Carrier a I₁ ≡ Carrier a I₂) →
         subst (El (proj₁ a)) C-eq (element a I₁) ≡ element a I₂)      ↝⟨ inverse $ instances-equal↔ ass a ⟩□

      (I₁ ≡ I₂)                                                        □

      where open Assumptions ass

    -- The type of (lifted) isomorphisms between two instances of a
    -- structure is equal to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is equal to equality.

    isomorphic≡equal :
      Assumptions →
      ∀ a {I₁ I₂} → Isomorphic a I₁ I₂ ≡ (I₁ ≡ I₂)
    isomorphic≡equal ass a {I₁} {I₂} =
      ≈⇒≡ univ₁ $ ↔⇒≈ (isomorphic↔equal ass a)
      where open Assumptions ass

------------------------------------------------------------------------
-- A universe of non-recursive, simple types

-- Codes for types.

infixr 20 _⊗_
infixr 15 _⊕_
infixr 10 _⇾_

data U : Set₁ where
  id prop     : U
  k           : Set → U
  _⇾_ _⊕_ _⊗_ : U → U → U

-- Interpretation of types.

El : U → Set₁ → Set₁
El id      B = B
El prop    B = Proposition (# 0)
El (k A)   B = ↑ _ A
El (a ⇾ b) B = El a B → El b B
El (a ⊕ b) B = El a B ⊎ El b B
El (a ⊗ b) B = El a B × El b B

-- El a preserves weak equivalences (assuming extensionality).

cast : Extensionality (# 1) (# 1) →
       ∀ a {B C} → B ≈ C → El a B ≈ El a C
cast ext id      B≈C = B≈C
cast ext prop    B≈C = Weak.id
cast ext (k A)   B≈C = Weak.id
cast ext (a ⇾ b) B≈C = →-cong ext (cast ext a B≈C) (cast ext b B≈C)
cast ext (a ⊕ b) B≈C = cast ext a B≈C ⊎-cong cast ext b B≈C
cast ext (a ⊗ b) B≈C = cast ext a B≈C ×-cong cast ext b B≈C

abstract

  -- The cast function respects identities (assuming extensionality).

  cast-id : (ext : Extensionality (# 1) (# 1)) →
            ∀ a {B} → cast ext a (Weak.id {A = B}) ≡ Weak.id
  cast-id ext id      = refl _
  cast-id ext prop    = refl _
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

Is-isomorphism : ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁
Is-isomorphism B↔C id      = λ x y → _↔_.to B↔C x ≡ y
Is-isomorphism B↔C prop    = λ { (P , _) (Q , _) → ↑ _ (P ⇔ Q) }
Is-isomorphism B↔C (k A)   = λ x y → x ≡ y
Is-isomorphism B↔C (a ⇾ b) = Is-isomorphism B↔C a →-rel
                             Is-isomorphism B↔C b
Is-isomorphism B↔C (a ⊕ b) = Is-isomorphism B↔C a ⊎-rel
                             Is-isomorphism B↔C b
Is-isomorphism B↔C (a ⊗ b) = Is-isomorphism B↔C a ×-rel
                             Is-isomorphism B↔C b

-- Another definition of "being an isomorphism" (defined using
-- extensionality).

Is-isomorphism′ : Extensionality (# 1) (# 1) →
                  ∀ {B C} → B ↔ C → ∀ a → El a B → El a C → Set₁
Is-isomorphism′ ext B↔C a x y = _≈_.to (cast ext a (↔⇒≈ B↔C)) x ≡ y

abstract

  -- The two definitions of "being an isomorphism" are "isomorphic"
  -- (in bijective correspondence), assuming univalence.

  isomorphism-definitions-isomorphic :
    (ass : Assumptions) → let open Assumptions ass in
    ∀ {B C} (B↔C : B ↔ C) a {x y} →
    Is-isomorphism B↔C a x y ↔ Is-isomorphism′ ext B↔C a x y

  isomorphism-definitions-isomorphic ass B↔C id {x} {y} =

    (_↔_.to B↔C x ≡ y)  □

  isomorphism-definitions-isomorphic ass B↔C prop {P} {Q} =

    ↑ _ (proj₁ P ⇔ proj₁ Q)  ↝⟨ ↑↔ ⟩

    (proj₁ P ⇔ proj₁ Q)      ↝⟨ ⇔↔≈ ext₀ (proj₂ P) (proj₂ Q) ⟩

    (proj₁ P ≈ proj₁ Q)      ↔⟨ inverse $ ≡≈≈ univ ⟩

    (proj₁ P ≡ proj₁ Q)      ↝⟨ ignore-propositional-component (H-level-propositional ext₀ 1) ⟩□

    (P ≡ Q)                □

    where open Assumptions ass

  isomorphism-definitions-isomorphic ass B↔C (k A) {x} {y} =

    (x ≡ y) □

  isomorphism-definitions-isomorphic ass B↔C (a ⇾ b) {f} {g} =
    let B≈C = ↔⇒≈ B↔C in

    (∀ x y → Is-isomorphism B↔C a x y →
             Is-isomorphism B↔C b (f x) (g y))                     ↔⟨ ∀-preserves ext (λ _ → ∀-preserves ext λ _ → ↔⇒≈ $
                                                                        →-cong ext (isomorphism-definitions-isomorphic ass B↔C a)
                                                                                   (isomorphism-definitions-isomorphic ass B↔C b)) ⟩
    (∀ x y → to (cast ext a B≈C) x ≡ y →
             to (cast ext b B≈C) (f x) ≡ g y)                      ↔⟨ inverse $ ∀-preserves ext (λ x →
                                                                        ↔⇒≈ $ ∀-intro ext (λ y _ → to (cast ext b B≈C) (f x) ≡ g y)) ⟩
    (∀ x → to (cast ext b B≈C) (f x) ≡ g (to (cast ext a B≈C) x))  ↔⟨ extensionality-isomorphism ext ⟩

    (to (cast ext b B≈C) ∘ f ≡ g ∘ to (cast ext a B≈C))            ↝⟨ inverse $ ∘from≡↔≡∘to ext (cast ext a B≈C) ⟩□

    (to (cast ext b B≈C) ∘ f ∘ from (cast ext a B≈C) ≡ g)          □

    where
    open _≈_
    open Assumptions ass

  isomorphism-definitions-isomorphic ass B↔C (a ⊕ b) {inj₁ x} {inj₁ y} =
    let B≈C = ↔⇒≈ B↔C in

    Is-isomorphism B↔C a x y                 ↝⟨ isomorphism-definitions-isomorphic ass B↔C a ⟩

    (to (cast ext a B≈C) x ≡ y)              ↝⟨ ≡↔inj₁≡inj₁ ⟩□

    (inj₁ (to (cast ext a B≈C) x) ≡ inj₁ y)  □

    where
    open _≈_
    open Assumptions ass

  isomorphism-definitions-isomorphic ass B↔C (a ⊕ b) {inj₂ x} {inj₂ y} =
    let B≈C = ↔⇒≈ B↔C in

    Is-isomorphism B↔C b x y                 ↝⟨ isomorphism-definitions-isomorphic ass B↔C b ⟩

    (to (cast ext b B≈C) x ≡ y)              ↝⟨ ≡↔inj₂≡inj₂ ⟩□

    (inj₂ (to (cast ext b B≈C) x) ≡ inj₂ y)  □

    where
    open _≈_
    open Assumptions ass

  isomorphism-definitions-isomorphic ass B↔C (a ⊕ b) {inj₁ x} {inj₂ y} =

    ⊥                  ↝⟨ ⊥↔uninhabited ⊎.inj₁≢inj₂ ⟩□

    (inj₁ _ ≡ inj₂ _)  □

  isomorphism-definitions-isomorphic ass B↔C (a ⊕ b) {inj₂ x} {inj₁ y} =

    ⊥                  ↝⟨ ⊥↔uninhabited (⊎.inj₁≢inj₂ ∘ sym) ⟩□

    (inj₂ _ ≡ inj₁ _)  □

  isomorphism-definitions-isomorphic ass B↔C (a ⊗ b) {x , u} {y , v} =
    let B≈C = ↔⇒≈ B↔C in

    Is-isomorphism  B↔C a x y × Is-isomorphism  B↔C b u v        ↝⟨ isomorphism-definitions-isomorphic ass B↔C a ×-cong
                                                                    isomorphism-definitions-isomorphic ass B↔C b ⟩
    (to (cast ext a B≈C) x ≡ y × to (cast ext b B≈C) u ≡ v)      ↝⟨ ≡×≡↔≡ ⟩□

    ((to (cast ext a B≈C) x , to (cast ext b B≈C) u) ≡ (y , v))  □

    where
    open _≈_
    open Assumptions ass

-- The universe above is a "universe with some extra stuff".

simple : Universe
simple = record
  { U              = U
  ; El             = λ a → El a ∘ ↑ _
  ; Is-isomorphism = λ B↔C a → Is-isomorphism (↑-cong B↔C) a
  ; resp           = λ ass a → _≈_.to ∘ cast (ext ass) a ∘ ↑-cong
  ; resp-id        = λ ass a x → cong (λ f → _≈_.to f x) (
                       cast (ext ass) a (↑-cong Weak.id)  ≡⟨ cong (cast (ext ass) a) $ lift-equality (ext ass) (refl _) ⟩
                       cast (ext ass) a Weak.id           ≡⟨ cast-id (ext ass) a ⟩∎
                       Weak.id                            ∎)
  ; isomorphism-definitions-isomorphic = λ ass B↔C a {x y} →
      Is-isomorphism (↑-cong B↔C) a x y                     ↝⟨ isomorphism-definitions-isomorphic ass (↑-cong B↔C) a ⟩
      (_≈_.to (cast (ext ass) a (↔⇒≈ (↑-cong B↔C))) x ≡ y)  ↝⟨ ≡⇒↝ _ $ cong (λ eq → _≈_.to (cast (ext ass) a eq) x ≡ y) $
                                                                 lift-equality (ext ass) (refl _) ⟩□
      (_≈_.to (cast (ext ass) a (↑-cong (↔⇒≈ B↔C))) x ≡ y)  □
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

      (-- Left and right identity laws.
       (∀ x → e ∙ x ≡ x) ×
       (∀ x → x ∙ e ≡ x) ×

       -- Associativity.
       (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z)) ,

       -- The laws are propositional (assuming extensionality).
      λ ass → let open Assumptions ass in
        ×-closure 1  (Π-closure ext 1 λ _ →
                      ↑-closure 2 M-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      ↑-closure 2 M-set _ _)
                     (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 M-set _ _)) }

-- The interpretation of the code is reasonable.

Instance-monoid :

  Instance monoid
    ≡
  Σ (SET (# 0)) λ { (M , _) →
  Σ ((↑ _ M → ↑ _ M → ↑ _ M) × ↑ _ M) λ { (_∙_ , e) →
  (∀ x → e ∙ x ≡ x) ×
  (∀ x → x ∙ e ≡ x) ×
  (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z) }}

Instance-monoid = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-monoid :
  ∀ {M₁ S₁ _∙₁_ e₁ laws₁ M₂ S₂ _∙₂_ e₂ laws₂} →

  Isomorphic monoid ((M₁ , S₁) , (_∙₁_ , e₁) , laws₁)
                    ((M₂ , S₂) , (_∙₂_ , e₂) , laws₂)
    ≡
  Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ (↑-cong M₁↔M₂) in
  (∀ x y → to x ≡ y → ∀ u v → to u ≡ v → to (x ∙₁ u) ≡ y ∙₂ v) ×
  to e₁ ≡ e₂

Isomorphic-monoid = refl _

-- Note that this definition of isomorphism is isomorphic to a more
-- standard one (assuming extensionality).

Isomorphism-monoid-isomorphic-to-standard :
  Extensionality (# 1) (# 1) →
  ∀ {M₁ S₁ _∙₁_ e₁ laws₁ M₂ S₂ _∙₂_ e₂ laws₂} →

  Isomorphic monoid ((M₁ , S₁) , (_∙₁_ , e₁) , laws₁)
                    ((M₂ , S₂) , (_∙₂_ , e₂) , laws₂)
    ↔
  Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ (↑-cong M₁↔M₂) in
  (∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y) ×
  to e₁ ≡ e₂

Isomorphism-monoid-isomorphic-to-standard ext
  {M₁} {S₁} {_∙₁_} {e₁} {M₂ = M₂} {_∙₂_ = _∙₂_} {e₂} =

  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ (↑-cong M₁↔M₂) in
   (∀ x y → to x ≡ y → ∀ u v → to u ≡ v → to (x ∙₁ u) ≡ y ∙₂ v) ×
   to e₁ ≡ e₂)                                                     ↔⟨ inverse $ ∃-cong (λ _ →
                                                                        (∀-preserves ext λ _ → ↔⇒≈ $ ∀-intro ext λ _ _ → _) ×-cong (_ □)) ⟩
  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ (↑-cong M₁↔M₂) in
   (∀ x u v → to u ≡ v → to (x ∙₁ u) ≡ to x ∙₂ v) ×
   to e₁ ≡ e₂)                                                     ↔⟨ inverse $ ∃-cong (λ _ →
                                                                        (∀-preserves ext λ _ → ∀-preserves ext λ _ → ↔⇒≈ $ ∀-intro ext λ _ _ → _)
                                                                          ×-cong
                                                                        (_ □)) ⟩□
  (Σ (M₁ ↔ M₂) λ M₁↔M₂ → let open _↔_ (↑-cong M₁↔M₂) in
   (∀ x u → to (x ∙₁ u) ≡ to x ∙₂ to u) ×
   to e₁ ≡ e₂)                                                     □

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
  (id ⇾ k ⊤ ⊕ id) ,

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

      λ ass → let open Assumptions ass in
        ×-closure 1  (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
        (×-closure 1 (Π-closure (lower-ext (# 0) (# 1) ext) 1 λ _ →
                      ⊥-propositional)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)
                     (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 F-set _ _)))))))))) }

-- The interpretation of the code is reasonable.

Instance-discrete-field :

  Instance discrete-field
    ≡
  Σ (SET (# 0)) λ { (F , _) →
  Σ ((↑ _ F → ↑ _ F → ↑ _ F) × ↑ _ F × (↑ _ F → ↑ _ F → ↑ _ F) ×
     ↑ _ F × (↑ _ F → ↑ _ F) × (↑ _ F → ↑ (# 1) ⊤ ⊎ ↑ _ F))
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
  (∀ x y → x ⁻¹ ≡ inj₂ y → x * y ≡ 1#) }}

Instance-discrete-field = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-discrete-field :
  ∀ {F₁ S₁ _+₁_ 0₁ _*₁_ 1₁ -₁_ _⁻¹₁ laws₁
     F₂ S₂ _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ laws₂} →

  Isomorphic discrete-field
    ((F₁ , S₁) , (_+₁_ , 0₁ , _*₁_ , 1₁ , -₁_ , _⁻¹₁) , laws₁)
    ((F₂ , S₂) , (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂) , laws₂)
    ≡
  Σ (F₁ ↔ F₂) λ F₁↔F₂ → let open _↔_ (↑-cong F₁↔F₂) in
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
vector-space ((F , _) , (_+F_ , _ , _*F_ , 1F , _ , _) , _) =
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

      λ ass → let open Assumptions ass in
        ×-closure 1  (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ↑-closure 2 V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      ↑-closure 2 V-set _ _)
        (×-closure 1 (Π-closure ext 1 λ _ →
                      ↑-closure 2 V-set _ _)
                     (Π-closure ext 1 λ _ →
                      ↑-closure 2 V-set _ _))))))) }

-- The interpretation of the code is reasonable.

Instance-vector-space :
  ∀ {F S _+F_ 0F _*F_ 1F -F_ _⁻¹F laws} →

  Instance (vector-space
              ((F , S) , (_+F_ , 0F , _*F_ , 1F , -F_ , _⁻¹F) , laws))
    ≡
  Σ (SET (# 0)) λ { (V , _) →
  Σ ((↑ _ V → ↑ _ V → ↑ _ V) × (↑ _ F → ↑ _ V → ↑ _ V) × ↑ _ V ×
     (↑ _ V → ↑ _ V))
    λ { (_+_ , _*_ , 0V , -_) →
  (∀ u v w → u + (v + w) ≡ (u + v) + w) ×
  (∀ x y v → x * (y * v) ≡ (x *F y) * v) ×
  (∀ u v → u + v ≡ v + u) ×
  (∀ x u v → x * (u + v) ≡ (x * u) + (x * v)) ×
  (∀ x y v → (x +F y) * v ≡ (x * v) + (y * v)) ×
  (∀ v → v + 0V ≡ v) ×
  (∀ v → 1F * v ≡ v) ×
  (∀ v → v + (- v) ≡ 0V) }}

Instance-vector-space = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-vector-space :
  ∀ {F V₁ S₁ _+₁_ _*₁_ 0₁ -₁_ laws₁
       V₂ S₂ _+₂_ _*₂_ 0₂ -₂_ laws₂} →

  Isomorphic (vector-space F)
             ((V₁ , S₁) , (_+₁_ , _*₁_ , 0₁ , -₁_) , laws₁)
             ((V₂ , S₂) , (_+₂_ , _*₂_ , 0₂ , -₂_) , laws₂)
    ≡
  Σ (V₁ ↔ V₂) λ V₁↔V₂ → let open _↔_ (↑-cong V₁↔V₂) in
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
  (id ⇾ id ⇾ prop) ,

  λ { (P , P-set) Le →

    let _≤_ : ↑ _ P → ↑ _ P → Set
        x ≤ y = proj₁ (Le x y)
    in

     -- Reflexivity.
    ((∀ x → x ≤ x) ×

     -- Transitivity.
     (∀ x y z → x ≤ y → y ≤ z → x ≤ z) ×

     -- Antisymmetry.
     (∀ x y → x ≤ y → y ≤ x → x ≡ y)) ,

    λ ass → let open Assumptions ass in
      ×-closure 1  (Π-closure (lower-ext (# 0) _ ext) 1 λ _ →
                    proj₂ (Le _ _))
      (×-closure 1 (Π-closure ext                     1 λ _ →
                    Π-closure ext                     1 λ _ →
                    Π-closure (lower-ext (# 0) _ ext) 1 λ _ →
                    Π-closure ext₀                    1 λ _ →
                    Π-closure ext₀                    1 λ _ →
                    proj₂ (Le _ _))
                   (Π-closure ext                     1 λ _ →
                    Π-closure ext                     1 λ _ →
                    Π-closure (lower-ext _ (# 0) ext) 1 λ _ →
                    Π-closure (lower-ext _ (# 0) ext) 1 λ _ →
                    ↑-closure 2 P-set _ _)) }

-- The interpretation of the code is reasonable.

Instance-poset :

  Instance poset
    ≡
  Σ (SET (# 0)) λ { (P , _) →
  Σ (↑ _ P → ↑ _ P → Proposition (# 0)) λ Le →
  let _≤_ : ↑ _ P → ↑ _ P → Set
      x ≤ y = proj₁ (Le x y)
  in
  (∀ x → x ≤ x) ×
  (∀ x y z → x ≤ y → y ≤ z → x ≤ z) ×
  (∀ x y → x ≤ y → y ≤ x → x ≡ y) }

Instance-poset = refl _

-- The notion of isomorphism that we get is also reasonable. It is the
-- usual notion of "order isomorphism".

Isomorphic-poset :
  ∀ {P₁ S₁ Le₁ laws₁ P₂ S₂ Le₂ laws₂} →
  let _≤₁_ : ↑ _ P₁ → ↑ _ P₁ → Set
      _≤₁_ x y = proj₁ (Le₁ x y)

      _≤₂_ : ↑ _ P₂ → ↑ _ P₂ → Set
      _≤₂_ x y = proj₁ (Le₂ x y)
  in

  Isomorphic poset ((P₁ , S₁) , Le₁ , laws₁) ((P₂ , S₂) , Le₂ , laws₂)
    ≡
  Σ (P₁ ↔ P₂) λ P₁↔P₂ → let open _↔_ (↑-cong P₁↔P₂) in
  ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ⇔ (b ≤₂ d))

Isomorphic-poset = refl _

------------------------------------------------------------------------
-- An example: sets equipped with fixpoint operators

set-with-fixpoint-operator : Code
set-with-fixpoint-operator =
  (id ⇾ id) ⇾ id ,

  λ { (_ , F-set) fix →

     -- The fixpoint operator property.
    (∀ f → f (fix f) ≡ fix f) ,

    λ ass → let open Assumptions ass in
      Π-closure ext 1 λ _ →
      ↑-closure 2 F-set _ _ }

-- The usual unfolding lemmas.

Instance-set-with-fixpoint-operator :

  Instance set-with-fixpoint-operator
    ≡
  Σ (SET (# 0)) λ { (F , _) →
  Σ ((↑ _ F → ↑ _ F) → ↑ _ F) λ fix →
  ∀ f → f (fix f) ≡ fix f }

Instance-set-with-fixpoint-operator = refl _

Isomorphic-set-with-fixpoint-operator :
  ∀ {F₁ S₁ fix₁ law₁ F₂ S₂ fix₂ law₂} →

  Isomorphic set-with-fixpoint-operator
             ((F₁ , S₁) , fix₁ , law₁) ((F₂ , S₂) , fix₂ , law₂)
    ≡
  Σ (F₁ ↔ F₂) λ F₁↔F₂ → let open _↔_ (↑-cong F₁↔F₂) in
  ∀ f g → (∀ x y → to x ≡ y → to (f x) ≡ g y) → to (fix₁ f) ≡ fix₂ g

Isomorphic-set-with-fixpoint-operator = refl _
