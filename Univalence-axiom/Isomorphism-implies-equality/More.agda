------------------------------------------------------------------------
-- A large(r) class of algebraic structures satisfies the property
-- that isomorphic instances of a structure are equal (assuming
-- univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Note that this module uses ordinary propositional equality, with a
-- computing J rule.

-- This module has been developed in collaboration with Thierry
-- Coquand.

module Univalence-axiom.Isomorphism-implies-equality.More where

open import Equality.Propositional
  hiding (refl) renaming (equality-with-J to eq)
open import Equality
open Derived-definitions-and-properties eq using (refl)

open import Bijection eq hiding (id; _∘_; inverse; _↔⟨_⟩_; finally-↔)
open import Equivalence using (_⇔_; module _⇔_)
open import Function-universe eq hiding (id; _∘_)
open import H-level eq hiding (Proposition; Type)
open import H-level.Closure eq
open import Prelude
open import Univalence-axiom eq
open import Weak-equivalence eq as Weak hiding (id; _∘_; inverse)

------------------------------------------------------------------------
-- A record packing up certain assumptions

-- Use of these or similar assumptions is not documented in comments
-- below. (The comments do not include remarks like "assuming
-- univalence".)

record Assumptions : Set₂ where
  field
    ext₁  : Extensionality (# 1) (# 1)
    univ  : Univalence (# 0)
    univ₁ : Univalence (# 1)

  ext : Extensionality (# 0) (# 0)
  ext = lower-extensionality (# 1) (# 1) ext₁

------------------------------------------------------------------------
-- A class of algebraic structures

-- An algebraic structure universe.

mutual

  -- Codes for structures.

  infixl 5 _▻_

  data Code : Set₂ where
    ε   : Code
    _▻_ : (c : Code) → Extension c → Code

  -- Structures can contain arbitrary "extensions".

  record Extension (c : Code) : Set₂ where
    field

      -- An instance-indexed type.

      Ext : ⟦ c ⟧ → Set₁

      -- A predicate specifying when two elements are isomorphic with
      -- respect to an isomorphism.

      Iso : {I J : ⟦ c ⟧} → Isomorphic c I J →
            Ext I → Ext J → Set₁

    -- An alternative definition of Iso.

    Iso′ : Assumptions →
           ∀ {I J} → Isomorphic c I J →
           Ext I → Ext J → Set₁
    Iso′ ass I≅J x y =
      subst Ext (_≈_.to (isomorphism≈equality ass c) I≅J) x ≡ y

    field

      -- Iso and Iso′ are weakly equivalent.

      Iso≈Iso′ :
        (ass : Assumptions) →
        ∀ {I J} (I≅J : Isomorphic c I J) {x y} →
        Iso I≅J x y ≈ Iso′ ass I≅J x y

  -- Interpretation of the codes. The elements of ⟦ c ⟧ are instances
  -- of the structure encoded by c.

  ⟦_⟧ : Code → Set₁
  ⟦ ε     ⟧ = ↑ _ ⊤
  ⟦ c ▻ e ⟧ = Σ ⟦ c ⟧ (Extension.Ext e)

  -- Isomorphisms.

  Isomorphic : (c : Code) → ⟦ c ⟧ → ⟦ c ⟧ → Set₁
  Isomorphic ε       _       _       = ↑ _ ⊤
  Isomorphic (c ▻ e) (I , x) (J , y) =
    Σ (Isomorphic c I J) λ I≅J → Extension.Iso e I≅J x y

  -- Isomorphism is weakly equivalent to equality.

  isomorphism≈equality : Assumptions →
                         (c : Code) {I J : ⟦ c ⟧} →
                         Isomorphic c I J ≈ (I ≡ J)

  isomorphism≈equality _ ε =

      ↑ _ ⊤              ↔⟨ contractible-isomorphic (↑-closure 0 ⊤-contractible)
                                                    (↑-closure 1 (mono₁ 0 ⊤-contractible) _ _) ⟩□
      lift tt ≡ lift tt  □

  isomorphism≈equality ass (c ▻ e) {I , x} {J , y} =

    (Σ (Isomorphic c I J) λ I≅J → Iso e I≅J x y)  ↝⟨ Σ-cong (isomorphism≈equality ass c)
                                                            (λ I≅J → Iso≈Iso′ e ass I≅J) ⟩
    (Σ (I ≡ J) λ I≡J → subst (Ext e) I≡J x ≡ y)   ↔⟨ Σ-≡,≡↔≡ ⟩□

    ((I , x) ≡ (J , y))                           □

    where open Extension

-- Isomorphism is equal to equality.

isomorphism≡equality :
  Univalence (# 0) →
  Univalence (# 1) →
  Univalence (# 2) →
  (c : Code) {I J : ⟦ c ⟧} →
  Isomorphic c I J ≡ (I ≡ J)
isomorphism≡equality univ univ₁ univ₂ c =
  ≈⇒≡ univ₁ $ isomorphism≈equality ass c
  where
  ass = record
    { ext₁  = dependent-extensionality univ₂ (λ _ → univ₁)
    ; univ  = univ
    ; univ₁ = univ₁
    }

------------------------------------------------------------------------
-- Reflexivity

-- The isomorphism relation is reflexive.

reflexivity : Assumptions → ∀ c I → Isomorphic c I I
reflexivity ass c I =
  _≈_.from (isomorphism≈equality ass c) (refl I)

-- Reflexivity relates an element to itself.

reflexivityE :
  (ass : Assumptions) →
  ∀ c e I x →
  Extension.Iso e (reflexivity ass c I) x x
reflexivityE ass c e I x =
  _≈_.from (Iso≈Iso′ ass (reflexivity ass c I)) (
    subst Ext (to (from (refl I))) x  ≡⟨ subst (λ eq → subst Ext eq x ≡ x)
                                               (sym $ right-inverse-of (refl I))
                                               (refl x) ⟩∎
    x                                 ∎)
  where
  open Extension e
  open _≈_ (isomorphism≈equality ass c)

-- Unfolding lemma (definitional) for reflexivity.

reflexivity-▻ :
  ∀ {ass c e I x} →
  reflexivity ass (c ▻ e) (I , x) ≡
  (reflexivity ass c I , reflexivityE ass c e I x)
reflexivity-▻ = refl _

------------------------------------------------------------------------
-- Recipe for defining extensions

-- Another kind of extension.

record Extension-with-resp (c : Code) : Set₂ where
  field

    -- An instance-indexed type.

    Ext : ⟦ c ⟧ → Set₁

    -- A predicate specifying when two elements are isomorphic with
    -- respect to an isomorphism.

    Iso : {I J : ⟦ c ⟧} → Isomorphic c I J →
          Ext I → Ext J → Set₁

    -- Ext, seen as a predicate, respects isomorphisms.

    resp : Assumptions →
           ∀ {I J} → Isomorphic c I J →
           Ext I → Ext J

    -- The resp function respects reflexivity.

    resp-refl : (ass : Assumptions) →
                ∀ {I} (x : Ext I) →
                resp ass (reflexivity ass c I) x ≡ x

  -- An alternative definition of Iso.

  Iso″ : Assumptions →
         {I J : ⟦ c ⟧} → Isomorphic c I J →
         Ext I → Ext J → Set₁
  Iso″ ass I≅J x y = resp ass I≅J x ≡ y

  field

    -- Iso and Iso″ are weakly equivalent.

    Iso≈Iso″ :
      (ass : Assumptions) →
      ∀ {I J} (I≅J : Isomorphic c I J) {x y} →
      Iso I≅J x y ≈ Iso″ ass I≅J x y

  -- Another alternative definition of Iso.

  Iso′ : Assumptions →
         ∀ {I J} → Isomorphic c I J →
         Ext I → Ext J → Set₁
  Iso′ ass I≅J x y =
    subst Ext (_≈_.to (isomorphism≈equality ass c) I≅J) x ≡ y

  -- Every element is isomorphic to itself, transported along the
  -- "outer" isomorphism.

  isomorphic-to-itself :
    (ass : Assumptions) →
    ∀ {I J} (I≅J : Isomorphic c I J) {x} →
    Iso″ ass I≅J x
         (subst Ext (_≈_.to (isomorphism≈equality ass c) I≅J) x)
  isomorphic-to-itself ass I≅J {x} = subst-unique′
    Ext
    (Isomorphic c)
    (_≈_.surjection $ inverse $ isomorphism≈equality ass c)
    (resp ass)
    (λ _ → resp-refl ass)
    I≅J
    x

  -- Iso and Iso′ are weakly equivalent.

  Iso≈Iso′ :
    (ass : Assumptions) →
    ∀ {I J} (I≅J : Isomorphic c I J) {x y} →
    Iso I≅J x y ≈ Iso′ ass I≅J x y
  Iso≈Iso′ ass I≅J {x} {y} =
    Iso      I≅J x y  ↝⟨ Iso≈Iso″ ass I≅J ⟩
    Iso″ ass I≅J x y  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ y) $ isomorphic-to-itself ass I≅J ⟩□
    Iso′ ass I≅J x y  □

  -- An extension constructed from the fields above.

  extension : Extension c
  extension = record { Ext = Ext; Iso = Iso; Iso≈Iso′ = Iso≈Iso′ }

------------------------------------------------------------------------
-- Type extractors

record Extractor (c : Code) : Set₂ where
  field

    -- Extracts a type from an instance.

    Type : ⟦ c ⟧ → Set

    -- Extracts a weak equivalence relating types extracted from
    -- isomorphic instances.

    Type-cong : ∀ {I J} → Isomorphic c I J → Type I ≈ Type J

    -- Reflexivity is mapped to the identity weak equivalence.

    Type-cong-reflexivity :
      (ass : Assumptions) →
      ∀ I → Type-cong (reflexivity ass c I) ≡ Weak.id

-- Constant type extractor.

[_] : ∀ {c} → Set → Extractor c
[_] {c} A = record
  { Type                  = λ _ → A
  ; Type-cong             = λ _ → Weak.id
  ; Type-cong-reflexivity = λ _ _ → refl _
  }

-- Successor type extractor.

infix 6 1+_

1+_ : ∀ {c e} → Extractor c → Extractor (c ▻ e)
1+_ {c} {e} extractor = record
  { Type                  = Type ∘ proj₁
  ; Type-cong             = Type-cong ∘ proj₁
  ; Type-cong-reflexivity = λ { ass (I , x) →
      Type-cong (reflexivity ass c I)  ≡⟨ Type-cong-reflexivity ass I ⟩∎
      Weak.id                          ∎ }
  }
  where
  open Extractor extractor

------------------------------------------------------------------------
-- An extension: types

-- Extends a structure with a type.

A-type : ∀ {c} → Extension c
A-type {c} = record
  { Ext      = λ _ → Set
  ; Iso      = λ _ A B → ↑ _ (A ≈ B)
  ; Iso≈Iso′ = λ ass I≅J {A B} →
                 let I≡J = _≈_.to (isomorphism≈equality ass c) I≅J in

                 ↑ _ (A ≈ B)                    ↔⟨ ↑↔ ⟩
                 (A ≈ B)                        ↝⟨ inverse $ ≡≈≈ (Assumptions.univ ass) ⟩
                 (A ≡ B)                        ↝⟨ ≡⇒≈ $ cong (λ C → C ≡ B) $ sym (subst-const I≡J) ⟩
                 (subst (λ _ → Set) I≡J A ≡ B)  □
  }

private

  -- Alternative, perhaps slightly easier definition.

  A-type′ : ∀ {c} → Extension c
  A-type′ {c} = Extension-with-resp.extension record
    { Ext       = λ _ → Set
    ; Iso       = λ _ A B → ↑ _ (A ≈ B)
    ; resp      = λ _ _ A → A
    ; resp-refl = λ _ → refl
    ; Iso≈Iso″  = λ ass _ {A} {B} →
                    ↑ _ (A ≈ B)  ↔⟨ ↑↔ ⟩
                    (A ≈ B)      ↝⟨ inverse $ ≡≈≈ (Assumptions.univ ass) ⟩□
                    (A ≡ B)      □
    }

-- A corresponding type extractor.

[0] : ∀ {c} → Extractor (c ▻ A-type)
[0] {c} = record
  { Type                  = λ { (_ , A) → A }
  ; Type-cong             = λ { (_ , lift A≈B) → A≈B }
  ; Type-cong-reflexivity = λ { ass (I , A) → elim₁
      (λ {p} q →
         ≡⇒≈ (_≈_.from (≡⇒≈ (cong (λ C → C ≡ A) (sym (subst-const p))))
                       (subst (λ eq → subst Ext eq A ≡ A)
                              (sym q) (refl A))) ≡
         Weak.id)
      (refl _)
      (_≈_.right-inverse-of (isomorphism≈equality ass c) (refl I)) }
  }
  where
  open Extension A-type

------------------------------------------------------------------------
-- An extension: propositions

-- Extends a structure with a proposition.

Proposition : ∀ {c} →

              -- The proposition.
              (P : ⟦ c ⟧ → Set) →

              -- The proposition must be propositional (given some
              -- assumptions).
              (Assumptions → ∀ I → Propositional (P I)) →

              Extension c
Proposition {c} P prop = record
  { Ext      = ↑ _ ∘ P
  ; Iso      = λ _ _ _ → ↑ _ ⊤
  ; Iso≈Iso′ = λ ass I≅J {_ p} →
                 ↑ _ ⊤    ↔⟨ contractible-isomorphic
                               (↑-closure 0 ⊤-contractible)
                               (mono₁ 0 (propositional⇒inhabited⇒contractible (↑-closure 1 (prop ass _)) p) _ _) ⟩□
                 (_ ≡ _)  □
  }

-- The proposition stating that a given type is a set.

Is-a-set : ∀ {c} → Extractor c → Extension c
Is-a-set extractor =
  Proposition (Is-set ∘ Type)
              (λ ass _ → H-level-propositional (Assumptions.ext ass) 2)
  where open Extractor extractor

------------------------------------------------------------------------
-- An extension: n-ary functions

-- N-ary functions.

_^_⟶_ : Set → ℕ → Set → Set
A ^ zero  ⟶ B = B
A ^ suc n ⟶ B = A → A ^ n ⟶ B

-- N-ary function morphisms.

Is-_-ary-morphism :
  (n : ℕ) {A B : Set} → (A ^ n ⟶ A) → (B ^ n ⟶ B) → (A → B) → Set
Is- zero  -ary-morphism x y m = m x ≡ y
Is- suc n -ary-morphism f g m =
  ∀ x → Is- n -ary-morphism (f x) (g (m x)) m

-- An n-ary function extension.

N-ary : ∀ {c} →

        -- Extracts the underlying type.
        Extractor c →

        -- The function's arity.
        ℕ →

        Extension c
N-ary {c} extractor n = Extension-with-resp.extension record
  { Ext       = λ I → ↑ _ (Type I ^ n ⟶ Type I)
  ; Iso       = λ { I≅J (lift f) (lift g) →
                    ↑ _ (Is- n -ary-morphism f g
                           (_≈_.to (Type-cong I≅J))) }
  ; resp      = λ _ I≅J → lift ∘ cast n (Type-cong I≅J) ∘ lower
  ; resp-refl = λ { ass (lift f) → cong lift $
                    cast n (Type-cong (reflexivity ass c _)) f  ≡⟨ cong (λ eq → cast n eq f) $ Type-cong-reflexivity ass _ ⟩
                    cast n Weak.id f                            ≡⟨ cast-id (Assumptions.ext ass) n f ⟩∎
                    f                                           ∎ }
  ; Iso≈Iso″  = λ ass I≅J {f g} →
                  let lf = lower f; lg = lower g; A≈B = Type-cong I≅J in

                  ↑ _ (Is- n -ary-morphism lf lg (_≈_.to A≈B))  ↔⟨ ↑↔ ⟩
                  Is- n -ary-morphism lf lg (_≈_.to A≈B)        ↝⟨ Iso≈Iso″ (Assumptions.ext ass) A≈B n lf lg ⟩
                  (cast n A≈B lf ≡ lg)                          ↝⟨ Weak.≈-≡ (↔⇒≈ ↑↔) ⟩□
                  (lift (cast n A≈B lf) ≡ g)                    □
  }
  where
  open Extractor extractor

  -- Changes the type of an n-ary function.

  cast : ∀ n → {A B : Set} → A ≈ B → A ^ n ⟶ A → B ^ n ⟶ B
  cast zero    A≈B = _≈_.to A≈B
  cast (suc n) A≈B = λ f x → cast n A≈B (f (_≈_.from A≈B x))

  -- Cast simplification lemma.

  cast-id : Extensionality (# 0) (# 0) →
            {A : Set} →
            ∀ n (f : A ^ n ⟶ A) → cast n Weak.id f ≡ f
  cast-id ext zero    x = refl x
  cast-id ext (suc n) f = ext λ x → cast-id ext n (f x)

  -- Two definitions of isomorphism are weakly equivalent.

  Iso≈Iso″ :
    {A B : Set} →
    Extensionality (# 0) (# 0) →
    (A≈B : A ≈ B)
    (n : ℕ) (f : A ^ n ⟶ A) (g : B ^ n ⟶ B) →
    Is- n -ary-morphism f g (_≈_.to A≈B) ≈ (cast n A≈B f ≡ g)

  Iso≈Iso″ ext A≈B zero x y =

    (_≈_.to A≈B x ≡ y)  □

  Iso≈Iso″ ext A≈B (suc n) f g =
    (∀ x → Is- n -ary-morphism (f x) (g (_≈_.to A≈B x)) (_≈_.to A≈B))  ↝⟨ Weak.∀-preserves ext (λ x → Iso≈Iso″ ext A≈B n (f x) (g (_≈_.to A≈B x))) ⟩
    (∀ x → cast n A≈B (f x) ≡ g (_≈_.to A≈B x))                        ↝⟨ Weak.extensionality-isomorphism ext ⟩
    (cast n A≈B ∘ f ≡ g ∘ _≈_.to A≈B)                                  ↝⟨ inverse $ ∘from≡↔≡∘to ext A≈B ⟩□
    (cast n A≈B ∘ f ∘ _≈_.from A≈B ≡ g)                                □

------------------------------------------------------------------------
-- An extension: simply typed functions

-- This section contains a generalisation of the development for n-ary
-- functions above.

-- Simple types.

data Simple-type (c : Code) : Set₂ where
  base : Extractor c → Simple-type c
  _⟶_  : Simple-type c → Simple-type c → Simple-type c

-- Interpretation of a simple type.

⟦_⟧⟶ : ∀ {c} → Simple-type c → ⟦ c ⟧ → Set
⟦ base A ⟧⟶ I = Extractor.Type A I
⟦ σ ⟶ τ  ⟧⟶ I = ⟦ σ ⟧⟶ I → ⟦ τ ⟧⟶ I

-- A simply typed function extension.

Simple : ∀ {c} → Simple-type c → Extension c
Simple {c} σ = Extension-with-resp.extension record
  { Ext       = λ I → ↑ _ (⟦ σ ⟧⟶ I)
  ; Iso       = λ { I≅J (lift f) (lift g) → ↑ _ (Iso σ I≅J f g) }
  ; resp      = λ ass I≅J →
                  lift ∘
                  _≈_.to (cast (Assumptions.ext ass) σ I≅J) ∘
                  lower
  ; resp-refl = λ { ass (lift f) → cong lift $
                    let open Assumptions ass in

                    _≈_.to (cast ext σ (reflexivity ass c _)) f  ≡⟨ cong (λ eq → _≈_.to eq f) $ cast-refl ass σ ⟩∎
                    f                                           ∎ }
  ; Iso≈Iso″  = λ ass I≅J {f g} →
                  let open Assumptions ass
                      lf = lower f; lg = lower g in

                  ↑ _ (Iso σ I≅J lf lg)                    ↔⟨ ↑↔ ⟩
                  Iso σ I≅J lf lg                          ↝⟨ Iso≈Iso″ ext σ I≅J ⟩
                  (_≈_.to (cast ext σ I≅J) lf ≡ lg)        ↝⟨ Weak.≈-≡ (↔⇒≈ ↑↔) ⟩□
                  (lift (_≈_.to (cast ext σ I≅J) lf) ≡ g)  □
  }
  where
  open Extractor

  -- Isomorphisms between simply typed values.

  Iso : (σ : Simple-type c) →
        ∀ {I J} → Isomorphic c I J → ⟦ σ ⟧⟶ I → ⟦ σ ⟧⟶ J → Set
  Iso (base A) I≅J x y = _≈_.to (Type-cong A I≅J) x ≡ y
  Iso (σ ⟶ τ)  I≅J f g = ∀ x y → Iso σ I≅J x y → Iso τ I≅J (f x) (g y)

  -- Cast (defined using extensionality).

  cast : Extensionality (# 0) (# 0) →
         (σ : Simple-type c) →
         ∀ {I J} → Isomorphic c I J → ⟦ σ ⟧⟶ I ≈ ⟦ σ ⟧⟶ J
  cast _   (base A) I≅J = Type-cong A I≅J
  cast ext (σ ⟶ τ)  I≅J = →-cong ext (cast ext σ I≅J) (cast ext τ I≅J)

  -- Cast simplification lemma.

  cast-refl : (ass : Assumptions) → let open Assumptions ass in
              ∀ σ {I} → cast ext σ (reflexivity ass c I) ≡ Weak.id
  cast-refl ass (base A) {I} =
    Type-cong A (reflexivity ass c I)  ≡⟨ Type-cong-reflexivity A ass I ⟩∎
    Weak.id                            ∎

  cast-refl ass (σ ⟶ τ) {I} =
    cast ext (σ ⟶ τ) (reflexivity ass c I)  ≡⟨ lift-equality ext $ cong _≈_.to $
                                                 cong₂ (→-cong ext) (cast-refl ass σ) (cast-refl ass τ) ⟩∎
    Weak.id                                 ∎
    where open Assumptions ass

  -- Two definitions of isomorphism are weakly equivalent.

  Iso≈Iso″ :
    (ext : Extensionality (# 0) (# 0)) →
    (σ : Simple-type c) →
    ∀ {I J} (I≅J : Isomorphic c I J) {f g} →
    Iso σ I≅J f g ≈ (_≈_.to (cast ext σ I≅J) f ≡ g)
  Iso≈Iso″ ext (base A) I≅J {x} {y} =

    (_≈_.to (Type-cong A I≅J) x ≡ y)  □

  Iso≈Iso″ ext (σ ⟶ τ) I≅J {f} {g} =

    (∀ x y → Iso σ I≅J x y → Iso τ I≅J (f x) (g y))                ↝⟨ ∀-preserves ext (λ _ → ∀-preserves ext λ _ →
                                                                        →-cong ext (Iso≈Iso″ ext σ I≅J) (Iso≈Iso″ ext τ I≅J)) ⟩
    (∀ x y → to (cast ext σ I≅J) x ≡ y →
             to (cast ext τ I≅J) (f x) ≡ g y)                      ↝⟨ inverse $ ∀-preserves ext (λ x → ↔⇒≈ $
                                                                        ∀-intro ext (λ y _ → to (cast ext τ I≅J) (f x) ≡ g y)) ⟩
    (∀ x → to (cast ext τ I≅J) (f x) ≡ g (to (cast ext σ I≅J) x))  ↝⟨ extensionality-isomorphism ext ⟩

    (to (cast ext τ I≅J) ∘ f ≡ g ∘ to (cast ext σ I≅J))            ↝⟨ inverse $ ∘from≡↔≡∘to ext (cast ext σ I≅J) ⟩□

    (to (cast ext τ I≅J) ∘ f ∘ from (cast ext σ I≅J) ≡ g)          □

    where open _≈_

------------------------------------------------------------------------
-- Some example structures

-- Example: magmas.

magma : Code
magma = ε ▻ A-type ▻ N-ary [0] 2

Magma : Set₁
Magma = ⟦ magma ⟧

private

  -- An unfolding of Magma.

  Magma-unfolded : Magma ≡
                   Σ (↑ _ ⊤ × Set) λ { (_ , A) → ↑ _ (A → A → A) }
  Magma-unfolded = refl _

  -- An unfolding of Isomorphic magma.

  Isomorphic-magma-unfolded :
    ∀ {A₁ : Set} {f₁ : A₁ → A₁ → A₁}
      {A₂ : Set} {f₂ : A₂ → A₂ → A₂} →
    Isomorphic magma ((_ , A₁) , lift f₁) ((_ , A₂) , lift f₂) ≡
    Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ≈ A₂)                              ) λ { (_ , lift A₁≈A₂) →
      let open _≈_ A₁≈A₂ in ↑ _ (
        ∀ x y → to (f₁ x y) ≡ f₂ (to x) (to y)) }
  Isomorphic-magma-unfolded = refl _

-- Example: semigroups. Note that one axiom states that the underlying
-- type is a set. This assumption is used to prove that the other
-- axiom is propositional.

semigroup : Code
semigroup =
  ε

  ▻ A-type

  ▻ Is-a-set [0]

  ▻ N-ary (1+ [0]) 2

  ▻ Proposition
      (λ { (_ , lift _∙_) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
      assoc-prop

  where
  assoc-prop = λ { ass ((_ , lift A-set) , _) →
    let open Assumptions ass in
    Π-closure (lower-extensionality _ _ ext) 1 λ _ →
    Π-closure (lower-extensionality _ _ ext) 1 λ _ →
    Π-closure (lower-extensionality _ _ ext) 1 λ _ →
    A-set _ _ }

Semigroup : Set₁
Semigroup = ⟦ semigroup ⟧

private

  -- An unfolding of Semigroup.

  Semigroup-unfolded :
    Semigroup ≡ Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                                        ) λ {  (_ , A) →
      ↑ _ (Is-set A)                            }) λ { ((_ , A) , _) →
      ↑ _ (A → A → A)                           }) λ { (_ , lift _∙_) →
      ↑ _ (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z) }
  Semigroup-unfolded = refl _

  -- An unfolding of Isomorphic semigroup.

  Isomorphic-semigroup-unfolded :
    ∀ {A₁ : Set} {is₁ : Is-set A₁} {_∙₁_ : A₁ → A₁ → A₁}
      {assoc₁ : ∀ x y z → x ∙₁ (y ∙₁ z) ≡ (x ∙₁ y) ∙₁ z}
      {A₂ : Set} {is₂ : Is-set A₂} {_∙₂_ : A₂ → A₂ → A₂}
      {assoc₂ : ∀ x y z → x ∙₂ (y ∙₂ z) ≡ (x ∙₂ y) ∙₂ z} →
    Isomorphic semigroup
      ((((_ , A₁) , lift is₁) , lift _∙₁_) , lift assoc₁)
      ((((_ , A₂) , lift is₂) , lift _∙₂_) , lift assoc₂) ≡
    Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ≈ A₂)                          ) λ { _ →
      ↑ _ ⊤                                 }) λ { ((_ , lift A₁≈A₂) , _) →
      let open _≈_ A₁≈A₂ in ↑ _ (
        ∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y) }) λ { _ →
      ↑ _ ⊤                                 }
  Isomorphic-semigroup-unfolded = refl _

-- Example: Sets with fixed-point operators.

set-with-fixed-point-operator : Code
set-with-fixed-point-operator =
  ε

  ▻ A-type

  ▻ Is-a-set [0]

  ▻ Simple ((base (1+ [0]) ⟶ base (1+ [0])) ⟶ base (1+ [0]))

  ▻ Proposition
      (λ { (_ , lift fix) →
           ∀ f → fix f ≡ f (fix f) })
      fix-point-prop

  where
  fix-point-prop = λ { ass ((_ , lift A-set) , _) →
    let open Assumptions ass in
    Π-closure (lower-extensionality _ _ ext) 1 λ _ →
    A-set _ _ }

Set-with-fixed-point-operator : Set₁
Set-with-fixed-point-operator = ⟦ set-with-fixed-point-operator ⟧

private

  -- An unfolding of Set-with-fixed-point-operator.

  Set-with-fixed-point-operator-unfolded :
    Set-with-fixed-point-operator ≡ Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                            ) λ {  (_ , A) →
      ↑ _ (Is-set A)                }) λ { ((_ , A) , _) →
      ↑ _ ((A → A) → A)             }) λ { (_ , lift fix) →
      ↑ _ (∀ f → fix f ≡ f (fix f)) }
  Set-with-fixed-point-operator-unfolded = refl _

  -- An unfolding of Isomorphic set-with-fixed-point-operator.

  Isomorphic-set-with-fixed-point-operator-unfolded :
    ∀ {A₁ : Set} {is₁ : Is-set A₁} {fix₁ : (A₁ → A₁) → A₁}
      {fixed-point₁ : ∀ f → fix₁ f ≡ f (fix₁ f)}
      {A₂ : Set} {is₂ : Is-set A₂} {fix₂ : (A₂ → A₂) → A₂}
      {fixed-point₂ : ∀ f → fix₂ f ≡ f (fix₂ f)} →
    Isomorphic set-with-fixed-point-operator
      ((((_ , A₁) , lift is₁) , lift fix₁) , lift fixed-point₁)
      ((((_ , A₂) , lift is₂) , lift fix₂) , lift fixed-point₂) ≡
    Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ≈ A₂)                             ) λ { _ →
      ↑ _ ⊤                                    }) λ { ((_ , lift A₁≈A₂) , _) →
      let open _≈_ A₁≈A₂ in ↑ _ (
        ∀ f g →
        (∀ x y → to x ≡ y → to (f x) ≡ g y) →
        to (fix₁ f) ≡ fix₂ g)                  }) λ { _ →
      ↑ _ ⊤                                    }
  Isomorphic-set-with-fixed-point-operator-unfolded = refl _

-- Example: abelian groups.

abelian-group : Code
abelian-group =
  ε

  -- The underlying type.
  ▻ A-type

  -- The underlying type is a set.
  ▻ Is-a-set [0]

  -- The binary group operation.
  ▻ N-ary (1+ [0]) 2

  -- Commutativity.
  ▻ Comm

  -- Associativity.
  ▻ Assoc

  -- Identity.
  ▻ N-ary (1+ 1+ 1+ 1+ [0]) 0

  -- Left identity.
  ▻ Left-identity

  -- Right identity.
  ▻ Right-identity

  -- Inverse.
  ▻ N-ary (1+ 1+ 1+ 1+ 1+ 1+ 1+ [0]) 1

  -- Left inverse.
  ▻ Left-inverse

  -- Right inverse.
  ▻ Right-inverse

  where
  bin = ε ▻ A-type ▻ Is-a-set [0] ▻ N-ary (1+ [0]) 2

  Comm = Proposition {bin}
    (λ { (_ , lift _∙_) →
       ∀ x y → x ∙ y ≡ y ∙ x })

    (λ { ass ((_ , lift A-set) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  comm = bin ▻ Comm

  Assoc = Proposition {comm}
    (λ { ((_ , lift _∙_) , _) →
         ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })

    (λ { ass (((_ , lift A-set) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  identity = comm ▻ Assoc ▻ N-ary (1+ 1+ 1+ 1+ [0]) 0

  Left-identity = Proposition {identity}
    (λ { ((((_ , lift _∙_) , _) , _) , lift e) →
         ∀ x → e ∙ x ≡ x })

    (λ { ass (((((_ , lift A-set) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  left-identity = identity ▻ Left-identity

  Right-identity = Proposition {left-identity}
    (λ { (((((_ , lift _∙_) , _) , _) , lift e) , _) →
         ∀ x → x ∙ e ≡ x })

    (λ { ass ((((((_ , lift A-set) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  inv = left-identity ▻ Right-identity ▻
        N-ary (1+ 1+ 1+ 1+ 1+ 1+ 1+ [0]) 1

  Left-inverse = Proposition {inv}
    (λ { (((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) →
         ∀ x → (x ⁻¹) ∙ x ≡ e })

    (λ { ass ((((((((_ , lift A-set) , _) , _) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

  left-inverse = inv ▻ Left-inverse

  Right-inverse = Proposition {left-inverse}
    (λ { ((((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) , _) →
         ∀ x → x ∙ (x ⁻¹) ≡ e })

    (λ { ass (((((((((_ , lift A-set) , _) , _) , _) , _) , _) , _) , _) , _) →
       let open Assumptions ass in
       Π-closure (lower-extensionality _ _ ext) 1 λ _ →
       A-set _ _
     })

Abelian-group : Set₁
Abelian-group = ⟦ abelian-group ⟧

private

  -- An unfolding of Abelian-group. Note that the inner structure is
  -- left-nested.

  Abelian-group-unfolded :
    Abelian-group ≡ Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      Set                                        ) λ {        (_ , A) →
      ↑ _ (Is-set A)                            }) λ {       ((_ , A) , _) →
      ↑ _ (A → A → A)                           }) λ {                  (_ , lift _∙_) →
      ↑ _ (∀ x y → x ∙ y ≡ y ∙ x)               }) λ {                 ((_ , lift _∙_) , _) →
      ↑ _ (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z) }) λ {    (((((_ , A) , _) , _  ) , _) , _) →
      ↑ _ A                                     }) λ {               ((((_ , lift _∙_) , _) , _) , lift e) →
      ↑ _ (∀ x → e ∙ x ≡ x)                     }) λ {              (((((_ , lift _∙_) , _) , _) , lift e) , _) →
      ↑ _ (∀ x → x ∙ e ≡ x)                     }) λ { ((((((((_ , A) , _) , _  ) , _) , _) , _) , _) , _) →
      ↑ _ (A → A)                               }) λ {            (((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) →
      ↑ _ (∀ x → (x ⁻¹) ∙ x ≡ e)                }) λ {           ((((((((_ , lift _∙_) , _) , _) , lift e) , _) , _) , lift _⁻¹) , _) →
      ↑ _ (∀ x → x ∙ (x ⁻¹) ≡ e)                }
  Abelian-group-unfolded = refl _

  -- An unfolding of Isomorphic abelian-group.

  Isomorphic-abelian-group-unfolded :
    ∀ {A₁ : Set} {is₁ : Is-set A₁} {_∙₁_ : A₁ → A₁ → A₁}
      {comm₁ : ∀ x y → x ∙₁ y ≡ y ∙₁ x}
      {assoc₁ : ∀ x y z → x ∙₁ (y ∙₁ z) ≡ (x ∙₁ y) ∙₁ z}
      {e₁ : A₁} {lid₁ : ∀ x → e₁ ∙₁ x ≡ x} {rid₁ : ∀ x → x ∙₁ e₁ ≡ x}
      {_⁻¹₁ : A₁ → A₁} {linv₁ : ∀ x → (x ⁻¹₁) ∙₁ x ≡ e₁}
      {rinv₁ : ∀ x → x ∙₁ (x ⁻¹₁) ≡ e₁}
      {A₂ : Set} {is₂ : Is-set A₂} {_∙₂_ : A₂ → A₂ → A₂}
      {comm₂ : ∀ x y → x ∙₂ y ≡ y ∙₂ x}
      {assoc₂ : ∀ x y z → x ∙₂ (y ∙₂ z) ≡ (x ∙₂ y) ∙₂ z}
      {e₂ : A₂} {lid₂ : ∀ x → e₂ ∙₂ x ≡ x} {rid₂ : ∀ x → x ∙₂ e₂ ≡ x}
      {_⁻¹₂ : A₂ → A₂} {linv₂ : ∀ x → (x ⁻¹₂) ∙₂ x ≡ e₂}
      {rinv₂ : ∀ x → x ∙₂ (x ⁻¹₂) ≡ e₂} →
    Isomorphic abelian-group
      (((((((((((_ , A₁) , lift is₁) , lift _∙₁_) , lift comm₁) ,
       lift assoc₁) , lift e₁) , lift lid₁) , lift rid₁) , lift _⁻¹₁) ,
       lift linv₁) , lift rinv₁)
      (((((((((((_ , A₂) , lift is₂) , lift _∙₂_) , lift comm₂) ,
       lift assoc₂) , lift e₂) , lift lid₂) , lift rid₂) , lift _⁻¹₂) ,
       lift linv₂) , lift rinv₂) ≡
    Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
      ↑ _ (A₁ ≈ A₂)                          ) λ { _ →
      ↑ _ ⊤                                 }) λ {       ((_ , lift A₁≈A₂) , _) →
      let open _≈_ A₁≈A₂ in ↑ _ (
        ∀ x y → to (x ∙₁ y) ≡ to x ∙₂ to y) }) λ { _ →
      ↑ _ ⊤                                 }) λ { _ →
      ↑ _ ⊤                                 }) λ {    (((((_ , lift A₁≈A₂) , _) , _) , _) , _) →
      let open _≈_ A₁≈A₂ in ↑ _ (
        to e₁ ≡ e₂)                         }) λ { _ →
      ↑ _ ⊤                                 }) λ { _ →
      ↑ _ ⊤                                 }) λ { ((((((((_ , lift A₁≈A₂) , _) , _) , _) , _) , _) , _) , _) →
      let open _≈_ A₁≈A₂ in ↑ _ (
        ∀ x → to (x ⁻¹₁) ≡ to x ⁻¹₂)        }) λ { _ →
      ↑ _ ⊤                                 }) λ { _ →
      ↑ _ ⊤                                 }
  Isomorphic-abelian-group-unfolded = refl _
