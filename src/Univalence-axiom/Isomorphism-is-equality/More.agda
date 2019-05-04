------------------------------------------------------------------------
-- A large(r) class of algebraic structures satisfies the property
-- that isomorphic instances of a structure are equal (assuming
-- univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Note that this module uses ordinary propositional equality, with a
-- computing J rule.

-- This module has been developed in collaboration with Thierry
-- Coquand.

module Univalence-axiom.Isomorphism-is-equality.More where

open import Equality.Propositional
  hiding (refl) renaming (equality-with-J to eq)
open import Equality
open Derived-definitions-and-properties eq using (refl)

open import Bijection eq hiding (id; _∘_; inverse; step-↔; finally-↔)
open import Equivalence eq as Eq hiding (id; _∘_; inverse)
open import Function-universe eq hiding (id; _∘_)
open import H-level eq as H-level hiding (Proposition; Type)
open import H-level.Closure eq
open import Preimage eq
open import Prelude
open import Univalence-axiom eq

------------------------------------------------------------------------
-- A record packing up certain assumptions

-- Use of these or similar assumptions is usually not documented in
-- comments below (with remarks like "assuming univalence").

record Assumptions : Set₂ where
  field
    ext₁  : Extensionality (# 1) (# 1)
    univ  : Univalence (# 0)
    univ₁ : Univalence (# 1)

  abstract

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

      Iso : (ass : Assumptions) →
            {I J : ⟦ c ⟧} → Isomorphic ass c I J →
            Ext I → Ext J → Set₁

    -- An alternative definition of Iso.

    Iso′ : (ass : Assumptions) →
           ∀ {I J} → Isomorphic ass c I J →
           Ext I → Ext J → Set₁
    Iso′ ass I≅J x y =
      subst Ext (_≃_.to (isomorphism≃equality ass c) I≅J) x ≡ y

    field

      -- Iso and Iso′ are equivalent.

      Iso≃Iso′ :
        (ass : Assumptions) →
        ∀ {I J} (I≅J : Isomorphic ass c I J) {x y} →
        Iso ass I≅J x y ≃ Iso′ ass I≅J x y

  -- Interpretation of the codes. The elements of ⟦ c ⟧ are instances
  -- of the structure encoded by c.

  ⟦_⟧ : Code → Set₁
  ⟦ ε     ⟧ = ↑ _ ⊤
  ⟦ c ▻ e ⟧ = Σ ⟦ c ⟧ (Extension.Ext e)

  -- Isomorphisms.

  Isomorphic : Assumptions → (c : Code) → ⟦ c ⟧ → ⟦ c ⟧ → Set₁
  Isomorphic _   ε       _       _       = ↑ _ ⊤
  Isomorphic ass (c ▻ e) (I , x) (J , y) =
    Σ (Isomorphic ass c I J) λ I≅J → Extension.Iso e ass I≅J x y

  -- Isomorphism is equivalent to equality.

  isomorphism≃equality : (ass : Assumptions) →
                         (c : Code) {I J : ⟦ c ⟧} →
                         Isomorphic ass c I J ≃ (I ≡ J)

  isomorphism≃equality _ ε =

      ↑ _ ⊤              ↔⟨ contractible-isomorphic (↑-closure 0 ⊤-contractible)
                                                    (+⇒≡ $ ↑-closure 1 (mono₁ 0 ⊤-contractible)) ⟩□
      lift tt ≡ lift tt  □

  isomorphism≃equality ass (c ▻ e) {I , x} {J , y} =

    (Σ (Isomorphic ass c I J) λ I≅J → Iso e ass I≅J x y)  ↝⟨ Σ-cong (isomorphism≃equality ass c)
                                                                    (λ I≅J → Iso≃Iso′ e ass I≅J) ⟩
    (Σ (I ≡ J) λ I≡J → subst (Ext e) I≡J x ≡ y)           ↔⟨ Σ-≡,≡↔≡ ⟩□

    ((I , x) ≡ (J , y))                                   □

    where open Extension

-- Isomorphism is equal to equality (assuming /only/ univalence).

isomorphism≡equality :
  (univ  : Univalence (# 0))
  (univ₁ : Univalence (# 1))
  (univ₂ : Univalence (# 2)) →

  let ass = record
        { ext₁  = dependent-extensionality univ₂ univ₁
        ; univ  = univ
        ; univ₁ = univ₁
        } in

  (c : Code) {I J : ⟦ c ⟧} →
  Isomorphic ass c I J ≡ (I ≡ J)
isomorphism≡equality univ univ₁ univ₂ c =
  ≃⇒≡ univ₁ $ isomorphism≃equality _ c

------------------------------------------------------------------------
-- Reflexivity

-- The isomorphism relation is reflexive.

reflexivity : (ass : Assumptions) → ∀ c I → Isomorphic ass c I I
reflexivity ass c I =
  _≃_.from (isomorphism≃equality ass c) (refl I)

-- Reflexivity relates an element to itself.

reflexivityE :
  (ass : Assumptions) →
  ∀ c e I x →
  Extension.Iso e ass (reflexivity ass c I) x x
reflexivityE ass c e I x =
  _≃_.from (Iso≃Iso′ ass (reflexivity ass c I)) (
    subst Ext (to (from (refl I))) x  ≡⟨ subst (λ eq → subst Ext eq x ≡ x)
                                               (sym $ right-inverse-of (refl I))
                                               (refl x) ⟩∎
    x                                 ∎)
  where
  open Extension e
  open _≃_ (isomorphism≃equality ass c)

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

    Iso : (ass : Assumptions) →
          {I J : ⟦ c ⟧} → Isomorphic ass c I J →
          Ext I → Ext J → Set₁

    -- Ext, seen as a predicate, respects isomorphisms.

    resp : (ass : Assumptions) →
           ∀ {I J} → Isomorphic ass c I J →
           Ext I → Ext J

    -- The resp function respects reflexivity.

    resp-refl : (ass : Assumptions) →
                ∀ {I} (x : Ext I) →
                resp ass (reflexivity ass c I) x ≡ x

  -- An alternative definition of Iso.

  Iso″ : (ass : Assumptions) →
         {I J : ⟦ c ⟧} → Isomorphic ass c I J →
         Ext I → Ext J → Set₁
  Iso″ ass I≅J x y = resp ass I≅J x ≡ y

  field

    -- Iso and Iso″ are equivalent.

    Iso≃Iso″ :
      (ass : Assumptions) →
      ∀ {I J} (I≅J : Isomorphic ass c I J) {x y} →
      Iso ass I≅J x y ≃ Iso″ ass I≅J x y

  -- Another alternative definition of Iso.

  Iso′ : (ass : Assumptions) →
         ∀ {I J} → Isomorphic ass c I J →
         Ext I → Ext J → Set₁
  Iso′ ass I≅J x y =
    subst Ext (_≃_.to (isomorphism≃equality ass c) I≅J) x ≡ y

  abstract

    -- Every element is isomorphic to itself, transported along the
    -- "outer" isomorphism.

    isomorphic-to-itself″ :
      (ass : Assumptions) →
      ∀ {I J} (I≅J : Isomorphic ass c I J) {x} →
      Iso″ ass I≅J x
           (subst Ext (_≃_.to (isomorphism≃equality ass c) I≅J) x)
    isomorphic-to-itself″ ass I≅J {x} = transport-theorem′
      Ext
      (Isomorphic ass c)
      (_≃_.surjection $ inverse $ isomorphism≃equality ass c)
      (resp ass)
      (λ _ → resp-refl ass)
      I≅J
      x

  -- Iso and Iso′ are equivalent.

  Iso≃Iso′ :
    (ass : Assumptions) →
    ∀ {I J} (I≅J : Isomorphic ass c I J) {x y} →
    Iso ass I≅J x y ≃ Iso′ ass I≅J x y
  Iso≃Iso′ ass I≅J {x} {y} = record
    { to             = to
    ; is-equivalence = λ y →
        (from y , right-inverse-of y) , irrelevance y
    }
    where
    -- This is the core of the definition. I could have defined
    -- Iso≃Iso′ ... = I≃I′. The rest is only included in order to
    -- control how much Agda unfolds the code.
    I≃I′ =
      Iso  ass I≅J x y  ↝⟨ Iso≃Iso″ ass I≅J ⟩
      Iso″ ass I≅J x y  ↝⟨ ≡⇒≃ $ cong (λ z → z ≡ y) $ isomorphic-to-itself″ ass I≅J ⟩□
      Iso′ ass I≅J x y  □

    to   = _≃_.to   I≃I′
    from = _≃_.from I≃I′

    abstract
      right-inverse-of : ∀ x → to (from x) ≡ x
      right-inverse-of = _≃_.right-inverse-of I≃I′

      irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
      irrelevance = _≃_.irrelevance I≃I′

  -- An extension constructed from the fields above.

  extension : Extension c
  extension = record { Ext = Ext; Iso = Iso; Iso≃Iso′ = Iso≃Iso′ }

  -- Every element is isomorphic to itself, transported (in another
  -- way) along the "outer" isomorphism.

  isomorphic-to-itself :
    (ass : Assumptions) →
    ∀ {I J} (I≅J : Isomorphic ass c I J) x →
    Iso ass I≅J x (resp ass I≅J x)
  isomorphic-to-itself ass I≅J x =
    _≃_.from (Iso≃Iso″ ass I≅J) (refl (resp ass I≅J x))

  abstract

    -- Simplification lemmas.

    resp-refl-lemma :
      (ass : Assumptions) →
      ∀ I x →
      resp-refl ass x ≡
      _≃_.from (≡⇒≃ $ cong (λ z → z ≡ x) $
                      isomorphic-to-itself″ ass (reflexivity ass c I))
               (subst (λ eq → subst Ext eq x ≡ x)
                      (sym $ _≃_.right-inverse-of
                               (isomorphism≃equality ass c)
                               (refl I))
                      (refl x))
    resp-refl-lemma ass I x =
      let rfl    = reflexivity ass c I
          iso≃eq = λ {I J} → isomorphism≃equality ass c {I = I} {J = J}
          rio    = right-inverse-of iso≃eq (refl I)
          lio    = left-inverse-of (inverse iso≃eq) (refl I)
          sx≡x   = subst (λ eq → subst Ext eq x ≡ x) (sym rio) (refl x)

          sx≡x-lemma =
            cong (λ eq → subst Ext eq x) rio                      ≡⟨ sym $ trans-reflʳ _ ⟩

            trans (cong (λ eq → subst Ext eq x) rio)
                  (refl x)                                        ≡⟨ sym $ subst-trans (cong (λ eq → subst Ext eq x) rio) ⟩

            subst (λ z → z ≡ x)
                  (sym $ cong (λ eq → subst Ext eq x) rio)
                  (refl x)                                        ≡⟨ cong (λ eq → subst (λ z → z ≡ x) eq (refl x)) $ sym $
                                                                          cong-sym (λ eq → subst Ext eq x) rio ⟩
            subst (λ z → z ≡ x)
                  (cong (λ eq → subst Ext eq x) $ sym rio)
                  (refl x)                                        ≡⟨ sym $ subst-∘ (λ z → z ≡ x) (λ eq → subst Ext eq x) (sym rio) ⟩∎

            subst (λ eq → subst Ext eq x ≡ x) (sym rio) (refl x)  ∎

          lemma₁ =
            trans (sym lio) rio  ≡⟨ cong (λ eq → trans (sym eq) rio) $ left-inverse-of∘inverse iso≃eq ⟩

            trans (sym rio) rio  ≡⟨ trans-symˡ rio ⟩∎

            refl (refl I)        ∎

          lemma₂ =
            elim-refl (λ {I J} _ → Ext I → Ext J) (λ _ e → e)  ≡⟨⟩

            cong (subst Ext) (refl (refl I))                   ≡⟨ cong (cong (subst Ext)) $ sym lemma₁ ⟩∎

            cong (subst Ext) (trans (sym lio) rio)             ∎

          lemma₃ =
            cong (λ r → r x)
                 (elim-refl (λ {I J} _ → Ext I → Ext J) (λ _ e → e))   ≡⟨ cong (cong (λ r → r x)) lemma₂ ⟩

            cong (λ r → r x) (cong (subst Ext) (trans (sym lio) rio))  ≡⟨ cong-∘ (λ r → r x) (subst Ext) (trans (sym lio) rio) ⟩

            cong (λ eq → subst Ext eq x) (trans (sym lio) rio)         ≡⟨ cong-trans (λ eq → subst Ext eq x) (sym lio) rio ⟩

            trans (cong (λ eq → subst Ext eq x) (sym lio))
                  (cong (λ eq → subst Ext eq x) rio)                   ≡⟨ cong (λ eq → trans eq (cong (λ eq → subst Ext eq x) rio)) $
                                                                               cong-sym (λ eq → subst Ext eq x) lio ⟩∎
            trans (sym (cong (λ eq → subst Ext eq x) lio))
                  (cong (λ eq → subst Ext eq x) rio)                   ∎
      in

      resp-refl ass x                                                  ≡⟨ sym $ trans-reflʳ _ ⟩

      trans (resp-refl ass x) (refl x)                                 ≡⟨ cong (trans (resp-refl ass x)) $ trans-symˡ (subst-refl Ext x) ⟩

      trans (resp-refl ass x)
            (trans (sym $ subst-refl Ext x) (subst-refl Ext x))        ≡⟨ sym $ trans-assoc _ (sym $ subst-refl Ext x) (subst-refl Ext x) ⟩

      trans (trans (resp-refl ass x) (sym $ subst-refl Ext x))
            (subst-refl Ext x)                                         ≡⟨ cong (trans (trans (resp-refl ass x) (sym $ subst-refl Ext x)))
                                                                               lemma₃ ⟩
      trans (trans (resp-refl ass x) (sym $ subst-refl Ext x))
            (trans (sym (cong (λ eq → subst Ext eq x) lio))
                   (cong (λ eq → subst Ext eq x) rio))                 ≡⟨ sym $ trans-assoc _ _ (cong (λ eq → subst Ext eq x) rio) ⟩

      trans (trans (trans (resp-refl ass x) (sym $ subst-refl Ext x))
                   (sym (cong (λ eq → subst Ext eq x) lio)))
            (cong (λ eq → subst Ext eq x) rio)                         ≡⟨ cong₂ trans
                                                                            (sym $ transport-theorem′-refl Ext (Isomorphic ass c) (inverse iso≃eq)
                                                                                                           (resp ass) (λ _ → resp-refl ass) x)
                                                                            sx≡x-lemma ⟩
      trans (isomorphic-to-itself″ ass rfl) sx≡x                       ≡⟨ sym $ subst-trans (isomorphic-to-itself″ ass rfl) ⟩

      subst (λ z → z ≡ x) (sym $ isomorphic-to-itself″ ass rfl) sx≡x   ≡⟨ subst-in-terms-of-inverse∘≡⇒↝ equivalence
                                                                            (isomorphic-to-itself″ ass rfl) (λ z → z ≡ x) _ ⟩∎
      from (≡⇒≃ $ cong (λ z → z ≡ x) $ isomorphic-to-itself″ ass rfl)
           sx≡x                                                        ∎

      where open _≃_

    isomorphic-to-itself-reflexivity :
      (ass : Assumptions) →
      ∀ I x →
      isomorphic-to-itself ass (reflexivity ass c I) x ≡
      subst (Iso ass (reflexivity ass c I) x)
            (sym $ resp-refl ass x)
            (reflexivityE ass c extension I x)
    isomorphic-to-itself-reflexivity ass I x =
      let rfl = reflexivity ass c I
          r-r = resp-refl ass x in

      from (Iso≃Iso″ ass rfl) (refl (resp ass rfl x))                  ≡⟨ elim¹ (λ {y} resp-x≡y → from (Iso≃Iso″ ass rfl) (refl (resp ass rfl x)) ≡
                                                                                                  subst (Iso ass rfl x) (sym resp-x≡y)
                                                                                                        (from (Iso≃Iso″ ass rfl) resp-x≡y))
                                                                                (refl _) r-r ⟩
      subst (Iso ass rfl x) (sym r-r) (from (Iso≃Iso″ ass rfl) r-r)    ≡⟨ cong (subst (Iso ass rfl x) (sym r-r) ∘ from (Iso≃Iso″ ass rfl))
                                                                               (resp-refl-lemma ass I x) ⟩∎
      subst (Iso ass rfl x) (sym r-r)
        (from (Iso≃Iso″ ass rfl)
           (from
              (≡⇒≃ $ cong (λ z → z ≡ x)
                          (isomorphic-to-itself″ ass rfl))
              (subst (λ eq → subst Ext eq x ≡ x)
                 (sym $ right-inverse-of (isomorphism≃equality ass c)
                                         (refl I)) (refl x))))         ∎

      where open _≃_

------------------------------------------------------------------------
-- Type extractors

record Extractor (c : Code) : Set₂ where
  field

    -- Extracts a type from an instance.

    Type : ⟦ c ⟧ → Set₁

    -- Extracts an equivalence relating types extracted from
    -- isomorphic instances.
    --
    -- Perhaps one could have a variant of Type-cong that is not based
    -- on any "Assumptions", and produces logical equivalences (_⇔_)
    -- instead of equivalences (_≃_). Then one could (hopefully)
    -- define isomorphism without using any assumptions.

    Type-cong : (ass : Assumptions) →
                ∀ {I J} → Isomorphic ass c I J → Type I ≃ Type J

    -- Reflexivity is mapped to the identity equivalence.

    Type-cong-reflexivity :
      (ass : Assumptions) →
      ∀ I → Type-cong ass (reflexivity ass c I) ≡ Eq.id

-- Constant type extractor.

[_] : ∀ {c} → Set₁ → Extractor c
[_] {c} A = record
  { Type                  = λ _ → A
  ; Type-cong             = λ _ _ → Eq.id
  ; Type-cong-reflexivity = λ _ _ → refl _
  }

-- Successor type extractor.

infix 6 1+_

1+_ : ∀ {c e} → Extractor c → Extractor (c ▻ e)
1+_ {c} {e} extractor = record
  { Type                  = Type ∘ proj₁
  ; Type-cong             = λ ass → Type-cong ass ∘ proj₁
  ; Type-cong-reflexivity = λ { ass (I , x) →
      Type-cong ass (reflexivity ass c I)  ≡⟨ Type-cong-reflexivity ass I ⟩∎
      Eq.id                                ∎ }
  }
  where
  open Extractor extractor

------------------------------------------------------------------------
-- An extension: types

-- Extends a structure with a type.

A-type : ∀ {c} → Extension c
A-type {c} = record
  { Ext      = λ _ → Set
  ; Iso      = λ _ _ A B → ↑ _ (A ≃ B)
  ; Iso≃Iso′ = λ ass I≅J {A B} →
                 let I≡J = _≃_.to (isomorphism≃equality ass c) I≅J in

                 ↑ _ (A ≃ B)                    ↔⟨ ↑↔ ⟩
                 (A ≃ B)                        ↝⟨ inverse $ ≡≃≃ (Assumptions.univ ass) ⟩
                 (A ≡ B)                        ↝⟨ ≡⇒≃ $ cong (λ C → C ≡ B) $ sym (subst-const I≡J) ⟩
                 (subst (λ _ → Set) I≡J A ≡ B)  □
  }

-- A corresponding type extractor.

[0] : ∀ {c} → Extractor (c ▻ A-type)
[0] {c} = record
  { Type                  = λ { (_ , A) → ↑ _ A }
  ; Type-cong             = λ { _ (_ , lift A≃B) → ↑-cong A≃B }
  ; Type-cong-reflexivity = λ { ass (I , A) → elim₁
      (λ {p} q →
         ↑-cong (≡⇒≃
           (from (≡⇒≃ (cong (λ C → C ≡ A) (sym (subst-const p))))
                 (subst (λ eq → subst Ext eq A ≡ A)
                        (sym q) (refl A)))) ≡
         Eq.id)
      (lift-equality (Assumptions.ext₁ ass) (refl _))
      (right-inverse-of (isomorphism≃equality ass c) (refl I)) }
  }
  where
  open Extension A-type
  open _≃_

------------------------------------------------------------------------
-- An extension: propositions

-- Extends a structure with a proposition.

Proposition : ∀ {c} →

              -- The proposition.
              (P : ⟦ c ⟧ → Set₁) →

              -- The proposition must be propositional (given some
              -- assumptions).
              (Assumptions → ∀ I → Is-proposition (P I)) →

              Extension c
Proposition {c} P prop = record
  { Ext      = P
  ; Iso      = λ _ _ _ _ → ↑ _ ⊤
  ; Iso≃Iso′ = λ ass I≅J {_ p} →
                 ↑ _ ⊤    ↔⟨ contractible-isomorphic
                               (↑-closure 0 ⊤-contractible)
                               (+⇒≡ $ mono₁ 0 (propositional⇒inhabited⇒contractible (prop ass _) p)) ⟩□
                 (_ ≡ _)  □
  }

-- The proposition stating that a given type is a set.

Is-a-set : ∀ {c} → Extractor c → Extension c
Is-a-set extractor =
  Proposition (Is-set ∘ Type)
              (λ ass _ → H-level-propositional (Assumptions.ext₁ ass) 2)
  where open Extractor extractor

------------------------------------------------------------------------
-- An extension: n-ary functions

-- N-ary functions.

_^_⟶_ : Set₁ → ℕ → Set₁ → Set₁
A ^ zero  ⟶ B = B
A ^ suc n ⟶ B = A → A ^ n ⟶ B

-- N-ary function morphisms.

Is-_-ary-morphism :
  ∀ (n : ℕ) {A B} → (A ^ n ⟶ A) → (B ^ n ⟶ B) → (A → B) → Set₁
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
  { Ext       = λ I → Type I ^ n ⟶ Type I
  ; Iso       = λ ass I≅J f g →
                    Is- n -ary-morphism f g (_≃_.to (Type-cong ass I≅J))
  ; resp      = λ ass I≅J → cast n (Type-cong ass I≅J)
  ; resp-refl = λ ass f →
                    cast n (Type-cong ass (reflexivity ass c _)) f  ≡⟨ cong (λ eq → cast n eq f) $ Type-cong-reflexivity ass _ ⟩
                    cast n Eq.id f                                  ≡⟨ cast-id (Assumptions.ext₁ ass) n f ⟩∎
                    f                                               ∎
  ; Iso≃Iso″  = λ ass I≅J {f g} →
      Iso≃Iso″ (Assumptions.ext₁ ass) (Type-cong ass I≅J) n f g
  }
  where
  open Extractor extractor

  -- Changes the type of an n-ary function.

  cast : ∀ n {A B} → A ≃ B → A ^ n ⟶ A → B ^ n ⟶ B
  cast zero    A≃B = _≃_.to A≃B
  cast (suc n) A≃B = λ f x → cast n A≃B (f (_≃_.from A≃B x))

  -- Cast simplification lemma.

  cast-id : Extensionality (# 1) (# 1) →
            ∀ {A} n (f : A ^ n ⟶ A) → cast n Eq.id f ≡ f
  cast-id ext zero    x = refl x
  cast-id ext (suc n) f = apply-ext ext λ x → cast-id ext n (f x)

  -- Two definitions of isomorphism are equivalent.

  Iso≃Iso″ :
    Extensionality (# 1) (# 1) →
    ∀ {A B} (A≃B : A ≃ B)
    (n : ℕ) (f : A ^ n ⟶ A) (g : B ^ n ⟶ B) →
    Is- n -ary-morphism f g (_≃_.to A≃B) ≃ (cast n A≃B f ≡ g)

  Iso≃Iso″ ext A≃B zero x y =

    (_≃_.to A≃B x ≡ y)  □

  Iso≃Iso″ ext A≃B (suc n) f g =

    (∀ x → Is- n -ary-morphism (f x) (g (_≃_.to A≃B x)) (_≃_.to A≃B))  ↝⟨ ∀-cong ext (λ x →
                                                                            Iso≃Iso″ ext A≃B n (f x) (g (_≃_.to A≃B x))) ⟩
    (∀ x → cast n A≃B (f x) ≡ g (_≃_.to A≃B x))                        ↝⟨ Eq.extensionality-isomorphism ext ⟩

    (cast n A≃B ∘ f ≡ g ∘ _≃_.to A≃B)                                  ↝⟨ inverse $ ∘from≡↔≡∘to ext A≃B ⟩□

    (cast n A≃B ∘ f ∘ _≃_.from A≃B ≡ g)                                □

------------------------------------------------------------------------
-- An extension: simply typed functions

-- This section contains a generalisation of the development for n-ary
-- functions above.

-- Simple types.

data Simple-type (c : Code) : Set₂ where
  base : Extractor c → Simple-type c
  _⟶_  : Simple-type c → Simple-type c → Simple-type c

-- Interpretation of a simple type.

⟦_⟧⟶ : ∀ {c} → Simple-type c → ⟦ c ⟧ → Set₁
⟦ base A ⟧⟶ I = Extractor.Type A I
⟦ σ ⟶ τ  ⟧⟶ I = ⟦ σ ⟧⟶ I → ⟦ τ ⟧⟶ I

-- A simply typed function extension.

Simple : ∀ {c} → Simple-type c → Extension c
Simple {c} σ = Extension-with-resp.extension record
  { Ext       = ⟦ σ ⟧⟶
  ; Iso       = λ ass → Iso ass σ
  ; resp      = λ ass I≅J → _≃_.to (cast ass σ I≅J)
  ; resp-refl = λ ass f → cong (λ eq → _≃_.to eq f) $ cast-refl ass σ
  ; Iso≃Iso″  = λ ass → Iso≃Iso″ ass σ
  }
  where
  open Extractor

  -- Isomorphisms between simply typed values.

  Iso : (ass : Assumptions) →
        (σ : Simple-type c) →
        ∀ {I J} → Isomorphic ass c I J → ⟦ σ ⟧⟶ I → ⟦ σ ⟧⟶ J → Set₁
  Iso ass (base A) I≅J x y = _≃_.to (Type-cong A ass I≅J) x ≡ y
  Iso ass (σ ⟶ τ)  I≅J f g =
    ∀ x y → Iso ass σ I≅J x y → Iso ass τ I≅J (f x) (g y)

  -- Cast.

  cast : (ass : Assumptions) →
         (σ : Simple-type c) →
         ∀ {I J} → Isomorphic ass c I J → ⟦ σ ⟧⟶ I ≃ ⟦ σ ⟧⟶ J
  cast ass (base A) I≅J = Type-cong A ass I≅J
  cast ass (σ ⟶ τ)  I≅J = →-cong ext₁ (cast ass σ I≅J) (cast ass τ I≅J)
    where open Assumptions ass

  -- Cast simplification lemma.

  cast-refl : (ass : Assumptions) →
              ∀ σ {I} → cast ass σ (reflexivity ass c I) ≡ Eq.id
  cast-refl ass (base A) {I} =
    Type-cong A ass (reflexivity ass c I)  ≡⟨ Type-cong-reflexivity A ass I ⟩∎
    Eq.id                                  ∎

  cast-refl ass (σ ⟶ τ) {I} =
    cast ass (σ ⟶ τ) (reflexivity ass c I)  ≡⟨ lift-equality ext₁ $ cong _≃_.to $
                                                 cong₂ (→-cong ext₁) (cast-refl ass σ) (cast-refl ass τ) ⟩∎
    Eq.id                                   ∎
    where open Assumptions ass

  -- Two definitions of isomorphism are equivalent.

  Iso≃Iso″ :
    (ass : Assumptions) →
    (σ : Simple-type c) →
    ∀ {I J} (I≅J : Isomorphic ass c I J) {f g} →
    Iso ass σ I≅J f g ≃ (_≃_.to (cast ass σ I≅J) f ≡ g)
  Iso≃Iso″ ass (base A) I≅J {x} {y} =

    (_≃_.to (Type-cong A ass I≅J) x ≡ y)  □

  Iso≃Iso″ ass (σ ⟶ τ) I≅J {f} {g} =

    (∀ x y → Iso ass σ I≅J x y → Iso ass τ I≅J (f x) (g y))        ↝⟨ ∀-cong ext₁ (λ _ → ∀-cong ext₁ λ _ →
                                                                        →-cong ext₁ (Iso≃Iso″ ass σ I≅J) (Iso≃Iso″ ass τ I≅J)) ⟩
    (∀ x y → to (cast ass σ I≅J) x ≡ y →
             to (cast ass τ I≅J) (f x) ≡ g y)                      ↝⟨ inverse $ ∀-cong ext₁ (λ x →
                                                                        ∀-intro ext₁ (λ y _ → to (cast ass τ I≅J) (f x) ≡ g y)) ⟩
    (∀ x → to (cast ass τ I≅J) (f x) ≡ g (to (cast ass σ I≅J) x))  ↝⟨ extensionality-isomorphism ext₁ ⟩

    (to (cast ass τ I≅J) ∘ f ≡ g ∘ to (cast ass σ I≅J))            ↝⟨ inverse $ ∘from≡↔≡∘to ext₁ (cast ass σ I≅J) ⟩□

    (to (cast ass τ I≅J) ∘ f ∘ from (cast ass σ I≅J) ≡ g)          □

    where
    open _≃_
    open Assumptions ass

------------------------------------------------------------------------
-- An unfinished extension: dependent types

-- The extension currently supports polymorphic types.

module Dependent where

  open Extractor

  ----------------------------------------------------------------------
  -- The extension

  -- Dependent types.

  data Ty (c : Code) : Set₂

  -- Extension: Dependently-typed functions.

  ext-with-resp : ∀ {c} → Ty c → Extension-with-resp c

  private
    open module E {c} (σ : Ty c) =
      Extension-with-resp (ext-with-resp σ)
      hiding (Iso; Iso≃Iso″; extension)
    open E public using () renaming (extension to Dep)

  data Ty c where
    set  : Ty c
    base : Extractor c → Ty c
    Π    : (σ : Ty c) → Ty (c ▻ Dep σ) → Ty c

  -- Interpretation of a dependent type.

  ⟦_⟧Π : ∀ {c} → Ty c → ⟦ c ⟧ → Set₁

  -- Isomorphisms between dependently typed functions.

  Iso :
    (ass : Assumptions) →
    ∀ {c} (σ : Ty c) →
    ∀ {I J} → Isomorphic ass c I J → ⟦ σ ⟧Π I → ⟦ σ ⟧Π J → Set₁

  -- A cast function.

  cast : (ass : Assumptions) →
         ∀ {c} (σ : Ty c) {I J} →
         Isomorphic ass c I J → ⟦ σ ⟧Π I ≃ ⟦ σ ⟧Π J

  -- Reflexivity is mapped to identity.

  cast-refl : (ass : Assumptions) →
              ∀ {c} (σ : Ty c) {I} →
              cast ass σ (reflexivity ass c I) ≡ Eq.id

  -- Two definitions of isomorphism are equivalent.

  Iso≃Iso″ : (ass : Assumptions) →
             ∀ {c} (σ : Ty c) {I J} (I≅J : Isomorphic ass c I J) {f g} →
             Iso ass σ I≅J f g ≃ (_≃_.to (cast ass σ I≅J) f ≡ g)

  -- Extension: Dependently-typed functions.

  ext-with-resp {c} σ = record
    { Ext       = ⟦ σ ⟧Π
    ; Iso       = λ ass → Iso ass σ
    ; resp      = λ ass I≅J → _≃_.to (cast ass σ I≅J)
    ; resp-refl = λ ass f → cong (λ eq → _≃_.to eq f) $ cast-refl ass σ
    ; Iso≃Iso″  = λ ass → Iso≃Iso″ ass σ
    }

  -- Interpretation of a dependent type.

  ⟦ set    ⟧Π _ = Set
  ⟦ base A ⟧Π I = Type A I
  ⟦ Π σ τ  ⟧Π I = (x : ⟦ σ ⟧Π I) → ⟦ τ ⟧Π (I , x)

  -- Isomorphisms between dependently typed functions.

  Iso _   set      _   A B = ↑ _ (A ≃ B)
  Iso ass (base A) I≅J x y = x ≡ _≃_.from (Type-cong A ass I≅J) y
  Iso ass (Π σ τ)  I≅J f g = ∀ x y →
    (x≅y : Iso ass σ I≅J x y) → Iso ass τ (I≅J , x≅y) (f x) (g y)

  -- A cast function.

  cast ass set      I≅J = Eq.id
  cast ass (base A) I≅J = Type-cong A ass I≅J
  cast ass (Π σ τ)  I≅J = Π-cong ext₁
    (cast ass σ I≅J)
    (λ x → cast ass τ (I≅J , isomorphic-to-itself σ ass I≅J x))
    where open Assumptions ass

  abstract

    -- Reflexivity is mapped to identity.

    cast-refl ass     set          = refl Eq.id
    cast-refl ass {c} (base A) {I} =

      Type-cong A ass (reflexivity ass c I)  ≡⟨ Type-cong-reflexivity A ass I ⟩∎

      Eq.id                                  ∎

    cast-refl ass {c} (Π σ τ) {I} =
      let rfl   = reflexivity ass c I
          rflE  = reflexivityE ass c (Dep σ) I in

      lift-equality-inverse ext₁ $
      apply-ext ext₁ λ f →
      apply-ext ext₁ λ x →

        from (cast ass τ (rfl , isomorphic-to-itself σ ass rfl x))
             (f (resp σ ass rfl x))                                 ≡⟨ cong (λ iso → from (cast ass τ (rfl , iso)) (f (resp σ ass rfl x))) $
                                                                            isomorphic-to-itself-reflexivity σ ass I x ⟩
        from (cast ass τ (rfl , subst (Iso ass σ rfl x)
                                      (sym $ resp-refl σ ass x)
                                      (rflE x)))
             (f (resp σ ass rfl x))                                 ≡⟨ elim¹ (λ {y} x≡y →
                                                                                from (cast ass τ (rfl , subst (Iso ass σ rfl x)
                                                                                                              x≡y (rflE x)))
                                                                                     (f y) ≡
                                                                                f x)
                                                                             (cong (λ h → _≃_.from h (f x)) $ cast-refl ass τ)
                                                                             (sym $ resp-refl σ ass x) ⟩∎
        f x                                                         ∎

      where
      open _≃_
      open Assumptions ass

  -- Two definitions of isomorphism are equivalent.

  Iso≃Iso‴ :
    (ass : Assumptions) →
    ∀ {c} (σ : Ty c) {I J} (I≅J : Isomorphic ass c I J) {f g} →
    Iso ass σ I≅J f g ≃ (f ≡ _≃_.from (cast ass σ I≅J) g)

  Iso≃Iso‴ ass set I≅J {A} {B} =

    ↑ _ (A ≃ B)  ↔⟨ ↑↔ ⟩

    (A ≃ B)      ↝⟨ inverse $ ≡≃≃ (Assumptions.univ ass) ⟩□

    (A ≡ B)      □

  Iso≃Iso‴ ass (base A) I≅J {x} {y} =

    (x ≡ _≃_.from (Type-cong A ass I≅J) y)  □

  Iso≃Iso‴ ass (Π σ τ) I≅J {f} {g} =
    let iso-to-itself = isomorphic-to-itself σ ass I≅J in

    (∀ x y (x≅y : Iso ass σ I≅J x y) →
           Iso ass τ (I≅J , x≅y) (f x) (g y))                        ↝⟨ ∀-cong ext₁ (λ x → ∀-cong ext₁ λ y →
                                                                          Π-cong ext₁ (Iso≃Iso″ ass σ I≅J) (λ x≅y →
           Iso ass τ (I≅J , x≅y) (f x) (g y)                                ↝⟨ Iso≃Iso″ ass τ (I≅J , x≅y) ⟩
           (resp τ ass (I≅J , x≅y) (f x) ≡ g y)                             ↝⟨ ≡⇒≃ $ cong (λ x≅y → resp τ ass (I≅J , x≅y) (f x) ≡ g y) $
                                                                                 sym $ left-inverse-of (Iso≃Iso″ ass σ I≅J) _ ⟩□
           (resp τ ass (I≅J , from (Iso≃Iso″ ass σ I≅J)
                                   (to (Iso≃Iso″ ass σ I≅J) x≅y))
               (f x) ≡ g y)                                                 □)) ⟩

    (∀ x y (x≡y : to (cast ass σ I≅J) x ≡ y) →
           resp τ ass (I≅J , from (Iso≃Iso″ ass σ I≅J) x≡y) (f x) ≡
           g y)                                                      ↝⟨ ∀-cong ext₁ (λ x → inverse $
                                                                          ∀-intro ext₁ (λ y x≡y → _ ≡ _)) ⟩
    (∀ x → resp τ ass (I≅J , iso-to-itself x) (f x) ≡
           g (resp σ ass I≅J x))                                     ↔⟨ extensionality-isomorphism ext₁ ⟩

    (resp τ ass (I≅J , iso-to-itself _) ∘ f ≡ g ∘ resp σ ass I≅J)    ↝⟨ to∘≡↔≡from∘ ext₁ (cast ass τ (I≅J , iso-to-itself _)) ⟩

    (f ≡ from (cast ass τ (I≅J , iso-to-itself _)) ∘
         g ∘ resp σ ass I≅J)                                         □

    where
    open _≃_
    open Assumptions ass

  abstract

    -- Two definitions of isomorphism are equivalent.

    Iso≃Iso″ ass σ I≅J {f} {g} =
      Iso ass σ I≅J f g                  ↝⟨ Iso≃Iso‴ ass σ I≅J ⟩

      (f ≡ _≃_.from (cast ass σ I≅J) g)  ↝⟨ inverse $ from≡↔≡to (inverse $ cast ass σ I≅J) ⟩□

      (_≃_.to (cast ass σ I≅J) f ≡ g)    □

  ----------------------------------------------------------------------
  -- An instantiation of the type extractor mechanism that gives us
  -- support for polymorphic types

  abstract

    reflexivityE-set :
      (ass : Assumptions) →
      ∀ {c} {I : ⟦ c ⟧} {A} →
      reflexivityE ass c (Dep set) I A ≡ lift Eq.id
    reflexivityE-set ass {c} {I} {A} =

      reflexivityE ass c (Dep set) I A                                 ≡⟨⟩

      lift (≡⇒≃ (to (from≡↔≡to (inverse Eq.id))
              (from (≡⇒≃ $ cong (λ B → B ≡ A) $
                       isomorphic-to-itself″ set ass
                         (reflexivity ass c I))
                    (subst (λ eq → subst (λ _ → Set) eq A ≡ A)
                           (sym $ right-inverse-of
                                    (isomorphism≃equality ass c)
                                    (refl I))
                           (refl A)))))                                ≡⟨ cong (λ eq → lift (≡⇒≃ (to (from≡↔≡to (inverse Eq.id)) eq))) $ sym $
                                                                            resp-refl-lemma set ass I A ⟩
      lift (≡⇒≃ (to (from≡↔≡to (inverse Eq.id))
                    (resp-refl set ass {I = I} A)))                    ≡⟨⟩

      lift (≡⇒≃ (to (from≡↔≡to (inverse Eq.id)) (refl A)))             ≡⟨⟩

      lift (≡⇒≃ (≡⇒→ (cong (λ B → B ≡ A)
                           (right-inverse-of (inverse Eq.id) A))
                     (cong id (refl A))))                              ≡⟨⟩

      lift (≡⇒≃ (≡⇒→ (cong (λ B → B ≡ A) (left-inverse-of Eq.id A))
                     (cong id (refl A))))                              ≡⟨ cong (λ eq → lift (≡⇒≃ (≡⇒→ (cong (λ B → B ≡ A) eq) (refl A))))
                                                                          left-inverse-of-id  ⟩
      lift (≡⇒≃ (≡⇒→ (cong (λ B → B ≡ A) (refl A)) (refl A)))          ≡⟨⟩

      lift (≡⇒≃ (≡⇒→ (refl (A ≡ A)) (refl A)))                         ≡⟨⟩

      lift (≡⇒≃ (refl A))                                              ≡⟨ refl _ ⟩∎

      lift Eq.id                                                       ∎

      where open _≃_

  ⟨0⟩ : ∀ {c} → Extractor (c ▻ Dep set)
  ⟨0⟩ {c} = record
    { Type                  = λ { (_ , A) → ↑ _ A }
    ; Type-cong             = λ { _ (_ , lift A≃B) → ↑-cong A≃B }
    ; Type-cong-reflexivity = λ { ass (I , A) →
        let open Assumptions ass; open _≃_ in

        lift-equality ext₁ (apply-ext ext₁ λ { (lift x) → cong lift (

          to (lower (reflexivityE ass c (Dep set) I A)) x  ≡⟨ cong (λ eq → to (lower eq) x) $ reflexivityE-set ass ⟩∎

          x                                                ∎ )})}
    }

------------------------------------------------------------------------
-- Examples

-- For examples, see
-- Univalence-axiom.Isomorphism-is-equality.More.Examples.
