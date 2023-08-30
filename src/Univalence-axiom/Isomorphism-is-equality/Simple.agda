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

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Univalence-axiom.Isomorphism-is-equality.Simple
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as B using (_↔_)
open Derived-definitions-and-properties eq
open import Equality.Decidable-UIP eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
  renaming (lower-extensionality to lower-ext)
open import Function-universe eq hiding (id) renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
open import Injection eq using (Injective)
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Nat eq
open import Preimage eq
open import Prelude as P hiding (id)
open import Univalence-axiom eq

------------------------------------------------------------------------
-- Universes with some extra stuff

-- A record type packing up some assumptions.

record Assumptions : Type₃ where
  field

    -- Univalence at three different levels.

    univ  : Univalence (# 0)
    univ₁ : Univalence (# 1)
    univ₂ : Univalence (# 2)

  opaque

    -- Extensionality.

    ext : ∀ {ℓ} → Extensionality ℓ (# 1)
    ext = dependent-extensionality univ₂ univ₁

    ext₁ : Extensionality (# 1) (# 1)
    ext₁ = ext

-- Universes with some extra stuff.

record Universe : Type₃ where

  -- Parameters.

  field

    -- Codes for something.

    U : Type₂

    -- Interpretation of codes.

    El : U → Type₁ → Type₁

    -- El a, seen as a predicate, respects equivalences.

    resp : ∀ a {B C} → B ≃ C → El a B → El a C

    -- The resp function respects identities (assuming univalence).

    resp-id : Assumptions → ∀ a {B} (x : El a B) → resp a Eq.id x ≡ x

  -- Derived definitions.

  -- A predicate that specifies what it means for an equivalence to be
  -- an isomorphism between two elements.

  Is-isomorphism : ∀ a {B C} → B ≃ C → El a B → El a C → Type₁
  Is-isomorphism a eq x y = resp a eq x ≡ y

  -- An alternative definition of Is-isomorphism, defined using
  -- univalence.

  Is-isomorphism′ : Assumptions →
                    ∀ a {B C} → B ≃ C → El a B → El a C → Type₁
  Is-isomorphism′ ass a eq x y = subst (El a) (≃⇒≡ univ₁ eq) x ≡ y
    where open Assumptions ass

  -- Every element is isomorphic to itself, transported along the
  -- isomorphism.

  isomorphic-to-itself :
    (ass : Assumptions) → let open Assumptions ass in
    ∀ a {B C} (eq : B ≃ C) x →
    Is-isomorphism a eq x (subst (El a) (≃⇒≡ univ₁ eq) x)
  isomorphic-to-itself ass a eq x =
    transport-theorem (El a) (resp a) (resp-id ass a) univ₁ eq x
    where open Assumptions ass

  -- Is-isomorphism and Is-isomorphism′ are isomorphic (assuming
  -- univalence).

  isomorphism-definitions-isomorphic :
    (ass : Assumptions) →
    ∀ a {B C} (eq : B ≃ C) {x y} →
    Is-isomorphism a eq x y ↔ Is-isomorphism′ ass a eq x y
  isomorphism-definitions-isomorphic ass a eq {x} {y} =
    Is-isomorphism      a eq x y  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ y) $ isomorphic-to-itself ass a eq x ⟩□
    Is-isomorphism′ ass a eq x y  □

------------------------------------------------------------------------
-- A universe-indexed family of classes of structures

module Class (Univ : Universe) where

  open Universe Univ

  -- Codes for structures.

  Code : Type₃
  Code =
    -- A code.
    Σ U λ a →

    -- A proposition.
    (C : Type₁) → El a C → Σ Type₁ λ P →
      -- The proposition should be propositional (assuming
      -- univalence).
      Assumptions → Is-proposition P

  -- Interpretation of the codes. The elements of "Instance c" are
  -- instances of the structure encoded by c.

  Instance : Code → Type₂
  Instance (a , P) =
    -- A carrier type.
    Σ Type₁ λ C →

    -- An element.
    Σ (El a C) λ x →

    -- The element should satisfy the proposition.
    proj₁ (P C x)

  -- The carrier type.

  Carrier : ∀ c → Instance c → Type₁
  Carrier _ X = proj₁ X

  -- The "element".

  element : ∀ c (X : Instance c) → El (proj₁ c) (Carrier c X)
  element _ X = proj₁ (proj₂ X)

  opaque

    -- One can prove that two instances of a structure are equal by
    -- proving that the carrier types and "elements" (suitably
    -- transported) are equal (assuming univalence).

    equality-pair-lemma :
      Assumptions →
      ∀ c {X Y : Instance c} →
      (X ≡ Y) ↔
      ∃ λ (eq : Carrier c X ≡ Carrier c Y) →
        subst (El (proj₁ c)) eq (element c X) ≡ element c Y
    equality-pair-lemma ass (a , P) {C , x , p} {D , y , q} =

      ((C , x , p) ≡ (D , y , q))                 ↔⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Σ-assoc ⟩

      (((C , x) , p) ≡ ((D , y) , q))             ↝⟨ inverse $ ignore-propositional-component (proj₂ (P D y) ass) ⟩

      ((C , x) ≡ (D , y))                         ↝⟨ inverse B.Σ-≡,≡↔≡ ⟩□

      (∃ λ (eq : C ≡ D) → subst (El a) eq x ≡ y)  □

  -- Structure isomorphisms.

  Isomorphic : ∀ c → Instance c → Instance c → Type₁
  Isomorphic (a , _) (C , x , _) (D , y , _) =
    Σ (C ≃ D) λ eq → Is-isomorphism a eq x y

  -- The type of isomorphisms between two instances of a structure
  -- is isomorphic to the type of equalities between the same
  -- instances (assuming univalence).
  --
  -- In short, isomorphism is isomorphic to equality.

  isomorphism-is-equality :
    Assumptions →
    ∀ c X Y → Isomorphic c X Y ↔ (X ≡ Y)
  isomorphism-is-equality ass (a , P) (C , x , p) (D , y , q) =

    (∃ λ (eq : C ≃ D) → resp a eq x ≡ y)                    ↝⟨ ∃-cong (λ eq → isomorphism-definitions-isomorphic ass a eq) ⟩

    (∃ λ (eq : C ≃ D) → subst (El a) (≃⇒≡ univ₁ eq) x ≡ y)  ↝⟨ inverse $
                                                                 Σ-cong (≡≃≃ univ₁) (λ eq → ≡⇒↝ _ $ sym $
                                                                   cong (λ eq → subst (El a) eq x ≡ y)
                                                                        (_≃_.left-inverse-of (≡≃≃ univ₁) eq)) ⟩
    (∃ λ (eq : C ≡ D) → subst (El a) eq x ≡ y)              ↝⟨ inverse $ equality-pair-lemma ass c ⟩□

    (X ≡ Y)                                                 □

    where
    open Assumptions ass

    c : Code
    c = a , P

    X : Instance c
    X = C , x , p

    Y : Instance c
    Y = D , y , q

  opaque
    unfolding equality-pair-lemma

    -- The type of (lifted) isomorphisms between two instances of a
    -- structure is equal to the type of equalities between the same
    -- instances (assuming univalence).
    --
    -- In short, isomorphism is equal to equality.

    isomorphic≡≡ :
      Assumptions →
      ∀ c {X Y} → ↑ (# 2) (Isomorphic c X Y) ≡ (X ≡ Y)
    isomorphic≡≡ ass c {X} {Y} =
      ≃⇒≡ univ₂ $ Eq.↔⇒≃ (
        ↑ _ (Isomorphic c X Y)  ↝⟨ B.↑↔ ⟩
        Isomorphic c X Y        ↝⟨ isomorphism-is-equality ass c X Y ⟩□
        (X ≡ Y)                 □)
      where open Assumptions ass

    -- The "first part" of the from component of
    -- isomorphism-is-equality is equal to a simple function.

    proj₁-from-isomorphism-is-equality :
      ∀ ass c X Y →
      proj₁ ∘ _↔_.from (isomorphism-is-equality ass c X Y) ≡
      elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y) (λ _ → Eq.id)
    proj₁-from-isomorphism-is-equality ass _ _ _ = apply-ext ext λ eq →

      ≡⇒≃ (proj₁ (Σ-≡,≡←≡ (proj₁ (Σ-≡,≡←≡
        (cong (λ { (x , (y , z)) → (x , y) , z }) eq)))))            ≡⟨ cong (≡⇒≃ ∘ proj₁ ∘ Σ-≡,≡←≡) $ proj₁-Σ-≡,≡←≡ _ ⟩

      ≡⇒≃ (proj₁ (Σ-≡,≡←≡ (cong proj₁
        (cong (λ { (x , (y , z)) → (x , y) , z }) eq))))             ≡⟨ cong (≡⇒≃ ∘ proj₁ ∘ Σ-≡,≡←≡) $
                                                                          cong-∘ proj₁ (λ { (x , (y , z)) → (x , y) , z }) _ ⟩
      ≡⇒≃ (proj₁ (Σ-≡,≡←≡ (cong (λ { (x , (y , z)) → x , y }) eq)))  ≡⟨ cong ≡⇒≃ $ proj₁-Σ-≡,≡←≡ _ ⟩

      ≡⇒≃ (cong proj₁ (cong (λ { (x , (y , z)) → x , y }) eq))       ≡⟨ cong ≡⇒≃ $ cong-∘ proj₁ (λ { (x , (y , z)) → x , y }) eq ⟩

      ≡⇒≃ (cong proj₁ eq)                                            ≡⟨ elim-cong _≃_ proj₁ _ ⟩∎

      elim (λ {X Y} _ → proj₁ X ≃ proj₁ Y) (λ _ → Eq.id) eq          ∎

      where open Assumptions ass

    -- In fact, the entire from component of isomorphism-is-equality
    -- is equal to a simple function.
    --
    -- The proof of this lemma is somewhat complicated. A much shorter
    -- proof can be constructed if El (proj₁ c) (proj₁ J) is a set
    -- (see
    -- Structure-identity-principle.from-isomorphism-is-equality′).

    from-isomorphism-is-equality :
      ∀ ass c X Y →
      _↔_.from (isomorphism-is-equality ass c X Y) ≡
      elim (λ {X Y} _ → Isomorphic c X Y)
           (λ { (_ , x , _) → Eq.id , resp-id ass (proj₁ c) x })
    from-isomorphism-is-equality ass (a , P) (C , x , p) _ =
      apply-ext ext (elim¹
        (λ eq → Σ-map ≡⇒≃ f (Σ-≡,≡←≡ (proj₁ (Σ-≡,≡←≡
                  (cong (λ { (C , (x , p)) → (C , x) , p }) eq)))) ≡
                elim (λ {X Y} _ → Isomorphic (a , P) X Y)
                     (λ { (_ , x , _) → Eq.id , resp-id ass a x })
                     eq)

        (Σ-map ≡⇒≃ f (Σ-≡,≡←≡ (proj₁ (Σ-≡,≡←≡
                        (cong (_↔_.to Σ-assoc) (refl (C , x , p))))))  ≡⟨ cong (Σ-map ≡⇒≃ f ∘ Σ-≡,≡←≡ ∘ proj₁ ∘ Σ-≡,≡←≡) $ cong-refl _ ⟩

         Σ-map ≡⇒≃ f (Σ-≡,≡←≡ (proj₁ (Σ-≡,≡←≡ (refl ((C , x) , p)))))  ≡⟨ cong (Σ-map ≡⇒≃ f ∘ Σ-≡,≡←≡ ∘ proj₁) Σ-≡,≡←≡-refl ⟩

         Σ-map ≡⇒≃ f (Σ-≡,≡←≡ (refl (C , x)))                          ≡⟨ cong (Σ-map ≡⇒≃ f) Σ-≡,≡←≡-refl ⟩

         (≡⇒≃ (refl C) , f (subst-refl (El a) x))                      ≡⟨ Σ-≡,≡→≡ ≡⇒≃-refl lemma₄ ⟩

         (Eq.id , resp-id ass a x)                                     ≡⟨ sym $ elim-refl (λ {X Y} _ → Isomorphic (a , P) X Y) _ ⟩∎

         elim (λ {X Y} _ → Isomorphic (a , P) X Y)
              (λ { (_ , x , _) → Eq.id , resp-id ass a x })
              (refl (C , x , p))                                       ∎))

      where
      open Assumptions ass

      f : ∀ {D} {y : El a D} {eq : C ≡ D} →
          subst (El a) eq x ≡ y →
          resp a (≡⇒≃ eq) x ≡ y
      f {y} {eq} eq′ =
        _↔_.from (≡⇒↝ _ $ cong (λ z → z ≡ y) $
                    transport-theorem (El a) (resp a) (resp-id ass a)
                                      univ₁ (≡⇒≃ eq) x)
           (_↔_.to (≡⇒↝ _ $ sym $ cong (λ eq → subst (El a) eq x ≡ y)
                      (_≃_.left-inverse-of (≡≃≃ univ₁) eq)) eq′)

      lemma₁ : ∀ {ℓ} {A B C : Type ℓ} {x} (eq₁ : B ≡ A) (eq₂ : C ≡ B) →
               _↔_.from (≡⇒↝ _ eq₂) (_↔_.to (≡⇒↝ _ (sym eq₁)) x) ≡
               _↔_.to (≡⇒↝ _ (sym (trans eq₂ eq₁))) x
      lemma₁ {x} eq₁ eq₂ =
        _↔_.from (≡⇒↝ _ eq₂) (_↔_.to (≡⇒↝ _ (sym eq₁)) x)      ≡⟨ sym $ cong (λ f → f (_↔_.to (≡⇒↝ _ (sym eq₁)) x)) $ ≡⇒↝-sym bijection ⟩
        _↔_.to (≡⇒↝ _ (sym eq₂)) (_↔_.to (≡⇒↝ _ (sym eq₁)) x)  ≡⟨ sym $ cong (λ f → f x) $ ≡⇒↝-trans bijection ⟩
        _↔_.to (≡⇒↝ _ (trans (sym eq₁) (sym eq₂))) x           ≡⟨ sym $ cong (λ eq → _↔_.to (≡⇒↝ _ eq) x) $ sym-trans _ _ ⟩∎
        _↔_.to (≡⇒↝ _ (sym (trans eq₂ eq₁))) x                 ∎

      lemma₂ : ∀ {a} {A : Type a} {x y z : A}
               (x≡y : x ≡ y) (y≡z : y ≡ z) →
               _↔_.to (≡⇒↝ _ (cong (λ x → x ≡ z) (sym x≡y))) y≡z ≡
               trans x≡y y≡z
      lemma₂ {y} {z} x≡y y≡z = elim₁
        (λ x≡y → _↔_.to (≡⇒↝ _ (cong (λ x → x ≡ z) (sym x≡y))) y≡z ≡
                 trans x≡y y≡z)
        (_↔_.to (≡⇒↝ _ (cong (λ x → x ≡ z) (sym (refl y)))) y≡z  ≡⟨ cong (λ eq → _↔_.to (≡⇒↝ _ (cong (λ x → x ≡ z) eq)) y≡z) sym-refl ⟩
         _↔_.to (≡⇒↝ _ (cong (λ x → x ≡ z) (refl y))) y≡z        ≡⟨ cong (λ eq → _↔_.to (≡⇒↝ _ eq) y≡z) $ cong-refl (λ x → x ≡ z) ⟩
         _↔_.to (≡⇒↝ _ (refl (y ≡ z))) y≡z                       ≡⟨ cong (λ f → _↔_.to f y≡z) ≡⇒↝-refl ⟩
         y≡z                                                     ≡⟨ sym $ trans-reflˡ _ ⟩∎
         trans (refl y) y≡z                                      ∎)
        x≡y

      lemma₃ :
        sym (trans (cong (λ z → z ≡ x) $
                      transport-theorem (El a) (resp a) (resp-id ass a)
                                        univ₁ (≡⇒≃ (refl C)) x)
               (cong (λ eq → subst (El a) eq x ≡ x)
                  (_≃_.left-inverse-of (≡≃≃ univ₁) (refl C)))) ≡
        cong (λ z → z ≡ x) (sym $
          trans (trans (cong (λ eq → resp a eq x) ≡⇒≃-refl)
                   (resp-id ass a x))
            (sym $ subst-refl (El a) x))
      lemma₃ =
        sym (trans (cong (λ z → z ≡ x) _)
               (cong (λ eq → subst (El a) eq x ≡ x) _))           ≡⟨ cong (λ eq → sym (trans (cong (λ z → z ≡ x)
                                                                                                (transport-theorem (El a) (resp a) (resp-id ass a)
                                                                                                                   univ₁ (≡⇒≃ (refl C)) x))
                                                                                         eq)) $ sym $
                                                                          cong-∘ (λ z → z ≡ x) (λ eq → subst (El a) eq x) _ ⟩
        sym (trans (cong (λ z → z ≡ x) _)
               (cong (λ z → z ≡ x)
                  (cong (λ eq → subst (El a) eq x) _)))           ≡⟨ cong sym $ sym $ cong-trans (λ z → z ≡ x) _ _ ⟩

        sym (cong (λ z → z ≡ x)
          (trans _ (cong (λ eq → subst (El a) eq x) _)))          ≡⟨ sym $ cong-sym (λ z → z ≡ x) _ ⟩

        cong (λ z → z ≡ x) (sym $
          trans (transport-theorem (El a) (resp a)
                   (resp-id ass a) univ₁ (≡⇒≃ (refl C)) x)
            (cong (λ eq → subst (El a) eq x) _))                  ≡⟨ cong (λ eq → cong (λ z → z ≡ x) (sym $
                                                                                    trans eq (cong (λ eq → subst (El a) eq x)
                                                                                                (_≃_.left-inverse-of (≡≃≃ univ₁) (refl C)))))
                                                                          (transport-theorem-≡⇒≃-refl (El a) (resp a) (resp-id ass a) univ₁ _) ⟩
        cong (λ z → z ≡ x) (sym $
          trans (trans (trans (trans (cong (λ eq → resp a eq x)
                                        ≡⇒≃-refl)
                                 (resp-id ass a x))
                          (sym $ subst-refl (El a) x))
                   (sym $ cong (λ eq → subst (El a) eq x)
                            (_≃_.left-inverse-of
                               (≡≃≃ univ₁) (refl C))))
            (cong (λ eq → subst (El a) eq x)
                  (_≃_.left-inverse-of (≡≃≃ univ₁) (refl C))))    ≡⟨ cong (cong (λ z → z ≡ x) ∘ sym) $
                                                                          trans-[trans-sym]- _ _ ⟩∎
        cong (λ z → z ≡ x) (sym $
           trans (trans (cong (λ eq → resp a eq x) ≡⇒≃-refl)
                    (resp-id ass a x))
             (sym $ subst-refl (El a) x))                         ∎

      lemma₄ : subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl
                     (f (subst-refl (El a) x)) ≡
               resp-id ass a x
      lemma₄ =
        subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl
          (f (subst-refl (El a) x))                                      ≡⟨ cong (subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl) $ lemma₁ _ _ ⟩

        subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl
          (_↔_.to (≡⇒↝ _ (sym (trans (cong (λ z → z ≡ x) $
                                        transport-theorem (El a)
                                          (resp a) (resp-id ass a)
                                          univ₁ (≡⇒≃ (refl C)) x)
                                 (cong (λ eq → subst (El a) eq x ≡ x)
                                    (_≃_.left-inverse-of
                                       (≡≃≃ univ₁) (refl C))))))
                  (subst-refl (El a) x))                                 ≡⟨ cong (λ eq → subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl
                                                                                           (_↔_.to (≡⇒↝ _ eq) (subst-refl (El a) x)))
                                                                                 lemma₃ ⟩
        subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl
          (_↔_.to (≡⇒↝ _
                     (cong (λ z → z ≡ x) $ sym
                        (trans (trans (cong (λ eq → resp a eq x)
                                         ≡⇒≃-refl)
                                  (resp-id ass a x))
                           (sym $ subst-refl (El a) x))))
                  (subst-refl (El a) x))                                 ≡⟨ cong (subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl) $ lemma₂ _ _ ⟩

        subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl
          (trans (trans (trans (cong (λ eq → resp a eq x) ≡⇒≃-refl)
                           (resp-id ass a x))
                    (sym $ subst-refl (El a) x))
             (subst-refl (El a) x))                                      ≡⟨ cong (λ eq → subst (λ eq → Is-isomorphism a eq x x) ≡⇒≃-refl eq)
                                                                                 (trans-[trans-sym]- _ _) ⟩
        subst (λ eq → resp a eq x ≡ x) ≡⇒≃-refl
          (trans (cong (λ eq → resp a eq x) ≡⇒≃-refl)
             (resp-id ass a x))                                          ≡⟨ subst-∘ (λ z → z ≡ x) (λ eq → resp a eq x) _ ⟩

        subst (λ z → z ≡ x)
          (cong (λ eq → resp a eq x) ≡⇒≃-refl)
          (trans (cong (λ eq → resp a eq x) ≡⇒≃-refl)
             (resp-id ass a x))                                          ≡⟨ cong (λ eq → subst (λ z → z ≡ x) eq
                                                                                           (trans (cong (λ eq → resp a eq x) ≡⇒≃-refl)
                                                                                              (resp-id ass a x))) $
                                                                                 sym $ sym-sym _ ⟩
        subst (λ z → z ≡ x)
          (sym $ sym $ cong (λ eq → resp a eq x) ≡⇒≃-refl)
          (trans (cong (λ eq → resp a eq x) ≡⇒≃-refl)
             (resp-id ass a x))                                          ≡⟨ subst-trans (sym $ cong (λ eq → resp a eq x) ≡⇒≃-refl) ⟩

        trans (sym $ cong (λ eq → resp a eq x) ≡⇒≃-refl)
          (trans (cong (λ eq → resp a eq x) ≡⇒≃-refl)
             (resp-id ass a x))                                          ≡⟨ sym $ trans-assoc _ _ _ ⟩

        trans (trans (sym $ cong (λ eq → resp a eq x) ≡⇒≃-refl)
                     (cong (λ eq → resp a eq x) ≡⇒≃-refl))
          (resp-id ass a x)                                              ≡⟨ cong (λ eq → trans eq _) $ trans-symˡ _ ⟩

        trans (refl (resp a Eq.id x)) (resp-id ass a x)                  ≡⟨ trans-reflˡ _ ⟩∎

        resp-id ass a x                                                  ∎

------------------------------------------------------------------------
-- A universe of non-recursive, simple types

-- Codes for types.

infixr 20 _⊗_
infixr 15 _⊕_
infixr 10 _⇾_

data U : Type₂ where
  id type     : U
  k           : Type₁ → U
  _⇾_ _⊗_ _⊕_ : U → U → U

-- Interpretation of types.

El : U → Type₁ → Type₁
El id      C = C
El type    C = Type
El (k A)   C = A
El (a ⇾ b) C = El a C → El b C
El (a ⊗ b) C = El a C × El b C
El (a ⊕ b) C = El a C ⊎ El b C

-- El a preserves logical equivalences.

cast : ∀ a {B C} → B ⇔ C → El a B ⇔ El a C
cast id      eq = eq
cast type    eq = Logical-equivalence.id
cast (k A)   eq = Logical-equivalence.id
cast (a ⇾ b) eq = →-cong _ (cast a eq) (cast b eq)
cast (a ⊗ b) eq = cast a eq ×-cong cast b eq
cast (a ⊕ b) eq = cast a eq ⊎-cong cast b eq

-- El a respects equivalences.

resp : ∀ a {B C} → B ≃ C → El a B → El a C
resp a eq = _⇔_.to (cast a (_≃_.logical-equivalence eq))

resp⁻¹ : ∀ a {B C} → B ≃ C → El a C → El a B
resp⁻¹ a eq = _⇔_.from (cast a (_≃_.logical-equivalence eq))

opaque

  -- The cast function respects identities (assuming extensionality).

  cast-id : Extensionality (# 1) (# 1) →
            ∀ a {B} → cast a (Logical-equivalence.id {A = B}) ≡
                      Logical-equivalence.id
  cast-id ext id      = refl _
  cast-id ext type    = refl _
  cast-id ext (k A)   = refl _
  cast-id ext (a ⇾ b) = cong₂ (→-cong _) (cast-id ext a) (cast-id ext b)
  cast-id ext (a ⊗ b) = cong₂ _×-cong_ (cast-id ext a) (cast-id ext b)
  cast-id ext (a ⊕ b) =
    cast a Logical-equivalence.id ⊎-cong cast b Logical-equivalence.id  ≡⟨ cong₂ _⊎-cong_ (cast-id ext a) (cast-id ext b) ⟩
    Logical-equivalence.id ⊎-cong Logical-equivalence.id                ≡⟨ cong₂ (λ f g → record { to = f; from = g })
                                                                                 (apply-ext ext [ refl ∘ inj₁ , refl ∘ inj₂ ])
                                                                                 (apply-ext ext [ refl ∘ inj₁ , refl ∘ inj₂ ]) ⟩∎
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
  ; resp-id = resp-id ∘ Assumptions.ext₁
  }

-- Let us use this universe below.

open Universe simple using (Is-isomorphism)
open Class simple

-- An alternative definition of "being an isomorphism".
--
-- This definition is in bijective correspondence with Is-isomorphism
-- (see below).

Is-isomorphism′ : ∀ a {B C} → B ≃ C → El a B → El a C → Type₁
Is-isomorphism′ id      eq = λ x y → _≃_.to eq x ≡ y
Is-isomorphism′ type    eq = λ X Y → ↑ _ (X ≃ Y)
Is-isomorphism′ (k A)   eq = λ x y → x ≡ y
Is-isomorphism′ (a ⇾ b) eq = Is-isomorphism′ a eq →-rel
                             Is-isomorphism′ b eq
Is-isomorphism′ (a ⊗ b) eq = Is-isomorphism′ a eq ×-rel
                             Is-isomorphism′ b eq
Is-isomorphism′ (a ⊕ b) eq = Is-isomorphism′ a eq ⊎-rel
                             Is-isomorphism′ b eq

-- An alternative definition of Isomorphic, using Is-isomorphism′
-- instead of Is-isomorphism.

Isomorphic′ : ∀ c → Instance c → Instance c → Type₁
Isomorphic′ (a , _) (C , x , _) (D , y , _) =
  Σ (C ≃ D) λ eq → Is-isomorphism′ a eq x y

-- El a preserves equivalences (assuming extensionality).
--
-- Note that _≃_.logical-equivalence (cast≃ ext a eq) is
-- (definitionally) equal to cast a (_≃_.logical-equivalence eq); this
-- property is used below.

cast≃ : Extensionality (# 1) (# 1) →
        ∀ a {B C} → B ≃ C → El a B ≃ El a C
cast≃ ext a {B} {C} B≃C = Eq.↔⇒≃ record
  { surjection = record
    { logical-equivalence = cast a B⇔C
    ; right-inverse-of    = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  B⇔C = _≃_.logical-equivalence B≃C

  cst : ∀ a → El a B ≃ El a C
  cst id      = B≃C
  cst type    = Eq.id
  cst (k A)   = Eq.id
  cst (a ⇾ b) = →-cong ext (cst a) (cst b)
  cst (a ⊗ b) = cst a ×-cong cst b
  cst (a ⊕ b) = cst a ⊎-cong cst b

  opaque

    -- The projection _≃_.logical-equivalence is homomorphic with
    -- respect to cast a/cst a.

    casts-related : ∀ a →
                    cast a (_≃_.logical-equivalence B≃C) ≡
                    _≃_.logical-equivalence (cst a)
    casts-related id      = refl _
    casts-related type    = refl _
    casts-related (k A)   = refl _
    casts-related (a ⇾ b) = cong₂ (→-cong _) (casts-related a)
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

  logical-equivalence-cast≃ :
    (ext : Extensionality (# 1) (# 1)) →
    ∀ a {B C} (eq : B ≃ C) →
    _≃_.logical-equivalence (cast≃ ext a eq) ≡
    cast a (_≃_.logical-equivalence eq)
  logical-equivalence-cast≃ _ _ _ = refl _

-- Alternative, shorter definition of cast≃, based on univalence.
--
-- This proof does not (at the time of writing) have the property that
-- _≃_.logical-equivalence (cast≃′ ass a eq) is definitionally equal
-- to cast a (_≃_.logical-equivalence eq).

cast≃′ : Assumptions → ∀ a {B C} → B ≃ C → El a B ≃ El a C
cast≃′ ass a eq =
  Eq.⟨ resp a eq
     , resp-is-equivalence (El a) (resp a) (resp-id ext₁ a) univ₁ eq
     ⟩
  where open Assumptions ass

opaque

  -- The two definitions of "being an isomorphism" are "isomorphic"
  -- (in bijective correspondence), assuming univalence.

  is-isomorphism-isomorphic :
    Assumptions →
    ∀ a {B C x y} (eq : B ≃ C) →
    Is-isomorphism a eq x y ↔ Is-isomorphism′ a eq x y

  is-isomorphism-isomorphic ass id {x} {y} eq =

    (_≃_.to eq x ≡ y)  □

  is-isomorphism-isomorphic ass type {x = X} {y = Y} eq =

    (X ≡ Y)      ↔⟨ ≡≃≃ univ ⟩

    (X ≃ Y)      ↝⟨ inverse B.↑↔ ⟩□

    ↑ _ (X ≃ Y)  □

    where open Assumptions ass

  is-isomorphism-isomorphic ass (k A) {x} {y} eq =

    (x ≡ y) □

  is-isomorphism-isomorphic ass (a ⇾ b) {x = f} {y = g} eq =

    (resp b eq ∘ f ∘ resp⁻¹ a eq ≡ g)                  ↝⟨ ∘from≡↔≡∘to ext₁ (cast≃ ext₁ a eq) ⟩

    (resp b eq ∘ f ≡ g ∘ resp a eq)                    ↔⟨ inverse $ Eq.extensionality-isomorphism ext₁ ⟩

    (∀ x → resp b eq (f x) ≡ g (resp a eq x))          ↝⟨ ∀-cong ext₁ (λ x →
                                                            ∀-intro (λ y _ → resp b eq (f x) ≡ g y) ext₁) ⟩
    (∀ x y → resp a eq x ≡ y → resp b eq (f x) ≡ g y)  ↝⟨ ∀-cong ext₁ (λ _ → ∀-cong ext₁ λ _ →
                                                            →-cong ext₁ (is-isomorphism-isomorphic ass a eq)
                                                                        (is-isomorphism-isomorphic ass b eq)) ⟩□
    (∀ x y → Is-isomorphism′ a eq x y →
             Is-isomorphism′ b eq (f x) (g y))         □

    where open Assumptions ass

  is-isomorphism-isomorphic ass (a ⊗ b) {x = x , u} {y = y , v} eq =

    ((resp a eq x , resp b eq u) ≡ (y , v))              ↝⟨ inverse ≡×≡↔≡ ⟩

    (resp a eq x ≡ y × resp b eq u ≡ v)                  ↝⟨ is-isomorphism-isomorphic ass a eq ×-cong
                                                            is-isomorphism-isomorphic ass b eq ⟩□
    Is-isomorphism′ a eq x y × Is-isomorphism′ b eq u v  □

    where open Assumptions ass

  is-isomorphism-isomorphic ass (a ⊕ b) {x = inj₁ x} {y = inj₁ y} eq =

    (inj₁ (resp a eq x) ≡ inj₁ y)  ↝⟨ inverse B.≡↔inj₁≡inj₁ ⟩

    (resp a eq x ≡ y)              ↝⟨ is-isomorphism-isomorphic ass a eq ⟩□

    Is-isomorphism′ a eq x y       □

    where open Assumptions ass

  is-isomorphism-isomorphic ass (a ⊕ b) {x = inj₂ x} {y = inj₂ y} eq =

    (inj₂ (resp b eq x) ≡ inj₂ y)  ↝⟨ inverse B.≡↔inj₂≡inj₂ ⟩

    (resp b eq x ≡ y)              ↝⟨ is-isomorphism-isomorphic ass b eq ⟩□

    Is-isomorphism′ b eq x y       □

    where open Assumptions ass

  is-isomorphism-isomorphic ass (a ⊕ b) {x = inj₁ x} {y = inj₂ y} eq =

    (inj₁ _ ≡ inj₂ _)  ↝⟨ inverse $ B.⊥↔uninhabited ⊎.inj₁≢inj₂ ⟩□

    ⊥                  □

  is-isomorphism-isomorphic ass (a ⊕ b) {x = inj₂ x} {y = inj₁ y} eq =

    (inj₂ _ ≡ inj₁ _)  ↝⟨ inverse $ B.⊥↔uninhabited (⊎.inj₁≢inj₂ ∘ sym) ⟩□

    ⊥                  □

  -- The two definitions of isomorphism are "isomorphic" (in bijective
  -- correspondence), assuming univalence.

  isomorphic-isomorphic :
    Assumptions →
    ∀ c X Y →
    Isomorphic c X Y ↔ Isomorphic′ c X Y
  isomorphic-isomorphic ass (a , _) (C , x , _) (D , y , _) =
    Σ (C ≃ D) (λ eq → Is-isomorphism  a eq x y)  ↝⟨ ∃-cong (λ eq → is-isomorphism-isomorphic ass a eq) ⟩
    Σ (C ≃ D) (λ eq → Is-isomorphism′ a eq x y)  □

------------------------------------------------------------------------
-- An example: monoids

monoid : Code
monoid =
  -- Binary operation.
  (id ⇾ id ⇾ id) ⊗

  -- Identity.
  id ,

  λ { C (_∙_ , e) →

       -- The carrier type is a set.
      (Is-set C ×

       -- Left and right identity laws.
       (∀ x → (e ∙ x) ≡ x) ×
       (∀ x → (x ∙ e) ≡ x) ×

       -- Associativity.
       (∀ x y z → (x ∙ (y ∙ z)) ≡ ((x ∙ y) ∙ z))) ,

       -- The laws are propositional (assuming extensionality).
      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (C-set , _) →
          ×-closure 1  (H-level-propositional ext₁ 2)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
                       (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set))) }}

-- The interpretation of the code is reasonable.

Instance-monoid :

  Instance monoid
    ≡
  Σ Type₁ λ C →
  Σ ((C → C → C) × C) λ { (_∙_ , e) →
  Is-set C ×
  (∀ x → (e ∙ x) ≡ x) ×
  (∀ x → (x ∙ e) ≡ x) ×
  (∀ x y z → (x ∙ (y ∙ z)) ≡ ((x ∙ y) ∙ z)) }

Instance-monoid = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-monoid :
  ∀ {C₁ _∙₁_ e₁ laws₁ C₂ _∙₂_ e₂ laws₂} →

  Isomorphic monoid (C₁ , (_∙₁_ , e₁) , laws₁)
                    (C₂ , (_∙₂_ , e₂) , laws₂)
    ≡
  Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
  ((λ x y → to (from x ∙₁ from y)) , to e₁) ≡ (_∙₂_ , e₂)

Isomorphic-monoid = refl _

-- Note that this definition of isomorphism is isomorphic to a more
-- standard one (assuming extensionality).

Isomorphism-monoid-isomorphic-to-standard :
  Extensionality (# 1) (# 1) →
  ∀ {C₁ _∙₁_ e₁ laws₁ C₂ _∙₂_ e₂ laws₂} →

  Isomorphic monoid (C₁ , (_∙₁_ , e₁) , laws₁)
                    (C₂ , (_∙₂_ , e₂) , laws₂)
    ↔
  Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
  (∀ x y → to (x ∙₁ y) ≡ (to x ∙₂ to y)) ×
  to e₁ ≡ e₂

Isomorphism-monoid-isomorphic-to-standard ext
  {C₁} {_∙₁_} {e₁} {laws₁} {C₂} {_∙₂_} {e₂} =

  (Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
   ((λ x y → to (from x ∙₁ from y)) , to e₁) ≡ (_∙₂_ , e₂))  ↝⟨ inverse $ Σ-cong (Eq.↔↔≃ ext (proj₁ laws₁)) (λ _ → _ □) ⟩

  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   ((λ x y → to (from x ∙₁ from y)) , to e₁) ≡ (_∙₂_ , e₂))  ↝⟨ inverse $ ∃-cong (λ _ → ≡×≡↔≡) ⟩

  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (λ x y → to (from x ∙₁ from y)) ≡ _∙₂_ ×
   to e₁ ≡ e₂)                                               ↔⟨ inverse $ ∃-cong (λ _ → Eq.extensionality-isomorphism ext ×-cong (_ □)) ⟩

  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (∀ x → (λ y → to (from x ∙₁ from y)) ≡ _∙₂_ x) ×
   to e₁ ≡ e₂)                                               ↔⟨ inverse $ ∃-cong (λ _ →
                                                                  ∀-cong ext (λ _ → Eq.extensionality-isomorphism ext)
                                                                    ×-cong
                                                                  (_ □)) ⟩
  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (∀ x y → to (from x ∙₁ from y) ≡ (x ∙₂ y)) ×
   to e₁ ≡ e₂)                                               ↔⟨ inverse $ ∃-cong (λ eq →
                                                                  Π-cong ext (Eq.↔⇒≃ eq) (λ x → Π-cong ext (Eq.↔⇒≃ eq) (λ y →
                                                                      ≡⇒≃ $ sym $ cong₂ (λ u v → _↔_.to eq (u ∙₁ v) ≡
                                                                                                 (_↔_.to eq x ∙₂ _↔_.to eq y))
                                                                                        (_↔_.left-inverse-of eq x)
                                                                                        (_↔_.left-inverse-of eq y)))
                                                                    ×-cong
                                                                  (_ □)) ⟩□
  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (∀ x y → to (x ∙₁ y) ≡ (to x ∙₂ to y)) ×
   to e₁ ≡ e₂)                                               □

------------------------------------------------------------------------
-- An example: posets

poset : Code
poset =
  -- The ordering relation.
  (id ⇾ id ⇾ type) ,

  λ C _≤_ →

     -- The carrier type is a set.
    (Is-set C ×

     -- The ordering relation is (pointwise) propositional.
     (∀ x y → Is-proposition (x ≤ y)) ×

     -- Reflexivity.
     (∀ x → x ≤ x) ×

     -- Transitivity.
     (∀ x y z → x ≤ y → y ≤ z → x ≤ z) ×

     -- Antisymmetry.
     (∀ x y → x ≤ y → y ≤ x → x ≡ y)) ,

    λ ass → let open Assumptions ass in
      [inhabited⇒+]⇒+ 0 λ { (C-set , ≤-prop , _) →
        ×-closure 1  (H-level-propositional ext₁ 2)
        (×-closure 1 (Π-closure ext₁                     1 λ _ →
                      Π-closure (lower-ext (# 0) _ ext₁) 1 λ _ →
                      H-level-propositional (lower-ext _ _ ext₁) 1)
        (×-closure 1 (Π-closure (lower-ext (# 0) _ ext₁) 1 λ _ →
                      ≤-prop _ _)
        (×-closure 1 (Π-closure ext₁                     1 λ _ →
                      Π-closure ext₁                     1 λ _ →
                      Π-closure (lower-ext (# 0) _ ext₁) 1 λ _ →
                      Π-closure (lower-ext _ _ ext₁)     1 λ _ →
                      Π-closure (lower-ext _ _ ext₁)     1 λ _ →
                      ≤-prop _ _)
                     (Π-closure ext₁                     1 λ _ →
                      Π-closure ext₁                     1 λ _ →
                      Π-closure ext                      1 λ _ →
                      Π-closure ext                      1 λ _ →
                      C-set)))) }

-- The interpretation of the code is reasonable. (Except, perhaps,
-- that the carrier type lives in Type₁ but the codomain of the
-- ordering relation is Type. In the corresponding example in
-- Univalence-axiom.Isomorphism-is-equality.Simple.Variant the carrier
-- type lives in Type.)

Instance-poset :

  Instance poset
    ≡
  Σ Type₁ λ C →
  Σ (C → C → Type) λ _≤_ →
  Is-set C ×
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
  ∀ {C₁ _≤₁_ laws₁ C₂ _≤₂_ laws₂} →

  Isomorphic poset (C₁ , _≤₁_ , laws₁) (C₂ , _≤₂_ , laws₂)
    ≡
  Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
  (λ a b → from a ≤₁ from b) ≡ _≤₂_

Isomorphic-poset = refl _

-- We can prove that this notion of isomorphism is isomorphic to the
-- usual notion of order isomorphism (assuming univalence).

Isomorphism-poset-isomorphic-to-order-isomorphism :
  Assumptions →
  ∀ {C₁ _≤₁_ laws₁ C₂ _≤₂_ laws₂} →

  Isomorphic poset (C₁ , _≤₁_ , laws₁) (C₂ , _≤₂_ , laws₂)
    ↔
  Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
  ∀ x y → (x ≤₁ y) ⇔ (to x ≤₂ to y)

Isomorphism-poset-isomorphic-to-order-isomorphism ass
  {C₁} {_≤₁_} {laws₁} {C₂} {_≤₂_} {laws₂} =

  (Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
   (λ a b → from a ≤₁ from b) ≡ _≤₂_)           ↝⟨ inverse $ Σ-cong (Eq.↔↔≃ ext₁ (proj₁ laws₁)) (λ _ → _ □) ⟩

  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (λ a b → from a ≤₁ from b) ≡ _≤₂_)           ↔⟨ inverse $ ∃-cong (λ _ → Eq.extensionality-isomorphism ext₁) ⟩

  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (∀ a → (λ b → from a ≤₁ from b) ≡ _≤₂_ a))   ↔⟨ inverse $ ∃-cong (λ _ → ∀-cong ext₁ λ _ → Eq.extensionality-isomorphism ext₁) ⟩

  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (∀ a b → (from a ≤₁ from b) ≡ (a ≤₂ b)))     ↔⟨ inverse $ ∃-cong (λ eq →
                                                     Π-cong ext₁ (Eq.↔⇒≃ eq) λ a → Π-cong ext₁ (Eq.↔⇒≃ eq) λ b →
                                                         ≡⇒≃ $ sym $ cong₂ (λ x y → (x ≤₁ y) ≡ (_↔_.to eq a ≤₂ _↔_.to eq b))
                                                                           (_↔_.left-inverse-of eq a)
                                                                           (_↔_.left-inverse-of eq b)) ⟩
  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (∀ a b → (a ≤₁ b) ≡ (to a ≤₂ to b)))         ↔⟨ ∃-cong (λ _ → ∀-cong ext₁ λ _ → ∀-cong ext₁ λ _ → ≡≃≃ univ) ⟩

  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (∀ a b → (a ≤₁ b) ≃ (to a ≤₂ to b)))         ↝⟨ inverse $ ∃-cong (λ _ → ∀-cong ext₁ λ _ → ∀-cong (lower-ext (# 0) _ ext₁) λ _ →
                                                     Eq.⇔↔≃ (lower-ext _ _ ext₁) (proj₁ (proj₂ laws₁) _ _)
                                                                                 (proj₁ (proj₂ laws₂) _ _)) ⟩□
  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   (∀ a b → (a ≤₁ b) ⇔ (to a ≤₂ to b)))         □

  where open Assumptions ass

-- The previous lemma implies that we can prove that the notion of
-- isomorphism that we get is /equal/ to the usual notion of order
-- isomorphism (assuming univalence).

Isomorphism-poset-equal-to-order-isomorphism :
  Assumptions →
  ∀ {C₁ _≤₁_ laws₁ C₂ _≤₂_ laws₂} →

  Isomorphic poset (C₁ , _≤₁_ , laws₁) (C₂ , _≤₂_ , laws₂)
    ≡
  Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
  ∀ x y → (x ≤₁ y) ⇔ (to x ≤₂ to y)
Isomorphism-poset-equal-to-order-isomorphism ass {laws₁} {laws₂} =
  ≃⇒≡ univ₁ $ Eq.↔⇒≃ $
    Isomorphism-poset-isomorphic-to-order-isomorphism ass
      {laws₁ = laws₁} {laws₂ = laws₂}
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
  ∀ {C₁ _≤₁_ laws₁ C₂ _≤₂_ laws₂} →

  Isomorphic′ poset (C₁ , _≤₁_ , laws₁) (C₂ , _≤₂_ , laws₂)
    ↔
  Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
  ∀ x y → (x ≤₁ y) ⇔ (to x ≤₂ to y)

Isomorphism′-poset-isomorphic-to-order-isomorphism ext
  {C₁} {_≤₁_} {laws₁} {C₂} {_≤₂_} {laws₂} =

  (Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
   ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≃ (b ≤₂ d)))  ↝⟨ inverse $ Σ-cong (Eq.↔↔≃ ext (proj₁ laws₁)) (λ _ → _ □) ⟩

  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   ∀ a b → to a ≡ b → ∀ c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≃ (b ≤₂ d)))  ↝⟨ inverse $ ∃-cong (λ _ → ∀-cong ext λ _ →
                                                                          ∀-intro (λ _ _ → _) ext) ⟩
  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   ∀ a c d → to c ≡ d → ↑ _ ((a ≤₁ c) ≃ (to a ≤₂ d)))                ↝⟨ inverse $ ∃-cong (λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                          ∀-intro (λ _ _ → _) ext) ⟩
  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   ∀ a c → ↑ _ ((a ≤₁ c) ≃ (to a ≤₂ to c)))                          ↝⟨ ∃-cong (λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                          B.↑↔) ⟩
  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   ∀ a c → (a ≤₁ c) ≃ (to a ≤₂ to c))                                ↝⟨ inverse $ ∃-cong (λ _ →
                                                                          ∀-cong ext λ _ → ∀-cong (lower-ext (# 0) _ ext) λ _ →
                                                                            Eq.⇔↔≃ (lower-ext _ _ ext) (proj₁ (proj₂ laws₁) _ _)
                                                                                                       (proj₁ (proj₂ laws₂) _ _)) ⟩□
  (Σ (C₁ ↔ C₂) λ eq → let open _↔_ eq in
   ∀ a c → (a ≤₁ c) ⇔ (to a ≤₂ to c))                                □

------------------------------------------------------------------------
-- An example: discrete fields

private

  -- Some lemmas used below.

  0* :
    {C : Type₁}
    (_+_ : C → C → C)
    (0# : C)
    (_*_ : C → C → C)
    (1# : C)
    (-_ : C → C) →
    (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) →
    (∀ x y → (x + y) ≡ (y + x)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) →
    (∀ x → (x + 0#) ≡ x) →
    (∀ x → (x * 1#) ≡ x) →
    (∀ x → (x + (- x)) ≡ 0#) →
    ∀ x → (0# * x) ≡ 0#
  0* _+_ 0# _*_ 1# -_ +-assoc +-comm *-comm *+ +0 *1 +- x =
    (0# * x)                  ≡⟨ sym $ +0 _ ⟩
    ((0# * x) + 0#)           ≡⟨ cong (_+_ _) $ sym $ +- _ ⟩
    ((0# * x) + (x + (- x)))  ≡⟨ +-assoc _ _ _ ⟩
    (((0# * x) + x) + (- x))  ≡⟨ cong (λ y → y + _) lemma ⟩
    (x + (- x))               ≡⟨ +- x ⟩∎
    0#                        ∎
    where
    lemma =
      ((0# * x) + x)         ≡⟨ cong (_+_ _) $ sym $ *1 _ ⟩
      ((0# * x) + (x * 1#))  ≡⟨ cong (λ y → y + (x * 1#)) $ *-comm _ _ ⟩
      ((x * 0#) + (x * 1#))  ≡⟨ sym $ *+ _ _ _ ⟩
      (x * (0# + 1#))        ≡⟨ cong (_*_ _) $ +-comm _ _ ⟩
      (x * (1# + 0#))        ≡⟨ cong (_*_ _) $ +0 _ ⟩
      (x * 1#)               ≡⟨ *1 _ ⟩∎
      x                      ∎

  dec-lemma₁ :
    {C : Type₁}
    (_+_ : C → C → C)
    (0# : C)
    (-_ : C → C) →
    (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) →
    (∀ x y → (x + y) ≡ (y + x)) →
    (∀ x → (x + 0#) ≡ x) →
    (∀ x → (x + (- x)) ≡ 0#) →
    (∀ x → Dec (x ≡ 0#)) →
    Decidable (_≡_ {A = C})
  dec-lemma₁ _+_ 0# -_ +-assoc +-comm +0 +- dec-0 x y =
    ⊎-map (λ x-y≡0 → x                  ≡⟨ sym $ +0 _ ⟩
                     (x + 0#)           ≡⟨ cong (_+_ _) $ sym $ +- _ ⟩
                     (x + (y + (- y)))  ≡⟨ cong (_+_ _) $ +-comm _ _ ⟩
                     (x + ((- y) + y))  ≡⟨ +-assoc _ _ _ ⟩
                     ((x + (- y)) + y)  ≡⟨ cong (λ x → x + _) x-y≡0 ⟩
                     (0# + y)           ≡⟨ +-comm _ _ ⟩
                     (y + 0#)           ≡⟨ +0 _ ⟩∎
                     y                  ∎)
          (λ x-y≢0 x≡y → x-y≢0 ((x + (- y))  ≡⟨ cong (_+_ _ ∘ -_) $ sym x≡y ⟩
                                (x + (- x))  ≡⟨ +- _ ⟩∎
                                0#           ∎))
          (dec-0 (x + (- y)))

  dec-lemma₂ :
    {C : Type₁}
    (_+_ : C → C → C)
    (0# : C)
    (_*_ : C → C → C)
    (1# : C)
    (-_ : C → C) →
    (_⁻¹ : C → ↑ (# 1) ⊤ ⊎ C) →
    (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) →
    (∀ x y → (x + y) ≡ (y + x)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) →
    (∀ x → (x + 0#) ≡ x) →
    (∀ x → (x * 1#) ≡ x) →
    (∀ x → (x + (- x)) ≡ 0#) →
    0# ≢ 1# →
    (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) →
    (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#) →
    Decidable (_≡_ {A = C})
  dec-lemma₂ _+_ 0# _*_ 1# -_ _⁻¹ +-assoc +-comm *-comm
             *+ +0 *1 +- 0≢1 ⁻¹₁ ⁻¹₂ =
    dec-lemma₁ _+_ 0# -_ +-assoc +-comm +0 +- dec-0
    where
    dec-0 : ∀ z → Dec (z ≡ 0#)
    dec-0 z with z ⁻¹ | ⁻¹₁ z | ⁻¹₂ z
    ... | inj₁ _   | hyp | _   = inj₁ (hyp (refl _))
    ... | inj₂ z⁻¹ | _   | hyp = inj₂ (λ z≡0 →
      0≢1 (0#          ≡⟨ sym $ 0* _+_ 0# _*_ 1# -_ +-assoc +-comm *-comm *+ +0 *1 +- _ ⟩
           (0# * z⁻¹)  ≡⟨ cong (λ x → x * _) $ sym z≡0 ⟩
           (z * z⁻¹)   ≡⟨ hyp z⁻¹ (refl _) ⟩∎
           1#          ∎))

  dec-lemma₃ :
    {C : Type₁}
    (_+_ : C → C → C)
    (0# : C)
    (-_ : C → C) →
    (_*_ : C → C → C)
    (1# : C) →
    (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) →
    (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) →
    (∀ x y → (x + y) ≡ (y + x)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x → (x + 0#) ≡ x) →
    (∀ x → (x * 1#) ≡ x) →
    (∀ x → (x + (- x)) ≡ 0#) →
    (∀ x → (∃ λ y → (x * y) ≡ 1#) Xor (x ≡ 0#)) →
    Decidable (_≡_ {A = C})
  dec-lemma₃ _+_ 0# -_ _*_ 1# +-assoc *-assoc +-comm *-comm +0 *1 +-
             inv-xor =
    dec-lemma₁ _+_ 0# -_ +-assoc +-comm +0 +-
               (λ x → [ inj₂ ∘ proj₂ , inj₁ ∘ proj₂ ] (inv-xor x))

  *-injective :
    {C : Type₁}
    (_*_ : C → C → C)
    (1# : C) →
    (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x → (x * 1#) ≡ x) →
    ∀ x → ∃ (λ y → (x * y) ≡ 1#) → Injective (_*_ x)
  *-injective _*_ 1# *-assoc *-comm *1 x (x⁻¹ , xx⁻¹≡1)
              {x = y₁} {y = y₂} xy₁≡xy₂ =
    y₁                ≡⟨ lemma y₁ ⟩
    (x⁻¹ * (x * y₁))  ≡⟨ cong (_*_ x⁻¹) xy₁≡xy₂ ⟩
    (x⁻¹ * (x * y₂))  ≡⟨ sym $ lemma y₂ ⟩∎
    y₂                ∎
    where
    lemma : ∀ y → y ≡ (x⁻¹ * (x * y))
    lemma y =
      y                ≡⟨ sym $ *1 _ ⟩
      (y * 1#)         ≡⟨ *-comm _ _ ⟩
      (1# * y)         ≡⟨ cong (λ x → x * y) $ sym xx⁻¹≡1 ⟩
      ((x * x⁻¹) * y)  ≡⟨ cong (λ x → x * y) $ *-comm _ _ ⟩
      ((x⁻¹ * x) * y)  ≡⟨ sym $ *-assoc _ _ _ ⟩∎
      (x⁻¹ * (x * y))  ∎

  inverse-propositional :
    {C : Type₁}
    (_*_ : C → C → C)
    (1# : C) →
    (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x → (x * 1#) ≡ x) →
    Is-set C →
    ∀ x → Is-proposition (∃ λ y → (x * y) ≡ 1#)
  inverse-propositional _*_ 1# *-assoc *-comm *1 C-set x =
    [inhabited⇒+]⇒+ 0 λ { inv →
    injection⁻¹-propositional
      (record { to        = _*_ x
              ; injective = *-injective _*_ 1# *-assoc *-comm *1 x inv
              })
      C-set 1# }

  proposition-lemma₁ :
    Extensionality (# 1) (# 1) →
    {C : Type₁}
    (0# : C)
    (_*_ : C → C → C)
    (1# : C) →
    (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x → (x * 1#) ≡ x) →
    Is-proposition (((x y : C) → x ≡ y ⊎ x ≢ y) ×
                    (∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#))
  proposition-lemma₁ ext 0# _*_ 1# *-assoc *-comm *1 =
    [inhabited⇒+]⇒+ 0 λ { (dec , _) →
    let C-set = decidable⇒set dec in
    ×-closure 1 (Π-closure ext 1 λ _ →
                 Π-closure ext 1 λ _ →
                 Dec-closure-propositional (lower-ext (# 0) _ ext)
                                           C-set)
                (Π-closure ext 1 λ x →
                 Π-closure ext 1 λ _ →
                 inverse-propositional _*_ 1# *-assoc *-comm *1
                                       C-set x) }

  proposition-lemma₂ :
    Extensionality (# 1) (# 1) →
    {C : Type₁}
    (_+_ : C → C → C)
    (0# : C)
    (-_ : C → C) →
    (_*_ : C → C → C)
    (1# : C) →
    (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) →
    (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) →
    (∀ x y → (x + y) ≡ (y + x)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x → (x + 0#) ≡ x) →
    (∀ x → (x * 1#) ≡ x) →
    (∀ x → (x + (- x)) ≡ 0#) →
    Is-proposition (∀ x → (∃ λ y → (x * y) ≡ 1#) Xor (x ≡ 0#))
  proposition-lemma₂ ext _+_ 0# -_ _*_ 1# +-assoc *-assoc +-comm *-comm
                     +0 *1 +- =
    [inhabited⇒+]⇒+ 0 λ inv-xor →
    let C-set = decidable⇒set $
                  dec-lemma₃ _+_ 0# -_ _*_ 1# +-assoc *-assoc
                             +-comm *-comm +0 *1 +- inv-xor in
    Π-closure ext 1 λ x →
    Xor-closure-propositional (lower-ext (# 0) _ ext)
      (inverse-propositional _*_ 1# *-assoc *-comm *1 C-set x)
      C-set

  proposition-lemma₃ :
    Extensionality (# 1) (# 1) →
    {C : Type₁}
    (_+_ : C → C → C)
    (0# : C)
    (_*_ : C → C → C)
    (1# : C) →
    (-_ : C → C) →
    (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) →
    (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) →
    (∀ x y → (x + y) ≡ (y + x)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) →
    (∀ x → (x + 0#) ≡ x) →
    (∀ x → (x * 1#) ≡ x) →
    (∀ x → (x + (- x)) ≡ 0#) →
    0# ≢ 1# →
    Is-proposition (Σ (C → ↑ _ ⊤ ⊎ C) λ _⁻¹ →
                      (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) ×
                      (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#))
  proposition-lemma₃ ext {C} _+_ 0# _*_ 1# -_ +-assoc *-assoc
                     +-comm *-comm *+ +0 *1 +- 0≢1
                     (inv , inv₁ , inv₂) (inv′ , inv₁′ , inv₂′) =
    _↔_.to (ignore-propositional-component
              (×-closure 1 (Π-closure ext 1 λ _ →
                            Π-closure ext 1 λ _ →
                            C-set)
                           (Π-closure ext 1 λ _ →
                            Π-closure ext 1 λ _ →
                            Π-closure ext 1 λ _ →
                            C-set)))
           (apply-ext ext inv≡inv′)
    where
    C-set : Is-set C
    C-set = decidable⇒set $
      dec-lemma₂ _+_ 0# _*_ 1# -_ inv +-assoc +-comm
                 *-comm *+ +0 *1 +- 0≢1 inv₁ inv₂

    01-lemma : ∀ x y → x ≡ 0# → (x * y) ≡ 1# → ⊥
    01-lemma x y x≡0 xy≡1 = 0≢1 (
      0#        ≡⟨ sym $ 0* _+_ 0# _*_ 1# -_ +-assoc +-comm *-comm *+ +0 *1 +- _ ⟩
      (0# * y)  ≡⟨ cong (λ x → x * _) $ sym x≡0 ⟩
      (x * y)   ≡⟨ xy≡1 ⟩∎
      1#        ∎)

    inv≡inv′ : ∀ x → inv x ≡ inv′ x
    inv≡inv′ x with inv  x | inv₁  x | inv₂  x
                  | inv′ x | inv₁′ x | inv₂′ x
    ... | inj₁ _   | _ | _   | inj₁ _    | _    | _ = refl _
    ... | inj₂ x⁻¹ | _ | hyp | inj₁ _    | hyp′ | _ = ⊥-elim $ 01-lemma x x⁻¹ (hyp′ (refl _)) (hyp x⁻¹ (refl _))
    ... | inj₁ _   | hyp | _ | inj₂ x⁻¹  | _ | hyp′ = ⊥-elim $ 01-lemma x x⁻¹ (hyp (refl _)) (hyp′ x⁻¹ (refl _))
    ... | inj₂ x⁻¹ | _ | hyp | inj₂ x⁻¹′ | _ | hyp′ =
      cong inj₂ $ *-injective _*_ 1# *-assoc *-comm *1 x
                              (x⁻¹ , hyp x⁻¹ (refl _))
        ((x * x⁻¹)   ≡⟨ hyp x⁻¹ (refl _) ⟩
         1#          ≡⟨ sym $ hyp′ x⁻¹′ (refl _) ⟩∎
         (x * x⁻¹′)  ∎)

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

  λ { C (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →

      (-- Associativity.
       (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) ×
       (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) ×

       -- Commutativity.
       (∀ x y → (x + y) ≡ (y + x)) ×
       (∀ x y → (x * y) ≡ (y * x)) ×

       -- Distributivity.
       (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) ×

       -- Identity laws.
       (∀ x → (x + 0#) ≡ x) ×
       (∀ x → (x * 1#) ≡ x) ×

       -- Additive inverse law.
       (∀ x → (x + (- x)) ≡ 0#) ×

       -- Zero and one are distinct.
       0# ≢ 1# ×

       -- Multiplicative inverse laws.
       (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) ×
       (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#)) ,

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (+-assoc , _ , +-comm , *-comm , *+ , +0 ,
                               *1 , +- , 0≢1 , ⁻¹₁ , ⁻¹₂) →
          let C-set : Is-set C
              C-set = decidable⇒set $
                        dec-lemma₂ _+_ 0# _*_ 1# -_ _⁻¹ +-assoc +-comm
                                   *-comm *+ +0 *1 +- 0≢1 ⁻¹₁ ⁻¹₂
          in
          ×-closure  1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure (lower-ext (# 0) (# 1) ext₁) 1 λ _ →
                        ⊥-propositional)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
                       (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)))))))))) }}

-- The interpretation of the code is reasonable.

Instance-discrete-field :

  Instance discrete-field
    ≡
  Σ Type₁ λ C →
  Σ ((C → C → C) × C × (C → C → C) × C × (C → C) × (C → ↑ _ ⊤ ⊎ C))
    λ { (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →
  (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) ×
  (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) ×
  (∀ x y → (x + y) ≡ (y + x)) ×
  (∀ x y → (x * y) ≡ (y * x)) ×
  (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) ×
  (∀ x → (x + 0#) ≡ x) ×
  (∀ x → (x * 1#) ≡ x) ×
  (∀ x → (x + (- x)) ≡ 0#) ×
  0# ≢ 1# ×
  (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) ×
  (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#) }

Instance-discrete-field = refl _

-- The notion of isomorphism that we get is reasonable.

Isomorphic-discrete-field :
  ∀ {C₁ _+₁_ 0₁ _*₁_ 1₁ -₁_ _⁻¹₁ laws₁
     C₂ _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ laws₂} →

  Isomorphic discrete-field
             (C₁ , (_+₁_ , 0₁ , _*₁_ , 1₁ , -₁_ , _⁻¹₁) , laws₁)
             (C₂ , (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂) , laws₂)
    ≡
  Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
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
  ∀ {C₁ _+₁_ 0₁ _*₁_ 1₁ -₁_ _⁻¹₁ laws₁
     C₂ _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ laws₂} →

  Isomorphic discrete-field
             (C₁ , (_+₁_ , 0₁ , _*₁_ , 1₁ , -₁_ , _⁻¹₁) , laws₁)
             (C₂ , (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_ , _⁻¹₂) , laws₂)
    ↔
  Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
  ((λ x y → to (from x +₁ from y)) ,
   to 0₁ ,
   (λ x y → to (from x *₁ from y)) ,
   to 1₁ ,
   (λ x → to (-₁ from x))) ≡
  (_+₂_ , 0₂ , _*₂_ , 1₂ , -₂_)

Isomorphic-discrete-field-isomorphic-to-one-without-⁻¹ ext
  {C₁} {_+₁_} {0₁} {_*₁_} {1₁} { -₁_} {_⁻¹₁}
  {_ , _ , _ , _ , _ , _ , _ , _ , _ , ⁻¹₁₁ , ⁻¹₁₂}
  {C₂} {_+₂_} {0₂} {_*₂_} {1₂} { -₂_} {_⁻¹₂}
  {+₂-assoc , *₂-assoc , +₂-comm , *₂-comm , *₂+₂ , +₂0₂ , *₂1₂ , +₂-₂ ,
   0₂≢1₂ , ⁻¹₂₁ , ⁻¹₂₂} =

  ∃-cong λ eq → let open _≃_ eq in

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
                                                              _⇔_.to contractible⇔↔⊤ $ propositional⇒inhabited⇒contractible
                                                                ⁻¹-set
                                                                (⁻¹-homo eq 0-homo *-homo 1-homo)) ⟩
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
  ⁻¹-set : Is-set (C₂ → ↑ _ ⊤ ⊎ C₂)
  ⁻¹-set =
    Π-closure ext 2 λ _ →
    ⊎-closure 0 (↑-closure 2 (mono (≤-step (≤-step ≤-refl))
                           ⊤-contractible))
                (decidable⇒set $
                   dec-lemma₂ _+₂_ 0₂ _*₂_ 1₂ -₂_ _⁻¹₂ +₂-assoc +₂-comm
                              *₂-comm *₂+₂ +₂0₂ *₂1₂ +₂-₂ 0₂≢1₂
                              ⁻¹₂₁ ⁻¹₂₂)

  ⁻¹-homo :
    (eq : C₁ ≃ C₂) → let open _≃_ eq in
    to 0₁ ≡ 0₂ →
    (λ x y → to (from x *₁ from y)) ≡ _*₂_ →
    to 1₁ ≡ 1₂ →
    (λ x → ⊎-map P.id to (from x ⁻¹₁)) ≡ _⁻¹₂
  ⁻¹-homo eq 0-homo *-homo 1-homo = cong proj₁ $
    proposition-lemma₃
      ext _+₂_ 0₂ _*₂_ 1₂ -₂_
      +₂-assoc *₂-assoc +₂-comm *₂-comm
      *₂+₂ +₂0₂ *₂1₂ +₂-₂ 0₂≢1₂
      ( (λ x → ⊎-map P.id to (from x ⁻¹₁))
      , (λ x x⁻¹₁≡₁ →
           let lemma =
                 (from x ⁻¹₁)                                  ≡⟨ [_,_] {C = λ z → z ≡ ⊎-map P.id from (⊎-map P.id to z)}
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
                 (from x ⁻¹₁)                                  ≡⟨ [_,_] {C = λ z → z ≡ ⊎-map P.id from (⊎-map P.id to z)}
                                                                        (λ _ → refl _)
                                                                        (λ _ → cong inj₂ $ sym $ left-inverse-of _)
                                                                        (from x ⁻¹₁) ⟩
                 ⊎-map P.id from (⊎-map P.id to (from x ⁻¹₁))  ≡⟨ cong (⊎-map P.id from) x⁻¹₁≡y ⟩∎
                 inj₂ (from y)                                 ∎
           in
           (x *₂ y)               ≡⟨ sym $ cong (λ _*_ → x * y) *-homo ⟩
           to (from x *₁ from y)  ≡⟨ cong to $ ⁻¹₁₂ (from x) (from y) lemma ⟩
           to 1₁                  ≡⟨ 1-homo ⟩∎
           1₂                     ∎)
      )
      (_⁻¹₂ , ⁻¹₂₁ , ⁻¹₂₂)
    where open _≃_ eq

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

  λ { C (_+_ , 0# , _*_ , 1# , -_) →

      (-- Associativity.
       (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) ×
       (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) ×

       -- Commutativity.
       (∀ x y → (x + y) ≡ (y + x)) ×
       (∀ x y → (x * y) ≡ (y * x)) ×

       -- Distributivity.
       (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) ×

       -- Identity laws.
       (∀ x → (x + 0#) ≡ x) ×
       (∀ x → (x * 1#) ≡ x) ×

       -- Additive inverse law.
       (∀ x → (x + (- x)) ≡ 0#) ×

       -- Zero and one are distinct.
       0# ≢ 1# ×

       -- Decidable equality.
       ((x y : C) → x ≡ y ⊎ x ≢ y) ×

       -- Non-zero elements are invertible.
       (∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#)) ,

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (_ , *-assoc , _ , *-comm , _ , _ , *1 ,
                               _ , _ , dec , _) →
          let C-set : Is-set C
              C-set = decidable⇒set dec
          in
          ×-closure  1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure (lower-ext (# 0) (# 1) ext₁) 1 λ _ →
                        ⊥-propositional)
          (proposition-lemma₁ ext₁ 0# _*_ 1#
                              *-assoc *-comm *1))))))))) }}

-- The two discrete field definitions above are isomorphic (assuming
-- extensionality).

Instance-discrete-field-isomorphic-to-Bridges-and-Richman's :
  Extensionality (# 1) (# 1) →

  Instance discrete-field
    ↔
  Instance discrete-field-à-la-Bridges-and-Richman

Instance-discrete-field-isomorphic-to-Bridges-and-Richman's ext =
  ∃-cong λ C →

  (Σ ((C → C → C) × C × (C → C → C) × C × (C → C) × (C → ↑ _ ⊤ ⊎ C))
      λ { (_+_ , 0# , _*_ , 1# , -_ , _⁻¹) →
          (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) ×
          (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) ×
          (∀ x y → (x + y) ≡ (y + x)) ×
          (∀ x y → (x * y) ≡ (y * x)) ×
          (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) ×
          (∀ x → (x + 0#) ≡ x) ×
          (∀ x → (x * 1#) ≡ x) ×
          (∀ x → (x + (- x)) ≡ 0#) ×
          0# ≢ 1# ×
          (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) ×
          (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#)})                  ↝⟨ lemma₁ _ _ _ _ _ _ _ ⟩

  (Σ ((C → C → C) × C × (C → C → C) × C × (C → C))
      λ { (_+_ , 0# , _*_ , 1# , -_) →
          Σ (C → ↑ _ ⊤ ⊎ C) λ _⁻¹ →
          (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) ×
          (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) ×
          (∀ x y → (x + y) ≡ (y + x)) ×
          (∀ x y → (x * y) ≡ (y * x)) ×
          (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) ×
          (∀ x → (x + 0#) ≡ x) ×
          (∀ x → (x * 1#) ≡ x) ×
          (∀ x → (x + (- x)) ≡ 0#) ×
          0# ≢ 1# ×
          (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) ×
          (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#)})                  ↝⟨ ∃-cong (λ _ → lemma₂ _ _ _ _ _ _ _ _ _ _ _) ⟩

  (Σ (((C → C → C) × C × (C → C → C) × C × (C → C)))
     λ { (_+_ , 0# , _*_ , 1# , -_) →
         (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) ×
         (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) ×
         (∀ x y → (x + y) ≡ (y + x)) ×
         (∀ x y → (x * y) ≡ (y * x)) ×
         (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) ×
         (∀ x → (x + 0#) ≡ x) ×
         (∀ x → (x * 1#) ≡ x) ×
         (∀ x → (x + (- x)) ≡ 0#) ×
         0# ≢ 1# ×
         Σ (C → ↑ _ ⊤ ⊎ C) λ _⁻¹ →
         (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) ×
         (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#) })                  ↝⟨ (∃-cong λ { (_+_ , 0# , _*_ , 1# , -_) →
                                                                          ∃-cong λ +-assoc →
                                                                          ∃-cong λ *-assoc →
                                                                          ∃-cong λ +-comm →
                                                                          ∃-cong λ *-comm →
                                                                          ∃-cong λ *+ →
                                                                          ∃-cong λ +0 →
                                                                          ∃-cong λ *1 →
                                                                          ∃-cong λ +- →
                                                                          ∃-cong λ 0≢1 →
                                                                          main-lemma C _+_ 0# _*_ 1# -_
                                                                                     +-assoc *-assoc +-comm *-comm *+ +0 *1 +- 0≢1 }) ⟩□
  (Σ ((C → C → C) × C × (C → C → C) × C × (C → C))
     λ { (_+_ , 0# , _*_ , 1# , -_) →
         (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) ×
         (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) ×
         (∀ x y → (x + y) ≡ (y + x)) ×
         (∀ x y → (x * y) ≡ (y * x)) ×
         (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) ×
         (∀ x → (x + 0#) ≡ x) ×
         (∀ x → (x * 1#) ≡ x) ×
         (∀ x → (x + (- x)) ≡ 0#) ×
         0# ≢ 1# ×
         ((x y : C) → x ≡ y ⊎ x ≢ y) ×
         (∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#) })                     □

  where
  main-lemma :
    (C : Type₁)
    (_+_ : C → C → C)
    (0# : C)
    (_*_ : C → C → C)
    (1# : C)
    (-_ : C → C) →
    (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) →
    (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) →
    (∀ x y → (x + y) ≡ (y + x)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) →
    (∀ x → (x + 0#) ≡ x) →
    (∀ x → (x * 1#) ≡ x) →
    (∀ x → (x + (- x)) ≡ 0#) →
    0# ≢ 1# →

    (Σ (C → ↑ _ ⊤ ⊎ C) λ _⁻¹ →
     (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) ×
     (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#))
      ↔
    (((x y : C) → x ≡ y ⊎ x ≢ y) ×
     (∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#))

  main-lemma C _+_ 0# _*_ 1# -_
             +-assoc *-assoc +-comm *-comm *+ +0 *1 +- 0≢1 =
    _≃_.bijection $
    Eq.⇔→≃
      (proposition-lemma₃ ext _+_ 0# _*_ 1# -_
                          +-assoc *-assoc +-comm *-comm
                          *+ +0 *1 +- 0≢1)
      (proposition-lemma₁ ext 0# _*_ 1# *-assoc *-comm *1)
      to
      from
    where
    To   = (((x y : C) → x ≡ y ⊎ x ≢ y) ×
            (∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#))
    From = Σ (C → ↑ _ ⊤ ⊎ C) λ _⁻¹ →
           (∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#) ×
           (∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#)

    to : From → To
    to (_⁻¹ , ⁻¹₁ , ⁻¹₂) = (dec , inv)
      where
      dec : Decidable (_≡_ {A = C})
      dec = dec-lemma₂ _+_ 0# _*_ 1# -_ _⁻¹ +-assoc +-comm *-comm *+
                       +0 *1 +- 0≢1 ⁻¹₁ ⁻¹₂

      inv : ∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#
      inv x x≢0 with x ⁻¹ | ⁻¹₁ x | ⁻¹₂ x
      ... | inj₁ _ | hyp | _   = ⊥-elim $ x≢0 (hyp (refl _))
      ... | inj₂ y | _   | hyp = y , hyp y (refl _)

    from : To → From
    from (dec , inv) = (_⁻¹ , ⁻¹₁ , ⁻¹₂)
      where
      _⁻¹ : C → ↑ _ ⊤ ⊎ C
      x ⁻¹ = ⊎-map (λ _ → _) (proj₁ ∘ inv x) (dec x 0#)

      ⁻¹₁ : ∀ x → (x ⁻¹) ≡ inj₁ (lift tt) → x ≡ 0#
      ⁻¹₁ x x⁻¹≡₁ with dec x 0#
      ... | inj₁ x≡0 = x≡0
      ... | inj₂ x≢0 = ⊥-elim $ ⊎.inj₁≢inj₂ (sym x⁻¹≡₁)

      ⁻¹₂ : ∀ x y → (x ⁻¹) ≡ inj₂ y → (x * y) ≡ 1#
      ⁻¹₂ x y x⁻¹≡y with dec x 0#
      ... | inj₁ x≡0 = ⊥-elim $ ⊎.inj₁≢inj₂ x⁻¹≡y
      ... | inj₂ x≢0 =
        (x * y)                  ≡⟨ cong (_*_ _) $ sym $ ⊎.cancel-inj₂ x⁻¹≡y ⟩
        (x * proj₁ (inv x x≢0))  ≡⟨ proj₂ (inv x x≢0) ⟩∎
        1#                       ∎

  lemma₁ : (A B C D E F : Type₁) (G : A × B × C × D × E × F → Type₁) →
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

  lemma₂ : (A B C D E F G H I J : Type₁) (K : A → Type₁) →
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

  λ { C (_+_ , 0# , _*_ , 1# , -_) →

      (-- Associativity.
       (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) ×
       (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) ×

       -- Commutativity.
       (∀ x y → (x + y) ≡ (y + x)) ×
       (∀ x y → (x * y) ≡ (y * x)) ×

       -- Distributivity.
       (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) ×

       -- Identity laws.
       (∀ x → (x + 0#) ≡ x) ×
       (∀ x → (x * 1#) ≡ x) ×

       -- Additive inverse law.
       (∀ x → (x + (- x)) ≡ 0#) ×

       -- An element is invertible xor it equals zero.
       (∀ x → (∃ λ y → (x * y) ≡ 1#) Xor (x ≡ 0#))) ,

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (+-assoc , *-assoc , +-comm , *-comm , _ ,
                               +0 , *1 , +- , inv-xor) →
          let C-set : Is-set C
              C-set = decidable⇒set $
                        dec-lemma₃ _+_ 0# -_ _*_ 1# +-assoc *-assoc
                                   +-comm *-comm +0 *1 +- inv-xor
          in
          ×-closure  1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        C-set)
          (proposition-lemma₂ ext₁ _+_ 0# -_ _*_ 1#
                              +-assoc *-assoc +-comm *-comm
                              +0 *1 +-)))))))) }}

-- nLab's definition of discrete fields is isomorphic to the variant
-- of Bridges and Richman's definition given above (assuming
-- extensionality, and assuming that I interpreted the informal
-- definitions correctly).

nLab's-isomorphic-to-Bridges-and-Richman's :
  Extensionality (# 1) (# 1) →

  Instance discrete-field-à-la-nLab
    ↔
  Instance discrete-field-à-la-Bridges-and-Richman

nLab's-isomorphic-to-Bridges-and-Richman's ext =
  ∃-cong λ C →
  ∃-cong λ { (_+_ , 0# , _*_ , 1# , -_) →
  ∃-cong λ +-assoc →
  ∃-cong λ *-assoc →
  ∃-cong λ +-comm →
  ∃-cong λ *-comm →
  ∃-cong λ *+ →
  ∃-cong λ +0 →
  ∃-cong λ *1 →
  ∃-cong λ +- →
  main-lemma C _+_ 0# _*_ 1# -_
             +-assoc *-assoc +-comm *-comm *+ +0 *1 +- }
  where
  main-lemma :
    (C : Type₁)
    (_+_ : C → C → C)
    (0# : C)
    (_*_ : C → C → C)
    (1# : C)
    (-_ : C → C) →
    (∀ x y z → (x + (y + z)) ≡ ((x + y) + z)) →
    (∀ x y z → (x * (y * z)) ≡ ((x * y) * z)) →
    (∀ x y → (x + y) ≡ (y + x)) →
    (∀ x y → (x * y) ≡ (y * x)) →
    (∀ x y z → (x * (y + z)) ≡ ((x * y) + (x * z))) →
    (∀ x → (x + 0#) ≡ x) →
    (∀ x → (x * 1#) ≡ x) →
    (∀ x → (x + (- x)) ≡ 0#) →

   (∀ x → (∃ λ y → (x * y) ≡ 1#) Xor (x ≡ 0#))
     ↔
   (0# ≢ 1# ×
    ((x y : C) → x ≡ y ⊎ x ≢ y) ×
    (∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#))
  main-lemma C _+_ 0# _*_ 1# -_
             +-assoc *-assoc +-comm *-comm *+ +0 *1 +- =
    _≃_.bijection $
    Eq.⇔→≃
      (proposition-lemma₂ ext _+_ 0# -_ _*_ 1#
                          +-assoc *-assoc +-comm *-comm
                          +0 *1 +-)
      (×-closure 1
         (¬-propositional (lower-ext (# 0) _ ext))
         (proposition-lemma₁ ext 0# _*_ 1# *-assoc
                             *-comm *1))
      to
      from
    where
    To   = 0# ≢ 1# ×
           ((x y : C) → x ≡ y ⊎ x ≢ y) ×
           (∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#)
    From = ∀ x → (∃ λ y → (x * y) ≡ 1#) Xor (x ≡ 0#)

    to : From → To
    to inv-xor = (0≢1 , dec , inv)
      where
      0≢1 : 0# ≢ 1#
      0≢1 0≡1 =
        [ (λ { (_        , 1≢0) → 1≢0 (sym 0≡1) })
        , (λ { (∄y[1y≡1] , _)   → ∄y[1y≡1] (1# , *1 1#) })
        ] (inv-xor 1#)

      dec : Decidable (_≡_ {A = C})
      dec = dec-lemma₃ _+_ 0# -_ _*_ 1# +-assoc *-assoc +-comm *-comm
                       +0 *1 +- inv-xor

      inv : ∀ x → x ≢ 0# → ∃ λ y → (x * y) ≡ 1#
      inv x x≢0 =
        [ proj₁
        , (λ { (_ , x≡0) → ⊥-elim (x≢0 x≡0) })
        ] (inv-xor x)

    from : To → From
    from (0≢1 , dec , inv) x =
      [ (λ x≡0 → inj₂ ( (λ { (y , xy≡1) → 0≢1 (0#        ≡⟨ sym $ 0* _+_ 0# _*_ 1# -_ +-assoc +-comm *-comm *+ +0 *1 +- y ⟩
                                               (0# * y)  ≡⟨ cong (λ x → x * y) $ sym x≡0 ⟩
                                               (x * y)   ≡⟨ xy≡1 ⟩∎
                                               1#        ∎) })
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
       (∀ u v w → (u + (v + w)) ≡ ((u + v) + w)) ×
       (∀ x y v → (x * (y * v)) ≡ ((x *F y) * v)) ×

       -- Commutativity.
       (∀ u v → (u + v) ≡ (v + u)) ×

       -- Distributivity.
       (∀ x u v → (x * (u + v)) ≡ ((x * u) + (x * v))) ×
       (∀ x y v → ((x +F y) * v) ≡ ((x * v) + (y * v))) ×

       -- Identity laws.
       (∀ v → (v + 0V) ≡ v) ×
       (∀ v → (1F * v) ≡ v) ×

       -- Inverse law.
       (∀ v → (v + (- v)) ≡ 0V)) ,

      λ ass → let open Assumptions ass in
        [inhabited⇒+]⇒+ 0 λ { (V-set , _) →
          ×-closure 1  (H-level-propositional ext₁ 2)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        V-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        V-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        V-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        V-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        Π-closure ext₁ 1 λ _ →
                        V-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        V-set)
          (×-closure 1 (Π-closure ext₁ 1 λ _ →
                        V-set)
                       (Π-closure ext₁ 1 λ _ →
                        V-set)))))))) }}

-- The interpretation of the code is reasonable.

Instance-vector-space :
  ∀ {F _+F_ 0F _*F_ 1F -F_ _⁻¹F laws} →

  Instance (vector-space
              (F , (_+F_ , 0F , _*F_ , 1F , -F_ , _⁻¹F) , laws))
    ≡
  Σ Type₁ λ V →
  Σ ((V → V → V) × (F → V → V) × V × (V → V))
    λ { (_+_ , _*_ , 0V , -_) →
  Is-set V ×
  (∀ u v w → (u + (v + w)) ≡ ((u + v) + w)) ×
  (∀ x y v → (x * (y * v)) ≡ ((x *F y) * v)) ×
  (∀ u v → (u + v) ≡ (v + u)) ×
  (∀ x u v → (x * (u + v)) ≡ ((x * u) + (x * v))) ×
  (∀ x y v → ((x +F y) * v) ≡ ((x * v) + (y * v))) ×
  (∀ v → (v + 0V) ≡ v) ×
  (∀ v → (1F * v) ≡ v) ×
  (∀ v → (v + (- v)) ≡ 0V) }

Instance-vector-space = refl _

-- The notion of isomorphism that we get is also reasonable.

Isomorphic-vector-space :
  ∀ {F V₁ _+₁_ _*₁_ 0₁ -₁_ laws₁
       V₂ _+₂_ _*₂_ 0₂ -₂_ laws₂} →

  Isomorphic (vector-space F)
             (V₁ , (_+₁_ , _*₁_ , 0₁ , -₁_) , laws₁)
             (V₂ , (_+₂_ , _*₂_ , 0₂ , -₂_) , laws₂)
    ≡
  Σ (V₁ ≃ V₂) λ eq → let open _≃_ eq in
  ((λ u v → to (from u +₁ from v)) ,
   (λ x v → to (x *₁ from v)) ,
   to 0₁ ,
   (λ x → to (-₁ from x))) ≡
  (_+₂_ , _*₂_ , 0₂ , -₂_)

Isomorphic-vector-space = refl _

------------------------------------------------------------------------
-- An example: sets equipped with fixpoint operators

set-with-fixpoint-operator : Code
set-with-fixpoint-operator =
  (id ⇾ id) ⇾ id ,

  λ C fix →

     -- The carrier type is a set.
    (Is-set C ×

     -- The fixpoint operator property.
     (∀ f → f (fix f) ≡ fix f)) ,

    λ ass → let open Assumptions ass in
      [inhabited⇒+]⇒+ 0 λ { (C-set , _) →
        ×-closure 1 (H-level-propositional ext₁ 2)
                    (Π-closure ext₁ 1 λ _ →
                     C-set) }

-- Some unfolding lemmas.

Instance-set-with-fixpoint-operator :

  Instance set-with-fixpoint-operator
    ≡
  Σ Type₁ λ C →
  Σ ((C → C) → C) λ fix →
  Is-set C ×
  (∀ f → f (fix f) ≡ fix f)

Instance-set-with-fixpoint-operator = refl _

Isomorphic-set-with-fixpoint-operator :
  ∀ {C₁ fix₁ laws₁ C₂ fix₂ laws₂} →

  Isomorphic set-with-fixpoint-operator
             (C₁ , fix₁ , laws₁) (C₂ , fix₂ , laws₂)
    ≡
  Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
  (λ f → to (fix₁ (λ x → from (f (to x))))) ≡ fix₂

Isomorphic-set-with-fixpoint-operator = refl _

Isomorphic′-set-with-fixpoint-operator :
  ∀ {C₁ fix₁ laws₁ C₂ fix₂ laws₂} →

  Isomorphic′ set-with-fixpoint-operator
              (C₁ , fix₁ , laws₁) (C₂ , fix₂ , laws₂)
    ≡
  Σ (C₁ ≃ C₂) λ eq → let open _≃_ eq in
  ∀ f g →
  (∀ x y → to x ≡ y → to (f x) ≡ g y) →
  to (fix₁ f) ≡ fix₂ g

Isomorphic′-set-with-fixpoint-operator = refl _
