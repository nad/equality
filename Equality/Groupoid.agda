------------------------------------------------------------------------
-- The equality can be turned into a groupoid which is sometimes
-- commutative
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

open import Equality

module Equality.Groupoid
  {reflexive} (eq : Equality-with-J reflexive) where

open Derived-definitions-and-properties eq
import Equality.Tactic as Tactic; open Tactic eq
open import Prelude hiding (id; _∘_)

------------------------------------------------------------------------
-- Groupoids

-- Using _≡_ as the underlying equality.

record Groupoid ℓ : Set (suc ℓ) where
  infix  8 _⁻¹
  infixr 7 _∘_
  infix  4 _∼_
  field
    Object : Set ℓ
    _∼_    : Object → Object → Set

    id  : ∀ {x} → x ∼ x
    _∘_ : ∀ {x y z} → y ∼ z → x ∼ y → x ∼ z
    _⁻¹ : ∀ {x y} → x ∼ y → y ∼ x

    left-identity  : ∀ {x y} (p : x ∼ y) → id ∘ p ≡ p
    right-identity : ∀ {x y} (p : x ∼ y) → p ∘ id ≡ p
    assoc          : ∀ {w x y z} (p : y ∼ z) (q : x ∼ y) (r : w ∼ x) →
                     p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    left-inverse   : ∀ {x y} (p : x ∼ y) → p ⁻¹ ∘ p ≡ id
    right-inverse  : ∀ {x y} (p : x ∼ y) → p ∘ p ⁻¹ ≡ id

  -- Note that this definition should perhaps contain more coherence
  -- properties: we have not assumed that _≡_ is proof-irrelevant.

  -- Some derived properties.

  abstract

    -- The identity is an identity for the inverse operator as well.

    identity : ∀ {x} → id {x = x} ⁻¹ ≡ id
    identity =
      id ⁻¹       ≡⟨ sym $ right-identity (id ⁻¹) ⟩
      id ⁻¹ ∘ id  ≡⟨ left-inverse id ⟩∎
      id          ∎

    -- The inverse operator is idempotent.

    idempotent : ∀ {x y} (p : x ∼ y) → p ⁻¹ ⁻¹ ≡ p
    idempotent p =
      p ⁻¹ ⁻¹               ≡⟨ sym $ right-identity (p ⁻¹ ⁻¹) ⟩
      p ⁻¹ ⁻¹ ∘ id          ≡⟨ sym $ cong (_∘_ (p ⁻¹ ⁻¹)) (left-inverse p) ⟩
      p ⁻¹ ⁻¹ ∘ (p ⁻¹ ∘ p)  ≡⟨ assoc _ _ _ ⟩
      (p ⁻¹ ⁻¹ ∘ p ⁻¹) ∘ p  ≡⟨ cong (λ q → q ∘ p) (left-inverse (p ⁻¹)) ⟩
      id ∘ p                ≡⟨ left-identity p ⟩∎
      p                     ∎

------------------------------------------------------------------------
-- _≡_ comes with a groupoid structure

groupoid : (A : Set) → Groupoid zero
groupoid A = record
  { Object = A
  ; _∼_    = _≡_

  ; id  = refl _
  ; _∘_ = flip trans
  ; _⁻¹ = sym

  ; left-identity  = left-identity
  ; right-identity = right-identity
  ; assoc          = assoc
  ; left-inverse   = left-inverse
  ; right-inverse  = right-inverse
  }
  where
  abstract
    left-identity : ∀ {x y} (p : x ≡ y) → trans p (refl _) ≡ p
    left-identity p = prove (Trans (Lift p) Refl) (Lift p) (refl _)

    right-identity : ∀ {x y} (p : x ≡ y) → trans (refl _) p ≡ p
    right-identity = λ p →
      prove (Trans Refl (Lift p)) (Lift p) (refl _)

    assoc : ∀ {w x y z} (p : y ≡ z) (q : x ≡ y) (r : w ≡ x) →
            trans (trans r q) p ≡ trans r (trans q p)
    assoc = λ p q r →
      prove (Trans (Trans (Lift r) (Lift q)) (Lift p))
            (Trans (Lift r) (Trans (Lift q) (Lift p)))
            (refl _)

    left-inverse : ∀ {x y} (p : x ≡ y) → trans p (sym p) ≡ refl _
    left-inverse =
      elim (λ p → trans p (sym p) ≡ refl _)
           (λ _ → prove (Trans Refl (Sym Refl)) Refl (refl _))

    right-inverse : ∀ {x y} (p : x ≡ y) → trans (sym p) p ≡ refl _
    right-inverse =
      elim (λ p → trans (sym p) p ≡ refl _)
           (λ _ → prove (Trans (Sym Refl) Refl) Refl (refl _))

------------------------------------------------------------------------
-- In some cases transitivity is commutative

-- This proof is based on an informal proof due to Thierry Coquand,
-- based on a result from homotopy theory.

module Transitivity-commutative
  {A : Set} (e : A) (_∙_ : A → A → A)
  (left-identity  : ∀ x → e ∙ x ≡ x)
  (right-identity : ∀ x → x ∙ e ≡ x)
  where

  open Groupoid (groupoid A)

  abstract

    commutative : (p q : e ≡ e) → p ∘ q ≡ q ∘ p
    commutative p q =
      p ∘ q                                 ≡⟨ cong (_∘_ p) (lem₁ _) ⟩
      p ∘ (ri ∘ li ⁻¹ ∘ q′ ∘ li ∘ ri ⁻¹)    ≡⟨ prove (Trans (Trans (Trans (Trans (Trans (Sym (Lift ri)) (Lift li)) (Lift q′))
                                                                          (Sym (Lift li))) (Lift ri)) (Lift p))
                                                     (Trans (Trans (Sym (Lift ri))
                                                                              (Trans (Trans (Lift li) (Lift q′)) (Sym (Lift li))))
                                                            (Trans (Lift ri) (Lift p)))
                                                     (refl _) ⟩
      (p ∘ ri) ∘ (li ⁻¹ ∘ q′ ∘ li) ∘ ri ⁻¹  ≡⟨ cong₂ (λ p q → p ∘ q ∘ ri ⁻¹) (lem₂ _) (lem₃ _) ⟩
      (ri ∘ lc p) ∘ rc q′ ∘ ri ⁻¹           ≡⟨ prove (Trans (Trans (Sym (Lift ri)) (Lift (rc q′))) (Trans (Lift (lc p)) (Lift ri)))
                                                     (Trans (Trans (Sym (Lift ri)) (Trans (Lift (rc q′)) (Lift (lc p)))) (Lift ri))
                                                     (refl _) ⟩
      ri ∘ (lc p ∘ rc q′) ∘ ri ⁻¹           ≡⟨ cong (λ p → ri ∘ p ∘ ri ⁻¹) (lem₄ _ _) ⟩
      ri ∘ (rc q′ ∘ lc p) ∘ ri ⁻¹           ≡⟨ prove (Trans (Trans (Sym (Lift ri)) (Trans (Lift (lc p)) (Lift (rc q′)))) (Lift ri))
                                                     (Trans (Trans (Trans (Sym (Lift ri)) (Lift (lc p))) (Lift (rc q′))) (Lift ri))
                                                     (refl _) ⟩
      ri ∘ rc q′ ∘ (lc p ∘ ri ⁻¹)           ≡⟨ cong₂ (λ p q → ri ∘ p ∘ q) (sym (lem₃ _)) (lem₅ _) ⟩
      ri ∘ (li ⁻¹ ∘ q′ ∘ li) ∘ (ri ⁻¹ ∘ p)  ≡⟨ prove (Trans (Trans (Trans (Lift p) (Sym (Lift ri)))
                                                                   (Trans (Trans (Lift li) (Lift q′)) (Sym (Lift li))))
                                                            (Lift ri))
                                                     (Trans (Lift p) (Trans (Trans (Trans (Trans (Sym (Lift ri)) (Lift li)) (Lift q′))
                                                                                   (Sym (Lift li)))
                                                                            (Lift ri)))
                                                     (refl _) ⟩
      (ri ∘ li ⁻¹ ∘ q′ ∘ li ∘ ri ⁻¹) ∘ p    ≡⟨ cong (λ q → q ∘ p) (sym (lem₁ _)) ⟩∎
      q ∘ p                                 ∎
      where

      -- Abbreviations.

      li : ∀ {x} → e ∙ x ≡ x
      li = left-identity _

      ri : ∀ {x} → x ∙ e ≡ x
      ri = right-identity _

      q′ : e ≡ e
      q′ = li ∘ ri ⁻¹ ∘ q ∘ ri ∘ li ⁻¹

      lc : ∀ {x y} → x ≡ y → (x ∙ e) ≡ (y ∙ e)
      lc = cong (λ x → (x ∙ e))

      rc : ∀ {x y} → x ≡ y → (e ∙ x) ≡ (e ∙ y)
      rc = cong (λ y → (e ∙ y))

      -- Lemmas.

      lem₁ : (p : e ≡ e) →
             p ≡ ri ∘ li ⁻¹ ∘ (li ∘ ri ⁻¹ ∘ p ∘ ri ∘ li ⁻¹) ∘ li ∘ ri ⁻¹
      lem₁ p =
        p                                                          ≡⟨ prove (Lift p) (Trans (Trans Refl (Lift p)) Refl) (refl _) ⟩
        refl _ ∘ p ∘ refl _                                        ≡⟨ sym (cong₂ (λ q r → q ∘ p ∘ r)
                                                                                 (right-inverse _) (right-inverse _)) ⟩
        (ri ∘ ri ⁻¹) ∘ p ∘ (ri ∘ ri ⁻¹)                            ≡⟨ prove (Trans (Trans (Trans (Sym (Lift ri)) (Lift ri)) (Lift p))
                                                                                   (Trans (Sym (Lift ri)) (Lift ri)))
                                                                            (Trans (Trans (Trans (Trans (Trans (Trans
                                                                               (Sym (Lift ri)) Refl) (Lift ri)) (Lift p))
                                                                               (Sym (Lift ri))) Refl) (Lift ri))
                                                                            (refl _) ⟩
        ri ∘ refl _ ∘ ri ⁻¹ ∘ p ∘ ri ∘ refl _ ∘ ri ⁻¹              ≡⟨ sym (cong₂ (λ q r → ri ∘ q ∘ ri ⁻¹ ∘ p ∘ ri ∘ r ∘ ri ⁻¹)
                                                                                 (left-inverse _) (left-inverse _)) ⟩
        ri ∘ (li ⁻¹ ∘ li) ∘ ri ⁻¹ ∘ p ∘ ri ∘ (li ⁻¹ ∘ li) ∘ ri ⁻¹  ≡⟨ prove (Trans (Trans (Trans (Trans (Trans (Trans
                                                                               (Sym (Lift ri)) (Trans (Lift li) (Sym (Lift li))))
                                                                               (Lift ri)) (Lift p)) (Sym (Lift ri)))
                                                                               (Trans (Lift li) (Sym (Lift li)))) (Lift ri))
                                                                            (Trans (Trans (Trans (Trans
                                                                               (Sym (Lift ri)) (Lift li))
                                                                               (Trans (Trans (Trans (Trans
                                                                                  (Sym (Lift li)) (Lift ri)) (Lift p)) (Sym (Lift ri)))
                                                                                  (Lift li))) (Sym (Lift li))) (Lift ri))
                                                                            (refl _) ⟩∎
        ri ∘ li ⁻¹ ∘ (li ∘ ri ⁻¹ ∘ p ∘ ri ∘ li ⁻¹) ∘ li ∘ ri ⁻¹    ∎

      lem₂ : ∀ {x y} (p : x ≡ y) → p ∘ ri ≡ ri ∘ lc p
      lem₂ = elim (λ p → p ∘ ri ≡ ri ∘ lc p) λ _ →
        prove (Trans (Lift ri) Refl)
              (Trans (Cong (λ x → (x ∙ e)) Refl) (Lift ri))
              (refl _)

      lem₃ : ∀ {x y} (p : x ≡ y) → li ⁻¹ ∘ p ∘ li ≡ rc p
      lem₃ = elim (λ p → li ⁻¹ ∘ p ∘ li ≡ rc p) λ x →
        li ⁻¹ ∘ refl x ∘ li  ≡⟨ prove (Trans (Trans (Lift li) Refl) (Sym (Lift li)))
                                      (Trans (Lift li) (Sym (Lift li)))
                                      (refl _) ⟩
        li ⁻¹ ∘ li           ≡⟨ left-inverse _ ⟩
        refl (e ∙ x)         ≡⟨ prove Refl (Cong (λ y → (e ∙ y)) Refl) (refl _) ⟩∎
        rc (refl x)          ∎

      lem₄ : (p q : e ≡ e) → lc p ∘ rc q ≡ rc q ∘ lc p
      lem₄ p q = elim
        (λ {x y} x≡y → lc x≡y ∘ cong (λ z → (x ∙ z)) q ≡
                       cong (λ z → (y ∙ z)) q ∘ lc x≡y)
        (λ x → prove (Trans (Cong (λ z → x ∙ z) (Lift q))
                            (Cong (λ x → x ∙ e) Refl))
                     (Trans (Cong (λ x → x ∙ e) Refl)
                            (Cong (λ z → x ∙ z) (Lift q)))
                     (refl _))
        p

      lem₅ : ∀ {x y} (p : x ≡ y) → lc p ∘ ri ⁻¹ ≡ ri ⁻¹ ∘ p
      lem₅ = elim (λ p → lc p ∘ ri ⁻¹ ≡ ri ⁻¹ ∘ p) λ _ →
        prove (Trans (Sym (Lift ri)) (Cong (λ x → (x ∙ e)) Refl))
              (Trans Refl (Sym (Lift ri)))
              (refl _)

-- In particular, groupoid (Ω n X x) is commutative for n greater than
-- or equal to 2.

mutual

  Ω : ℕ → (X : Set) → X → Set
  Ω zero    X x = X
  Ω (suc n) X x = Ω-elem n x ≡ Ω-elem n x

  Ω-elem : ∀ n {X} (x : X) → Ω n X x
  Ω-elem zero    x = x
  Ω-elem (suc n) x = refl (Ω-elem n x)

Ω[2+n]-commutative : ∀ {X} {x : X} {n} →
  let open Groupoid (groupoid (Ω (2 + n) X x)) in
  ∀ p q → p ∘ q ≡ q ∘ p
Ω[2+n]-commutative p q =
  Transitivity-commutative.commutative
    id _∘_ left-identity right-identity p q
  where open Groupoid (groupoid _)

------------------------------------------------------------------------
-- More lemmas

abstract

  -- A fusion law for subst.

  subst-subst :
    {A : Set} (P : A → Set)
    {x y z : A} (x≡y : x ≡ y) (y≡z : y ≡ z) (p : P x) →
    subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
  subst-subst P x≡y y≡z p =
    elim (λ {x y} x≡y → ∀ {z} (y≡z : y ≡ z) p →
            subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p)
         (λ x y≡z p →
            subst P y≡z (subst P (refl x) p)  ≡⟨ cong (subst P y≡z) $ subst-refl P p ⟩
            subst P y≡z p                     ≡⟨ cong (λ q → subst P q p) $
                                                      (prove (Lift y≡z)
                                                             (Trans Refl (Lift y≡z))
                                                             (refl _)) ⟩∎
            subst P (trans (refl x) y≡z) p    ∎)
         x≡y y≡z p

  -- Substitutivity and symmetry sometimes cancel each other out.

  subst-subst-sym :
    {A : Set} (P : A → Set) {x y : A} (x≡y : x ≡ y) (p : P y) →
    subst P x≡y (subst P (sym x≡y) p) ≡ p
  subst-subst-sym P {y = y} x≡y p =
    subst P x≡y (subst P (sym x≡y) p)  ≡⟨ subst-subst P _ _ _ ⟩
    subst P (trans (sym x≡y) x≡y) p    ≡⟨ cong (λ q → subst P q p) $
                                               Groupoid.right-inverse (groupoid _) x≡y ⟩
    subst P (refl y) p                 ≡⟨ subst-refl P p ⟩∎
    p                                  ∎
