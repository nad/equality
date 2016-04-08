------------------------------------------------------------------------
-- The equality can be turned into a groupoid which is sometimes
-- commutative
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Equality.Groupoid
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Equality.Tactic eq
open import Groupoid eq
open import Prelude hiding (id; _∘_)

------------------------------------------------------------------------
-- _≡_ comes with a groupoid structure

groupoid : ∀ {a} (A : Set a) → Groupoid a a
groupoid A = record
  { Object = A
  ; _∼_    = _≡_

  ; id  = refl _
  ; _∘_ = flip trans
  ; _⁻¹ = sym

  ; left-identity  = trans-reflʳ
  ; right-identity = trans-reflˡ
  ; assoc          = λ z≡u y≡z x≡y → trans-assoc x≡y y≡z z≡u
  ; left-inverse   = trans-symʳ
  ; right-inverse  = trans-symˡ
  }

------------------------------------------------------------------------
-- In some cases transitivity is commutative

-- This proof is based on an informal proof due to Thierry Coquand,
-- based on a result from homotopy theory.

module Transitivity-commutative
  {a} {A : Set a} (e : A) (_∙_ : A → A → A)
  (left-identity  : ∀ x → (e ∙ x) ≡ x)
  (right-identity : ∀ x → (x ∙ e) ≡ x)
  where

  open Groupoid (groupoid A) hiding (left-identity; right-identity)

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

      li : ∀ {x} → (e ∙ x) ≡ x
      li = left-identity _

      ri : ∀ {x} → (x ∙ e) ≡ x
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

  Ω : ℕ → ∀ {x} (X : Set x) → X → Set x
  Ω zero    X x = X
  Ω (suc n) X x = Ω-elem n x ≡ Ω-elem n x

  Ω-elem : ∀ n {x} {X : Set x} (x : X) → Ω n X x
  Ω-elem zero    x = x
  Ω-elem (suc n) x = refl (Ω-elem n x)

Ω[2+n]-commutative : ∀ {ℓ} {X : Set ℓ} {x : X} {n} →
  let open Groupoid (groupoid (Ω (2 + n) X x)) in
  (p q : Ω (3 + n) X x) → p ∘ q ≡ q ∘ p
Ω[2+n]-commutative {X = X} {x} {n} p q =
  Transitivity-commutative.commutative
    id _∘_ left-identity right-identity p q
  where open Groupoid (groupoid (Ω (1 + n) X x))
