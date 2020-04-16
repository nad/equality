------------------------------------------------------------------------
-- Unit tests for Tactic.By.Parametrised
------------------------------------------------------------------------

-- Nothing is exported from this module.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Tactic.By.Parametrised.Tests
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Maybe eq
open import Monad eq
open import TC-monad eq

open import Tactic.By.Parametrised eq

------------------------------------------------------------------------
-- Some unit tests

private

  module Tests
    (assumption : 48 ≡ 42)
    (lemma      : ∀ n → n + 8 ≡ n + 2)
    (f          : ℕ → ℕ → ℕ → ℕ)
    where

    g : ℕ → ℕ → ℕ → ℕ
    g zero    _ _ = 12
    g (suc _) _ _ = 12

    fst : ∀ {a b} {A : Set a} {B : A → Set b} →
          Σ A B → A
    fst = proj₁

    {-# NOINLINE fst #-}

    test₁ : ⟨ 40 + 2 ⟩ ≡ 42
    test₁ = ⟨by⟩ refl

    test₂ : 48 ≡ 42 → ⟨ 42 ⟩ ≡ 48
    test₂ eq = ⟨by⟩ eq

    test₃ : (f : ℕ → ℕ) → f ⟨ 42 ⟩ ≡ f 48
    test₃ f = ⟨by⟩ assumption

    test₄ : (f : ℕ → ℕ) → f ⟨ 48 ⟩ ≡ f 42
    test₄ f = ⟨by⟩ assumption

    test₅ : (f : ℕ → ℕ → ℕ) → f ⟨ 42 ⟩ ⟨ 42 ⟩ ≡ f 48 48
    test₅ f = ⟨by⟩ assumption

    test₆ : (f : ℕ → ℕ → ℕ → ℕ) → f ⟨ 48 ⟩ 45 ⟨ 48 ⟩ ≡ f 42 45 42
    test₆ f = ⟨by⟩ assumption

    test₇ : f ⟨ 48 ⟩ (f ⟨ 48 ⟩ 45 ⟨ 48 ⟩) ⟨ 48 ⟩ ≡ f 42 (f 42 45 42) 42
    test₇ = ⟨by⟩ assumption

    test₈ : ∀ n → g n (g n 45 ⟨ 48 ⟩) ⟨ 48 ⟩ ≡ g n (g n 45 42) 42
    test₈ n = ⟨by⟩ assumption

    test₉ : (f : ℕ → ℕ) → f ⟨ 42 ⟩ ≡ f 48
    test₉ f = ⟨by⟩ (lemma 40)

    test₁₀ : (f : ℕ → ℕ) → f ⟨ 42 ⟩ ≡ f 48
    test₁₀ f = ⟨by⟩ (λ (_ : ⊤) → assumption)

    test₁₁ : (f : ℕ × ℕ → ℕ × ℕ) → (∀ x → ⟨ _≡_ ⟩ (f x) x) →
             fst ⟨ f (12 , 73) ⟩ ≡ fst {B = λ _ → ℕ} (12 , 73)
    test₁₁ _ hyp = ⟨by⟩ hyp

    test₁₂ : (h : ℕ → Maybe ℕ) →
             ((xs : ℕ) → h xs ≡ just xs) →
             (xs : ℕ) → suc ⟨$⟩ h xs ≡ suc ⟨$⟩ return xs
    test₁₂ h hyp xs =
      suc ⟨$⟩ ⟨ h xs ⟩   ≡⟨ ⟨by⟩ (hyp xs) ⟩∎
      suc ⟨$⟩ return xs  ∎

    test₁₃ : (h : List ⊤ → Maybe (List ⊤)) →
             ((xs : List ⊤) → h xs ≡ just xs) →
             (x : ⊤) (xs : List ⊤) → _
    test₁₃ h hyp x xs =
      _∷_ ⟨$⟩ return x ⊛ ⟨ h xs ⟩   ≡⟨ ⟨by⟩ (hyp xs) ⟩∎
      _∷_ ⟨$⟩ return x ⊛ return xs  ∎

    test₁₄ : (h : List ℕ → Maybe (List ℕ)) →
             ((xs : List ℕ) → h xs ≡ just xs) →
             (x : ℕ) (xs : List ℕ) → _
    test₁₄ h hyp x xs =
      _∷_ ⟨$⟩ ⟨ h xs ⟩   ≡⟨ ⟨by⟩ (hyp xs) ⟩∎
      _∷_ ⟨$⟩ return xs  ∎

    test₁₅ :
      (F : Set → Set → Set)
      (G : Bool → Set → Set) →
      ((A : Set) → F (G false A) A ≡ G false (F A A)) →
      (A : Set) →
      G false (F (G false A) A) ≡
      G false (G false (F A A))
    test₁₅ F G hyp A =
      G false ⟨ F (G false A) A ⟩  ≡⟨ ⟨by⟩ hyp ⟩∎
      G false (G false (F A A))    ∎

    test₁₆ : 48 ≡ 42 →
             _≡_ {A = ℕ → ℕ} (λ x → x + ⟨ 42 ⟩) (λ x → x + 48)
    test₁₆ hyp = ⟨by⟩ hyp

    test₁₇ :
      (P : ℕ → Set)
      (f : ∀ {n} → P n → P n)
      (p : P 0) →
      f ⟨ subst P (refl _) p ⟩ ≡ f p
    test₁₇ _ _ _ = ⟨by⟩ subst-refl

    test₁₈ :
      (subst′ :
         ∀ {a p} {A : Set a} {x y : A}
         (P : A → Set p) → x ≡ y → P x → P y) →
      (∀ {a p} {A : Set a} {x : A} (P : A → Set p) (p : P x) →
       subst′ P (refl x) p ≡ p) →
      (P : ℕ → Set)
      (f : ∀ {n} → P n → P n)
      (p : P 0) →
      f ⟨ subst′ P (refl 0) p ⟩ ≡ f p
    test₁₈ _ subst′-refl _ _ _ = ⟨by⟩ subst′-refl
