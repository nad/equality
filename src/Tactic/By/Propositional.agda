------------------------------------------------------------------------
-- Some tactics aimed at making equational reasoning proofs more
-- readable for propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.By.Propositional where

open import Equality.Propositional
open import Prelude

open import List equality-with-J
open import Maybe equality-with-J
open import Monad equality-with-J
open import Tactic.By equality-with-J as TB
open import TC-monad equality-with-J as TC hiding (Type)

open TB public using (⟨_⟩)

private

  -- Constructs the type of equalities between its two arguments.

  equality : Term → Term → TC.Type
  equality lhs rhs = def (quote _≡_) (varg lhs ∷ varg rhs ∷ [])

  -- An illustration of what the cong functions constructed by
  -- make-cong-called look like.

  cong₃′ :
    ∀ {a b c d : Level}
      {A : Type a} {B : Type b} {C : Type c} {D : Type d}
      {x₁ y₁ x₂ y₂ x₃ y₃}
    (f : A → B → C → D) →
    x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → f x₁ x₂ x₃ ≡ f y₁ y₂ y₃
  cong₃′ f refl refl refl = refl

  -- Constructs a "cong" function (similar to cong and cong₂ in
  -- Equality), with the given name, for functions with the given
  -- number of arguments.

  make-cong-called : Name → ℕ → TC ⊤
  make-cong-called cong n = do
    declareDef (varg cong) (type-of-cong equality n)
    defineFun cong (the-clause ∷ [])
    where
    the-clause = clause
      (("f" , varg unknown) ∷ [])
      (varg (var 0) ∷ replicate n (varg (con (quote refl) [])))
      (con (quote refl) [])

  unquoteDecl cong₃  = make-cong-called cong₃   3
  unquoteDecl cong₄  = make-cong-called cong₄   4
  unquoteDecl cong₅  = make-cong-called cong₅   5
  unquoteDecl cong₆  = make-cong-called cong₆   6
  unquoteDecl cong₇  = make-cong-called cong₇   7
  unquoteDecl cong₈  = make-cong-called cong₈   8
  unquoteDecl cong₉  = make-cong-called cong₉   9
  unquoteDecl cong₁₀ = make-cong-called cong₁₀ 10

  -- Constructs a "cong" function (similar to cong and cong₂ in
  -- Equality) for functions with the given number of arguments. The
  -- name of the constructed function is returned (for 1 and 2 the
  -- functions in Equality are returned). The cong functions for
  -- functions with 3 up to 10 arguments are cached to avoid creating
  -- lots of copies of the same functions.

  make-cong : ℕ → TC Name
  make-cong  1 = return (quote cong)
  make-cong  2 = return (quote cong₂)
  make-cong  3 = return (quote cong₃)
  make-cong  4 = return (quote cong₄)
  make-cong  5 = return (quote cong₅)
  make-cong  6 = return (quote cong₆)
  make-cong  7 = return (quote cong₇)
  make-cong  8 = return (quote cong₈)
  make-cong  9 = return (quote cong₉)
  make-cong 10 = return (quote cong₁₀)
  make-cong n  = do
    cong ← freshName "cong"
    make-cong-called cong n
    return cong

open Tactics
  (λ where
     (def (quote _≡_) (arg _ a ∷ arg _ A ∷ arg _ x ∷ arg _ y ∷ [])) →
       return $ just (a , A , x , y)
     _ → return nothing)
  equality
  (λ a A x → con (quote refl) (harg a ∷ harg A ∷ harg x ∷ []))
  (λ p → def (quote sym) (varg p ∷ []))
  (λ lhs rhs f p → def (quote cong)
                       (replicate 4 (harg unknown) ++
                        harg lhs ∷ harg rhs ∷ varg f ∷ varg p ∷ []))
  false
  make-cong
  true
  public

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

    fst : ∀ {a b} {A : Type a} {B : A → Type b} →
          Σ A B → A
    fst = proj₁

    {-# NOINLINE fst #-}

    record R (F : Type → Type) : Type₁ where
      field
        p : {A : Type} {x : F A} → x ≡ x

    open R ⦃ … ⦄ public

    -- Tests for by.

    module By-tests where

      test₁ : 40 + 2 ≡ 42
      test₁ = by definition

      test₂ : 48 ≡ 42 → 42 ≡ 48
      test₂ eq = by eq

      test₃ : (f : ℕ → ℕ) → f 42 ≡ f 48
      test₃ f = by assumption

      test₄ : (f : ℕ → ℕ) → f 48 ≡ f 42
      test₄ f = by assumption

      test₅ : (f : ℕ → ℕ → ℕ) → f 42 48 ≡ f 48 42
      test₅ f = by assumption

      test₆ : (f : ℕ → ℕ → ℕ → ℕ) → f 42 45 48 ≡ f 48 45 42
      test₆ f = by assumption

      test₇ : f 48 (f 42 45 48) 42 ≡ f 48 (f 48 45 42) 48
      test₇ = by assumption

      test₈ : ∀ n → g n (g n 45 48) 42 ≡ g n (g n 45 42) 48
      test₈ n = by assumption

      test₉ : (f : ℕ → ℕ) → f 42 ≡ f 48
      test₉ f = by (lemma 40)

      test₁₀ : (f : ℕ → ℕ) → f 42 ≡ f 48
      test₁₀ f = by (λ (_ : ⊤) → assumption)

      test₁₁ : (f : ℕ × ℕ → ℕ × ℕ) → (∀ x → ⟨ _≡_ ⟩ (f x) x) →
               fst (f (12 , 73)) ≡ fst {B = λ _ → ℕ} (12 , 73)
      test₁₁ _ hyp = by hyp

      -- Two test cases for the extra check in try-refl.

      -- test₁₂ : (h : ℕ → Maybe ℕ) →
      --          ((xs : ℕ) → h xs ≡ just xs) →
      --          (xs : ℕ) → suc ⟨$⟩ h xs ≡ suc ⟨$⟩ return xs
      -- test₁₂ h hyp xs =
      --   suc ⟨$⟩ h xs       ≡⟨ by (hyp xs) ⟩∎
      --   suc ⟨$⟩ return xs  ∎

      test₁₃ : (h : List ⊤ → Maybe (List ⊤)) →
               ((xs : List ⊤) → h xs ≡ just xs) →
               (x : ⊤) (xs : List ⊤) → _
      test₁₃ h hyp x xs =
        _∷_ ⟨$⟩ return x ⊛ h xs       ≡⟨ by (hyp xs) ⟩∎
        _∷_ ⟨$⟩ return x ⊛ return xs  ∎

      -- This test case fails if "refl a A lhs" is replaced by
      -- "refl unknown unknown lhs" in try-refl.

      test₁₅ :
        (F : Type → Type → Type)
        (G : Bool → Type → Type) →
        ((A : Type) → F (G false A) A ≡ G false (F A A)) →
        (A : Type) →
        G false (F (G false A) A) ≡
        G false (G false (F A A))
      test₁₅ F G hyp A =
        G false (F (G false A) A)  ≡⟨ by hyp ⟩∎
        G false (G false (F A A))  ∎

      -- test₁₇ :
      --   (P : ℕ → Type)
      --   (f : ∀ {n} → P n → P n)
      --   (p : P 0) →
      --   f (subst P refl p) ≡ f p
      -- test₁₇ P _ _ = by (subst-refl P)

      test₁₈ :
        (subst′ :
           ∀ {a p} {A : Type a} {x y : A}
           (P : A → Type p) → x ≡ y → P x → P y) →
        (∀ {a p} {A : Type a} {x : A} (P : A → Type p) (p : P x) →
         subst′ P refl p ≡ p) →
        (P : ℕ → Type)
        (f : ∀ {n} → P n → P n)
        (p : P 0) →
        f (subst′ P refl p) ≡ f p
      test₁₈ _ subst′-refl P _ _ = by (subst′-refl P)

      -- test₁₉ :
      --   {F : Type → Type} ⦃ r : R F ⦄ {A : Type} {x₁ x₂ : F A}
      --   (p₁ p₂ : x₁ ≡ x₂) (assumption : p₁ ≡ p₂) →
      --   trans p p₁ ≡ trans p p₂
      -- test₁₉ p₁ p₂ assumption =
      --   trans p p₁  ≡⟨ by assumption ⟩∎
      --   trans p p₂  ∎

    -- Tests for ⟨by⟩.

    module ⟨By⟩-tests where

      -- At the time of writing the following test case works if the
      -- "cong-with-lhs-and-rhs" argument is true, but then test₁₈
      -- fails.

      -- test₁ : ⟨ 40 + 2 ⟩ ≡ 42
      -- test₁ = ⟨by⟩ refl

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
        (F : Type → Type → Type)
        (G : Bool → Type → Type) →
        ((A : Type) → F (G false A) A ≡ G false (F A A)) →
        (A : Type) →
        G false (F (G false A) A) ≡
        G false (G false (F A A))
      test₁₅ F G hyp A =
        G false ⟨ F (G false A) A ⟩  ≡⟨ ⟨by⟩ hyp ⟩∎
        G false (G false (F A A))    ∎

      test₁₆ : 48 ≡ 42 →
               _≡_ {A = ℕ → ℕ} (λ x → x + ⟨ 42 ⟩) (λ x → x + 48)
      test₁₆ hyp = ⟨by⟩ hyp

      test₁₇ :
        (P : ℕ → Type)
        (f : ∀ {n} → P n → P n)
        (p : P 0) →
        f ⟨ subst P refl p ⟩ ≡ f p
      test₁₇ P _ _ = ⟨by⟩ (subst-refl P)

      test₁₈ :
        (subst′ :
           ∀ {a p} {A : Type a} {x y : A}
           (P : A → Type p) → x ≡ y → P x → P y) →
        (∀ {a p} {A : Type a} {x : A} (P : A → Type p) (p : P x) →
         subst′ P refl p ≡ p) →
        (P : ℕ → Type)
        (f : ∀ {n} → P n → P n)
        (p : P 0) →
        f ⟨ subst′ P refl p ⟩ ≡ f p
      test₁₈ _ subst′-refl _ _ _ = ⟨by⟩ subst′-refl

      test₁₉ :
        {F : Type → Type} ⦃ r : R F ⦄ {A : Type} {x₁ x₂ : F A}
        (p₁ p₂ : x₁ ≡ x₂) (assumption : p₁ ≡ p₂) →
        trans p p₁ ≡ trans p p₂
      test₁₉ p₁ p₂ assumption =
        trans p p₁      ≡⟨⟩
        trans p ⟨ p₁ ⟩  ≡⟨ ⟨by⟩ assumption ⟩∎
        trans p p₂      ∎
