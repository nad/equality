------------------------------------------------------------------------
-- A solver for certain natural number equalities
------------------------------------------------------------------------

-- The code is based on "Proving Equalities in a Commutative Ring Done
-- Right in Coq" by Grégoire and Mahboubi, but specialised to natural
-- numbers.

-- Note that the implementation uses propositional equality.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Nat.Solver {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Dec
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Fin eq as Fin using (⌞_⌟)
import List eq as L
open import N-ary eq
open import Nat.Solver.Normal eq as N hiding (⟦_⟧)
open import Vec eq

private variable
  m n : ℕ
  ρ   : Vec ℕ n

------------------------------------------------------------------------
-- Polynomials

-- Polynomials. The polynomials are indexed by the number of
-- variables.

infixr 9 _:^_
infixl 8 _:*_
infixl 7 _:+_

data Polynomial (m : ℕ) : Type where
  _:+_ _:*_ : (p₁ p₂ : Polynomial m) → Polynomial m
  con       : (n : ℕ) → Polynomial m
  var       : (x : Fin m) → Polynomial m
  _:^_      : (p : Polynomial m) (n : ℕ) → Polynomial m

-- Semantics of polynomials.

⟦_⟧ : Polynomial n → Vec ℕ n → ℕ
⟦ p₁ :+ p₂ ⟧ ρ = ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ
⟦ p₁ :* p₂ ⟧ ρ = ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ ρ
⟦ con n ⟧    ρ = n
⟦ var x ⟧    ρ = index ρ x
⟦ p :^ n ⟧   ρ = ⟦ p ⟧ ρ ^ n

------------------------------------------------------------------------
-- Normalisation

-- Normalisation of polynomials.

normalise : Polynomial m → Normal
normalise (p₁ :+ p₂) = normalise p₁ +ᴺ normalise p₂
normalise (p₁ :* p₂) = normalise p₁ *ᴺ normalise p₂
normalise (con n)    = con n
normalise (var x)    = varᴺ ⌞ x ⌟
normalise (p :^ n)   = normalise p ^ᴺ n

opaque
  unfolding Canonical

  -- Normalisation produces canonical normal forms.

  normalise-canonical : (p : Polynomial m) → Canonical (normalise p)
  normalise-canonical (p₁ :+ p₂) =
    +ᴺ-Canonical _ _ (normalise-canonical p₁)
      (normalise-canonical p₂)
  normalise-canonical (p₁ :* p₂) =
    *ᴺ-Canonical _ _ (normalise-canonical p₁)
      (normalise-canonical p₂)
  normalise-canonical (con n) =
    _
  normalise-canonical (var _) =
    varᴺ-Canonical _
  normalise-canonical (p :^ n) =
    ^ᴺ-Canonical n (normalise-canonical p)

opaque

  -- Normalisation is correctly defined (ignoring canonicity).

  normalise-correct :
    (p : Polynomial m) →
    N.⟦ normalise p ⟧ (to-list ρ) ≡ ⟦ p ⟧ ρ
  normalise-correct {ρ} (p₁ :+ p₂) =
    N.⟦ normalise p₁ +ᴺ normalise p₂ ⟧ (to-list ρ)                   ≡⟨ +ᴺ-correct (normalise p₁) (normalise p₂) ⟩
    N.⟦ normalise p₁ ⟧ (to-list ρ) + N.⟦ normalise p₂ ⟧ (to-list ρ)  ≡⟨ cong₂ _+_ (normalise-correct p₁) (normalise-correct p₂) ⟩∎
    ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ                                              ∎
  normalise-correct {ρ} (p₁ :* p₂) =
    N.⟦ normalise p₁ *ᴺ normalise p₂ ⟧ (to-list ρ)                   ≡⟨ *ᴺ-correct (normalise p₁) (normalise p₂) ⟩
    N.⟦ normalise p₁ ⟧ (to-list ρ) * N.⟦ normalise p₂ ⟧ (to-list ρ)  ≡⟨ cong₂ _*_ (normalise-correct p₁) (normalise-correct p₂) ⟩∎
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ ρ                                              ∎
  normalise-correct (con n) =
    n  ∎
  normalise-correct {ρ} (var x) =
    let eq = sym (length-to-list ρ) in
    N.⟦ varᴺ ⌞ x ⌟ ⟧ (to-list ρ)                           ≡⟨ varᴺ-correct ⌞ x ⌟ ⟩
    L.index-with-default 0 (to-list ρ) ⌞ x ⌟               ≡⟨ cong (L.index-with-default _ (to-list ρ)) (sym (Fin.⌞subst⌟ _ _)) ⟩
    L.index-with-default 0 (to-list ρ) ⌞ subst Fin eq x ⌟  ≡⟨ Fin.index-with-default≡index (to-list ρ) ⟩
    L.index (to-list ρ) (subst Fin eq x)                   ≡⟨ sym (index≡index-to-list ρ _) ⟩∎
    index ρ x                                              ∎
  normalise-correct {ρ} (p :^ n) =
    N.⟦ normalise p ^ᴺ n ⟧ (to-list ρ)  ≡⟨ ^ᴺ-correct (normalise p) n ⟩
    N.⟦ normalise p ⟧ (to-list ρ) ^ n   ≡⟨ cong (_^ n) (normalise-correct p) ⟩∎
    ⟦ p ⟧ ρ ^ n                         ∎

------------------------------------------------------------------------
-- The solver

-- All variables.

all-vars : Vec (Polynomial n) n
all-vars = map var all-numbers

opaque

  -- A solver for natural number equalities.

  solve :
    ∀ n (f : N-ary n (Polynomial n) (Polynomial n × Polynomial n)) →
    let p₁ , p₂ = _$ⁿ_ {n = n} f all-vars in
    {ok : T (normalise p₁ N.≟ normalise p₂)} →
    Eqⁿ n (curryⁿ ⟦ p₁ ⟧) (curryⁿ ⟦ p₂ ⟧)
  solve n f {ok} =
    let ⟦_⟧′ : Normal → N-ary n ℕ ℕ
        ⟦ p ⟧′ = curryⁿ (N.⟦ p ⟧ ∘ to-list)

        eq₁ : (p : Polynomial n) →
              Eqⁿ n ⟦ normalise p ⟧′ (curryⁿ ⟦ p ⟧)
        eq₁ p = curryⁿ-cong n λ _ → normalise-correct p

        p₁ , p₂ = _$ⁿ_ {n = n} f all-vars

        eq₂ : Eqⁿ n ⟦ normalise p₁ ⟧′ ⟦ normalise p₂ ⟧′
        eq₂ =
          subst (λ p → Eqⁿ n ⟦ normalise p₁ ⟧′ ⟦ p ⟧′)
            (_⇔_.to (≟-correct (normalise p₁) (normalise p₂)) ok)
            (reflⁿ n)
    in
    transⁿ n (transⁿ n (symⁿ n (eq₁ p₁)) eq₂) (eq₁ p₂)

-- A synonym of _,_. See the examples below for uses of this synonym.

infix 4 _:=_

_:=_ : Polynomial n → Polynomial n → Polynomial n × Polynomial n
_:=_ = _,_

opaque

  -- An example.

  _ :
    ∀ m n →
    m + 2 + n * (2 + m) ^ 2 ≡
    1 + m + n * 4 * (1 + m) + m * n * m + 1
  _ = solve 2
        (λ m n →
           m :+ con 2 :+ n :* (con 2 :+ m) :^ 2 :=
           con 1 :+ m :+ n :* con 4 :* (con 1 :+ m) :+
           m :* n :* m :+ con 1)

opaque

  -- Another example.

  _ :
    ∀ a b c d e f g →
    (a + b + c + d + e + f + g) ^ 8 ≡
    (g + f + e + d + c + b + a) ^ 8
  _ = solve 7
        (λ a b c d e f g →
           (a :+ b :+ c :+ d :+ e :+ f :+ g) :^ 8 :=
           (g :+ f :+ e :+ d :+ c :+ b :+ a) :^ 8)
