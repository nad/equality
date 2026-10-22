------------------------------------------------------------------------
-- N-ary functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module N-ary {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

import Bijection eq as B
open import Function-universe eq as F hiding (_∘_)
open import Vec eq

private variable
  a   : Level
  A B : Type _
  n   : ℕ

------------------------------------------------------------------------
-- N-ary

-- N-ary functions.

N-ary : ℕ → Type a → Type a → Type a
N-ary 0       _ B = B
N-ary (suc n) A B = A → N-ary n A B

-- Post-composition with unary functions.

_∘ⁿ_ :
  {@0 A B C : Type a} →
  (B → C) → N-ary n A B → N-ary n A C
_∘ⁿ_ {n = zero}  f = f
_∘ⁿ_ {n = suc _} f = (f ∘ⁿ_) ∘_

-- Function application.

_$ⁿ_ :
  {@0 A B : Type a} →
  N-ary n A B → Vec A n → B
_$ⁿ_ {n = zero}  x _        = x
_$ⁿ_ {n = suc _} f (x , xs) = f x $ⁿ xs

-- Currying.

curryⁿ :
  {@0 A B : Type a} →
  (Vec A n → B) → N-ary n A B
curryⁿ {n = zero}  f = f _
curryⁿ {n = suc _} f = λ x → curryⁿ (f ∘ (x ,_))

------------------------------------------------------------------------
-- Eqⁿ

-- Pointwise equality of n-ary functions.

Eqⁿ :
  {A B : Type a} →
  (n : ℕ) (_ _ : N-ary n A B) → Type a
Eqⁿ zero    x y = x ≡ y
Eqⁿ (suc n) f g = ∀ x → Eqⁿ n (f x) (g x)

opaque

  -- Reflexivity.

  reflⁿ : ∀ n {f : N-ary n A B} → Eqⁿ n f f
  reflⁿ zero    = refl _
  reflⁿ (suc n) = λ _ → reflⁿ n

opaque

  -- Symmetry.

  symⁿ :
    ∀ n {f g : N-ary n A B} →
    Eqⁿ n f g → Eqⁿ n g f
  symⁿ zero    = sym
  symⁿ (suc n) = symⁿ n ∘_

opaque

  -- Transitivity.

  transⁿ :
    ∀ n {f g h : N-ary n A B} →
    Eqⁿ n f g → Eqⁿ n g h → Eqⁿ n f h
  transⁿ zero    = trans
  transⁿ (suc n) = λ p q x → transⁿ n (p x) (q x)

opaque

  -- The function curryⁿ "preserves equality".

  curryⁿ-cong :
    ∀ n {f g : Vec A n → B} →
    (∀ xs → f xs ≡ g xs) →
    Eqⁿ n (curryⁿ f) (curryⁿ g)
  curryⁿ-cong zero    eq = eq _
  curryⁿ-cong (suc n) eq = λ x → curryⁿ-cong n (eq ∘ (x ,_))

------------------------------------------------------------------------
-- Eqⁿʰ

-- A variant of Eqⁿ with implicit arguments.

Eqⁿʰ :
  {A B : Type a} →
  (n : ℕ) (_ _ : N-ary n A B) → Type a
Eqⁿʰ zero    x y = x ≡ y
Eqⁿʰ (suc n) f g = ∀ {x} → Eqⁿʰ n (f x) (g x)

opaque

  -- One can convert between Eqⁿ and Eqⁿʰ.

  Eqⁿ⇔Eqⁿʰ :
    ∀ n {f g : N-ary n A B} →
    Eqⁿ n f g ⇔ Eqⁿʰ n f g
  Eqⁿ⇔Eqⁿʰ zero            = F.id
  Eqⁿ⇔Eqⁿʰ (suc n) {f} {g} =
    (∀ x → Eqⁿ n (f x) (g x))     ↝⟨ (∀-cong _ λ _ → Eqⁿ⇔Eqⁿʰ n) ⟩
    (∀ x → Eqⁿʰ n (f x) (g x))    ↔⟨ inverse B.implicit-Π↔Π ⟩□
    (∀ {x} → Eqⁿʰ n (f x) (g x))  □
