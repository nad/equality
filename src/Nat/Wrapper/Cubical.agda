------------------------------------------------------------------------
-- An example related to Nat.Wrapper, defined in Cubical Agda
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Bijection
open import Equality
import Erased
open import Prelude hiding (zero; suc; _+_)

module Nat.Wrapper.Cubical
  {e⁺}
  (eq : ∀ {a p} → Equality-with-J a p e⁺)

  -- An instantiation of the []-cong axioms.
  (open Erased eq)
  (ax : ∀ {a} → []-cong-axiomatisation a)

  -- The underlying representation of natural numbers.
  (Nat′ : Set)
  -- A bijection between this representation and the unary natural
  -- numbers.
  (open Bijection eq using (_↔_))
  (Nat′↔ℕ : Nat′ ↔ ℕ)
  where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equality.Path.Isomorphisms eq
open import Function-universe eq as F hiding (_∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
open import Nat eq
open import Univalence-axiom eq

open import Nat.Wrapper eq ax Nat′ Nat′↔ℕ

------------------------------------------------------------------------
-- Could Nat have been defined using the propositional truncation
-- instead of Erased?

-- Could Nat have been defined using ∥_∥ instead of Erased? Let us
-- try.

-- Given a truncated natural number we can kind of apply Nat-[_] to
-- it, because Nat-[_] is a family of contractible types. (The code
-- uses univalence.)

Nat-[]′ : ∥ ℕ ∥ → ∃ λ (A : Set) → Contractible A
Nat-[]′ = Trunc.rec
  (∃-H-level-H-level-1+ ext univ 0)
  (λ n → Nat-[ n ]
       , propositional⇒inhabited⇒contractible
           Nat-[]-propositional
           ( _↔_.from Nat′↔ℕ n
           , [ _↔_.right-inverse-of Nat′↔ℕ n ]
           ))

Nat-[_]′ : ∥ ℕ ∥ → Set
Nat-[ n ]′ = proj₁ (Nat-[]′ n)

-- Thus we can form a variant of Nat.

Nat-with-∥∥ : Set
Nat-with-∥∥ = Σ ∥ ℕ ∥ Nat-[_]′

-- However, this variant is isomorphic to the unit type.

Nat-with-∥∥↔⊤ : Nat-with-∥∥ ↔ ⊤
Nat-with-∥∥↔⊤ =
  _⇔_.to contractible⇔↔⊤ $
  Σ-closure 0
    (propositional⇒inhabited⇒contractible
       truncation-is-proposition ∣ 0 ∣)
    (proj₂ ∘ Nat-[]′)

-- And thus it is not isomorphic to the natural numbers.

¬-Nat-with-∥∥↔ℕ : ¬ (Nat-with-∥∥ ↔ ℕ)
¬-Nat-with-∥∥↔ℕ =
  Nat-with-∥∥ ↔ ℕ  ↝⟨ F._∘ inverse Nat-with-∥∥↔⊤ ⟩
  ⊤ ↔ ℕ            ↝⟨ (λ hyp → _↔_.injective (inverse hyp) (refl _)) ⟩
  0 ≡ 1            ↝⟨ 0≢+ ⟩□
  ⊥                □
