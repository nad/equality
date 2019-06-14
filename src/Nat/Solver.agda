------------------------------------------------------------------------
-- A solver for certain natural number equalities
------------------------------------------------------------------------

-- The standard library's solver is used.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Nat.Solver
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

import Equality.Propositional as EP
open import Equality.Instances-related
open import Prelude

open import Bijection eq using (_↔_)
open import Function-universe eq

open import Data.Nat.Solver
open import Data.Vec as Vec
open import Data.Vec.N-ary
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (Equivalence)
import Relation.Binary.Reflection
import Relation.Binary.PropositionalEquality as P

open +-*-Solver public using (_:=_; _:+_; _:*_; _:^_)
open +-*-Solver.Polynomial public using (con)

open +-*-Solver hiding (solve)
open Relation.Binary.Reflection (P.setoid _) var ⟦_⟧ ⟦_⟧↓ correct
  using (close)

private

  -- Some simple lemmas.

  ≡↔≡ : ∀ {a} {A : Set a} {x y : A} → x ≡ y ↔ x P.≡ y
  ≡↔≡ = proj₁ (all-equality-types-isomorphic eq EP.equality-with-J)

  ≡→≡ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x P.≡ y
  ≡→≡ = _↔_.to ≡↔≡

  ≡←≡ : ∀ {a} {A : Set a} {x y : A} → x P.≡ y → x ≡ y
  ≡←≡ = _↔_.from ≡↔≡

-- A variant of +-*-Solver.solve.

solve :
  ∀ n (f : N-ary n (Polynomial n)
                   (Polynomial n × Polynomial n)) →
  Eqʰ n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧↓)
            (curryⁿ ⟦ proj₂ (close n f) ⟧↓) →
  Eq  n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧)
            (curryⁿ ⟦ proj₂ (close n f) ⟧)
solve n f =
  Eqʰ n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧↓)
            (curryⁿ ⟦ proj₂ (close n f) ⟧↓)                        ↝⟨ Eqʰ-to-Eq n _≡_ ⟩

  Eq n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧↓)
           (curryⁿ ⟦ proj₂ (close n f) ⟧↓)                         ↔⟨⟩

  ∀ⁿ n (curryⁿ λ xs → (curryⁿ ⟦ proj₁ (close n f) ⟧↓ $ⁿ xs) ≡
                      (curryⁿ ⟦ proj₂ (close n f) ⟧↓ $ⁿ xs))       ↝⟨ Equivalence.to (uncurry-∀ⁿ n) ⟨$⟩_ ⟩

  (∀ (xs : Vec _ n) →
     (curryⁿ λ xs → (curryⁿ ⟦ proj₁ (close n f) ⟧↓ $ⁿ xs) ≡
                    (curryⁿ ⟦ proj₂ (close n f) ⟧↓ $ⁿ xs)) $ⁿ xs)  ↝⟨ (∀-cong _ λ xs → ≡⇒↝ _ $ ≡←≡ $ left-inverse _ xs) ⟩

  (∀ (xs : Vec _ n) →
     (curryⁿ ⟦ proj₁ (close n f) ⟧↓ $ⁿ xs) ≡
     (curryⁿ ⟦ proj₂ (close n f) ⟧↓ $ⁿ xs))                        ↝⟨ (∀-cong _ λ _ → ≡→≡) ⟩

  (∀ (xs : Vec _ n) →
     (curryⁿ ⟦ proj₁ (close n f) ⟧↓ $ⁿ xs) P.≡
     (curryⁿ ⟦ proj₂ (close n f) ⟧↓ $ⁿ xs))                        ↝⟨ (∀-cong _ λ xs → ≡⇒↝ _ $ sym $ ≡←≡ $ left-inverse _ xs) ⟩

  (∀ (xs : Vec _ n) →
     (curryⁿ λ xs → (curryⁿ ⟦ proj₁ (close n f) ⟧↓ $ⁿ xs) P.≡
                    (curryⁿ ⟦ proj₂ (close n f) ⟧↓ $ⁿ xs)) $ⁿ xs)  ↝⟨ Equivalence.from (uncurry-∀ⁿ n) ⟨$⟩_ ⟩

  ∀ⁿ n (curryⁿ λ xs → (curryⁿ ⟦ proj₁ (close n f) ⟧↓ $ⁿ xs) P.≡
                      (curryⁿ ⟦ proj₂ (close n f) ⟧↓ $ⁿ xs))       ↔⟨⟩

  Eq n P._≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧↓)
             (curryⁿ ⟦ proj₂ (close n f) ⟧↓)                       ↝⟨ Eq-to-Eqʰ n P._≡_ ⟩

  Eqʰ n P._≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧↓)
              (curryⁿ ⟦ proj₂ (close n f) ⟧↓)                      ↝⟨ +-*-Solver.solve n f ⟩

  Eq n P._≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧)
             (curryⁿ ⟦ proj₂ (close n f) ⟧)                        ↔⟨⟩

  ∀ⁿ n (curryⁿ λ xs → (curryⁿ ⟦ proj₁ (close n f) ⟧ $ⁿ xs) P.≡
                      (curryⁿ ⟦ proj₂ (close n f) ⟧ $ⁿ xs))        ↝⟨ Equivalence.to (uncurry-∀ⁿ n) ⟨$⟩_ ⟩

  (∀ (xs : Vec _ n) →
     (curryⁿ λ xs → (curryⁿ ⟦ proj₁ (close n f) ⟧ $ⁿ xs) P.≡
                    (curryⁿ ⟦ proj₂ (close n f) ⟧ $ⁿ xs)) $ⁿ xs)   ↝⟨ (∀-cong _ λ xs → ≡⇒↝ _ $ ≡←≡ $ left-inverse _ xs) ⟩

  (∀ (xs : Vec _ n) →
     (curryⁿ ⟦ proj₁ (close n f) ⟧ $ⁿ xs) P.≡
     (curryⁿ ⟦ proj₂ (close n f) ⟧ $ⁿ xs))                         ↝⟨ (∀-cong _ λ _ → ≡←≡) ⟩

  (∀ (xs : Vec _ n) →
     (curryⁿ ⟦ proj₁ (close n f) ⟧ $ⁿ xs) ≡
     (curryⁿ ⟦ proj₂ (close n f) ⟧ $ⁿ xs))                         ↝⟨ (∀-cong _ λ xs → ≡⇒↝ _ $ sym $ ≡←≡ $ left-inverse _ xs) ⟩

  (∀ (xs : Vec _ n) →
     (curryⁿ λ xs → (curryⁿ ⟦ proj₁ (close n f) ⟧ $ⁿ xs) ≡
                    (curryⁿ ⟦ proj₂ (close n f) ⟧ $ⁿ xs)) $ⁿ xs)   ↝⟨ Equivalence.from (uncurry-∀ⁿ n) ⟨$⟩_ ⟩

  ∀ⁿ n (curryⁿ λ xs → (curryⁿ ⟦ proj₁ (close n f) ⟧ $ⁿ xs) ≡
                      (curryⁿ ⟦ proj₂ (close n f) ⟧ $ⁿ xs))        ↔⟨⟩

  Eq n _≡_ (curryⁿ ⟦ proj₁ (close n f) ⟧)
           (curryⁿ ⟦ proj₂ (close n f) ⟧)                          □
