------------------------------------------------------------------------
-- Spheres
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- This module follows the HoTT book rather closely.

import Equality.Path as P

module Sphere
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equality.Tactic equality-with-J
import Equivalence equality-with-J as Equiv
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Nat equality-with-J as Nat
open import Pointed-type equality-with-J
open import Suspension eq as Suspension

private
  variable
    a b : Level
    A B : Type a
    C   : Pointed-type a
    x   : A
    n   : ℕ

-- Spheres.

𝕊[_-1] : ℕ → Type
𝕊[ zero  -1] = ⊥
𝕊[ suc n -1] = Susp 𝕊[ n -1]

-- Spheres with non-negative dimensions.

𝕊 : ℕ → Type
𝕊 n = 𝕊[ 1 + n -1]

-- The booleans are isomorphic to the 0-dimensional sphere.

Bool↔𝕊⁰ : Bool ↔ 𝕊 0
Bool↔𝕊⁰ = Bool↔Susp-⊥

-- Based maps from spheres with non-negative dimensions (using north
-- as the point) are isomorphic to iterated loop spaces.

𝕊→ᴮ↔ : ∀ n → (𝕊 n , north) →ᴮ C ↔ proj₁ (Ω[ n ] C)
𝕊→ᴮ↔ {C = C} = lemma zero
  where
  lemma : ∀ m n → (𝕊 n , north) →ᴮ Ω[ m ] C ↔ proj₁ (Ω[ m + n ] C)
  lemma m zero =
    (𝕊 0 , north) →ᴮ Ω[ m ] C  ↝⟨ Σ-cong (→-cong ext (inverse Bool↔𝕊⁰) F.id) (λ _ → F.id) ⟩
    (Bool , true) →ᴮ Ω[ m ] C  ↝⟨ Bool→ᴮ↔ ext ⟩
    proj₁ (Ω[ m ] C)           ↝⟨ ≡⇒↝ _ $ cong (λ n → proj₁ (Ω[ n ] C)) $ sym $ Nat.+-right-identity {n = m} ⟩□
    proj₁ (Ω[ m + 0 ] C)       □

  lemma m (suc n) =
    (𝕊 (suc n) , north) →ᴮ Ω[ m ] C  ↝⟨ Susp→ᴮ↔ ⟩
    (𝕊 n , north) →ᴮ Ω[ suc m ] C    ↝⟨ lemma (suc m) n ⟩
    proj₁ (Ω[ suc m + n ] C)         ↝⟨ ≡⇒↝ _ $ cong (λ n → proj₁ (Ω[ n ] C)) $ Nat.suc+≡+suc m ⟩□
    proj₁ (Ω[ m + suc n ] C)         □

-- A corollary.

+↔∀contractible𝕊→ᴮ :
  H-level (1 + n) A ↔
  (∀ x → Contractible ((𝕊 n , north) →ᴮ (A , x)))
+↔∀contractible𝕊→ᴮ {n = n} {A = A} =
  H-level (1 + n) A                                ↔⟨ _↔_.to (Equiv.⇔↔≃ ext (H-level-propositional ext _)
                                                                            (Π-closure ext 1 λ _ →
                                                                             H-level-propositional ext _))
                                                             (+⇔∀contractible-Ω[] _) ⟩
  (∀ x → Contractible (proj₁ $ Ω[ n ] (A , x)))    ↝⟨ (∀-cong ext λ _ → H-level-cong ext 0 (inverse $ 𝕊→ᴮ↔ _)) ⟩□
  (∀ x → Contractible ((𝕊 n , north) →ᴮ (A , x)))  □
