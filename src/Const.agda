------------------------------------------------------------------------
-- Some properties related to the const function
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Const
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude

import Bijection eq as Bijection
open Derived-definitions-and-properties eq
open import Embedding eq
open import Equivalence eq as Eq using (_≃_)
open import Fin eq
open import Function-universe eq
open import H-level eq
open import H-level.Closure eq
open import Injection eq using (Injective)
import Nat eq as Nat
open import Univalence-axiom eq

-- If A is inhabited, then the function const : B → (A → B) is
-- injective.

const-is-injective :
  ∀ {a b} →
  {A : Set a} {B : Set b} →
  A → Injective {B = A → B} const
const-is-injective x {y} {z} =
  const y ≡ const z  ↝⟨ cong (_$ x) ⟩□
  y ≡ z              □

-- Thus, if B is a set, then const is also an embedding (assuming
-- extensionality).

const-is-embedding :
  ∀ {a b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  {A : Set a} {B : Set b} →
  Is-set B →
  A → Is-embedding {B = A → B} const
const-is-embedding {a} {b} ext B-set x =
  _≃_.to (Injective≃Is-embedding
            ext B-set
            (Π-closure (lower-extensionality b a ext) 2 λ _ →
             B-set)
            const)
    (const-is-injective x)

-- However, if B is not a set, then one can construct a counterexample
-- (assuming extensionality and univalence).
--
-- This example is due to Thierry Coquand. (His proof was not
-- identical to the one below.)

const-is-not-embedding :
  ∀ {a b} →
  Extensionality (a ⊔ b) (lsuc b) →
  Univalence b →
  Univalence (# 0) →
  ¬ ({A : Set a} {B : Set (lsuc b)} →
     A → Is-embedding {B = A → B} const)
const-is-not-embedding {a} {b} ext univ univ₀ hyp =
  from-⊎ (2 Nat.≟ 4) 2≡4
  where
  ext-b : Extensionality b b
  ext-b = lower-extensionality a (lsuc b) ext

  ext-ab₊ : Extensionality a (lsuc b)
  ext-ab₊ = lower-extensionality b lzero ext

  ext₁ : Extensionality (# 0) (# 1)
  ext₁ = lower-extensionality _ (lsuc b) ext

  ext₀ : Extensionality (# 0) (# 0)
  ext₀ = lower-extensionality _ _ ext

  emb : Is-embedding {B = ↑ a (Fin 2) → Set b} const
  emb = hyp (lift true)

  2≡4 : 2 ≡ 4
  2≡4 = _⇔_.to isomorphic-same-size (
    Fin 2                                      ↝⟨ inverse $ [Fin≡Fin]↔Fin! ext₀ univ₀ 2 ⟩
    Fin 2 ≡ Fin 2                              ↔⟨ inverse $ ≡-preserves-≃ ext-b univ univ₀ (Eq.↔⇒≃ Bijection.↑↔) (Eq.↔⇒≃ Bijection.↑↔) ⟩
    ↑ b (Fin 2) ≡ ↑ b (Fin 2)                  ↔⟨ Eq.⟨ _ , emb (↑ b (Fin 2)) (↑ b (Fin 2)) ⟩ ⟩
    const (↑ b (Fin 2)) ≡ const (↑ b (Fin 2))  ↔⟨ inverse $ Eq.extensionality-isomorphism ext-ab₊ ⟩
    (↑ a (Fin 2) → ↑ b (Fin 2) ≡ ↑ b (Fin 2))  ↔⟨ →-cong ext-ab₊ (Eq.↔⇒≃ Bijection.↑↔)
                                                    (≡-preserves-≃ ext-b univ univ₀ (Eq.↔⇒≃ Bijection.↑↔) (Eq.↔⇒≃ Bijection.↑↔)) ⟩
    (Fin 2 → Fin 2 ≡ Fin 2)                    ↝⟨ ∀-cong ext₁ (λ _ → [Fin≡Fin]↔Fin! ext₀ univ₀ 2) ⟩
    (Fin 2 → Fin 2)                            ↝⟨ [Fin→Fin]↔Fin^ ext₀ 2 2 ⟩□
    Fin 4                                      □)
