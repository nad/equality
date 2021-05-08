------------------------------------------------------------------------
-- Some results that could not be placed in Function-universe because
-- they make use of --sized-types
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

open import Equality

module Function-universe.Size
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Prelude
open import Prelude.Size

import Bijection eq as B
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq

private
  variable
    S   : Size-universe
    p q : Level
    P   : S → Type p
    k   : Kind

-- Π-types with something from the size universe in the domain can be
-- expressed using something from Type in the domain.

Π-size-≃ :
  ((i : S) → P i) ≃
  ((i : S in-type) → P (size i))
Π-size-≃ = Eq.↔→≃
  (λ p i → p (size i))
  (λ p i → p (record { size = i }))
  refl
  refl

-- Implicit Π-types with something from the size universe in the
-- domain can be expressed using something from Type in the domain.

implicit-Π-size-≃ :
  ({i : S} → P i) ≃
  ({i : S in-type} → P (size i))
implicit-Π-size-≃ = Eq.↔→≃
  (λ p {i} → p {size i})
  (λ p {i} → p {record { size = i }})
  refl
  refl

-- Implicit Π-types with something from the size universe in the
-- domain are equivalent to explicit Π-types.

implicit-Π-size-≃-Π-size :
  ({i : S} → P i) ≃ ((i : S) → P i)
implicit-Π-size-≃-Π-size {P = P} =
  (∀ {i} → P i)         ↔⟨ implicit-Π-size-≃ ⟩
  (∀ {i} → P (size i))  ↔⟨ B.implicit-Π↔Π ⟩
  (∀ i → P (size i))    ↔⟨ inverse Π-size-≃ ⟩□
  (∀ i → P i)           □

-- A preservation lemma for Π-types with something from the size
-- universe in the domain.

∀-size-cong :
  {P : S → Type p} {Q : S → Type q} →
  Extensionality? k lzero (p ⊔ q) →
  (∀ i → P i ↝[ k ] Q i) →
  (∀ i → P i) ↝[ k ] (∀ i → Q i)
∀-size-cong {P = P} {Q = Q} ext P↝Q =
  (∀ i → P i)         ↔⟨ Π-size-≃ ⟩
  (∀ i → P (size i))  ↝⟨ ∀-cong ext (λ i → P↝Q (size i)) ⟩
  (∀ i → Q (size i))  ↔⟨ inverse Π-size-≃ ⟩□
  (∀ i → Q i)         □

-- A preservation lemma for implicit Π-types with something from the
-- size universe in the domain.

implicit-∀-size-cong :
  {P : S → Type p} {Q : S → Type q} →
  Extensionality? k lzero (p ⊔ q) →
  (∀ {i} → P (size i) ↝[ k ] Q (size i)) →
  (∀ {i} → P i) ↝[ k ] (∀ {i} → Q i)
implicit-∀-size-cong {P = P} {Q = Q} ext P↝Q =
  (∀ {i} → P i)         ↔⟨ implicit-Π-size-≃ ⟩
  (∀ {i} → P (size i))  ↝⟨ implicit-∀-cong ext P↝Q ⟩
  (∀ {i} → Q (size i))  ↔⟨ inverse implicit-Π-size-≃ ⟩□
  (∀ {i} → Q i)         □
