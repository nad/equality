------------------------------------------------------------------------
-- Connectedness for pointed types
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Pointed-type.Connected
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J
open import Group eq as G using (_≃ᴳ_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
import Nat equality-with-J as Nat
open import Pointed-type equality-with-J
open import Pointed-type.Homotopy-group eq

private
  variable
    p : Level
    P : Pointed-type p

-- Connectedness.
--
-- This definition of what it means for a pointed type to be connected
-- is based on a characterisation given in the HoTT Book.

Connected : Pointed-type p → Type p
Connected (A , x) = (y : A) → ∥ x ≡ y ∥

-- The connected component of a pointed type.
--
-- I got this definition from Christian Sattler.

Connected-component : Pointed-type p → Pointed-type p
Connected-component (A , x) =
  (∃ λ y → ∥ x ≡ y ∥) , (x , ∣ refl _ ∣)

-- There is a based embedding from the connected component of P to P.
--
-- This definition was suggested to me by Christian Sattler.

Connected-component↣ᴮ : Connected-component P ↝[ embedding ]ᴮ P
Connected-component↣ᴮ =
    record { to           = proj₁
           ; is-embedding = λ x y →
               _≃_.is-equivalence $
               Eq.with-other-function
                 (x ≡ y              ↔⟨ inverse $ ignore-propositional-component T.truncation-is-proposition ⟩□
                  proj₁ x ≡ proj₁ y  □)
                 (cong proj₁)
                 proj₁-Σ-≡,≡←≡
           }
  , refl _

-- The connected component is connected.
--
-- This definition was suggested to me by Christian Sattler.

Connected-Connected-component :
  {P : Pointed-type p} →
  Connected (Connected-component P)
Connected-Connected-component y =
  flip T.∥∥-map (proj₂ y) λ eq →
    Σ-≡,≡→≡ eq (T.truncation-is-proposition _ _)

-- If P has a certain positive h-level, then the same applies to the
-- connected component of P.

H-level-Connected-component :
  ∀ {P : Pointed-type p} n →
  H-level (1 + n) (proj₁ P) →
  H-level (1 + n) (proj₁ (Connected-component P))
H-level-Connected-component {P = A , x} n =
  H-level (1 + n) A                    ↝⟨ (λ h →
                                             Σ-closure (1 + n) h λ _ →
                                             mono (Nat.suc≤suc (Nat.zero≤ n))
                                             T.truncation-is-proposition) ⟩
  H-level (1 + n) (∃ λ y → ∥ x ≡ y ∥)  □

-- If the loop space of P has a certain h-level, then the same applies
-- to the loop space of the connected component of P.

H-level-Ω-Connected-component :
  ∀ {P : Pointed-type p} n →
  H-level n (proj₁ (Ω P)) →
  H-level n (proj₁ (Ω (Connected-component P)))
H-level-Ω-Connected-component {P = _ , x} n =
  H-level n (x ≡ x)              ↝⟨ H-level-cong _ _ (ignore-propositional-component T.truncation-is-proposition) ⟩□
  H-level n ((x , _) ≡ (x , _))  □

-- The fundamental group of the connected component of P is equivalent
-- to the fundamental group of P.
--
-- This definition was suggested to me by Christian Sattler.

Fundamental-group′-Connected-component≃ᴳ :
  {s₁ : Is-set (proj₁ (Ω (Connected-component P)))}
  {s₂ : Is-set (proj₁ (Ω P))} →
  Fundamental-group′ (Connected-component P) s₁ ≃ᴳ
  Fundamental-group′ P s₂
Fundamental-group′-Connected-component≃ᴳ {P = _ , x} = λ where
  .G.Homomorphic.related →
    Eq.with-other-function
      ((x , _) ≡ (x , _)  ↔⟨ inverse $ ignore-propositional-component T.truncation-is-proposition ⟩□
       x ≡ x              □)
      (cong proj₁)
      proj₁-Σ-≡,≡←≡
  .G.Homomorphic.homomorphic p q →
    cong proj₁ (trans p q)               ≡⟨ cong-trans _ _ _ ⟩∎
    trans (cong proj₁ p) (cong proj₁ q)  ∎
