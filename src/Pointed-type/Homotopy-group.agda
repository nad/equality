------------------------------------------------------------------------
-- Homotopy groups of pointed types
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Pointed-type.Homotopy-group
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equality.Groupoid equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J
open import Group equality-with-J as G using (Group; Abelian; _≃ᴳ_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation eq as T
open import Pointed-type equality-with-J as PT
  using (Pointed-type; _≃ᴮ_; Ω; Ω[_])

private
  variable
    a p q : Level
    P     : Pointed-type p
    n     : ℕ

-- Homotopy-group-[1+ n ] P is the (1+n)-th homotopy group of the
-- pointed type P.
--
-- This definition is taken from the HoTT book.

Homotopy-group-[1+_] : ℕ → Pointed-type a → Group a
Homotopy-group-[1+ n ] P = λ where
    .Group.Carrier        → Carrier
    .Group.Carrier-is-set → Carrier-is-set
    .Group._∘_            → _∘′_
    .Group.id             → id′
    .Group._⁻¹            → _⁻¹
    .Group.left-identity  → left-identity
    .Group.right-identity → right-identity
    .Group.assoc          → assoc
    .Group.left-inverse   → left-inverse
    .Group.right-inverse  → right-inverse
  where
  Carrier = ∥ proj₁ (Ω[ 1 + n ] P) ∥[1+ 1 ]
  _∘′_    = ∥∥-zip trans
  id′     = ∣ refl _ ∣
  _⁻¹     = ∥∥-map sym

  abstract

    Carrier-is-set : Is-set Carrier
    Carrier-is-set = truncation-has-correct-h-level 1

    left-identity : (x : Carrier) → (id′ ∘′ x) ≡ x
    left-identity = T.elim λ where
      .T.∣∣ʳ _      → cong ∣_∣ $ trans-reflˡ _
      .T.h-levelʳ _ → mono₁ 2 $ truncation-has-correct-h-level 1

    right-identity : (x : Carrier) → (x ∘′ id′) ≡ x
    right-identity = T.elim λ where
      .T.∣∣ʳ _      → cong ∣_∣ $ trans-reflʳ _
      .T.h-levelʳ _ → mono₁ 2 $ truncation-has-correct-h-level 1

    assoc : (x y z : Carrier) → (x ∘′ (y ∘′ z)) ≡ ((x ∘′ y) ∘′ z)
    assoc = T.elim λ where
      .T.h-levelʳ _ → Π-closure ext 2 λ _ →
                      Π-closure ext 2 λ _ →
                      mono₁ 2 $ truncation-has-correct-h-level 1
      .T.∣∣ʳ _      → T.elim λ where
        .T.h-levelʳ _ → Π-closure ext 2 λ _ →
                        mono₁ 2 $ truncation-has-correct-h-level 1
        .T.∣∣ʳ _      → T.elim λ where
          .T.h-levelʳ _ → mono₁ 2 $ truncation-has-correct-h-level 1
          .T.∣∣ʳ _      → cong ∣_∣ $ sym $ trans-assoc _ _ _

    left-inverse : (x : Carrier) → ((x ⁻¹) ∘′ x) ≡ id′
    left-inverse = T.elim λ where
      .T.∣∣ʳ _      → cong ∣_∣ $ trans-symˡ _
      .T.h-levelʳ _ → mono₁ 2 $ truncation-has-correct-h-level 1

    right-inverse : (x : Carrier) → (x ∘′ (x ⁻¹)) ≡ id′
    right-inverse = T.elim λ where
      .T.∣∣ʳ _      → cong ∣_∣ $ trans-symʳ _
      .T.h-levelʳ _ → mono₁ 2 $ truncation-has-correct-h-level 1

-- The fundamental group of a pointed type.
--
-- This definition is taken from the HoTT book.

Fundamental-group : Pointed-type a → Group a
Fundamental-group = Homotopy-group-[1+ 0 ]

-- The n-th homotopy group of a pointed type is abelian when n is at
-- least two.
--
-- (This result is stated in the HoTT book.)

abelian : ∀ n → Abelian (Homotopy-group-[1+ suc n ] P)
abelian n = T.elim λ where
  .T.h-levelʳ _ → Π-closure ext 2 λ _ →
                  mono₁ 2 $ truncation-has-correct-h-level 1
  .T.∣∣ʳ p      → T.elim λ where
    .T.h-levelʳ _ → mono₁ 2 $ truncation-has-correct-h-level 1
    .T.∣∣ʳ q      → cong ∣_∣ $ Ω[2+n]-commutative n p q

-- If there is a based equivalence between P and Q, then their
-- homotopy groups are isomorphic.

≃ᴮ→≃ᴳ :
  ∀ (P : Pointed-type p) (Q : Pointed-type q) n →
  P ≃ᴮ Q → Homotopy-group-[1+ n ] P ≃ᴳ Homotopy-group-[1+ n ] Q
≃ᴮ→≃ᴳ P Q n P≃Q = λ where
  .G.Homomorphic.related →
    ∥∥-cong (proj₁ (PT.Ω[ suc n ]-cong-≃ᴮ P≃Q))
  .G.Homomorphic.homomorphic → T.elim λ where
    .T.h-levelʳ _ → Π-closure ext 2 λ _ →
                    mono₁ 2 $ truncation-has-correct-h-level 1
    .T.∣∣ʳ _      → T.elim λ where
      .T.h-levelʳ _ → mono₁ 2 $ truncation-has-correct-h-level 1
      .T.∣∣ʳ _      → cong ∣_∣ (PT.Ω[1+ n ]-cong-≃ᴮ-trans P≃Q)

-- Homotopy-group-[1+ n ] commutes with PT._×_/G._×_.

Homotopy-group-[1+_]-× :
  ∀ n (P : Pointed-type p) (Q : Pointed-type q) →
  Homotopy-group-[1+ n ] (P PT.× Q) ≃ᴳ
  (Homotopy-group-[1+ n ] P G.× Homotopy-group-[1+ n ] Q)
Homotopy-group-[1+ n ]-× P Q = λ where
    .G.Homomorphic.related →
      ∥ proj₁ (Ω[ 1 + n ] (P PT.× Q)) ∥[1+ 1 ]                           ↝⟨ T.∥∥-cong (proj₁ PT.Ω[ 1 + n ]-×) ⟩
      ∥ proj₁ (Ω[ 1 + n ] P) × proj₁ (Ω[ 1 + n ] Q) ∥[1+ 1 ]             ↝⟨ inverse T.∥∥×∥∥≃∥×∥ ⟩□
      ∥ proj₁ (Ω[ 1 + n ] P) ∥[1+ 1 ] × ∥ proj₁ (Ω[ 1 + n ] Q) ∥[1+ 1 ]  □
    .G.Homomorphic.homomorphic → T.elim λ where
      .T.h-levelʳ _ → Π-closure ext 2 λ _ → s
      .T.∣∣ʳ p → T.elim λ where
        .T.h-levelʳ _ → s
        .T.∣∣ʳ q →
          Σ-map ∣_∣ ∣_∣ (_≃_.to (proj₁ PT.Ω[ 1 + n ]-×) (trans p q))  ≡⟨ cong (Σ-map ∣_∣ ∣_∣) PT.Ω[1+ n ]-×-trans ⟩∎

          (Σ-map ∣_∣ ∣_∣ $ Σ-zip trans trans
             (_≃_.to (proj₁ PT.Ω[ 1 + n ]-×) p)
             (_≃_.to (proj₁ PT.Ω[ 1 + n ]-×) q))                      ∎
  where
  s =
    mono₁ 2 $
    ×-closure 2
      (truncation-has-correct-h-level 1)
      (truncation-has-correct-h-level 1)

-- Homotopy-group-[1+ n ]′ P s is the (1+n)-th homotopy group of the
-- pointed type P.
--
-- The definition does not use set truncation. Instead a certain loop
-- space is required to be a set.

Homotopy-group-[1+_]′ :
  ∀ n (P : Pointed-type a) → Is-set (proj₁ (Ω[ 1 + n ] P)) → Group a
Homotopy-group-[1+ n ]′ P s = λ where
    .Group.Carrier        → Carrier
    .Group.Carrier-is-set → Carrier-is-set
    .Group._∘_            → _∘′_
    .Group.id             → id′
    .Group._⁻¹            → _⁻¹
    .Group.left-identity  → left-identity
    .Group.right-identity → right-identity
    .Group.assoc          → assoc
    .Group.left-inverse   → left-inverse
    .Group.right-inverse  → right-inverse
  where
  Carrier = proj₁ (Ω[ 1 + n ] P)
  _∘′_    = trans
  id′     = refl _
  _⁻¹     = sym

  abstract

    Carrier-is-set : Is-set Carrier
    Carrier-is-set = s

    left-identity : (x : Carrier) → (id′ ∘′ x) ≡ x
    left-identity _ = trans-reflˡ _

    right-identity : (x : Carrier) → (x ∘′ id′) ≡ x
    right-identity _ = trans-reflʳ _

    assoc : (x y z : Carrier) → (x ∘′ (y ∘′ z)) ≡ ((x ∘′ y) ∘′ z)
    assoc _ _ _ = sym $ trans-assoc _ _ _

    left-inverse : (x : Carrier) → ((x ⁻¹) ∘′ x) ≡ id′
    left-inverse _ = trans-symˡ _

    right-inverse : (x : Carrier) → (x ∘′ (x ⁻¹)) ≡ id′
    right-inverse _ = trans-symʳ _

-- The fundamental group of a pointed type.
--
-- The definition does not use set truncation. Instead a certain loop
-- space is required to be a set.

Fundamental-group′ :
  (P : Pointed-type a) → Is-set (proj₁ (Ω P)) → Group a
Fundamental-group′ = Homotopy-group-[1+ 0 ]′

-- Homotopy-group-[1+ n ]′ P s is isomorphic to
-- Homotopy-group-[1+ n ] P.

Homotopy-group-[1+]′≃ᴳHomotopy-group-[1+] :
  {s : Is-set (proj₁ (Ω[ 1 + n ] P))} →
  Homotopy-group-[1+ n ]′ P s ≃ᴳ Homotopy-group-[1+ n ] P
Homotopy-group-[1+]′≃ᴳHomotopy-group-[1+] {s} = λ where
  .G.Homomorphic.related →
    inverse $ Eq.↔⇒≃ $ _⇔_.to T.+⇔∥∥↔ (λ {_ _} → s)
  .G.Homomorphic.homomorphic p q →
    ∣ trans p q ∣  ≡⟨⟩
    ∣ trans p q ∣  ∎
