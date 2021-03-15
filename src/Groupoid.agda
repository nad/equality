------------------------------------------------------------------------
-- Groupoids
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Groupoid
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude hiding (id; _∘_)

open import Bijection eq hiding (id; _∘_)
open Derived-definitions-and-properties eq

-- Groupoids using _≡_ as the underlying equality.

record Groupoid o p : Type (lsuc (o ⊔ p)) where
  infix  8 _⁻¹
  infixr 7 _∘_
  infix  4 _∼_
  field
    Object : Type o
    _∼_    : Object → Object → Type p

    id  : ∀ {x} → x ∼ x
    _∘_ : ∀ {x y z} → y ∼ z → x ∼ y → x ∼ z
    _⁻¹ : ∀ {x y} → x ∼ y → y ∼ x

    left-identity  : ∀ {x y} (p : x ∼ y) → id ∘ p ≡ p
    right-identity : ∀ {x y} (p : x ∼ y) → p ∘ id ≡ p
    assoc          : ∀ {w x y z} (p : y ∼ z) (q : x ∼ y) (r : w ∼ x) →
                     p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    left-inverse   : ∀ {x y} (p : x ∼ y) → p ⁻¹ ∘ p ≡ id
    right-inverse  : ∀ {x y} (p : x ∼ y) → p ∘ p ⁻¹ ≡ id

  -- Note that this definition should perhaps contain more coherence
  -- properties: we have not assumed that _≡_ is proof-irrelevant.

  -- Some derived properties.

  abstract

    -- The identity is an identity for the inverse operator as well.

    identity : ∀ {x} → id {x = x} ⁻¹ ≡ id
    identity =
      id ⁻¹       ≡⟨ sym $ right-identity (id ⁻¹) ⟩
      id ⁻¹ ∘ id  ≡⟨ left-inverse id ⟩∎
      id          ∎

    -- If p is idempotent with respect to _∘_, then p is equal to the
    -- identity element.

    idempotent⇒≡id : ∀ {x} {p : x ∼ x} → p ∘ p ≡ p → p ≡ id
    idempotent⇒≡id {p = p} p∘p≡p =
      p               ≡⟨ sym $ left-identity _ ⟩
      id ∘ p          ≡⟨ cong (_∘ _) $ sym $ left-inverse _ ⟩
      (p ⁻¹ ∘ p) ∘ p  ≡⟨ sym $ assoc _ _ _ ⟩
      p ⁻¹ ∘ (p ∘ p)  ≡⟨ cong (p ⁻¹ ∘_) p∘p≡p ⟩
      p ⁻¹ ∘ p        ≡⟨ left-inverse _ ⟩∎
      id              ∎

    -- Groupoids are left-cancellative and right-cancellative.

    left-cancellative :
      ∀ {x y z} {p : y ∼ z} {q₁ q₂ : x ∼ y} →
      p ∘ q₁ ≡ p ∘ q₂ → q₁ ≡ q₂
    left-cancellative {p = p} {q₁} {q₂} p∘q₁≡p∘q₂ =
      q₁               ≡⟨ sym $ left-identity _ ⟩
      id ∘ q₁          ≡⟨ cong (_∘ _) $ sym $ left-inverse _ ⟩
      (p ⁻¹ ∘ p) ∘ q₁  ≡⟨ sym $ assoc _ _ _ ⟩
      p ⁻¹ ∘ (p ∘ q₁)  ≡⟨ cong (p ⁻¹ ∘_) p∘q₁≡p∘q₂ ⟩
      p ⁻¹ ∘ (p ∘ q₂)  ≡⟨ assoc _ _ _ ⟩
      (p ⁻¹ ∘ p) ∘ q₂  ≡⟨ cong (_∘ _) $ left-inverse _ ⟩
      id ∘ q₂          ≡⟨ left-identity _ ⟩∎
      q₂               ∎

    right-cancellative :
      ∀ {x y z} {p₁ p₂ : y ∼ z} {q : x ∼ y} →
      p₁ ∘ q ≡ p₂ ∘ q → p₁ ≡ p₂
    right-cancellative {p₁ = p₁} {p₂} {q} p₁∘q≡p₂∘q =
      p₁               ≡⟨ sym $ right-identity _ ⟩
      p₁ ∘ id          ≡⟨ cong (_ ∘_) $ sym $ right-inverse _ ⟩
      p₁ ∘ (q ∘ q ⁻¹)  ≡⟨ assoc _ _ _ ⟩
      (p₁ ∘ q) ∘ q ⁻¹  ≡⟨ cong (_∘ q ⁻¹) p₁∘q≡p₂∘q ⟩
      (p₂ ∘ q) ∘ q ⁻¹  ≡⟨ sym $ assoc _ _ _ ⟩
      p₂ ∘ (q ∘ q ⁻¹)  ≡⟨ cong (_ ∘_) $ right-inverse _ ⟩
      p₂ ∘ id          ≡⟨ right-identity _ ⟩∎
      p₂               ∎

    -- The inverse operator is involutive.

    involutive : ∀ {x y} (p : x ∼ y) → p ⁻¹ ⁻¹ ≡ p
    involutive p =
      p ⁻¹ ⁻¹               ≡⟨ sym $ right-identity (p ⁻¹ ⁻¹) ⟩
      p ⁻¹ ⁻¹ ∘ id          ≡⟨ sym $ cong (_∘_ (p ⁻¹ ⁻¹)) (left-inverse p) ⟩
      p ⁻¹ ⁻¹ ∘ (p ⁻¹ ∘ p)  ≡⟨ assoc _ _ _ ⟩
      (p ⁻¹ ⁻¹ ∘ p ⁻¹) ∘ p  ≡⟨ cong (λ q → q ∘ p) (left-inverse (p ⁻¹)) ⟩
      id ∘ p                ≡⟨ left-identity p ⟩∎
      p                     ∎

    -- A lemma that can be used to move something from one side of an
    -- equality to the other.

    ⁻¹∘≡→≡∘ :
      ∀ {x y z} {p : y ∼ z} {q : x ∼ z} {r : x ∼ y} →
      p ⁻¹ ∘ q ≡ r → q ≡ p ∘ r
    ⁻¹∘≡→≡∘ {p = p} {q = q} {r = r} hyp =
      q               ≡⟨ sym $ left-identity _ ⟩
      id ∘ q          ≡⟨ cong (_∘ _) $ sym $ right-inverse _ ⟩
      (p ∘ p ⁻¹) ∘ q  ≡⟨ sym $ assoc _ _ _ ⟩
      p ∘ (p ⁻¹ ∘ q)  ≡⟨ cong (_ ∘_) hyp ⟩∎
      p ∘ r           ∎

    -- A corollary.

    ⁻¹∘≡id→≡ : ∀ {x y} {p q : x ∼ y} → p ⁻¹ ∘ q ≡ id → q ≡ p
    ⁻¹∘≡id→≡ {p = p} {q = q} hyp =
      q       ≡⟨ ⁻¹∘≡→≡∘ hyp ⟩
      p ∘ id  ≡⟨ right-identity _ ⟩∎
      p       ∎

    -- Another lemma that can be used to move something from one side
    -- of an equality to the other.

    ∘⁻¹≡→≡∘ :
      ∀ {x y z} {p : z ∼ y} {q : z ∼ x} {r : x ∼ y} →
      p ∘ q ⁻¹ ≡ r → p ≡ r ∘ q
    ∘⁻¹≡→≡∘ {p = p} {q = q} {r = r} hyp =
      p               ≡⟨ sym $ right-identity _ ⟩
      p ∘ id          ≡⟨ cong (_ ∘_) $ sym $ left-inverse _ ⟩
      p ∘ (q ⁻¹ ∘ q)  ≡⟨ assoc _ _ _ ⟩
      (p ∘ q ⁻¹) ∘ q  ≡⟨ cong (_∘ _) hyp ⟩∎
      r ∘ q           ∎

    -- A corollary.

    ∘⁻¹≡id→≡ : ∀ {x y} {p q : x ∼ y} → p ∘ q ⁻¹ ≡ id → p ≡ q
    ∘⁻¹≡id→≡ {p = p} {q = q} hyp =
      p       ≡⟨ ∘⁻¹≡→≡∘ hyp ⟩
      id ∘ q  ≡⟨ left-identity _ ⟩∎
      q       ∎

    -- A lemma relating _∘_ and _⁻¹.

    ∘⁻¹ :
      ∀ {x y z} {p : y ∼ z} {q : x ∼ y} →
      (p ∘ q) ⁻¹ ≡ q ⁻¹ ∘ p ⁻¹
    ∘⁻¹ {p = p} {q = q} = right-cancellative
      ((p ∘ q) ⁻¹ ∘ (p ∘ q)     ≡⟨ left-inverse _ ⟩
       id                       ≡⟨ sym $ left-inverse _ ⟩
       q ⁻¹ ∘ q                 ≡⟨ cong (q ⁻¹ ∘_) $ sym $ left-identity _ ⟩
       q ⁻¹ ∘ (id ∘ q)          ≡⟨ cong (q ⁻¹ ∘_) $ cong (_∘ _) $ sym $ left-inverse _ ⟩
       q ⁻¹ ∘ ((p ⁻¹ ∘ p) ∘ q)  ≡⟨ cong (q ⁻¹ ∘_) $ sym $ assoc _ _ _ ⟩
       q ⁻¹ ∘ (p ⁻¹ ∘ (p ∘ q))  ≡⟨ assoc _ _ _ ⟩∎
       (q ⁻¹ ∘ p ⁻¹) ∘ (p ∘ q)  ∎)

  -- The inverse operator is a bijection.

  ⁻¹-bijection : ∀ {x y} → x ∼ y ↔ y ∼ x
  ⁻¹-bijection = record
    { surjection = record
      { logical-equivalence = record
        { to   = _⁻¹
        ; from = _⁻¹
        }
      ; right-inverse-of = involutive
      }
    ; left-inverse-of = involutive
    }
