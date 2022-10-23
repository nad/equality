------------------------------------------------------------------------
-- Groupoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Groupoid
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude hiding (id; _∘_; _^_)

open import Bijection eq hiding (id; _∘_)
open Derived-definitions-and-properties eq
open import Integer.Basics eq as Int using (ℤ; +_; -[1+_])
import Nat eq as Nat

private
  variable
    a       : Level
    A       : Type a
    w x y z : A
    n       : ℕ
    j       : ℤ

-- Groupoids using _≡_ as the underlying equality.

record Groupoid o ℓ : Type (lsuc (o ⊔ ℓ)) where
  infix  8 _⁻¹
  infixr 7 _∘_
  infix  4 _∼_
  field
    Object : Type o
    _∼_    : Object → Object → Type ℓ

    id  : x ∼ x
    _∘_ : y ∼ z → x ∼ y → x ∼ z
    _⁻¹ : x ∼ y → y ∼ x

    left-identity  : (p : x ∼ y) → id ∘ p ≡ p
    right-identity : (p : x ∼ y) → p ∘ id ≡ p
    assoc          : (p : y ∼ z) (q : x ∼ y) (r : w ∼ x) →
                     p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    left-inverse   : (p : x ∼ y) → p ⁻¹ ∘ p ≡ id
    right-inverse  : (p : x ∼ y) → p ∘ p ⁻¹ ≡ id

  -- Note that this definition should perhaps contain more coherence
  -- properties: we have not assumed that _≡_ is proof-irrelevant.

  private
    variable
      p p₁ p₂ q q₁ q₂ r : x ∼ y

  -- Some derived properties.

  abstract

    -- The identity is an identity for the inverse operator as well.

    identity : id {x = x} ⁻¹ ≡ id
    identity =
      id ⁻¹       ≡⟨ sym $ right-identity (id ⁻¹) ⟩
      id ⁻¹ ∘ id  ≡⟨ left-inverse id ⟩∎
      id          ∎

    -- If p is idempotent with respect to _∘_, then p is equal to the
    -- identity element.

    idempotent⇒≡id : p ∘ p ≡ p → p ≡ id
    idempotent⇒≡id {p = p} p∘p≡p =
      p               ≡⟨ sym $ left-identity _ ⟩
      id ∘ p          ≡⟨ cong (_∘ _) $ sym $ left-inverse _ ⟩
      (p ⁻¹ ∘ p) ∘ p  ≡⟨ sym $ assoc _ _ _ ⟩
      p ⁻¹ ∘ (p ∘ p)  ≡⟨ cong (p ⁻¹ ∘_) p∘p≡p ⟩
      p ⁻¹ ∘ p        ≡⟨ left-inverse _ ⟩∎
      id              ∎

    -- Groupoids are left-cancellative and right-cancellative.

    left-cancellative :
      p ∘ q₁ ≡ p ∘ q₂ → q₁ ≡ q₂
    left-cancellative {p = p} {q₁ = q₁} {q₂ = q₂} p∘q₁≡p∘q₂ =
      q₁               ≡⟨ sym $ left-identity _ ⟩
      id ∘ q₁          ≡⟨ cong (_∘ _) $ sym $ left-inverse _ ⟩
      (p ⁻¹ ∘ p) ∘ q₁  ≡⟨ sym $ assoc _ _ _ ⟩
      p ⁻¹ ∘ (p ∘ q₁)  ≡⟨ cong (p ⁻¹ ∘_) p∘q₁≡p∘q₂ ⟩
      p ⁻¹ ∘ (p ∘ q₂)  ≡⟨ assoc _ _ _ ⟩
      (p ⁻¹ ∘ p) ∘ q₂  ≡⟨ cong (_∘ _) $ left-inverse _ ⟩
      id ∘ q₂          ≡⟨ left-identity _ ⟩∎
      q₂               ∎

    right-cancellative :
      p₁ ∘ q ≡ p₂ ∘ q → p₁ ≡ p₂
    right-cancellative {p₁ = p₁} {q = q} {p₂ = p₂} p₁∘q≡p₂∘q =
      p₁               ≡⟨ sym $ right-identity _ ⟩
      p₁ ∘ id          ≡⟨ cong (_ ∘_) $ sym $ right-inverse _ ⟩
      p₁ ∘ (q ∘ q ⁻¹)  ≡⟨ assoc _ _ _ ⟩
      (p₁ ∘ q) ∘ q ⁻¹  ≡⟨ cong (_∘ q ⁻¹) p₁∘q≡p₂∘q ⟩
      (p₂ ∘ q) ∘ q ⁻¹  ≡⟨ sym $ assoc _ _ _ ⟩
      p₂ ∘ (q ∘ q ⁻¹)  ≡⟨ cong (_ ∘_) $ right-inverse _ ⟩
      p₂ ∘ id          ≡⟨ right-identity _ ⟩∎
      p₂               ∎

    -- The inverse operator is involutive.

    involutive : (p : x ∼ y) → p ⁻¹ ⁻¹ ≡ p
    involutive p =
      p ⁻¹ ⁻¹               ≡⟨ sym $ right-identity (p ⁻¹ ⁻¹) ⟩
      p ⁻¹ ⁻¹ ∘ id          ≡⟨ sym $ cong (_∘_ (p ⁻¹ ⁻¹)) (left-inverse p) ⟩
      p ⁻¹ ⁻¹ ∘ (p ⁻¹ ∘ p)  ≡⟨ assoc _ _ _ ⟩
      (p ⁻¹ ⁻¹ ∘ p ⁻¹) ∘ p  ≡⟨ cong (λ q → q ∘ p) (left-inverse (p ⁻¹)) ⟩
      id ∘ p                ≡⟨ left-identity p ⟩∎
      p                     ∎

    -- A lemma that can be used to move something from one side of an
    -- equality to the other.

    ⁻¹∘≡→≡∘ : p ⁻¹ ∘ q ≡ r → q ≡ p ∘ r
    ⁻¹∘≡→≡∘ {p = p} {q = q} {r = r} hyp =
      q               ≡⟨ sym $ left-identity _ ⟩
      id ∘ q          ≡⟨ cong (_∘ _) $ sym $ right-inverse _ ⟩
      (p ∘ p ⁻¹) ∘ q  ≡⟨ sym $ assoc _ _ _ ⟩
      p ∘ (p ⁻¹ ∘ q)  ≡⟨ cong (_ ∘_) hyp ⟩∎
      p ∘ r           ∎

    -- A corollary.

    ⁻¹∘≡id→≡ : p ⁻¹ ∘ q ≡ id → q ≡ p
    ⁻¹∘≡id→≡ {p = p} {q = q} hyp =
      q       ≡⟨ ⁻¹∘≡→≡∘ hyp ⟩
      p ∘ id  ≡⟨ right-identity _ ⟩∎
      p       ∎

    -- Another lemma that can be used to move something from one side
    -- of an equality to the other.

    ∘⁻¹≡→≡∘ : p ∘ q ⁻¹ ≡ r → p ≡ r ∘ q
    ∘⁻¹≡→≡∘ {p = p} {q = q} {r = r} hyp =
      p               ≡⟨ sym $ right-identity _ ⟩
      p ∘ id          ≡⟨ cong (_ ∘_) $ sym $ left-inverse _ ⟩
      p ∘ (q ⁻¹ ∘ q)  ≡⟨ assoc _ _ _ ⟩
      (p ∘ q ⁻¹) ∘ q  ≡⟨ cong (_∘ _) hyp ⟩∎
      r ∘ q           ∎

    -- A corollary.

    ∘⁻¹≡id→≡ : p ∘ q ⁻¹ ≡ id → p ≡ q
    ∘⁻¹≡id→≡ {p = p} {q = q} hyp =
      p       ≡⟨ ∘⁻¹≡→≡∘ hyp ⟩
      id ∘ q  ≡⟨ left-identity _ ⟩∎
      q       ∎

    -- A lemma relating _∘_ and _⁻¹.

    ∘⁻¹ : (p ∘ q) ⁻¹ ≡ q ⁻¹ ∘ p ⁻¹
    ∘⁻¹ {p = p} {q = q} = right-cancellative
      ((p ∘ q) ⁻¹ ∘ (p ∘ q)     ≡⟨ left-inverse _ ⟩
       id                       ≡⟨ sym $ left-inverse _ ⟩
       q ⁻¹ ∘ q                 ≡⟨ cong (q ⁻¹ ∘_) $ sym $ left-identity _ ⟩
       q ⁻¹ ∘ (id ∘ q)          ≡⟨ cong (q ⁻¹ ∘_) $ cong (_∘ _) $ sym $ left-inverse _ ⟩
       q ⁻¹ ∘ ((p ⁻¹ ∘ p) ∘ q)  ≡⟨ cong (q ⁻¹ ∘_) $ sym $ assoc _ _ _ ⟩
       q ⁻¹ ∘ (p ⁻¹ ∘ (p ∘ q))  ≡⟨ assoc _ _ _ ⟩∎
       (q ⁻¹ ∘ p ⁻¹) ∘ (p ∘ q)  ∎)

    -- If p ∘ q is equal to id, then q is equal to p ⁻¹.

    ⁻¹-unique-right : p ∘ q ≡ id → q ≡ p ⁻¹
    ⁻¹-unique-right {p = p} {q = q} ∘≡id = ⁻¹∘≡id→≡
      (p ⁻¹ ⁻¹ ∘ q  ≡⟨ cong (_∘ _) $ involutive _ ⟩
       p ∘ q        ≡⟨ ∘≡id ⟩∎
       id           ∎)

    -- If p ∘ q is equal to id, then p is equal to q ⁻¹.

    ⁻¹-unique-left : p ∘ q ≡ id → p ≡ q ⁻¹
    ⁻¹-unique-left {p = p} {q = q} ∘≡id = ∘⁻¹≡id→≡
      (p ∘ q ⁻¹ ⁻¹  ≡⟨ cong (_ ∘_) $ involutive _ ⟩
       p ∘ q        ≡⟨ ∘≡id ⟩∎
       id           ∎)

  -- The inverse operator is a bijection.

  ⁻¹-bijection : x ∼ y ↔ y ∼ x
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

  -- Exponentiation.

  infixl 8 _^+_
  infixr 8 _^_

  _^+_ : x ∼ x → ℕ → x ∼ x
  p ^+ 0     = id
  p ^+ suc n = p ∘ p ^+ n

  _^_ : x ∼ x → ℤ → x ∼ x
  p ^ + n      = p ^+ n
  p ^ -[1+ n ] = (p ⁻¹) ^+ suc n

  -- _^+_ is homomorphic with respect to _∘_/_+_.

  ^+∘^+ : ∀ m → p ^+ m ∘ p ^+ n ≡ p ^+ (m + n)
  ^+∘^+ {p = p} {n = n} zero =
    id ∘ p ^+ n  ≡⟨ left-identity _ ⟩∎
    p ^+ n       ∎
  ^+∘^+ {p = p} {n = n} (suc m) =
    (p ∘ p ^+ m) ∘ p ^+ n  ≡⟨ sym $ assoc _ _ _ ⟩
    p ∘ (p ^+ m ∘ p ^+ n)  ≡⟨ cong (_ ∘_) $ ^+∘^+ m ⟩∎
    p ∘ p ^+ (m + n)       ∎

  -- Some rearrangement lemmas for _^+_.

  ∘^+≡^+∘ :
    p ∘ q ≡ q ∘ p →
    ∀ n → p ∘ q ^+ n ≡ q ^+ n ∘ p
  ∘^+≡^+∘ {p = p} _ zero =
    p ∘ id  ≡⟨ right-identity _ ⟩
    p       ≡⟨ sym $ left-identity _ ⟩∎
    id ∘ p  ∎
  ∘^+≡^+∘ {p = p} {q = q} comm (suc n) =
    p ∘ (q ∘ q ^+ n)  ≡⟨ assoc _ _ _ ⟩
    (p ∘ q) ∘ q ^+ n  ≡⟨ cong (_∘ q ^+ n) comm ⟩
    (q ∘ p) ∘ q ^+ n  ≡⟨ sym $ assoc _ _ _ ⟩
    q ∘ (p ∘ q ^+ n)  ≡⟨ cong (q ∘_) $ ∘^+≡^+∘ comm n ⟩
    q ∘ (q ^+ n ∘ p)  ≡⟨ assoc _ _ _ ⟩∎
    (q ∘ q ^+ n) ∘ p  ∎

  ^+∘^+≡^+∘^+ : ∀ m n → p ^+ m ∘ p ^+ n ≡ p ^+ n ∘ p ^+ m
  ^+∘^+≡^+∘^+ {p = p} m n =
    p ^+ m ∘ p ^+ n  ≡⟨ ^+∘^+ m ⟩
    p ^+ (m + n)     ≡⟨ cong (p ^+_) $ Nat.+-comm m ⟩
    p ^+ (n + m)     ≡⟨ sym $ ^+∘^+ n ⟩∎
    p ^+ n ∘ p ^+ m  ∎

  private

    -- Some lemmas which are used to define ^∘^ below.

    lemma₁ : ∀ n → (p ∘ p ^+ n) ∘ (p ⁻¹ ∘ q) ≡ p ^+ n ∘ q
    lemma₁ {p = p} {q = q} n =
      (p ∘ p ^+ n) ∘ (p ⁻¹ ∘ q)  ≡⟨ cong (_∘ (p ⁻¹ ∘ q)) $ ∘^+≡^+∘ (refl _) n ⟩
      (p ^+ n ∘ p) ∘ (p ⁻¹ ∘ q)  ≡⟨ sym $ assoc _ _ _ ⟩
      p ^+ n ∘ (p ∘ (p ⁻¹ ∘ q))  ≡⟨ cong (p ^+ n ∘_) $ assoc _ _ _ ⟩
      p ^+ n ∘ ((p ∘ p ⁻¹) ∘ q)  ≡⟨ cong (p ^+ n ∘_) $ cong (_∘ q) $ right-inverse _ ⟩
      p ^+ n ∘ (id ∘ q)          ≡⟨ cong (p ^+ n ∘_) $ left-identity _ ⟩∎
      p ^+ n ∘ q                 ∎

    lemma₂ : ∀ n → (p ⁻¹ ∘ (p ⁻¹) ^+ n) ∘ (p ∘ q) ≡ (p ⁻¹) ^+ n ∘ q
    lemma₂ {p = p} {q = q} n =
      (p ⁻¹ ∘ (p ⁻¹) ^+ n) ∘ (p ∘ q)        ≡⟨ cong (λ r → (p ⁻¹ ∘ (p ⁻¹) ^+ n) ∘ (r ∘ q)) $ sym $ involutive _ ⟩
      (p ⁻¹ ∘ (p ⁻¹) ^+ n) ∘ (p ⁻¹ ⁻¹ ∘ q)  ≡⟨ lemma₁ n ⟩∎
      (p ⁻¹) ^+ n ∘ q                       ∎

    lemma₃ : ∀ m n → p ^+ m ∘ (p ⁻¹) ^+ suc n ≡ p ^ Int.+ m +-[1+ n ]
    lemma₃ {p = p} zero n =
      id ∘ (p ⁻¹) ^+ suc n  ≡⟨ left-identity _ ⟩∎
      (p ⁻¹) ^+ suc n       ∎
    lemma₃ {p = p} (suc m) zero =
      (p ∘ p ^+ m) ∘ p ⁻¹ ∘ id  ≡⟨ lemma₁ m ⟩
      p ^+ m ∘ id               ≡⟨ right-identity _ ⟩∎
      p ^+ m                    ∎
    lemma₃ {p = p} (suc m) (suc n) =
      (p ∘ p ^+ m) ∘ (p ⁻¹ ∘ (p ⁻¹) ^+ suc n)  ≡⟨ lemma₁ m ⟩
      p ^+ m ∘ (p ⁻¹) ^+ suc n                 ≡⟨ lemma₃ m n ⟩∎
      p ^ Int.+ m +-[1+ n ]                    ∎

    lemma₄ : ∀ m n → (p ⁻¹) ^+ suc m ∘ p ^+ n ≡ p ^ Int.+ n +-[1+ m ]
    lemma₄ {p = p} m zero =
      (p ⁻¹) ^+ suc m ∘ id  ≡⟨ right-identity _ ⟩∎
      (p ⁻¹) ^+ suc m       ∎
    lemma₄ {p = p} zero (suc n) =
      (p ⁻¹ ∘ id) ∘ p ∘ p ^+ n  ≡⟨ lemma₂ zero ⟩
      id ∘ p ^+ n               ≡⟨ left-identity _ ⟩∎
      p ^+ n                    ∎
    lemma₄ {p = p} (suc m) (suc n) =
      (p ⁻¹ ∘ (p ⁻¹) ^+ suc m) ∘ (p ∘ p ^+ n)  ≡⟨ lemma₂ (suc m) ⟩
      (p ⁻¹) ^+ suc m ∘ p ^+ n                 ≡⟨ lemma₄ m n ⟩∎
      p ^ Int.+ n +-[1+ m ]                    ∎

  -- _^_ is homomorphic with respect to _∘_/Int._+_.

  ^∘^ : ∀ i → p ^ i ∘ p ^ j ≡ p ^ (i Int.+ j)
  ^∘^ {j = + _}      (+ m)            = ^+∘^+ m
  ^∘^ {j = -[1+ n ]} (+ m)            = lemma₃ m n
  ^∘^ {j = + n}      -[1+ m ]         = lemma₄ m n
  ^∘^ {p = p} {j = -[1+ n ]} -[1+ m ] =
    (p ⁻¹) ^+ suc m ∘ (p ⁻¹) ^+ suc n  ≡⟨ ^+∘^+ (suc m) ⟩
    (p ⁻¹) ^+ (suc m + suc n)          ≡⟨ cong ((p ⁻¹) ^+_) $ cong suc $ sym $ Nat.suc+≡+suc m ⟩∎
    (p ⁻¹) ^+ (2 + m + n)              ∎

  -- _^+ n commutes with _⁻¹.

  ^+⁻¹ : ∀ n → (p ^+ n) ⁻¹ ≡ (p ⁻¹) ^+ n
  ^+⁻¹         zero    = identity
  ^+⁻¹ {p = p} (suc n) =
    (p ∘ p ^+ n) ⁻¹     ≡⟨ ∘⁻¹ ⟩
    (p ^+ n) ⁻¹ ∘ p ⁻¹  ≡⟨ cong (_∘ p ⁻¹) $ ^+⁻¹ n ⟩
    (p ⁻¹) ^+ n ∘ p ⁻¹  ≡⟨ sym $ ∘^+≡^+∘ (refl _) n ⟩∎
    p ⁻¹ ∘ (p ⁻¹) ^+ n  ∎

  -- _^ i commutes with _⁻¹.

  ^⁻¹ : ∀ i → (p ^ i) ⁻¹ ≡ (p ⁻¹) ^ i
  ^⁻¹ (+ n)    = ^+⁻¹ n
  ^⁻¹ -[1+ n ] = ^+⁻¹ (suc n)

  -- Any power of id is equal to id.

  id^+ : ∀ n → id ^+ n ≡ id {x = x}
  id^+ zero    = refl _
  id^+ (suc n) =
    id ∘ id ^+ n  ≡⟨ left-identity _ ⟩
    id ^+ n       ≡⟨ id^+ n ⟩∎
    id            ∎

  id^ : ∀ i → id ^ i ≡ id {x = x}
  id^ (+ n) = id^+ n
  id^ -[1+ n ] =
    (id ⁻¹) ^+ suc n  ≡⟨ sym $ ^+⁻¹ (suc n) ⟩
    (id ^+ suc n) ⁻¹  ≡⟨ cong _⁻¹ $ id^+ (suc n) ⟩
    id ⁻¹             ≡⟨ identity ⟩∎
    id                ∎

  private

    lemma₅ : ∀ m n → p ^+ suc m ^+ n ≡ p ^+ n ∘ p ^+ m ^+ n
    lemma₅ _ zero =
      id       ≡⟨ sym $ left-identity _ ⟩∎
      id ∘ id  ∎
    lemma₅ {p = p} m (suc n) =
      p ^+ suc m ∘ p ^+ suc m ^+ n           ≡⟨ cong (p ^+ suc m ∘_) $ lemma₅ m n ⟩
      p ^+ suc m ∘ (p ^+ n ∘ p ^+ m ^+ n)    ≡⟨ assoc _ _ _ ⟩
      (p ^+ suc m ∘ p ^+ n) ∘ p ^+ m ^+ n    ≡⟨⟩
      ((p ∘ p ^+ m) ∘ p ^+ n) ∘ p ^+ m ^+ n  ≡⟨ cong (_∘ p ^+ m ^+ n) $ sym $ assoc _ _ _ ⟩
      (p ∘ p ^+ m ∘ p ^+ n) ∘ p ^+ m ^+ n    ≡⟨ cong (_∘ p ^+ m ^+ n) $ cong (p ∘_) $ ^+∘^+≡^+∘^+ m n ⟩
      (p ∘ p ^+ n ∘ p ^+ m) ∘ p ^+ m ^+ n    ≡⟨ cong (_∘ p ^+ m ^+ n) $ assoc _ _ _ ⟩
      ((p ∘ p ^+ n) ∘ p ^+ m) ∘ p ^+ m ^+ n  ≡⟨ sym $ assoc _ _ _ ⟩∎
      (p ∘ p ^+ n) ∘ p ^+ m ∘ p ^+ m ^+ n    ∎

  -- More rearrangement lemmas for _^+_.

  ^+^+≡^+* : ∀ m → p ^+ m ^+ n ≡ p ^+ (m * n)
  ^+^+≡^+* {n = n} zero =
    id ^+ n  ≡⟨ id^+ n ⟩∎
    id       ∎
  ^+^+≡^+* {p = p} {n = n} (suc m) =
    p ^+ suc m ^+ n        ≡⟨ lemma₅ m n ⟩
    p ^+ n ∘ p ^+ m ^+ n   ≡⟨ cong (p ^+ n ∘_) $ ^+^+≡^+* m ⟩
    p ^+ n ∘ p ^+ (m * n)  ≡⟨ ^+∘^+ n ⟩
    p ^+ (n + m * n)       ≡⟨⟩
    p ^+ (suc m * n)       ∎

  ∘^+≡^+∘^+ :
    p ∘ q ≡ q ∘ p →
    ∀ n →
    (p ∘ q) ^+ n ≡ p ^+ n ∘ q ^+ n
  ∘^+≡^+∘^+ _ zero =
    id       ≡⟨ sym $ left-identity _ ⟩∎
    id ∘ id  ∎
  ∘^+≡^+∘^+ {p = p} {q = q} comm (suc n) =
    (p ∘ q) ^+ suc n             ≡⟨⟩
    (p ∘ q) ∘ (p ∘ q) ^+ n       ≡⟨ cong ((p ∘ q) ∘_) $ ∘^+≡^+∘^+ comm n ⟩
    (p ∘ q) ∘ (p ^+ n ∘ q ^+ n)  ≡⟨ sym $ assoc _ _ _ ⟩
    p ∘ (q ∘ p ^+ n ∘ q ^+ n)    ≡⟨ cong (p ∘_) $ assoc _ _ _ ⟩
    p ∘ ((q ∘ p ^+ n) ∘ q ^+ n)  ≡⟨ cong (p ∘_) $ cong (_∘ (q ^+ n)) $ ∘^+≡^+∘ (sym comm) n ⟩
    p ∘ ((p ^+ n ∘ q) ∘ q ^+ n)  ≡⟨ cong (p ∘_) $ sym $ assoc _ _ _ ⟩
    p ∘ (p ^+ n ∘ q ∘ q ^+ n)    ≡⟨ assoc _ _ _ ⟩
    (p ∘ p ^+ n) ∘ q ∘ q ^+ n    ≡⟨⟩
    p ^+ suc n ∘ q ^+ suc n      ∎
