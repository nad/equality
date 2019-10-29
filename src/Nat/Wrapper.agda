------------------------------------------------------------------------
-- A wrapper that turns a representation of natural numbers, possibly
-- with several representations for some numbers, into a
-- representation with unique representatives, that additionally
-- computes roughly like the unary natural numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality
open import Prelude hiding (zero; suc; _+_)
import Surjection

module Nat.Wrapper
  {reflexive}
  (eq : ∀ {a p} → Equality-with-J a p reflexive)
  (open Surjection eq using (_↠_))

  -- The underlying representation of natural numbers.
  (Nat′ : Set)
  -- A split surjection from this representation to the unary natural
  -- numbers.
  (Nat′↠ℕ : Nat′ ↠ ℕ)
  where

open Derived-definitions-and-properties eq

open import Bijection eq using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Erased.Cubical eq
open import Erased.Cubical.Singleton eq
open import Function-universe eq hiding (_∘_)
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc

private

  module N where
    open import Nat eq public
    open Prelude public using (zero; suc; _+_)

------------------------------------------------------------------------
-- The wrapper

private

  -- Converts from the underlying representation to unary natural
  -- numbers.

  to-ℕ : Nat′ → ℕ
  to-ℕ = _↠_.to Nat′↠ℕ

-- Natural numbers built on top of Nat′, indexed by corresponding
-- unary natural numbers, and truncated so that any two numbers that
-- stand for the same unary natural number are seen as equal.

Nat-[_] : @0 ℕ → Set
Nat-[ m ] = ∥ (∃ λ (n : Nat′) → Erased (to-ℕ n ≡ m)) ∥

-- Nat-[ n ] is a proposition.

Nat-[]-propositional : {@0 n : ℕ} → Is-proposition Nat-[ n ]
Nat-[]-propositional = truncation-is-proposition

-- A non-indexed variant of Nat-[_].

Nat : Set
Nat = ∃ λ (n : Erased ℕ) → Nat-[ erased n ]

-- Returns the (erased) index.

@0 ⌊_⌋ : Nat → ℕ
⌊ [ n ] , _ ⌋ = n

-- There is a bijection between equality of two values of type Nat and
-- erased equality of the corresponding unary natural number indices.

≡-for-indices↔≡ :
  {m n : Nat} →
  Erased (⌊ m ⌋ ≡ ⌊ n ⌋) ↔ m ≡ n
≡-for-indices↔≡ {m = m} {n = n} =
  Erased (⌊ m ⌋ ≡ ⌊ n ⌋)  ↝⟨ Erased-≡↔[]≡[] ⟩
  proj₁ m ≡ proj₁ n       ↝⟨ ignore-propositional-component Nat-[]-propositional ⟩□
  m ≡ n                   □

------------------------------------------------------------------------
-- Conversion functions

private

  -- Equality is very stable for the natural numbers.

  ℕ-very-stable : Very-stable-≡ ℕ
  ℕ-very-stable = Decidable-equality→Very-stable-≡ N._≟_

-- Nat-[ n ] is isomorphic to the type of natural numbers equal
-- (with erased equality proofs) to n.

Nat-[]↔Σℕ : {@0 n : ℕ} → Nat-[ n ] ↔ ∃ λ m → Erased (m ≡ n)
Nat-[]↔Σℕ = ↠→↔Erased-singleton Nat′↠ℕ ℕ-very-stable

-- Nat is isomorphic to the type of unary natural numbers.

Nat↔ℕ : Nat ↔ ℕ
Nat↔ℕ = Σ-Erased-∥-Σ-Erased-≡-∥↔ Nat′↠ℕ ℕ-very-stable

-- Converts from ℕ to Nat.

⌈_⌉ : ℕ → Nat
⌈_⌉ = _↔_.from Nat↔ℕ

-- The index matches the result of _↔_.to Nat↔ℕ.

@0 ≡⌊⌋ : ∀ n → _↔_.to Nat↔ℕ n ≡ ⌊ n ⌋
≡⌊⌋ n = to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ Nat′↠ℕ ℕ-very-stable n

------------------------------------------------------------------------
-- Arithmetic with Nat-[_]

-- A helper function that can be used to define constants.

nullary-[] :
  {@0 n : ℕ}
  (m : Nat′) →
  @0 to-ℕ m ≡ n →
  Nat-[ n ]
nullary-[] m hyp = ∣ m , [ hyp ] ∣

-- A helper function that can be used to define unary operators.

unary-[] :
  {@0 n : ℕ} {@0 f : ℕ → ℕ}
  (g : Nat′ → Nat′) →
  @0 (∀ n → to-ℕ (g n) ≡ f (to-ℕ n)) →
  Nat-[ n ] → Nat-[ f n ]
unary-[] {n = n} {f = f} g hyp = Trunc.rec
  truncation-is-proposition
  (uncurry λ n′ p →
     ∣ g n′
     , [ to-ℕ (g n′)  ≡⟨ hyp _ ⟩
         f (to-ℕ n′)  ≡⟨ cong f (erased p) ⟩∎
         f n          ∎
       ]
     ∣)

-- A helper function that can be used to define binary
-- operators.

binary-[] :
  {@0 m n : ℕ} {@0 f : ℕ → ℕ → ℕ}
  (g : Nat′ → Nat′ → Nat′) →
  @0 (∀ m n → to-ℕ (g m n) ≡ f (to-ℕ m) (to-ℕ n)) →
  Nat-[ m ] → Nat-[ n ] → Nat-[ f m n ]
binary-[] {m = m} {n = n} {f = f} g hyp = Trunc.rec
  (Π-closure ext 1 λ _ →
   truncation-is-proposition)
  (uncurry λ m′ p → Trunc.rec
     truncation-is-proposition
     (uncurry λ n′ q →
        ∣ g m′ n′
        , [ to-ℕ (g m′ n′)         ≡⟨ hyp _ _ ⟩
            f (to-ℕ m′) (to-ℕ n′)  ≡⟨ cong₂ f (erased p) (erased q) ⟩∎
            f m n                  ∎
          ]
        ∣))

-- The code below is parametrised by implementations of (and
-- correctness properties for) certain arithmetic operations for Nat′.

record Arithmetic : Set where
  field
    zero      : Nat′
    to-ℕ-zero : to-ℕ zero ≡ N.zero

    suc       : Nat′ → Nat′
    to-ℕ-suc  : ∀ n → to-ℕ (suc n) ≡ N.suc (to-ℕ n)

    _+_       : Nat′ → Nat′ → Nat′
    to-ℕ-+    : ∀ m n → to-ℕ (m + n) ≡ to-ℕ m N.+ to-ℕ n

    ⌊_/2⌋     : Nat′ → Nat′
    to-ℕ-⌊/2⌋ : ∀ n → to-ℕ ⌊ n /2⌋ ≡ N.⌊ to-ℕ n /2⌋

    ⌈_/2⌉     : Nat′ → Nat′
    to-ℕ-⌈/2⌉ : ∀ n → to-ℕ ⌈ n /2⌉ ≡ N.⌈ to-ℕ n /2⌉

-- If certain arithmetic operations are defined for Nat′, then they
-- can be defined for Nat-[_] as well.

module Arithmetic-for-Nat-[] (a : Arithmetic) where

  private

    module A = Arithmetic a

  -- Zero.

  zero : Nat-[ N.zero ]
  zero = nullary-[] A.zero A.to-ℕ-zero

  -- The number's successor.

  suc : {@0 n : ℕ} → Nat-[ n ] → Nat-[ N.suc n ]
  suc = unary-[] A.suc A.to-ℕ-suc

  -- Addition.

  infixl 6 _+_

  _+_ : {@0 m n : ℕ} → Nat-[ m ] → Nat-[ n ] → Nat-[ m N.+ n ]
  _+_ = binary-[] A._+_ A.to-ℕ-+

  -- Division by two, rounded downwards.

  ⌊_/2⌋ : {@0 n : ℕ} → Nat-[ n ] → Nat-[ N.⌊ n /2⌋ ]
  ⌊_/2⌋ = unary-[] A.⌊_/2⌋ A.to-ℕ-⌊/2⌋

  -- Division by two, rounded upwards.

  ⌈_/2⌉ : {@0 n : ℕ} → Nat-[ n ] → Nat-[ N.⌈ n /2⌉ ]
  ⌈_/2⌉ = unary-[] A.⌈_/2⌉ A.to-ℕ-⌈/2⌉

------------------------------------------------------------------------
-- Arithmetic with Nat

-- A helper function that can be used to define constants,
-- along with correctness results.
--
-- Note that the first of the correctness results holds by
-- definition.

nullary :
  (n : ℕ) (m : Nat′) →
  @0 to-ℕ m ≡ n →
  ∃ λ (o : Nat) →
    Erased (⌊ o ⌋ ≡ n) ×
    _↔_.to Nat↔ℕ o ≡ n
nullary n m hyp =
    o
  , [ refl _ ]
  , Very-stable→Stable 1 ℕ-very-stable _ _
       [ _↔_.to Nat↔ℕ o  ≡⟨ ≡⌊⌋ o ⟩
         ⌊ o ⌋           ≡⟨⟩
         n               ∎
       ]
  where
  o = _ , nullary-[] m hyp

-- A helper function that can be used to define unary operators,
-- along with correctness results.
--
-- Note that the first of the correctness results holds by
-- definition.

unary :
  (f : ℕ → ℕ) (g : Nat′ → Nat′) →
  @0 (∀ n → to-ℕ (g n) ≡ f (to-ℕ n)) →
  ∃ λ (h : Nat → Nat) →
    (∀ n → Erased (⌊ h n ⌋ ≡ f ⌊ n ⌋)) ×
    (∀ n → _↔_.to Nat↔ℕ (h n) ≡ f (_↔_.to Nat↔ℕ n))
unary f g hyp =
    h
  , (λ _ → [ refl _ ])
  , (λ n → Very-stable→Stable 1 ℕ-very-stable _ _
       [ _↔_.to Nat↔ℕ (h n)  ≡⟨ ≡⌊⌋ (h n) ⟩
         ⌊ h n ⌋             ≡⟨⟩
         f ⌊ n ⌋             ≡⟨ sym $ cong f $ ≡⌊⌋ n ⟩∎
         f (_↔_.to Nat↔ℕ n)  ∎
       ])
  where
  h = Σ-map _ (unary-[] g hyp)

-- A helper function that can be used to define binary operators,
-- along with correctness results.
--
-- Note that the first of the correctness results holds by
-- definition.

binary :
  (f : ℕ → ℕ → ℕ) (g : Nat′ → Nat′ → Nat′) →
  @0 (∀ m n → to-ℕ (g m n) ≡ f (to-ℕ m) (to-ℕ n)) →
  ∃ λ (h : Nat → Nat → Nat) →
    (∀ m n → Erased (⌊ h m n ⌋ ≡ f ⌊ m ⌋ ⌊ n ⌋)) ×
    (∀ m n →
       _↔_.to Nat↔ℕ (h m n) ≡ f (_↔_.to Nat↔ℕ m) (_↔_.to Nat↔ℕ n))
binary f g hyp =
    h
  , (λ _ _ → [ refl _ ])
  , (λ m n → Very-stable→Stable 1 ℕ-very-stable _ _
       [ _↔_.to Nat↔ℕ (h m n)                 ≡⟨ ≡⌊⌋ (h m n) ⟩
         ⌊ h m n ⌋                            ≡⟨⟩
         f ⌊ m ⌋ ⌊ n ⌋                        ≡⟨ sym $ cong₂ f (≡⌊⌋ m) (≡⌊⌋ n) ⟩∎
         f (_↔_.to Nat↔ℕ m) (_↔_.to Nat↔ℕ n)  ∎
       ])
  where
  h = Σ-zip _ (binary-[] g hyp)

-- If certain arithmetic operations are defined for Nat′, then they
-- can be defined for Nat-[_] as well.

module Arithmetic-for-Nat (a : Arithmetic) where

  private

    module A = Arithmetic a

  -- Zero.

  private

    zero′ = nullary N.zero A.zero A.to-ℕ-zero

  zero : Nat
  zero = proj₁ zero′

  to-ℕ-zero : _↔_.to Nat↔ℕ zero ≡ N.zero
  to-ℕ-zero = proj₂ (proj₂ zero′)

  -- The number's successor.

  private

    suc′ = unary N.suc A.suc A.to-ℕ-suc

  suc : Nat → Nat
  suc = proj₁ suc′

  to-ℕ-suc : ∀ n → _↔_.to Nat↔ℕ (suc n) ≡ N.suc (_↔_.to Nat↔ℕ n)
  to-ℕ-suc = proj₂ (proj₂ suc′)

  -- Addition.

  private

    +′ = binary N._+_ A._+_ A.to-ℕ-+

  infixl 6 _+_

  _+_ : Nat → Nat → Nat
  _+_ = proj₁ +′

  to-ℕ-+ :
    ∀ m n → _↔_.to Nat↔ℕ (m + n) ≡ _↔_.to Nat↔ℕ m N.+ _↔_.to Nat↔ℕ n
  to-ℕ-+ = proj₂ (proj₂ +′)

  -- Division by two, rounded downwards.

  private

    ⌊/2⌋ = unary N.⌊_/2⌋ A.⌊_/2⌋ A.to-ℕ-⌊/2⌋

  ⌊_/2⌋ : Nat → Nat
  ⌊_/2⌋ = proj₁ ⌊/2⌋

  to-ℕ-⌊/2⌋ : ∀ n → _↔_.to Nat↔ℕ ⌊ n /2⌋ ≡ N.⌊ _↔_.to Nat↔ℕ n /2⌋
  to-ℕ-⌊/2⌋ = proj₂ (proj₂ ⌊/2⌋)

  -- Division by two, rounded upwards.

  private

    ⌈/2⌉ = unary N.⌈_/2⌉ A.⌈_/2⌉ A.to-ℕ-⌈/2⌉

  ⌈_/2⌉ : Nat → Nat
  ⌈_/2⌉ = proj₁ ⌈/2⌉

  to-ℕ-⌈/2⌉ : ∀ n → _↔_.to Nat↔ℕ ⌈ n /2⌉ ≡ N.⌈ _↔_.to Nat↔ℕ n /2⌉
  to-ℕ-⌈/2⌉ = proj₂ (proj₂ ⌈/2⌉)

------------------------------------------------------------------------
-- Some examples

private

  module Nat-[]-examples (a : Arithmetic) where

    open Arithmetic-for-Nat-[] a

    -- Converts unary natural numbers to binary natural numbers.

    from-ℕ : ∀ n → Nat-[ n ]
    from-ℕ = proj₂ ∘ _↔_.from Nat↔ℕ

    -- Nat n is a proposition, so it is easy to prove that two values
    -- of this type are equal.

    example₁ : from-ℕ 4 + ⌊ from-ℕ 12 /2⌋ ≡ from-ℕ 10
    example₁ = Nat-[]-propositional _ _

    -- However, stating that two values of type Nat m and Nat n are
    -- equal, for equal natural numbers m and n, can be awkward.

    @0 example₂ :
      {@0 m n : ℕ} →
      (b : Nat-[ m ]) (c : Nat-[ n ]) →
      subst Nat-[_] (N.+-comm m) (b + c) ≡ c + b
    example₂ _ _ = Nat-[]-propositional _ _

  module Nat-examples (a : Arithmetic) where

    open Arithmetic-for-Nat a

    -- If Nat is used instead of Nat-[_], then it can be easier to
    -- state that two values are equal.

    example₁ : ⌈ 4 ⌉ + ⌊ ⌈ 12 ⌉ /2⌋ ≡ ⌈ 10 ⌉
    example₁ = _↔_.to ≡-for-indices↔≡ [ refl _ ]

    example₂ : ∀ m n → m + n ≡ n + m
    example₂ m n = _↔_.to ≡-for-indices↔≡
      [ ⌊ m ⌋ N.+ ⌊ n ⌋  ≡⟨ N.+-comm ⌊ m ⌋ ⟩∎
        ⌊ n ⌋ N.+ ⌊ m ⌋  ∎
      ]
