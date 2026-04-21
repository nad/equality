------------------------------------------------------------------------
-- An instantiation of Nat.Wrapper with binary natural numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
import Erased.Without-box-cong

module Nat.Wrapper.Binary
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)

  -- An instantiation of the []-cong axioms.
  (ax : ∀ {a} → Erased.Without-box-cong.[]-cong-axiomatisation eq a)
  where

open Derived-definitions-and-properties eq

open import Dec
open import Prelude renaming (_+_ to _⊕_)

open import Bijection eq using (_↔_)
open import Erased eq ax
import Nat eq as Nat
import Nat.Binary eq as Bin
import Nat.Wrapper eq as Wrapper

------------------------------------------------------------------------
-- Binary natural numbers

private

  module Bin-wrapper = Wrapper Bin.Bin Bin.Bin↔ℕ
  open Bin-wrapper using (Operations)

-- Some definitions from Nat.Wrapper are reexported.

open Bin-wrapper public
  using (⌊_⌋; ⌈_⌉; ≡⌊⌋;
         nullary-[]; nullary; nullary-correct;
         unary-[]; unary; unary-correct;
         binary-[]; binary; binary-correct;
         n-ary-[]; n-ary; n-ary-correct)
  renaming
    ( Nat-[_] to Bin-[_]
    ; Nat to Bin
    ; Nat-[]↔Σℕ to Bin-[]↔Σℕ
    )

open Bin-wrapper.[]-cong ax public
  using (≡-for-indices↔≡)
  renaming
    ( Nat-[]-propositional to Bin-[]-propositional
    ; Nat↔ℕ to Bin↔ℕ
    )

private

  -- An implementation of some operations for Bin.

  Operations-for-Bin : Operations
  Operations-for-Bin = λ where
    .Operations.zero                   → Bin.zero
    .Operations.to-ℕ-zero              → Bin.to-ℕ-zero
    .Operations.suc                    → Bin.suc
    .Operations.to-ℕ-suc               → Bin.to-ℕ-suc
    .Operations._+_                    → Bin._+_
    .Operations.to-ℕ-+                 → Bin.to-ℕ-+
    .Operations._*_                    → Bin._*_
    .Operations.to-ℕ-*                 → Bin.to-ℕ-*
    .Operations._^_                    → Bin._^_
    .Operations.to-ℕ-^                 → Bin.to-ℕ-^
    .Operations.⌊_/2⌋                  → Bin.⌊_/2⌋
    .Operations.to-ℕ-⌊/2⌋              → Bin.to-ℕ-⌊/2⌋
    .Operations.⌈_/2⌉                  → Bin.⌈_/2⌉
    .Operations.to-ℕ-⌈/2⌉              → Bin.to-ℕ-⌈/2⌉
    .Operations._*2^_                  → Bin._*2^_
    .Operations.to-ℕ-*2^               → Bin.to-ℕ-*2^
    .Operations._≟_                    → Bin._≟_
    .Operations.from-bits              → Bin.from-bits
    .Operations.to-ℕ-from-bits         → Bin.to-ℕ-from-bits
    .Operations.to-bits                → Bin.to-bits
    .Operations.to-ℕ-from-bits-to-bits → Bin.to-ℕ-from-bits-to-bits

-- Operations for Bin-[_].

module Operations-for-Bin-[] =
  Bin-wrapper.Operations-for-Nat-[] Operations-for-Bin

-- Operations for Bin.

module Operations-for-Bin =
  Bin-wrapper.Operations-for-Nat Operations-for-Bin

------------------------------------------------------------------------
-- Some examples

private

  module Bin-[]-examples where

    open Operations-for-Bin-[]

    -- Converts unary natural numbers to binary natural numbers.

    from-ℕ : ∀ n → Bin-[ n ]
    from-ℕ = proj₂ ∘ _↔_.from Bin↔ℕ

    -- Bin n is a proposition, so it is easy to prove that two values
    -- of this type are equal.

    example₁ : from-ℕ 4 + ⌊ from-ℕ 12 /2⌋ ≡ from-ℕ 10
    example₁ = Bin-[]-propositional _ _

    -- However, stating that two values of type Bin m and Bin n are
    -- equal, for equal natural numbers m and n, can be awkward.

    @0 example₂ :
      {@0 m n : ℕ}
      (b : Bin-[ m ]) (c : Bin-[ n ]) →
      subst (λ n → Bin-[ n ]) (Nat.+-comm m) (b + c) ≡ c + b
    example₂ _ _ = Bin-[]-propositional _ _

  module Bin-examples where

    open Operations-for-Bin

    -- If Bin is used instead of Bin-[_], then it can be easier to
    -- state that two values are equal.

    example₁ : ⌈ 4 ⌉ + ⌊ ⌈ 12 ⌉ /2⌋ ≡ ⌈ 10 ⌉
    example₁ = _↔_.to ≡-for-indices↔≡ [ refl _ ]

    example₂ : ∀ m n → m + n ≡ n + m
    example₂ m n = _↔_.to ≡-for-indices↔≡
      [ ⌊ m ⌋ ⊕ ⌊ n ⌋  ≡⟨ Nat.+-comm ⌊ m ⌋ ⟩∎
        ⌊ n ⌋ ⊕ ⌊ m ⌋  ∎
      ]

    -- One can construct a proof showing that ⌈ 5 ⌉ is either equal or
    -- not equal to ⌈ 2 ⌉ + ⌈ 3 ⌉, but the proof does not compute to
    -- "inj₁ something" at compile-time.

    example₃ : Dec (⌈ 5 ⌉ ≡ ⌈ 2 ⌉ + ⌈ 3 ⌉)
    example₃ =
      Dec-map (_↔_.logical-equivalence ≡-for-indices↔≡)
        (⌈ 5 ⌉ ≟ ⌈ 2 ⌉ + ⌈ 3 ⌉)
