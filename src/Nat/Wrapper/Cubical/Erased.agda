------------------------------------------------------------------------
-- A variant of Nat.Wrapper.Cubical, defined using --erased-cubical
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

open import Equality.Path as P
open import Prelude hiding (zero; suc; _+_)

open import Bijection equality-with-J using (_↔_)

module Nat.Wrapper.Cubical.Erased
  -- The underlying representation of natural numbers.
  (Nat′ : Type)
  -- A bijection between this representation and the unary natural
  -- numbers.
  (Nat′↔ℕ : Nat′ ↔ ℕ)
  where

open import Equality.Path.Univalence
open import Logical-equivalence using (_⇔_)

import Equivalence equality-with-J as Eq
open import Equivalence.Erased.Cubical equality-with-paths as EEq
  using (_≃ᴱ_)
import Equivalence.Erased.Contractible-preimages.Cubical
         equality-with-paths
  as ECP
open import Erased.Cubical equality-with-paths
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.Erased equality-with-paths
  as Trunc
import Nat equality-with-J as Nat
import Univalence-axiom equality-with-J as U

open import Nat.Wrapper equality-with-J Nat′ Nat′↔ℕ as NW
open NW.[]-cong instance-of-[]-cong-axiomatisation

private
  variable
    A   : Type
    m n : A

------------------------------------------------------------------------
-- Could Nat have been defined using the propositional truncation
-- operator (with an erased higher constructor) instead of Erased?

-- Could Nat have been defined using ∥_∥ᴱ instead of Erased? Let us
-- try.

-- Given a truncated natural number we can kind of apply Nat-[_] to
-- it, because Nat-[_] is a family of contractible types. (The code
-- uses erased univalence.)

Nat-[]′ : ∥ ℕ ∥ᴱ → ∃ λ (A : Type) → Contractible A
Nat-[]′ = Trunc.rec λ where
  .truncation-is-propositionʳ →
    U.∃-H-level-H-level-1+ ext univ 0
  .∣∣ʳ n →
      Nat-[ n ]
    , propositional⇒inhabited⇒contractible
        Nat-[]-propositional
        ( _↔_.from Nat′↔ℕ n
        , [ _↔_.right-inverse-of Nat′↔ℕ n ]
        )

Nat-[_]′ : ∥ ℕ ∥ᴱ → Type
Nat-[ n ]′ = proj₁ (Nat-[]′ n)

-- Thus we can form a variant of Nat.

Nat-with-∥∥ᴱ : Type
Nat-with-∥∥ᴱ = Σ ∥ ℕ ∥ᴱ Nat-[_]′

-- However, this variant is equivalent (with erased proofs) to the
-- unit type.

Nat-with-∥∥ᴱ≃ᴱ⊤ : Nat-with-∥∥ᴱ ≃ᴱ ⊤
Nat-with-∥∥ᴱ≃ᴱ⊤ =
  _⇔_.to EEq.Contractibleᴱ⇔≃ᴱ⊤ $
  ECP.Contractibleᴱ-Σ
    (ECP.inhabited→Is-proposition→Contractibleᴱ
       ∣ 0 ∣ truncation-is-proposition)
    (ECP.Contractible→Contractibleᴱ ∘ proj₂ ∘ Nat-[]′)

-- And thus it is not isomorphic to the natural numbers.

¬-Nat-with-∥∥ᴱ↔ℕ : ¬ (Nat-with-∥∥ᴱ ↔ ℕ)
¬-Nat-with-∥∥ᴱ↔ℕ =
  Stable-¬
    [ Nat-with-∥∥ᴱ ↔ ℕ  ↝⟨ F._∘ inverse (from-equivalence (EEq.≃ᴱ→≃ Nat-with-∥∥ᴱ≃ᴱ⊤)) ⟩
      ⊤ ↔ ℕ             ↝⟨ (λ hyp → _↔_.injective (inverse hyp) refl) ⟩
      0 ≡ 1             ↝⟨ Nat.0≢+ ⟩□
      ⊥                 □
    ]

------------------------------------------------------------------------
-- Addition of "wrapped" numbers is commutative and associative

module _ (o : Operations) where

  open Operations-for-Nat o
  open Operations-for-Nat-correct o

  private

    -- A lemma used several times below.

    from[to+to]≡+ :
      ∀ m n →
      _↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ m Prelude.+ _↔_.to Nat↔ℕ n) ≡ m + n
    from[to+to]≡+ m n =
      _↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ m Prelude.+ _↔_.to Nat↔ℕ n)  ≡⟨ cong (_↔_.from Nat↔ℕ) $ sym $ to-ℕ-+ m n ⟩
      _↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ (m + n))                     ≡⟨ _↔_.left-inverse-of Nat↔ℕ _ ⟩∎
      m + n                                                     ∎

  -- First two "traditional" proofs.

  -- Addition is commutative.

  +-comm-traditional : ∀ m {n} → m + n ≡ n + m
  +-comm-traditional m {n} =
    m + n                                                     ≡⟨ sym $ from[to+to]≡+ m n ⟩
    _↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ m Prelude.+ _↔_.to Nat↔ℕ n)  ≡⟨ cong (_↔_.from Nat↔ℕ) $ Nat.+-comm (_↔_.to Nat↔ℕ m) ⟩
    _↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ n Prelude.+ _↔_.to Nat↔ℕ m)  ≡⟨ from[to+to]≡+ n m ⟩∎
    n + m                                                     ∎

  -- Addition is associative.

  +-assoc-traditional : ∀ m {n o} → m + (n + o) ≡ (m + n) + o
  +-assoc-traditional m {n} {o} =
    m + (n + o)                                                     ≡⟨ cong (m +_) $ sym $ from[to+to]≡+ n o ⟩

    m + (_↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ n Prelude.+ _↔_.to Nat↔ℕ o))  ≡⟨ sym $ from[to+to]≡+ m (_↔_.from Nat↔ℕ _) ⟩

    _↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ m
                      Prelude.+
                    _↔_.to Nat↔ℕ (_↔_.from Nat↔ℕ
                      (_↔_.to Nat↔ℕ n Prelude.+ _↔_.to Nat↔ℕ o)))   ≡⟨ cong (λ n → _↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ m Prelude.+ n)) $
                                                                       _↔_.right-inverse-of Nat↔ℕ _ ⟩
    _↔_.from Nat↔ℕ
      (_↔_.to Nat↔ℕ m
         Prelude.+
       (_↔_.to Nat↔ℕ n Prelude.+ _↔_.to Nat↔ℕ o))                   ≡⟨ cong (_↔_.from Nat↔ℕ) $ Nat.+-assoc (_↔_.to Nat↔ℕ m) ⟩

    _↔_.from Nat↔ℕ
      ((_↔_.to Nat↔ℕ m Prelude.+ _↔_.to Nat↔ℕ n)
         Prelude.+
       _↔_.to Nat↔ℕ o)                                              ≡⟨ cong (λ n → _↔_.from Nat↔ℕ (n Prelude.+ _↔_.to Nat↔ℕ o)) $ sym $
                                                                       _↔_.right-inverse-of Nat↔ℕ _ ⟩
    _↔_.from Nat↔ℕ
      (_↔_.to Nat↔ℕ (_↔_.from Nat↔ℕ
         (_↔_.to Nat↔ℕ m Prelude.+ _↔_.to Nat↔ℕ n))
         Prelude.+
       _↔_.to Nat↔ℕ o)                                              ≡⟨ from[to+to]≡+ (_↔_.from Nat↔ℕ _) o ⟩

    (_↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ m Prelude.+ _↔_.to Nat↔ℕ n)) + o  ≡⟨ cong (_+ o) $ from[to+to]≡+ m n ⟩∎

    (m + n) + o                                                     ∎

  -- The following proofs are instead based on a technique used by
  -- Vezzosi, Mörtberg and Abel in "Cubical Agda: A Dependently Typed
  -- Programming Language with Univalence and Higher Inductive Types".

  -- The type of unary natural numbers is equal to the type of wrapped
  -- natural numbers (in erased contexts).

  @0 ℕ≡Nat : ℕ ≡ Nat
  ℕ≡Nat = sym (≃⇒≡ (Eq.↔⇒≃ Nat↔ℕ))

  -- Addition of unary natural numbers is, in a certain sense, equal
  -- to addition of wrapped natural numbers (in erased contexts).

  @0 +≡+ : P.[ (λ i → ℕ≡Nat i → ℕ≡Nat i → ℕ≡Nat i) ] Prelude._+_ ≡ _+_
  +≡+ =
    Prelude._+_                                                         ≡⟨ (λ i → transport
                                                                                    (λ j → ℕ≡Nat (min i j) → ℕ≡Nat (min i j) → ℕ≡Nat (min i j))
                                                                                    (- i) Prelude._+_) ⟩h
    transport (λ i → ℕ≡Nat i → ℕ≡Nat i → ℕ≡Nat i) 0̲ Prelude._+_         ≡⟨⟩
    (λ m n → _↔_.from Nat↔ℕ (_↔_.to Nat↔ℕ m Prelude.+ _↔_.to Nat↔ℕ n))  ≡⟨ (⟨ext⟩ λ m → ⟨ext⟩ λ n → from[to+to]≡+ m n) ⟩∎
    _+_                                                                 ∎

  -- Addition is commutative (in erased contexts).

  @0 +-comm-cubical : ∀ m {n} → m + n ≡ n + m
  +-comm-cubical =
    transport
      (λ i → (m {n} : ℕ≡Nat i) → +≡+ i m n ≡ +≡+ i n m)
      0̲
      Nat.+-comm

  -- Addition is associative (in erased contexts).

  @0 +-assoc-cubical : ∀ m {n o} → m + (n + o) ≡ (m + n) + o
  +-assoc-cubical =
    transport
      (λ i → (m {n o} : ℕ≡Nat i) →
             +≡+ i m (+≡+ i n o) ≡ +≡+ i (+≡+ i m n) o)
      0̲
      Nat.+-assoc

  -- This proof technique seems to scale better than the one used
  -- above, at least for examples of the kind used here. However, when
  -- --erased-cubical is used it only works in erased contexts.
