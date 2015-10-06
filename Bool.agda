------------------------------------------------------------------------
-- Some definitions related to and properties of booleans
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Bool
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude hiding (id; _∘_)

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence eq using (_≃_; ↔⇒≃; lift-equality)
open import Function-universe eq

-- Bool is isomorphic to Fin 2.

Bool↔Fin2 : Bool ↔ Fin 2
Bool↔Fin2 =
  ⊤ ⊎ ⊤      ↝⟨ inverse $ id ⊎-cong ⊎-right-identity ⟩□
  ⊤ ⊎ ⊤ ⊎ ⊥  □

-- A non-trivial automorphism on Bool.

swap : Bool ↔ Bool
swap = record
  { surjection = record
    { logical-equivalence = record
      { to   = not
      ; from = not
      }
    ; right-inverse-of = not∘not
    }
  ; left-inverse-of = not∘not
  }
  where
  not∘not : ∀ b → not (not b) ≡ b
  not∘not true  = refl _
  not∘not false = refl _

private

  non-trivial : _↔_.to swap ≢ id
  non-trivial not≡id = Bool.true≢false (cong (_$ false) not≡id)

-- Equality rearrangement lemmas.

not≡⇒≢ : (b₁ b₂ : Bool) → not b₁ ≡ b₂ → b₁ ≢ b₂
not≡⇒≢ true  true  f≡t _   = Bool.true≢false (sym f≡t)
not≡⇒≢ true  false _   t≡f = Bool.true≢false t≡f
not≡⇒≢ false true  _   f≡t = Bool.true≢false (sym f≡t)
not≡⇒≢ false false t≡f _   = Bool.true≢false t≡f

≢⇒not≡ : (b₁ b₂ : Bool) → b₁ ≢ b₂ → not b₁ ≡ b₂
≢⇒not≡ true  true  t≢t = ⊥-elim (t≢t (refl _))
≢⇒not≡ true  false _   = refl _
≢⇒not≡ false true  _   = refl _
≢⇒not≡ false false f≢f = ⊥-elim (f≢f (refl _))

-- Bool ≃ Bool is isomorphic to Bool (assuming extensionality).

[Bool≃Bool]↔Bool₁ : Extensionality lzero lzero →
                    (Bool ≃ Bool) ↔ Bool
[Bool≃Bool]↔Bool₁ ext = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ eq → _≃_.to eq true
      ; from = if_then id else ↔⇒≃ swap
      }
    ; right-inverse-of = λ { true → refl _; false → refl _ }
    }
  ; left-inverse-of = λ eq → lift-equality ext (ext (lemma₂ eq))
  }
  where
  lemma₁ : ∀ b → _≃_.to (if b then id else ↔⇒≃ swap) false ≡ not b
  lemma₁ true  = refl _
  lemma₁ false = refl _

  lemma₂ : ∀ eq b →
           _≃_.to (if _≃_.to eq true then id else ↔⇒≃ swap) b ≡
           _≃_.to eq b
  lemma₂ eq true  with _≃_.to eq true
  ...             | true  = refl _
  ...             | false = refl _
  lemma₂ eq false =
    _≃_.to (if _≃_.to eq true then id else ↔⇒≃ swap) false  ≡⟨ lemma₁ (_≃_.to eq true) ⟩
    not (_≃_.to eq true)                                    ≡⟨ ≢⇒not≡ _ _ (Bool.true≢false ∘ _≃_.injective eq) ⟩∎
    _≃_.to eq false                                         ∎

-- Another proof showing that Bool ≃ Bool is isomorphic to Bool
-- (assuming extensionality).

[Bool≃Bool]↔Bool₂ : Extensionality lzero lzero →
                    (Bool ≃ Bool) ↔ Bool
[Bool≃Bool]↔Bool₂ ext = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ eq → _≃_.to eq false
      ; from = if_then ↔⇒≃ swap else id
      }
    ; right-inverse-of = λ { true → refl _; false → refl _ }
    }
  ; left-inverse-of = λ eq → lift-equality ext (ext (lemma₂ eq))
  }
  where
  lemma₁ : ∀ b → _≃_.to (if b then ↔⇒≃ swap else id) true ≡ not b
  lemma₁ true  = refl _
  lemma₁ false = refl _

  lemma₂ : ∀ eq b →
           _≃_.to (if _≃_.to eq false then ↔⇒≃ swap else id) b ≡
           _≃_.to eq b
  lemma₂ eq false with _≃_.to eq false
  ...             | true  = refl _
  ...             | false = refl _
  lemma₂ eq true  =
    _≃_.to (if _≃_.to eq false then ↔⇒≃ swap else id) true  ≡⟨ lemma₁ (_≃_.to eq false) ⟩
    not (_≃_.to eq false)                                   ≡⟨ ≢⇒not≡ _ _ (Bool.true≢false ∘ sym ∘ _≃_.injective eq) ⟩∎
    _≃_.to eq true                                          ∎

private

  -- The two proofs are not equal.

  distinct : {ext : Extensionality lzero lzero} →
             [Bool≃Bool]↔Bool₁ ext ≢ [Bool≃Bool]↔Bool₂ ext
  distinct =
    Bool.true≢false ∘ cong (λ iso → _≃_.to (_↔_.from iso true) true)
