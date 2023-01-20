------------------------------------------------------------------------
-- Some definitions related to and properties of booleans
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Bool
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (id; _∘_; swap)

open import Bijection eq as Bijection using (_↔_)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence eq using (_≃_; ↔⇒≃; lift-equality)
open import Extensionality eq
open import Function-universe eq
open import H-level eq
open import H-level.Closure eq

-- The not function is involutive.

not-involutive : (b : Bool) → not (not b) ≡ b
not-involutive true  = refl _
not-involutive false = refl _

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
    ; right-inverse-of = not-involutive
    }
  ; left-inverse-of = not-involutive
  }

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

not≡↔≡not : {b₁ b₂ : Bool} → not b₁ ≡ b₂ ↔ b₁ ≡ not b₂
not≡↔≡not {(true)} {(true)} =
  false ≡ true  ↝⟨ inverse $ Bijection.⊥↔uninhabited (Bool.true≢false ∘ sym) ⟩
  ⊥₀            ↝⟨ Bijection.⊥↔uninhabited Bool.true≢false ⟩□
  true ≡ false  □
not≡↔≡not {(true)} {(false)} =
  false ≡ false  ↝⟨ inverse Bijection.≡↔inj₂≡inj₂ ⟩
  tt ≡ tt        ↝⟨ Bijection.≡↔inj₁≡inj₁ ⟩□
  true ≡ true    □
not≡↔≡not {(false)} {(true)} =
  true ≡ true    ↝⟨ inverse Bijection.≡↔inj₁≡inj₁ ⟩
  tt ≡ tt        ↝⟨ Bijection.≡↔inj₂≡inj₂ ⟩□
  false ≡ false  □
not≡↔≡not {(false)} {(false)} =
  true ≡ false  ↝⟨ inverse $ Bijection.⊥↔uninhabited Bool.true≢false ⟩
  ⊥₀            ↝⟨ Bijection.⊥↔uninhabited (Bool.true≢false ∘ sym) ⟩□
  false ≡ true  □

-- Some lemmas related to T.

T↔≡true : {b : Bool} → T b ↔ b ≡ true
T↔≡true {(false)} =   $⟨ Bool.true≢false ⟩
  true ≢ false      ↝⟨ (_∘ sym) ⟩
  false ≢ true      ↝⟨ Bijection.⊥↔uninhabited ⟩□
  ⊥ ↔ false ≡ true  □
T↔≡true {(true)} =              $⟨ refl true ⟩
  true ≡ true                 ↝⟨ propositional⇒inhabited⇒contractible Bool-set ⟩
  Contractible (true ≡ true)  ↝⟨ _⇔_.to contractible⇔↔⊤ ⟩
  true ≡ true ↔ ⊤             ↝⟨ inverse ⟩□
  ⊤ ↔ true ≡ true             □

T-not↔≡false : ∀ {b} → T (not b) ↔ b ≡ false
T-not↔≡false {b} =
  T (not b)     ↝⟨ T↔≡true ⟩
  not b ≡ true  ↝⟨ not≡↔≡not ⟩□
  b ≡ false     □

T-not⇔¬T :
  (b : Bool) → T (not b) ⇔ ¬ T b
T-not⇔¬T true =
  ⊥        ↔⟨ Bijection.⊥↔uninhabited (_$ _) ⟩
  (⊤ → ⊥)  □
T-not⇔¬T false =
  ⊤    ↝⟨ record { to = λ _ → id } ⟩□
  ¬ ⊥  □

T-not↔¬T : (b : Bool) → T (not b) ↝[ lzero ∣ lzero ] ¬ T b
T-not↔¬T true _ =
  ⊥        ↔⟨ Bijection.⊥↔uninhabited (_$ _) ⟩
  (⊤ → ⊥)  □
T-not↔¬T false ext =
  ⊤    ↝⟨ inverse-ext? ¬⊥↔⊤ ext ⟩□
  ¬ ⊥  □

¬T⇔≡false : ∀ {b} → ¬ T b ⇔ b ≡ false
¬T⇔≡false {b} =
  ¬ T b      ↝⟨ inverse $ T-not⇔¬T b ⟩
  T (not b)  ↔⟨ T-not↔≡false ⟩□
  b ≡ false  □

¬T↔≡false : ∀ {b} → ¬ T b ↝[ lzero ∣ lzero ] b ≡ false
¬T↔≡false {b = b} ext =
  ¬ T b      ↝⟨ inverse-ext? (T-not↔¬T b) ext ⟩
  T (not b)  ↔⟨ T-not↔≡false ⟩□
  b ≡ false  □

T-∧↔T×T : ∀ b₁ {b₂} → T (b₁ ∧ b₂) ↔ T b₁ × T b₂
T-∧↔T×T true {b₂} =
  T b₂      ↝⟨ inverse ×-left-identity ⟩□
  ⊤ × T b₂  □
T-∧↔T×T false {b₂} =
  ⊥         ↝⟨ inverse ×-left-zero ⟩□
  ⊥ × T b₂  □

T-∨⇔T⊎T : ∀ b₁ {b₂} → T (b₁ ∨ b₂) ⇔ T b₁ ⊎ T b₂
T-∨⇔T⊎T true       = record { to = inj₁ }
T-∨⇔T⊎T false {b₂} =
  T b₂      ↔⟨ inverse ⊎-left-identity ⟩□
  ⊥ ⊎ T b₂  □

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
  ; left-inverse-of = λ eq →
      lift-equality ext (apply-ext ext (lemma₂ eq))
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
  ; left-inverse-of = λ eq →
      lift-equality ext (apply-ext ext (lemma₂ eq))
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
