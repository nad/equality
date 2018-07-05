------------------------------------------------------------------------
-- Some omniscience principles
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Omniscience where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Double-negation equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Nat equality-with-J

-- I don't know who first stated LPO and WLPO, or who first proved
-- various properties about these principles.

-- The limited principle of omniscience.

LPO : Set
LPO = (f : ℕ → Bool) → (∀ n → f n ≡ false) ⊎ (∃ λ n → f n ≡ true)

-- The weak limited principle of omniscience.

WLPO : Set
WLPO = (f : ℕ → Bool) → Dec (∀ n → f n ≡ false)

-- WLPO is propositional (assuming extensionality).

WLPO-propositional :
  Extensionality lzero lzero →
  Is-proposition WLPO
WLPO-propositional ext =
  Π-closure ext 1 λ f →
  Dec-closure-propositional ext
    (Π-closure ext 1 λ _ →
     Bool-set _ _)

mutual

  -- There is a propositional property that is logically equivalent to
  -- LPO (assuming extensionality).
  --
  -- I think that Escardo has proved some variant of this property. The
  -- proof below uses a technique suggested by Exercise 3.19 in the HoTT
  -- book.

  LPO⇔propositional :
    Extensionality lzero lzero →
    ∃ λ (P : Set) → Is-proposition P × (LPO ⇔ P)
  LPO⇔propositional ext =
    let P , P-prop , LPO⇔ = LPO⇔propositional′ ext in

      (∀ f → P f ⊎ ¬ P f)
    , (Π-closure ext 1 λ f →
       ⊎-closure-propositional
         (flip _$_) (P-prop f) (¬-propositional ext))
    , LPO⇔

  -- A variant of the previous property.

  LPO⇔propositional′ :
    Extensionality lzero lzero →
    ∃ λ (P : (ℕ → Bool) → Set) →
      (∀ f → Is-proposition (P f)) ×
      (LPO ⇔ ∀ f → P f ⊎ ¬ P f)
  LPO⇔propositional′ ext =
      P
    , P-prop
    , (((f : ℕ → Bool) → (∀ n → f n ≡ false) ⊎ (∃ λ n → f n ≡ true))  ↝⟨ (∀-cong _ λ _ →
                                                                            record { to = ≡false→¬P; from = ¬P→≡false }
                                                                              ⊎-cong
                                                                            record { to = ≡true→P; from = Σ-map id proj₁ }) ⟩
       ((f : ℕ → Bool) → ¬ P f ⊎ P f)                                 ↝⟨ (∀-cong _ λ _ → from-bijection ⊎-comm) ⟩□
       ((f : ℕ → Bool) → P f ⊎ ¬ P f)                                 □)
    where
    P = λ (f : ℕ → Bool) →
          ∃ λ n → f n ≡ true × ∀ {m} → m < n → f m ≡ false

    P-prop : ∀ f → Is-proposition (P f)
    P-prop f =
      _⇔_.from propositional⇔irrelevant λ where
        (n₁ , fn₁≡true , <n₁→≡false) (n₂ , fn₂≡true , <n₂→≡false) →
          Σ-≡,≡→≡
            (case n₁ <⊎≡⊎> n₂ of λ where
              (inj₁ n₁<n₂)        → ⊥-elim (Bool.true≢false (
                                      true   ≡⟨ sym fn₁≡true ⟩
                                      f n₁   ≡⟨ <n₂→≡false n₁<n₂ ⟩∎
                                      false  ∎))
              (inj₂ (inj₁ n₁≡n₂)) → n₁≡n₂
              (inj₂ (inj₂ n₁>n₂)) → ⊥-elim (Bool.true≢false (
                                      true   ≡⟨ sym fn₂≡true ⟩
                                      f n₂   ≡⟨ <n₁→≡false n₁>n₂ ⟩∎
                                      false  ∎)))
            (_⇔_.to propositional⇔irrelevant
               (×-closure 1
                  (Bool-set _ _)
                  (implicit-Π-closure ext 1 λ _ →
                   Π-closure ext 1 λ _ →
                   Bool-set _ _))
               _ _)

    ¬P→≡false : ∀ {f} → ¬ (P f) → (∀ n → f n ≡ false)
    ¬P→≡false {f} ¬Pf =
      well-founded-elim _ λ n hyp →
        case inspect (f n) of λ where
          (false , fn≡false) → fn≡false
          (true  , fn≡true)  → ⊥-elim (¬Pf (n , fn≡true , hyp))

    ≡false→¬P : ∀ {f} → (∀ n → f n ≡ false) → ¬ (P f)
    ≡false→¬P {f} ≡false (n , ≡true , _) = Bool.true≢false (
      true   ≡⟨ sym ≡true ⟩
      f n    ≡⟨ ≡false n ⟩∎
      false  ∎)

    ≡true→P : ∀ {f} → (∃ λ n → f n ≡ true) → P f
    ≡true→P {f} (n , fn≡true) =
      helper (≤→≤↑ (zero≤ _)) (λ o<0 → ⊥-elim (≮0 _ o<0))
      where
      helper : ∀ {m} → m ≤↑ n → (∀ {o} → o < m → f o ≡ false) → P f
      helper     (≤↑-refl refl) <→≡false = n , fn≡true , <→≡false
      helper {m} (≤↑-step m<n)  <→≡false with inspect (f m)
      ... | true  , fm≡true  = m , fm≡true , <→≡false
      ... | false , fm≡false = helper m<n λ o<1+m →
        case ≤→≤↑ o<1+m of λ where
          (≤↑-refl refl)    → fm≡false
          (≤↑-step 1+o<1+m) → <→≡false (pred-mono (≤↑→≤ 1+o<1+m))

-- LPO implies WLPO.

LPO→WLPO : LPO → WLPO
LPO→WLPO LPO f =
  ⊎-map id
        (uncurry λ n fn≡true ∀n→fn≡false → Bool.true≢false (
           true   ≡⟨ sym fn≡true ⟩
           f n    ≡⟨ ∀n→fn≡false n ⟩∎
           false  ∎))
        (LPO f)

-- LPO follows from excluded middle (assuming extensionality).

LEM→LPO : Extensionality lzero lzero → Excluded-middle lzero → LPO
LEM→LPO ext =
  let P , P-prop , LPO⇔P = LPO⇔propositional′ ext in

  ({P : Set} → Is-proposition P → Dec P)  ↝⟨ _∘ P-prop ⟩
  (∀ f → P f ⊎ ¬ P f)                     ↝⟨ _⇔_.from LPO⇔P ⟩□
  LPO                                     □
