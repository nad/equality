------------------------------------------------------------------------
-- A parametrised specification of "natrec", along with a proof that
-- the specification is propositional (assuming extensionality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
open import Prelude hiding (ℕ; zero; suc)

-- The module is parametrised by equality and some type that is closed
-- under "zero" and "suc".

module Nat.Eliminator
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive)
  (ℕ : Type) (zero : ℕ) (suc : ℕ → ℕ)
  where

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Equivalence eq hiding (_∘_)
open import Function-universe eq hiding (_∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Surjection eq using (_↠_)

-- Specification of natrec.

Natrec : (ℓ : Level) → Type (lsuc ℓ)
Natrec ℓ =
  (P : ℕ → Type ℓ) (z : P zero) (s : ∀ n → P n → P (suc n)) →
  ∃ λ (natrec : ∀ n → P n) →
    natrec zero ≡ z
      ×
    ∀ n → natrec (suc n) ≡ s n (natrec n)

-- This specification is propositional (assuming extensionality).
--
-- Note that the proof uses some lemmas that are defined by recursion
-- on natural numbers. I suspect that it would be easy (although
-- perhaps somewhat tedious) to avoid such recursion.
--
-- I got the idea for this result from Christian Sattler, who
-- mentioned the work of Awodey, Gambino and Sojakova: in "Inductive
-- types in homotopy type theory" they prove something similar for a
-- non-dependent eliminator.

Natrec-propositional :
  ∀ {ℓ} →
  Extensionality (lsuc ℓ) ℓ →
  Is-proposition (Natrec ℓ)
Natrec-propositional {ℓ} ext₊ =
  [inhabited⇒+]⇒+ 0 λ natrec₀ →
  Π-closure ext₊ 1 λ P →
  Π-closure ext₌ 1 λ z →
  Π-closure ext₌ 1 λ s →
  H-level.respects-surjection (∃-cong (lemma natrec₀ P z s)) 1
    (mono₁ 0 (singleton-contractible _))
  where
  ext₌ : Extensionality ℓ ℓ
  ext₌ = lower-extensionality _ lzero ext₊

  ext₀ : Extensionality lzero ℓ
  ext₀ = lower-extensionality _ lzero ext₊

  ext : Extensionality lzero ℓ
  ext = good-ext ext₀

  lemma :
    (natrec₀ : Natrec ℓ)
    (P : ℕ → Type ℓ) (z : P zero) (s : ∀ n → P n → P (suc n))
    (natrec : ∀ n → P n) →

    natrec ≡ proj₁ (natrec₀ P z s)

      ↠

    (natrec zero ≡ z
       ×
     ∀ n → natrec (suc n) ≡ s n (natrec n))

  lemma natrec₀ P z s natrec = record
    { logical-equivalence = record
      { to   = λ eq →
                   (natrec zero      ≡⟨ cong (_$ zero) eq ⟩
                    rec₀ P z s zero  ≡⟨ nz₀ P z s ⟩∎
                    z                ∎)
                 , λ n →
                     natrec (suc n)      ≡⟨ cong (_$ suc n) eq ⟩
                     rec₀ P z s (suc n)  ≡⟨ ns₀ P z s n ⟩
                     s n (rec₀ P z s n)  ≡⟨ sym $ cong (s n) $ cong (_$ n) eq ⟩∎
                     s n (natrec n)      ∎
      ; from = λ { (nz , ns) → apply-ext ext $
                     lower ∘
                     rec₀ (λ n → ↑ ℓ (natrec n ≡ rec₀ P z s n))
                       (lift (
                          natrec zero      ≡⟨ nz ⟩
                          z                ≡⟨ sym $ nz₀ P z s ⟩∎
                          rec₀ P z s zero  ∎))
                       (λ n ih → lift (
                          natrec (suc n)      ≡⟨ ns n ⟩
                          s n (natrec n)      ≡⟨ cong (s n) (lower ih) ⟩
                          s n (rec₀ P z s n)  ≡⟨ sym $ ns₀ P z s n ⟩∎
                          rec₀ P z s (suc n)  ∎))
                 }
      }
    ; right-inverse-of = λ { (nz , ns) →
          let f = lower ∘
                  rec₀ _
                    (lift (trans nz (sym $ nz₀ P z s)))
                    (λ n ih →
                       lift (trans (ns n)
                               (trans (cong (s n) (lower ih))
                                  (sym $ ns₀ P z s n)))) in

          _↔_.to ≡×≡↔≡
            ( (trans (cong (_$ zero) (apply-ext ext f)) (nz₀ P z s)  ≡⟨ cong (flip trans (nz₀ P z s)) $ cong-good-ext ext₀ f ⟩
               trans (f zero) (nz₀ P z s)                            ≡⟨ cong (flip trans (nz₀ P z s) ∘ lower) $ nz₀ _ _ _ ⟩
               trans (trans nz (sym $ nz₀ P z s)) (nz₀ P z s)        ≡⟨ trans-[trans-sym]- _ (nz₀ P z s) ⟩∎
               nz                                                    ∎)

            , apply-ext ext λ n →
                trans
                  (cong (_$ suc n) (apply-ext ext f))
                  (trans (ns₀ P z s n)
                     (sym $ cong (s n) $ cong (_$ n) (apply-ext ext f)))     ≡⟨ cong₂ (λ p q → trans p (trans (ns₀ P z s n) (sym $ cong (s n) q)))
                                                                                  (cong-good-ext ext₀ f) (cong-good-ext ext₀ f) ⟩
                trans
                  (f (suc n))
                  (trans (ns₀ P z s n) (sym $ cong (s n) (f n)))             ≡⟨ cong (flip trans (trans _ (sym $ cong (s n) (f n))) ∘ lower) $
                                                                                  ns₀ _ _ _ _ ⟩
                trans
                  (trans (ns n)
                     (trans (cong (s n) (f n))
                        (sym $ ns₀ P z s n)))
                  (trans (ns₀ P z s n) (sym $ cong (s n) (f n)))             ≡⟨ cong (flip trans (trans _ (sym $ cong (s n) (f n)))) $
                                                                                  sym $ trans-assoc _ _ (sym $ ns₀ P z s n) ⟩
                trans
                  (trans (trans (ns n) (cong (s n) (f n)))
                     (sym $ ns₀ P z s n))
                  (trans (ns₀ P z s n) (sym $ cong (s n) (f n)))             ≡⟨ sym $ trans-assoc _ _ (sym $ cong (s n) (f n)) ⟩

                trans
                  (trans (trans (trans (ns n) (cong (s n) (f n)))
                            (sym $ ns₀ P z s n))
                     (ns₀ P z s n))
                  (sym $ cong (s n) (f n))                                   ≡⟨ cong (flip trans (sym $ cong (s n) (f n))) $
                                                                                  trans-[trans-sym]- _ (ns₀ P z s n) ⟩
                trans
                  (trans (ns n) (cong (s n) (f n)))
                  (sym $ cong (s n) (f n))                                   ≡⟨ trans-[trans]-sym _ (cong (s n) (f n)) ⟩∎

                ns n                                                         ∎
            )
        }
    }
    where
    rec₀ : (P : ℕ → Type ℓ) (z : P zero) (s : ∀ n → P n → P (suc n)) →
           ∀ n → P n
    rec₀ P z s = proj₁ (natrec₀ P z s)

    nz₀ : (P : ℕ → Type ℓ) (z : P zero) (s : ∀ n → P n → P (suc n)) →
          rec₀ P z s zero ≡ z
    nz₀ P z s = proj₁ (proj₂ (natrec₀ P z s))

    ns₀ : (P : ℕ → Type ℓ) (z : P zero) (s : ∀ n → P n → P (suc n)) →
          ∀ n → rec₀ P z s (suc n) ≡ s n (rec₀ P z s n)
    ns₀ P z s = proj₂ (proj₂ (natrec₀ P z s))
