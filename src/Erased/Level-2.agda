------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

-- The definitions in this module are reexported from Erased.

-- This module imports Equivalence.Erased.

{-# OPTIONS --without-K --safe #-}

open import Equality
import Erased.Level-1
open import Prelude hiding ([_,_])

module Erased.Level-2
  {c⁺}
  (eq-J : ∀ {a p} → Equality-with-J a p c⁺)
  {ℓ₁ ℓ₂}
  (ax₁ : Erased.Level-1.[]-cong-axiomatisation eq-J ℓ₁)
  (ax₂ : Erased.Level-1.[]-cong-axiomatisation eq-J ℓ₂)
  (ax  : Erased.Level-1.[]-cong-axiomatisation eq-J (ℓ₁ ⊔ ℓ₂))
  where

open Derived-definitions-and-properties eq-J
open Erased.Level-1 eq-J
open Erased.Level-1.Erased-cong eq-J ax ax
open Erased.Level-1.[]-cong₁ eq-J ax₂
open Erased.Level-1.[]-cong₂ eq-J ax₁ ax₂ ax

open import Logical-equivalence using (_⇔_)

open import Bijection eq-J as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq-J as Emb using (Embedding; Is-embedding)
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J as H-level
open import H-level.Closure eq-J
open import Injection eq-J using (_↣_; Injective)
open import Monad eq-J hiding (map; map-id; map-∘)
open import Preimage eq-J using (_⁻¹_)
open import Surjection eq-J using (_↠_; Split-surjective)

private

  module EEq′ = EEq.[]-cong₂ ax₁ ax₂ ax

  variable
    a b c ℓ       : Level
    A B           : Type a
    eq k k′ p x y : A
    P             : A → Type p
    f g           : A → B
    n             : ℕ

------------------------------------------------------------------------
-- Erased commutes with all kinds of functions (in some cases assuming
-- extensionality)

-- Erased commutes with all kinds of functions (assuming
-- extensionality).

Erased-↝↝↝ :
  {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
  Erased (A ↝[ k ] B) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ] (Erased A ↝[ k ] Erased B)
Erased-↝↝↝ {k = implication} _ = from-isomorphism Erased-Π↔Π-Erased

Erased-↝↝↝ {k = logical-equivalence} _ = from-isomorphism Erased-⇔↔⇔

Erased-↝↝↝ {k = injection} {A = A} {B = B} ext =
  Erased (A ↣ B)                                              ↔⟨ Erased-cong-↔ ↣↔∃-Injective ⟩
  Erased (∃ λ (f : A → B) → Injective f)                      ↔⟨ Erased-Σ↔Σ ⟩
  (∃ λ (f : Erased (A → B)) → Erased (Injective (erased f)))  ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ _ → Erased-Injective↔Injective ext) ⟩
  (∃ λ (f : Erased A → Erased B) → Injective f)               ↔⟨ inverse ↣↔∃-Injective ⟩□
  Erased A ↣ Erased B                                         □

Erased-↝↝↝ {k = embedding} {A = A} {B = B} ext =
  Erased (Embedding A B)                                         ↔⟨ Erased-cong-↔ Emb.Embedding-as-Σ ⟩
  Erased (∃ λ (f : A → B) → Is-embedding f)                      ↔⟨ Erased-Σ↔Σ ⟩
  (∃ λ (f : Erased (A → B)) → Erased (Is-embedding (erased f)))  ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ _ → Erased-Is-embedding↔Is-embedding ext) ⟩
  (∃ λ (f : Erased A → Erased B) → Is-embedding f)               ↔⟨ inverse Emb.Embedding-as-Σ ⟩□
  Embedding (Erased A) (Erased B)                                □

Erased-↝↝↝ {k = surjection} {A = A} {B = B} {k = k′} ext =
  Erased (A ↠ B)                                                     ↔⟨ Erased-cong-↔ ↠↔∃-Split-surjective ⟩
  Erased (∃ λ (f : A → B) → Split-surjective f)                      ↔⟨ Erased-Σ↔Σ ⟩
  (∃ λ (f : Erased (A → B)) → Erased (Split-surjective (erased f)))  ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ _ →
                                                                        Erased-Split-surjective↔Split-surjective
                                                                          (lower-extensionality? k′ ℓ₁ lzero ext)) ⟩
  (∃ λ (f : Erased A → Erased B) → Split-surjective f)               ↔⟨ inverse ↠↔∃-Split-surjective ⟩□
  Erased A ↠ Erased B                                                □

Erased-↝↝↝ {k = bijection} {A = A} {B = B} ext =
  Erased (A ↔ B)                                                      ↔⟨ Erased-cong-↔ Bijection.↔-as-Σ ⟩
  Erased (∃ λ (f : A → B) → Has-quasi-inverse f)                      ↔⟨ Erased-Σ↔Σ ⟩
  (∃ λ (f : Erased (A → B)) → Erased (Has-quasi-inverse (erased f)))  ↝⟨ (Σ-cong Erased-Π↔Π-Erased λ _ →
                                                                          Erased-Has-quasi-inverse↔Has-quasi-inverse ext) ⟩
  (∃ λ (f : Erased A → Erased B) → Has-quasi-inverse f)               ↔⟨ inverse Bijection.↔-as-Σ ⟩□
  Erased A ↔ Erased B                                                 □

Erased-↝↝↝ {k = equivalence} {A = A} {B = B} ext =
  Erased (A ≃ B)                                                   ↔⟨ Erased-cong-↔ Eq.≃-as-Σ ⟩
  Erased (∃ λ (f : A → B) → Is-equivalence f)                      ↔⟨ Erased-Σ↔Σ ⟩
  (∃ λ (f : Erased (A → B)) → Erased (Is-equivalence (erased f)))  ↝⟨ Σ-cong Erased-Π↔Π-Erased (λ _ → Erased-Is-equivalence↔Is-equivalence ext) ⟩
  (∃ λ (f : Erased A → Erased B) → Is-equivalence f)               ↔⟨ inverse Eq.≃-as-Σ ⟩□
  Erased A ≃ Erased B                                              □

Erased-↝↝↝ {k = equivalenceᴱ} {A = A} {B = B} ext =
  Erased (A ≃ᴱ B)                                                   ↔⟨ Erased-cong-≃ EEq.≃ᴱ-as-Σ ⟩
  Erased (∃ λ (f : A → B) → Is-equivalenceᴱ f)                      ↔⟨ Erased-Σ↔Σ ⟩
  (∃ λ (f : Erased (A → B)) → Erased (Is-equivalenceᴱ (erased f)))  ↝⟨ (Σ-cong Erased-Π↔Π-Erased λ _ →
                                                                        EEq′.Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ ext) ⟩
  (∃ λ (f : Erased A → Erased B) → Is-equivalenceᴱ f)               ↔⟨ inverse EEq.≃ᴱ-as-Σ ⟩□
  Erased A ≃ᴱ Erased B                                              □

-- Erased commutes with all kinds of functions (in some cases
-- assuming extensionality).

Erased-↝↔↝ :
  {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
  Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
  Erased (A ↝[ k ] B) ↔ (Erased A ↝[ k ] Erased B)
Erased-↝↔↝ {k = implication}         = λ _ → Erased-Π↔Π-Erased
Erased-↝↔↝ {k = logical-equivalence} = λ _ → Erased-⇔↔⇔
Erased-↝↔↝ {k = injection}           = Erased-↝↝↝
Erased-↝↔↝ {k = embedding}           = Erased-↝↝↝
Erased-↝↔↝ {k = surjection}          = Erased-↝↝↝
Erased-↝↔↝ {k = bijection}           = Erased-↝↝↝
Erased-↝↔↝ {k = equivalence}         = Erased-↝↝↝
Erased-↝↔↝ {k = equivalenceᴱ}        = Erased-↝↝↝

-- Erased-↝↔↝ and Erased-↝↝↝ produce equal functions.

to-Erased-↝↔↝≡to-Erased-↝↝↝ :
  {@0 A : Type ℓ₁} {@0 B : Type ℓ₂}
  (ext : Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂))
  (ext′ : Extensionality? k′ (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂)) →
  _↔_.to (Erased-↝↔↝ {k = k} {A = A} {B = B} ext) ≡
  to-implication (Erased-↝↝↝ {k = k} {A = A} {B = B} {k = k′} ext′)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = implication}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = logical-equivalence} _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = injection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = embedding}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = surjection}          _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = bijection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = equivalence}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = implication}         {k′ = equivalenceᴱ}        _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = implication}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = logical-equivalence} _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = injection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = embedding}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = surjection}          _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = bijection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = equivalence}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = logical-equivalence} {k′ = equivalenceᴱ}        _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = implication}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = logical-equivalence} _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = injection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = embedding}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = surjection}          _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = bijection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = equivalence}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = injection}           {k′ = equivalenceᴱ}        _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = implication}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = logical-equivalence} _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = injection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = embedding}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = surjection}          _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = bijection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = equivalence}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = surjection}          {k′ = equivalenceᴱ}        _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = implication}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = logical-equivalence} _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = injection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = embedding}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = surjection}          _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = bijection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = equivalence}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = bijection}           {k′ = equivalenceᴱ}        _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = implication}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = logical-equivalence} _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = injection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = embedding}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = surjection}          _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = bijection}           _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = equivalence}         _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = equivalenceᴱ}        _   _ = refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = implication}         ext _ = apply-ext ext λ _ → EEq′.to≡to→≡-Erased ext (refl _)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = logical-equivalence} ext _ = apply-ext ext λ _ → EEq′.to≡to→≡-Erased ext (refl _)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = injection}           ext _ = apply-ext ext λ _ → EEq′.to≡to→≡-Erased ext (refl _)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = embedding}           ext _ = apply-ext ext λ _ → EEq′.to≡to→≡-Erased ext (refl _)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = surjection}          ext _ = apply-ext ext λ _ → EEq′.to≡to→≡-Erased ext (refl _)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = bijection}           ext _ = apply-ext ext λ _ → EEq′.to≡to→≡-Erased ext (refl _)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = equivalence}         ext _ = apply-ext ext λ _ → EEq′.to≡to→≡-Erased ext (refl _)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = equivalenceᴱ}        ext _ = apply-ext ext λ _ → EEq′.to≡to→≡-Erased ext (refl _)
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = implication}         ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = logical-equivalence} ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = injection}           ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = embedding}           ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = surjection}          ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = bijection}           ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = equivalence}         ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _
to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = embedding} {k′ = equivalenceᴱ}        ext _ = apply-ext ext λ _ → _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _

-- Erased preserves all kinds of functions.

Erased-cong :
  {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
  @0 A ↝[ k ] B → Erased A ↝[ k ] Erased B
Erased-cong A↝B = Erased-↝↝↝ _ [ A↝B ]

-- Dec-Erased preserves symmetric kinds of functions (in some cases
-- assuming extensionality).

Dec-Erased-cong :
  {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
  @0 Extensionality? ⌊ k ⌋-sym (ℓ₁ ⊔ ℓ₂) lzero →
  @0 A ↝[ ⌊ k ⌋-sym ] B →
  Dec-Erased A ↝[ ⌊ k ⌋-sym ] Dec-Erased B
Dec-Erased-cong ext A↝B =
  Erased-cong A↝B ⊎-cong Erased-cong (→-cong ext A↝B F.id)
