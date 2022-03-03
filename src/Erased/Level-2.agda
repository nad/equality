------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

-- The definitions in this module are reexported from Erased.

-- This module imports Equivalence.Erased.

{-# OPTIONS --without-K --safe #-}

open import Equality
open import Prelude hiding ([_,_])

module Erased.Level-2
  {c⁺} (eq-J : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq-J

open import Logical-equivalence using (_⇔_)

open import Bijection eq-J as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq-J as Emb using (Embedding; Is-embedding)
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Extensionality eq-J
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J as H-level
open import H-level.Closure eq-J
open import Injection eq-J using (_↣_; Injective)
open import Monad eq-J hiding (map; map-id; map-∘)
open import Preimage eq-J using (_⁻¹_)
open import Surjection eq-J using (_↠_; Split-surjective)

open import Erased.Level-1 eq-J as E₁
  hiding (module []-cong; module []-cong₂-⊔)

private

  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B              : Type a
    eq k k′ p x y    : A
    P                : A → Type p
    f g              : A → B
    n                : ℕ

------------------------------------------------------------------------
-- Results that depend on an instantiation of the []-cong axioms (for
-- two universe levels as well as their maximum)

module []-cong₂-⊔
  (ax₁ : E₁.[]-cong-axiomatisation ℓ₁)
  (ax₂ : E₁.[]-cong-axiomatisation ℓ₂)
  (ax  : E₁.[]-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  where

  open E₁.Erased-cong ax ax
  open E₁.[]-cong₁ ax₂
  open E₁.[]-cong₂ ax₁ ax₂
  open E₁.[]-cong₂-⊔ ax₁ ax₂ ax

  private

    module EEq′ = EEq.[]-cong₂-⊔ ax₁ ax₂ ax

  ----------------------------------------------------------------------
  -- Erased commutes with all kinds of functions (in some cases
  -- assuming extensionality)

  private

    -- A lemma used below.

    Erased-≃ᴱ↔≃ᴱ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
      Erased (A ≃ᴱ B) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]ᴱ (Erased A ≃ᴱ Erased B)
    Erased-≃ᴱ↔≃ᴱ {A = A} {B = B} ext =
      Erased (A ≃ᴱ B)                                                   ↔⟨ Erased-cong-≃ EEq.≃ᴱ-as-Σ ⟩
      Erased (∃ λ (f : A → B) → Is-equivalenceᴱ f)                      ↔⟨ Erased-Σ↔Σ ⟩
      (∃ λ (f : Erased (A → B)) → Erased (Is-equivalenceᴱ (erased f)))  ↝⟨ (Σ-cong Erased-Π↔Π-Erased λ _ →
                                                                            EEq′.Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ ext) ⟩
      (∃ λ (f : Erased A → Erased B) → Is-equivalenceᴱ f)               ↔⟨ inverse EEq.≃ᴱ-as-Σ ⟩□
      Erased A ≃ᴱ Erased B                                              □

  -- Erased commutes with all kinds of functions (in some cases
  -- assuming extensionality).

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

  Erased-↝↝↝ {k = equivalenceᴱ} ext = Erased-≃ᴱ↔≃ᴱ ext

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
  Erased-↝↔↝ {k = equivalenceᴱ}        = λ ([ ext ]) → Erased-≃ᴱ↔≃ᴱ ext

  private

    -- A lemma used below.

    to≡to→≡ :
      {@0 A : Type (ℓ₁ ⊔ ℓ₂)} {@0 B : Type ℓ₁} {@0 C : Type ℓ₂}
      {f g : Erased A → Erased B ≃ᴱ Erased C} →
      Erased (Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂)) →
      @0 (∀ {x y} → _≃ᴱ_.to (f x) y ≡ _≃ᴱ_.to (g x) y) →
      f ≡ g
    to≡to→≡ {A = A} {B = B} {C = C} {f = f} {g = g} [ ext ] eq =  $⟨ [ (λ _ _ → eq) ] ⟩
      Erased (∀ x y → _≃ᴱ_.to (f x) y ≡ _≃ᴱ_.to (g x) y)          ↝⟨ Erased-cong-≃ (∀-cong ext λ _ → EEq.to≡to≃≡ ext) ⟩
      Erased (∀ x → f x ≡ g x)                                    ↝⟨ Erased-cong-≃ (Eq.extensionality-isomorphism ext) ⟩
      Erased (f ≡ g)                                              ↝⟨ Erased-cong-≃ (inverse $ Eq.≃-≡ lemma₂) ⟩
      Erased (_≃_.to lemma₂ f ≡ _≃_.to lemma₂ g)                  ↝⟨ Erased-cong-≃ (inverse $ E₁.[]-cong₁.≡≃[]≡[] ax) ⟩
      Erased (_≃_.to lemma₂ f .erased ≡ _≃_.to lemma₂ g .erased)  ↝⟨ E₁.[]-cong₁.Erased-≡≃[]≡[] ax ⟩
      _≃_.to lemma₂ f ≡ _≃_.to lemma₂ g                           ↝⟨ Eq.≃-≡ lemma₂ ⟩□
      f ≡ g                                                       □
      where
      abstract

        lemma₁ :
          (Erased A → Erased B ≃ᴱ Erased C) ≃
          (Erased A → Erased (Erased B ≃ᴱ Erased C))
        lemma₁ = Eq.↔→≃
          ([_]→ ∘_)
          (λ f x →
             EEq.⟨ (λ y → [ _≃ᴱ_.to (f x .erased) y .erased ])
                 , ( (λ y → [ _≃ᴱ_.from (f x .erased) y .erased ])
                   , [ _≃ᴱ_.is-equivalence (f x .erased)
                         .proj₂ .erased ]
                   )
                 ⟩)
          refl
          refl

        lemma₂ :
          (Erased A → Erased B ≃ᴱ Erased C) ≃
          Erased (A → Erased B ≃ᴱ Erased C)
        lemma₂ =
          (Erased A → Erased B ≃ᴱ Erased C)           ↝⟨ lemma₁ ⟩
          (Erased A → Erased (Erased B ≃ᴱ Erased C))  ↔⟨ inverse Erased-Π↔Π-Erased ⟩□
          Erased (A → Erased B ≃ᴱ Erased C)           □

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
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = implication}         ext _ = apply-ext ext λ _ → Eq.lift-equality ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = logical-equivalence} ext _ = apply-ext ext λ _ → Eq.lift-equality ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = injection}           ext _ = apply-ext ext λ _ → Eq.lift-equality ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = embedding}           ext _ = apply-ext ext λ _ → Eq.lift-equality ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = surjection}          ext _ = apply-ext ext λ _ → Eq.lift-equality ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = bijection}           ext _ = apply-ext ext λ _ → Eq.lift-equality ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = equivalence}         ext _ = apply-ext ext λ _ → Eq.lift-equality ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalence}         {k′ = equivalenceᴱ}        ext _ = apply-ext ext λ _ → Eq.lift-equality ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = implication}         ext _ = to≡to→≡ ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = logical-equivalence} ext _ = to≡to→≡ ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = injection}           ext _ = to≡to→≡ ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = embedding}           ext _ = to≡to→≡ ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = surjection}          ext _ = to≡to→≡ ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = bijection}           ext _ = to≡to→≡ ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = equivalence}         ext _ = to≡to→≡ ext (refl _)
  to-Erased-↝↔↝≡to-Erased-↝↝↝ {k = equivalenceᴱ}        {k′ = equivalenceᴱ}        ext _ = to≡to→≡ ext (refl _)
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

------------------------------------------------------------------------
-- Results that depend on three instances of the axiomatisation of
-- []-cong, all for the same universe level

module []-cong₁₃
  (ax₁ : E₁.[]-cong-axiomatisation ℓ)
  (ax₂ : E₁.[]-cong-axiomatisation ℓ)
  (ax  : E₁.[]-cong-axiomatisation ℓ)
  where

  -- Note that []-cong₂-⊔, which contains Erased-cong, is instantiated
  -- with all of the module parameters.

  open []-cong₂-⊔ ax₁ ax₂ ax

  private
    module BC₁ = E₁.[]-cong₁ ax₁
    module BC₂ = E₁.[]-cong₁ ax₂

  ----------------------------------------------------------------------
  -- Erased-cong maps F.id to F.id for all kinds of functions (in some
  -- cases assuming extensionality)

  private

    -- Lemmas used in the implementation of Erased-cong-id.

    Erased-cong-≃-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong {k = equivalence} F.id ≡ F.id {A = Erased A}
    Erased-cong-≃-id ext = Eq.lift-equality ext (refl _)

    Erased-cong-≃ᴱ-id :
      {@0 A : Type ℓ} →
      Erased (Extensionality ℓ ℓ) →
      Erased-cong {k = equivalenceᴱ} F.id ≡ F.id {A = Erased A}
    Erased-cong-≃ᴱ-id [ ext ] =
      EEq.[]-cong₂-⊔.to≡to→≡-Erased ax₁ ax₂ ax ext (refl _)

    Erased-cong-Embedding-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong {k = embedding} F.id ≡ F.id {A = Erased A}
    Erased-cong-Embedding-id ext =
      _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _

    Erased-cong-↠-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong {k = surjection} F.id ≡ F.id {A = Erased A}
    Erased-cong-↠-id ext =                              $⟨ lemma ⟩
      _↔_.to ↠↔∃-Split-surjective (Erased-cong F.id) ≡
      _↔_.to ↠↔∃-Split-surjective F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism ↠↔∃-Split-surjective) ⟩□

      Erased-cong F.id ≡ F.id                           □
      where
      lemma :
        (map id , λ x → [ erased x ] , BC₂.[]-cong [ refl _ ]) ≡
        (id , λ x → x , refl _)
      lemma =
        cong (_ ,_) $ apply-ext ext λ _ → cong (_ ,_) BC₂.[]-cong-[refl]

    Erased-cong-↔-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong {k = bijection} F.id ≡ F.id {A = Erased A}
    Erased-cong-↔-id ext =                          $⟨ lemma ⟩
      _↔_.to Bijection.↔-as-Σ (Erased-cong F.id) ≡
      _↔_.to Bijection.↔-as-Σ F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism Bijection.↔-as-Σ) ⟩□

      Erased-cong F.id ≡ F.id                       □
      where
      lemma :
        ( map id
        , map id
        , (λ { [ x ] → BC₂.[]-cong [ refl x ] })
        , (λ { [ x ] → BC₁.[]-cong [ refl x ] })
        ) ≡
        (id , id , refl , refl)
      lemma = cong (λ p → id , id , p) $ cong₂ _,_
        (apply-ext ext λ _ → BC₂.[]-cong-[refl])
        (apply-ext ext λ _ → BC₁.[]-cong-[refl])

    Erased-cong-↣-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong {k = injection} F.id ≡ F.id {A = Erased A}
    Erased-cong-↣-id ext =                       $⟨ lemma ⟩
      _↔_.to ↣↔∃-Injective (Erased-cong F.id) ≡
      _↔_.to ↣↔∃-Injective F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism ↣↔∃-Injective) ⟩□

      Erased-cong F.id ≡ F.id                    □
      where
      lemma :
        ( map id
        , λ {_ _} → _↣_.injective (Erased-cong F.id)
        ) ≡
        (id , λ {_ _} → _↣_.injective F.id)
      lemma =
        cong (_ ,_) $
        implicit-extensionality ext λ _ →
        implicit-extensionality ext λ _ →
        apply-ext ext λ eq →
          BC₁.[]-cong (BC₂.[]-cong⁻¹ eq)  ≡⟨ []-cong-unique ax₁ ax₂ ⟩
          BC₂.[]-cong (BC₂.[]-cong⁻¹ eq)  ≡⟨ _↔_.right-inverse-of BC₂.Erased-≡↔[]≡[] _ ⟩∎
          eq                              ∎

  -- Erased-cong maps F.id to F.id for all kinds of functions (in some
  -- cases assuming extensionality).

  Erased-cong-id :
    {@0 A : Type ℓ} →
    Extensionality? k ℓ ℓ →
    Erased-cong F.id ≡ F.id {k = k} {A = Erased A}
  Erased-cong-id {k = implication}         = λ _ → map-id
  Erased-cong-id {k = logical-equivalence} = λ _ → Erased-cong-⇔-id
  Erased-cong-id {k = injection}           = Erased-cong-↣-id
  Erased-cong-id {k = embedding}           = Erased-cong-Embedding-id
  Erased-cong-id {k = surjection}          = Erased-cong-↠-id
  Erased-cong-id {k = bijection}           = Erased-cong-↔-id
  Erased-cong-id {k = equivalence}         = Erased-cong-≃-id
  Erased-cong-id {k = equivalenceᴱ}        = Erased-cong-≃ᴱ-id

------------------------------------------------------------------------
-- Results that depend on instances of the axiomatisation of []-cong
-- for three universe levels, as well as for the maximum of each pair
-- drawn from these three levels

module []-cong₃-⊔
  (ax₁  : []-cong-axiomatisation ℓ₁)
  (ax₂  : []-cong-axiomatisation ℓ₂)
  (ax₃  : []-cong-axiomatisation ℓ₃)
  (ax₁₂ : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  (ax₁₃ : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₃))
  (ax₂₃ : []-cong-axiomatisation (ℓ₂ ⊔ ℓ₃))
  where

  private
    module EC₁ = []-cong₂-⊔ ax₁ ax₃ ax₁₃
    module EC₂ = []-cong₂-⊔ ax₂ ax₃ ax₂₃
    module EC₃ = []-cong₂-⊔ ax₁ ax₂ ax₁₂

  ----------------------------------------------------------------------
  -- Erased-cong commutes with F._∘_ for all kinds of functions (in
  -- some cases assuming extensionality)

  private

    -- Lemmas used in the implementation of Erased-cong-∘.

    Erased-cong-≃-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ≃ C) (@0 g : A ≃ B) →
      EC₁.Erased-cong {k = equivalence} (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-≃-∘ ext _ _ = Eq.lift-equality ext (refl _)

    Erased-cong-≃ᴱ-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Erased (Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃)) →
      (@0 f : B ≃ᴱ C) (@0 g : A ≃ᴱ B) →
      EC₁.Erased-cong {k = equivalenceᴱ} (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-≃ᴱ-∘ [ ext ] _ _ =
      EEq.[]-cong₂-⊔.to≡to→≡-Erased ax₁ ax₃ ax₁₃ ext (refl _)

    Erased-cong-Embedding-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : Embedding B C) (@0 g : Embedding A B) →
      EC₁.Erased-cong {k = embedding} (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-Embedding-∘ ext _ _ =
      _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _

    right-inverse-of-cong-∘ :
      ∀ {ℓ₁ ℓ₂ ℓ₃}
      (ax₁  : []-cong-axiomatisation ℓ₁)
      (ax₂  : []-cong-axiomatisation ℓ₂)
      (ax₃  : []-cong-axiomatisation ℓ₃)
      (ax₁₂ : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
      (ax₁₃ : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₃))
      (ax₂₃ : []-cong-axiomatisation (ℓ₂ ⊔ ℓ₃)) →
      let module EC₁′ = []-cong₂-⊔ ax₁ ax₃ ax₁₃
          module EC₂′ = []-cong₂-⊔ ax₂ ax₃ ax₂₃
          module EC₃′ = []-cong₂-⊔ ax₁ ax₂ ax₁₂
      in
      ∀ {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} {x} →
      (@0 f : B ↠ C) (@0 g : A ↠ B) →
      _↠_.right-inverse-of (EC₁′.Erased-cong (f F.∘ g)) x ≡
      _↠_.right-inverse-of (EC₂′.Erased-cong f F.∘ EC₃′.Erased-cong g) x
    right-inverse-of-cong-∘ ax₁ ax₂ ax₃ _ _ _ {x = [ x ]} f g =
      BC₃.[]-cong [ trans (cong (_↠_.to f)
                                  (_↠_.right-inverse-of g
                                     (_↠_.from f x)))
                               (_↠_.right-inverse-of f x)
                  ]                                         ≡⟨ E₁.[]-cong₁.[]-cong-trans ax₃ ⟩

      trans (BC₃.[]-cong [ cong (_↠_.to f)
                             (_↠_.right-inverse-of g
                                (_↠_.from f x)) ])
        (BC₃.[]-cong [ _↠_.right-inverse-of f x ])          ≡⟨ cong (λ p → trans p _) (E₁.[]-cong₂.[]-cong-cong ax₂ ax₃) ⟩∎

      trans (cong (map (_↠_.to f))
                     (BC₂.[]-cong [ _↠_.right-inverse-of g
                                      (_↠_.from f x) ]))
        (BC₃.[]-cong [ _↠_.right-inverse-of f x ])          ∎
      where
      module BC₂ = E₁.[]-cong₁ ax₂
      module BC₃ = E₁.[]-cong₁ ax₃

    Erased-cong-↠-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality ℓ₃ (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ↠ C) (@0 g : A ↠ B) →
      EC₁.Erased-cong {k = surjection} (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-↠-∘ ext f g =                                    $⟨ lemma ⟩
      _↔_.to ↠↔∃-Split-surjective (EC₁.Erased-cong (f F.∘ g)) ≡
      _↔_.to ↠↔∃-Split-surjective
        (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)                ↝⟨ Eq.≃-≡ (from-isomorphism ↠↔∃-Split-surjective) ⟩□

      EC₁.Erased-cong (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g                    □
      where
      lemma :
        ( map (_↠_.to f ∘ _↠_.to g)
        , (λ x →
               [ _↠_.from g (_↠_.from f (erased x)) ]
             , _↠_.right-inverse-of (EC₁.Erased-cong (f F.∘ g)) x)
        )
        ≡
        ( (λ x → [ _↠_.to f (_↠_.to g (erased x)) ])
        , (λ x →
               [ _↠_.from g (_↠_.from f (erased x)) ]
             , _↠_.right-inverse-of
                 (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g) x)
        )
      lemma =
        cong (_ ,_) $ apply-ext ext λ ([ x ]) →
          cong ([ _↠_.from g (_↠_.from f x) ] ,_)
            (right-inverse-of-cong-∘ ax₁ ax₂ ax₃ ax₁₂ ax₁₃ ax₂₃ f g)

    Erased-cong-↔-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ↔ C) (@0 g : A ↔ B) →
      EC₁.Erased-cong {k = bijection} (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-↔-∘ ext f g =                                            $⟨ lemma ⟩
      _↔_.to Bijection.↔-as-Σ (EC₁.Erased-cong (f F.∘ g)) ≡
      _↔_.to Bijection.↔-as-Σ (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)  ↝⟨ Eq.≃-≡ (from-isomorphism Bijection.↔-as-Σ) ⟩□

      EC₁.Erased-cong (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g                            □
      where
      lemma :
        ( map (_↔_.to f ∘ _↔_.to g)
        , map (_↔_.from g ∘ _↔_.from f)
        , _↔_.right-inverse-of (EC₁.Erased-cong (f F.∘ g))
        , _↔_.left-inverse-of (EC₁.Erased-cong (f F.∘ g))
        )
        ≡
        ( (λ x → [ _↔_.to f (_↔_.to g (erased x)) ])
        , (λ x → [ _↔_.from g (_↔_.from f (erased x)) ])
        , _↔_.right-inverse-of (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)
        , _↔_.left-inverse-of (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)
        )
      lemma =
        cong (λ p → map (_↔_.to f ∘ _↔_.to g)
                  , map (_↔_.from g ∘ _↔_.from f) , p) $
        cong₂ _,_
          (apply-ext (lower-extensionality ℓ₁ ℓ₁ ext) λ _ →
             right-inverse-of-cong-∘ ax₁ ax₂ ax₃ ax₁₂ ax₁₃ ax₂₃
               (_↔_.surjection f) (_↔_.surjection g))
          (apply-ext (lower-extensionality ℓ₃ ℓ₃ ext) λ _ →
           right-inverse-of-cong-∘ ax₃ ax₂ ax₁ ax₂₃ ax₁₃ ax₁₂
              (_↔_.surjection $ inverse g)
              (_↔_.surjection $ inverse f))

    Erased-cong-↣-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ↣ C) (@0 g : A ↣ B) →
      EC₁.Erased-cong {k = injection} (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-↣-∘ ext f g =                                         $⟨ lemma ⟩
      _↔_.to ↣↔∃-Injective (EC₁.Erased-cong (f F.∘ g)) ≡
      _↔_.to ↣↔∃-Injective (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)  ↝⟨ Eq.≃-≡ (from-isomorphism ↣↔∃-Injective) ⟩□

      EC₁.Erased-cong (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g                         □
      where
      module BC₁ = E₁.[]-cong₁ ax₁
      module BC₂ = E₁.[]-cong₁ ax₂
      module BC₃ = E₁.[]-cong₁ ax₃

      lemma :
        ( map (_↣_.to f ∘ _↣_.to g)
        , λ {_ _} → _↣_.injective (EC₁.Erased-cong (f F.∘ g))
        )
        ≡
        ( (λ x → [ _↣_.to f (_↣_.to g (erased x)) ])
        , λ {_ _} →
            _↣_.injective (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)
        )
      lemma =
        cong (_ ,_) $
        implicit-extensionality
          (lower-extensionality ℓ₃ lzero ext) λ _ →
        implicit-extensionality
          (lower-extensionality ℓ₃ lzero ext) λ _ →
        apply-ext (lower-extensionality ℓ₁ ℓ₃ ext) λ eq →
          let eq′ = [ _↣_.injective f (erased (BC₃.[]-cong⁻¹ eq)) ]
          in
          BC₁.[]-cong [ _↣_.injective g (erased eq′) ]                  ≡⟨ cong BC₁.[]-cong $
                                                                           BC₁.[]-cong [ cong (_↣_.injective g ∘ erased) $ sym $
                                                                                         _↔_.left-inverse-of BC₂.Erased-≡↔[]≡[] _ ] ⟩∎
          BC₁.[]-cong [ _↣_.injective g
                          (erased (BC₂.[]-cong⁻¹ (BC₂.[]-cong eq′))) ]  ∎

  -- Erased-cong commutes with F._∘_ for all kinds of functions (in
  -- some cases assuming extensionality).

  Erased-cong-∘ :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
    Extensionality? k (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
    (@0 f : B ↝[ k ] C) (@0 g : A  ↝[ k ] B) →
    EC₁.Erased-cong (f F.∘ g) ≡ EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
  Erased-cong-∘ {k = implication}         = λ _ f → map-∘ f
  Erased-cong-∘ {k = logical-equivalence} = λ _ → Erased-cong-⇔-∘
  Erased-cong-∘ {k = injection}           = Erased-cong-↣-∘
  Erased-cong-∘ {k = embedding}           = λ ext f g →
                                              Erased-cong-Embedding-∘
                                                ext f g
  Erased-cong-∘ {k = surjection}          = λ ext →
                                              Erased-cong-↠-∘
                                                (lower-extensionality ℓ₁ lzero ext)
  Erased-cong-∘ {k = bijection}           = Erased-cong-↔-∘
  Erased-cong-∘ {k = equivalence}         = Erased-cong-≃-∘
  Erased-cong-∘ {k = equivalenceᴱ}        = λ ext f g →
                                              Erased-cong-≃ᴱ-∘ ext f g

------------------------------------------------------------------------
-- Results that depend on instances of the axiomatisation of []-cong
-- for all universe levels

module []-cong (ax : ∀ {ℓ} → []-cong-axiomatisation ℓ) where

  private
    open module BC₂ {ℓ₁ ℓ₂} = []-cong₂-⊔ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) ax
      public
    open module BC₁₃ {ℓ} = []-cong₁₃ (ax {ℓ = ℓ}) ax ax
      public
    open module BC₃ {ℓ₁ ℓ₂ ℓ₃} =
      []-cong₃-⊔ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) (ax {ℓ = ℓ₃}) ax ax ax
      public
