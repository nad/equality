------------------------------------------------------------------------
-- Embeddings
------------------------------------------------------------------------

-- Partially following the HoTT book.

{-# OPTIONS --without-K #-}

open import Equality

module Embedding
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Injection eq as Injection using (Injective; _↣_)
open import Preimage eq using (_⁻¹_)

------------------------------------------------------------------------
-- Embeddings

-- The property of being an embedding.

Is-embedding : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Is-embedding f = ∀ x y → Is-equivalence (cong f {x = x} {y = y})

-- Is-embedding is propositional (assuming extensionality).

Is-embedding-propositional :
  ∀ {a b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  ∀ {A : Set a} {B : Set b} {f : A → B} →
  Is-proposition (Is-embedding f)
Is-embedding-propositional {b = b} ext =
  Π-closure (lower-extensionality b lzero ext) 1 λ _ →
  Π-closure (lower-extensionality b lzero ext) 1 λ _ →
  Eq.propositional ext _

-- Embeddings.

record Embedding {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    to           : From → To
    is-embedding : Is-embedding to

  equivalence : ∀ {x y} → (x ≡ y) ≃ (to x ≡ to y)
  equivalence = ⟨ _ , is-embedding _ _ ⟩

------------------------------------------------------------------------
-- Preorder

-- Embedding is a preorder.

id : ∀ {a} {A : Set a} → Embedding A A
id {A = A} = record
  { to           = P.id
  ; is-embedding = λ x y →
      Eq.respects-extensional-equality
        cong-id
        (singleton-contractible {A = x ≡ y})
  }

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      Embedding B C → Embedding A B → Embedding A C
f ∘ g = record
  { to           = to f ⊚ to g
  ; is-embedding = λ _ _ →
      Eq.respects-extensional-equality
        (cong-∘ (to f) (to g))
        (Two-out-of-three.f-g
           (two-out-of-three _ _)
           (is-embedding g _ _) (is-embedding f _ _))
  }
  where
  open Embedding

------------------------------------------------------------------------
-- Preimages

-- If f is an embedding, then f ⁻¹ y is propositional.
--
-- This result is taken (perhaps with some changes) from the proof of
-- Theorem 4.6.3 in the HoTT book (first edition).

embedding→⁻¹-propositional :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} →
  Is-embedding f →
  ∀ y → Is-proposition (f ⁻¹ y)
embedding→⁻¹-propositional {f = f} is-emb y =
  _⇔_.from propositional⇔irrelevant
    λ { (x₁ , eq₁) (x₂ , eq₂) →
        let
          equiv : (x₁ ≡ x₂) ≃ (f x₁ ≡ f x₂)
          equiv = ⟨ _ , is-emb _ _ ⟩

          x₁≡x₂ : x₁ ≡ x₂
          x₁≡x₂ = _≃_.from equiv
            (f x₁  ≡⟨ eq₁ ⟩
             y     ≡⟨ sym eq₂ ⟩∎
             f x₂  ∎)
        in
        Σ-≡,≡→≡
          x₁≡x₂
          (subst (λ z → f z ≡ y) x₁≡x₂ eq₁              ≡⟨ subst-∘ (_≡ y) f x₁≡x₂ ⟩
           subst (_≡ y) (cong f x₁≡x₂) eq₁              ≡⟨ cong (λ eq → subst (_≡ y) eq eq₁) $ sym $ sym-sym (cong f x₁≡x₂) ⟩
           subst (_≡ y) (sym $ sym $ cong f x₁≡x₂) eq₁  ≡⟨ subst-trans (sym $ cong f x₁≡x₂) ⟩
           trans (sym $ cong f x₁≡x₂) eq₁               ≡⟨ cong (λ eq → trans (sym eq) eq₁) $ _≃_.right-inverse-of equiv _ ⟩
           trans (sym $ trans eq₁ (sym eq₂)) eq₁        ≡⟨ cong (flip trans eq₁) $ sym-trans eq₁ (sym eq₂) ⟩
           trans (trans (sym (sym eq₂)) (sym eq₁)) eq₁  ≡⟨ trans-[trans-sym]- _ eq₁ ⟩
           sym (sym eq₂)                                ≡⟨ sym-sym _ ⟩∎
           eq₂                                          ∎) }

------------------------------------------------------------------------
-- Injections

-- Functions that are embeddings are injective.

injective : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} →
            Is-embedding f → Injective f
injective is-emb = _≃_.from ⟨ _ , is-emb _ _ ⟩

-- Embeddings are injections.

injection : ∀ {a b} {A : Set a} {B : Set b} → Embedding A B → A ↣ B
injection f = record
  { to        = Embedding.to f
  ; injective = injective (Embedding.is-embedding f)
  }

private

  -- If the domain of f is a set, then Injective f is propositional
  -- (assuming extensionality).

  Injective-propositional :
    ∀ {a b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    ∀ {A : Set a} {B : Set b} {f : A → B} →
    Is-set A → Is-proposition (Injective f)
  Injective-propositional {a} {b} ext A-set =
    implicit-Π-closure (lower-extensionality b lzero ext) 1 λ _ →
    implicit-Π-closure (lower-extensionality b lzero ext) 1 λ _ →
    Π-closure (lower-extensionality a b ext)              1 λ _ →
    A-set _ _

-- For functions between sets the property of being injective is
-- equivalent to the property of being an embedding (assuming
-- extensionality).

Injective≃Is-embedding :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-set A → Is-set B →
  (f : A → B) → Injective f ≃ Is-embedding f
Injective≃Is-embedding ext A-set B-set f =
  _↔_.to
    (⇔↔≃ ext
         (Injective-propositional ext A-set)
         (Is-embedding-propositional ext))
    (record { to   = λ cong-f⁻¹ _ _ →
                         _≃_.is-equivalence $
                         _↔_.to (⇔↔≃ ext (A-set _ _) (B-set _ _))
                                (record { from = cong-f⁻¹ })
            ; from = injective
            })

-- If A and B are sets, then the type of injections from A to B is
-- isomorphic to the type of embeddings from A to B (assuming
-- extensionality).

↣↔Embedding :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-set A → Is-set B →
  (A ↣ B) ↔ Embedding A B
↣↔Embedding {A = A} {B} ext A-set B-set = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → record
                 { to           = _↣_.to f
                 ; is-embedding =
                     _≃_.to (Injective≃Is-embedding ext A-set B-set _)
                            (_↣_.injective f)
                 }
      ; from = injection
      }
    ; right-inverse-of = λ f →
        cong (uncurry λ to (emb : Is-embedding to) →
                        record { to = to; is-embedding = emb })
             (Σ-≡,≡→≡ (refl _)
                      (_⇔_.to propositional⇔irrelevant
                         (Is-embedding-propositional ext) _ _))
    }
  ; left-inverse-of = λ f →
      cong (uncurry λ to (inj : Injective to) →
                      record { to = to; injective = inj })
           (Σ-≡,≡→≡ (refl _)
                    (_⇔_.to propositional⇔irrelevant
                       (Injective-propositional ext A-set) _ _))
  }