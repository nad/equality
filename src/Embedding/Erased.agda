------------------------------------------------------------------------
-- Embeddings with erased "proofs"
------------------------------------------------------------------------

-- Partially following the HoTT book.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Embedding.Erased
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude hiding (id; _∘_)

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Embedding eq as Emb using (Is-embedding; Embedding)
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (_⁻¹ᴱ_)
open import Erased.Level-1 eq using (Erased; []-cong-axiomatisation)
open import Function-universe eq hiding (id; _∘_; equivalence)
open import H-level.Closure eq
open import Preimage eq using (_⁻¹_)

private
  variable
    a b t   : Level
    A B C   : Type a
    f k x y : A

------------------------------------------------------------------------
-- Embeddings

-- The property of being an embedding with erased "proofs".

Is-embeddingᴱ : {A : Type a} {B : Type b} → (A → B) → Type (a ⊔ b)
Is-embeddingᴱ f = ∀ x y → Is-equivalenceᴱ (cong {x = x} {y = y} f)

-- Is-embeddingᴱ is propositional in erased contexts (assuming
-- extensionality).

@0 Is-embeddingᴱ-propositional :
  {A : Type a} {B : Type b} {f : A → B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-proposition (Is-embeddingᴱ f)
Is-embeddingᴱ-propositional {b = b} ext =
  Π-closure (lower-extensionality b lzero ext) 1 λ _ →
  Π-closure (lower-extensionality b lzero ext) 1 λ _ →
  EEq.Is-equivalenceᴱ-propositional ext _

-- Embeddings with erased proofs.

record Embeddingᴱ (From : Type f) (To : Type t) : Type (f ⊔ t) where
  field
    to           : From → To
    is-embedding : Is-embeddingᴱ to

  equivalence : (x ≡ y) ≃ᴱ (to x ≡ to y)
  equivalence = EEq.⟨ _ , is-embedding _ _ ⟩

------------------------------------------------------------------------
-- Some conversion functions

-- The type family above could have been defined using Σ.

Embeddingᴱ-as-Σ : Embeddingᴱ A B ↔ ∃ λ (f : A → B) → Is-embeddingᴱ f
Embeddingᴱ-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ emb → Embeddingᴱ.to emb , Embeddingᴱ.is-embedding emb
      ; from = λ { (f , is) → record { to = f; is-embedding = is } }
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Conversions between Is-embedding and Is-embeddingᴱ.

Is-embedding→Is-embeddingᴱ : Is-embedding f → Is-embeddingᴱ f
Is-embedding→Is-embeddingᴱ {f = f} =
  (∀ x y → Eq.Is-equivalence (cong {x = x} {y = y} f))  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → EEq.Is-equivalence→Is-equivalenceᴱ) ⟩□
  (∀ x y → Is-equivalenceᴱ (cong {x = x} {y = y} f))    □

@0 Is-embedding≃Is-embeddingᴱ :
  {A : Type a} {B : Type b} {f : A → B} →
  Is-embedding f ↝[ a ∣ a ⊔ b ] Is-embeddingᴱ f
Is-embedding≃Is-embeddingᴱ {f = f} {k = k} ext =
  (∀ x y → Eq.Is-equivalence (cong {x = x} {y = y} f))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → from-equivalence
                                                            EEq.Is-equivalence≃Is-equivalenceᴱ) ⟩□
  (∀ x y → Is-equivalenceᴱ (cong {x = x} {y = y} f))    □

@0 Is-embeddingᴱ→Is-embedding : Is-embeddingᴱ f → Is-embedding f
Is-embeddingᴱ→Is-embedding = inverse-ext? Is-embedding≃Is-embeddingᴱ _

-- Conversions between Embedding and Embeddingᴱ.

Embedding→Embeddingᴱ : Embedding A B → Embeddingᴱ A B
Embedding→Embeddingᴱ {A = A} {B = B} =
  Embedding A B                        ↔⟨ Emb.Embedding-as-Σ ⟩
  (∃ λ (f : A → B) → Is-embedding f)   ↝⟨ (∃-cong λ _ → Is-embedding→Is-embeddingᴱ) ⟩
  (∃ λ (f : A → B) → Is-embeddingᴱ f)  ↔⟨ inverse Embeddingᴱ-as-Σ ⟩□
  Embeddingᴱ A B                       □

@0 Embedding≃Embeddingᴱ :
  {A : Type a} {B : Type b} →
  Embedding A B ↝[ a ∣ a ⊔ b ] Embeddingᴱ A B
Embedding≃Embeddingᴱ {A = A} {B = B} ext =
  Embedding A B                        ↔⟨ Emb.Embedding-as-Σ ⟩
  (∃ λ (f : A → B) → Is-embedding f)   ↝⟨ (∃-cong λ _ → Is-embedding≃Is-embeddingᴱ ext) ⟩
  (∃ λ (f : A → B) → Is-embeddingᴱ f)  ↔⟨ inverse Embeddingᴱ-as-Σ ⟩□
  Embeddingᴱ A B                       □

@0 Embeddingᴱ→Embedding : Embeddingᴱ A B → Embedding A B
Embeddingᴱ→Embedding = inverse-ext? Embedding≃Embeddingᴱ _

-- Data corresponding to the erased proofs of an embedding with
-- erased proofs.

Erased-proofs :
  {A : Type a} {B : Type b} →
  (to : A → B) →
  (∀ {x y} → to x ≡ to y → x ≡ y) →
  Type (a ⊔ b)
Erased-proofs to from =
  ∀ {x y} → EEq.Erased-proofs (cong {x = x} {y = y} to) from

-- Extracts "erased proofs" from a regular embedding.

[proofs] :
  (A↝B : Embedding A B) →
  Erased-proofs
    (Embedding.to A↝B)
    (_≃_.from (Embedding.equivalence A↝B))
[proofs] A↝B = EEq.[proofs] (Embedding.equivalence A↝B)

-- Converts two functions and some erased proofs to an embedding with
-- erased proofs.
--
-- Note that Agda can in many cases infer "to" and "from" from the
-- first explicit argument, see (for instance) _∘_ below.

[Embedding]→Embeddingᴱ :
  {to : A → B} {from : ∀ {x y} → to x ≡ to y → x ≡ y} →
  @0 Erased-proofs to from →
  Embeddingᴱ A B
[Embedding]→Embeddingᴱ {to = to} {from = from} ep = record
  { to           = to
  ; is-embedding = λ _ _ → _≃ᴱ_.is-equivalence (EEq.[≃]→≃ᴱ ep)
  }

------------------------------------------------------------------------
-- Preorder

-- Embeddingᴱ is a preorder.

id : Embeddingᴱ A A
id = Embedding→Embeddingᴱ Emb.id

infixr 9 _∘_

_∘_ : Embeddingᴱ B C → Embeddingᴱ A B → Embeddingᴱ A C
f ∘ g =
  [Embedding]→Embeddingᴱ
    ([proofs] (Embeddingᴱ→Embedding f Emb.∘ Embeddingᴱ→Embedding g))

------------------------------------------------------------------------
-- "Preimages"

-- If f is an embedding (with erased proofs), then f ⁻¹ᴱ y is
-- propositional (in an erased context).
--
-- This result is based on the proof of Theorem 4.6.3 in the HoTT book
-- (first edition).

@0 embedding→⁻¹ᴱ-propositional :
  Is-embeddingᴱ f →
  ∀ y → Is-proposition (f ⁻¹ᴱ y)
embedding→⁻¹ᴱ-propositional {f = f} =
  Is-embeddingᴱ f                   ↝⟨ Is-embeddingᴱ→Is-embedding ⟩
  Is-embedding f                    ↝⟨ Emb.embedding→⁻¹-propositional ⟩
  (∀ y → Is-proposition (f ⁻¹ y))   ↝⟨ (∀-cong _ λ _ → H-level-cong _ 1 ECP.⁻¹≃⁻¹ᴱ) ⟩□
  (∀ y → Is-proposition (f ⁻¹ᴱ y))  □

------------------------------------------------------------------------
-- Results that depend on an axiomatisation of []-cong

module []-cong (ax : ∀ {a} → []-cong-axiomatisation a) where

  ----------------------------------------------------------------------
  -- More conversion functions

  -- Equivalences (with erased proofs) from Erased A to B are
  -- embeddings (with erased proofs).

  Is-equivalenceᴱ→Is-embeddingᴱ-Erased :
    {f : Erased A → B} →
    Is-equivalenceᴱ f → Is-embeddingᴱ f
  Is-equivalenceᴱ→Is-embeddingᴱ-Erased eq _ _ =
    _≃ᴱ_.is-equivalence $ inverse $
      EEq.[]-cong.to≡to≃ᴱ≡-Erased ax EEq.⟨ _ , eq ⟩

  -- Equivalences with erased proofs between Erased A and B can be
  -- converted to embeddings with erased proofs.

  Erased≃→Embedding : Erased A ≃ᴱ B → Embeddingᴱ (Erased A) B
  Erased≃→Embedding EEq.⟨ f , is-equiv ⟩ = record
    { to           = f
    ; is-embedding = Is-equivalenceᴱ→Is-embeddingᴱ-Erased is-equiv
    }
