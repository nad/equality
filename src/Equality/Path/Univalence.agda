------------------------------------------------------------------------
-- A proof of univalence
------------------------------------------------------------------------

-- The code is based on code by Anders Mörtberg from Agda's reference
-- manual or the cubical library.

{-# OPTIONS --cubical --safe #-}

module Equality.Path.Univalence where

open import Agda.Builtin.Cubical.Glue as Glue hiding (_≃_)

open import Equality.Path
open import Prelude

open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence.Contractible-preimages equality-with-J as CP
import Equivalence.Half-adjoint equality-with-J as HA
open import Function-universe equality-with-J hiding (id)
open import Preimage equality-with-J
open import Univalence-axiom equality-with-J hiding (≃⇒≡)

private
  variable
    a b ℓ : Level
    A     : Type a

private

  -- Conversions between CP._≃_ and Glue._≃_.

  ≃-CP⇒≃-Glue : {B : Type b} → A CP.≃ B → A Glue.≃ B
  ≃-CP⇒≃-Glue = Σ-map id (λ eq → record { equiv-proof = eq })

  ≃-Glue⇒≃-CP : {B : Type b} → A Glue.≃ B → A CP.≃ B
  ≃-Glue⇒≃-CP = Σ-map id Glue.isEquiv.equiv-proof

  -- Equivalences can be converted to equalities (if the two types live
  -- in the same universe).

  ≃-CP⇒≡ : {A B : Type ℓ} → A CP.≃ B → A ≡ B
  ≃-CP⇒≡ {A = A} {B = B} A≃B = λ i → primGlue B
    (λ { (i = 0̲) → A
       ; (i = 1̲) → B
    })
    (λ { (i = 0̲) → ≃-CP⇒≃-Glue A≃B
       ; (i = 1̲) → ≃-CP⇒≃-Glue CP.id
    })

  -- If ≃-CP⇒≡ is applied to the identity equivalence, then the result
  -- is equal to CP.id.

  ≃-CP⇒≡-id : ≃-CP⇒≡ CP.id ≡ refl {x = A}
  ≃-CP⇒≡-id {A = A} = λ i j → primGlue A
    {φ = max i (max j (- j))}
    (λ _ → A)
    (λ _ → ≃-CP⇒≃-Glue CP.id)

  -- ≃-CP⇒≡ is a left inverse of CP.≡⇒≃.

  ≃-CP⇒≡∘≡⇒≃ :
    {A B : Type ℓ} (A≡B : A ≡ B) →
    ≃-CP⇒≡ (CP.≡⇒≃ A≡B) ≡ A≡B
  ≃-CP⇒≡∘≡⇒≃ = elim
    (λ A≡B → ≃-CP⇒≡ (CP.≡⇒≃ A≡B) ≡ A≡B)
    (λ A →
       ≃-CP⇒≡ (CP.≡⇒≃ refl)  ≡⟨ cong ≃-CP⇒≡ CP.≡⇒≃-refl ⟩
       ≃-CP⇒≡ CP.id          ≡⟨ ≃-CP⇒≡-id ⟩∎
       refl                  ∎)

  -- ≃-CP⇒≡ is a right inverse of CP.≡⇒≃.

  ≡⇒≃∘≃-CP⇒≡ :
    {A B : Type ℓ} (A≃B : A CP.≃ B) →
    CP.≡⇒≃ (≃-CP⇒≡ A≃B) ≡ A≃B
  ≡⇒≃∘≃-CP⇒≡ {A = A} {B = B} A≃B =
    Σ-≡,≡→≡
      (proj₁ (CP.≡⇒≃ (≃-CP⇒≡ A≃B))                            ≡⟨⟩
       proj₁ (transport (λ i → A CP.≃ ≃-CP⇒≡ A≃B i) 0̲ CP.id)  ≡⟨⟩
       transport (λ i → A → ≃-CP⇒≡ A≃B i) 0̲ id                ≡⟨⟩
       transport (λ _ → A → B) 0̲ (proj₁ A≃B)                  ≡⟨ cong (_$ proj₁ A≃B) $ transport-refl 0̲ ⟩∎
       proj₁ A≃B                                              ∎)
      (CP.propositional ext _ _ _)

  -- Univalence for CP._≃_.

  univ-CP : CP.Univalence ℓ
  univ-CP =
    Is-equivalence≃Is-equivalence-CP _ $
    _≃_.is-equivalence $
    Eq.↔→≃ _ ≃-CP⇒≡ ≡⇒≃∘≃-CP⇒≡ ≃-CP⇒≡∘≡⇒≃

-- Univalence.

univ : ∀ {ℓ} → Univalence ℓ
univ {A = A} {B = B} = record
  { univalence = from , proofs
  }
  where
  univ′ : Univalence′ A B
  univ′ = _≃_.from (Univalence≃Univalence-CP ext) univ-CP

  from : A ≃ B → A ≡ B
  from = proj₁ (Univalence′.univalence univ′)

  abstract

    proofs : HA.Proofs ≡⇒≃ from
    proofs = proj₂ (Univalence′.univalence univ′)

-- Equivalences can be converted to equalities (if the two types live
-- in the same universe).

≃⇒≡ : {A B : Type ℓ} → A ≃ B → A ≡ B
≃⇒≡ = _≃_.from Eq.⟨ _ , Univalence′.univalence univ ⟩

private

  -- The type primGlue A B f is equivalent to A.

  primGlue≃-CP :
    (φ : I)
    (B : Partial φ (Type ℓ))
    (f : PartialP φ (λ x → B x Glue.≃ A)) →
    primGlue A B f CP.≃ A
  primGlue≃-CP {A = A} φ B f =
      prim^unglue {φ = φ}
    , λ x →
          ( prim^glue
              (λ p → CP.inverse (proj₂ (f-CP p)) x)
              (hcomp (lemma₁ x) x)
          , (hcomp (lemma₁ x) x  ≡⟨ sym $ hfill (lemma₁ x) (inˢ x) ⟩∎
             x                   ∎)
          )
        , λ y i →
              prim^glue (λ { (φ = 1̲) → proj₁ (lemma₂ is-one y i) })
                        (hcomp (lemma₃ y i) x)
            , (hcomp (lemma₃ y i) x  ≡⟨ sym $ hfill (lemma₃ y i) (inˢ x) ⟩∎
               x                     ∎)
    where
    f-CP : PartialP φ (λ x → B x CP.≃ A)
    f-CP p = ≃-Glue⇒≃-CP (f p)

    lemma₁ : A → ∀ i → Partial φ A
    lemma₁ x i (φ = 1̲) = (
      x                                               ≡⟨ sym (CP.right-inverse-of (proj₂ (f-CP is-one)) x) ⟩∎
      proj₁ (f-CP _) (CP.inverse (proj₂ (f-CP _)) x)  ∎) i

    lemma₂ :
      ∀ {x} p (y : proj₁ (f-CP p) ⁻¹ x) →
      ( CP.inverse (proj₂ (f-CP p)) x
      , CP.right-inverse-of (proj₂ (f-CP p)) x
      ) ≡
      y
    lemma₂ {x} p = CP.irrelevance (proj₂ (f-CP p)) x

    lemma₃ : ∀ {x} → prim^unglue {e = f} ⁻¹ x →
             ∀ i → I → Partial (max φ (max i (- i))) A
    lemma₃     y i j (φ = 1̲) = sym (proj₂ (lemma₂ is-one y i)) j
    lemma₃ {x} _ i j (i = 0̲) = hfill (lemma₁ x) (inˢ x) j
    lemma₃     y i j (i = 1̲) = sym (proj₂ y) j

-- An alternative formulation of univalence.

other-univ : Other-univalence ℓ
other-univ {ℓ = ℓ} {B = B} =                  $⟨ other-univ-CP ⟩
  Contractible (∃ λ (A : Type ℓ) → A CP.≃ B)  ↝⟨ (H-level-cong _ 0 $
                                                  ∃-cong λ _ → inverse $
                                                  ≃≃≃-CP {k = equivalence} ext) ⦂ (_ → _) ⟩□
  Contractible (∃ λ (A : Type ℓ) → A ≃ B)     □
  where
  other-univ-CP : Contractible (∃ λ (A : Type ℓ) → A CP.≃ B)
  other-univ-CP =
      (B , CP.id)
    , λ (A , A≃B) i →
          let C : ∀ i → Partial (max i (- i)) (Type ℓ)
              C = λ { i (i = 0̲) → B
                    ; i (i = 1̲) → A
                    }

              f : ∀ i → PartialP (max i (- i)) (λ j → C i j Glue.≃ B)
              f = λ { i (i = 0̲) → ≃-CP⇒≃-Glue CP.id
                    ; i (i = 1̲) → ≃-CP⇒≃-Glue A≃B
                    }
          in
            primGlue     _ _ (f i)
          , primGlue≃-CP _ _ (f i)
