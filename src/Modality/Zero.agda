------------------------------------------------------------------------
-- The zero modality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Modality.Zero
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

import Accessibility eq as A
open import Bijection eq using (_↔_)
open import Equality.Decision-procedures eq
open import Equivalence eq using (_≃_)
open import Equivalence.Path-split eq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import Modality.Basics eq

private
  variable
    a b ℓ ℓ′ p : Level
    A          : Type a

------------------------------------------------------------------------
-- The zero modality

-- The zero modality.
--
-- This modality is taken from "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

Zero : Type ℓ → Type ℓ
Zero _ = ↑ _ ⊤

-- A type A is Zero-stable if Zero A implies A.

Zero-stable : Type ℓ → Type ℓ
Zero-stable A = Zero A → A

-- A type is Zero-modal if it is contractible.
--
-- This definition is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

Zero-modal : Type ℓ → Type ℓ
Zero-modal = Contractible

-- Zero-modal types are Zero-stable.

Zero-modal→Zero-stable : Zero-modal A → Zero-stable A
Zero-modal→Zero-stable m _ = proj₁ m

-- A type A has Zero-stable equality if x ≡ y is Zero-stable for all
-- values x and y of type A.

Zero-stable-≡ : Type a → Type a
Zero-stable-≡ = For-iterated-equality 1 Zero-stable

-- A type A has Zero-modal equality if x ≡ y is Zero-modal for all
-- values x and y of type A.

Zero-modal-≡ : Type a → Type a
Zero-modal-≡ = For-iterated-equality 1 Zero-modal

-- The zero modality is a modality.
--
-- This proof is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

Zero-modality : Modality ℓ
Zero-modality {ℓ} = λ where
    .◯            → Zero
    .η            → return
    .modality-for → λ where
      .Modal               → Zero-modal
      .Modal-propositional → λ ext → H-level-propositional ext 0
      .Modal-◯             → ↑-closure 0 ⊤-contractible
      .Modal-respects-≃    → H-level-cong _ 0
      .extendable-along-η  → extendable
  where
  open Modality
  open Modality-for

  return : A → Zero A
  return = _

  extendable :
    {A : Type ℓ} {P : Zero A → Type ℓ} →
    (∀ x → Zero-modal (P x)) →
    Is-∞-extendable-along-[ return {A = A} ] P
  extendable cB zero    = _
  extendable cB (suc n) =
      (λ g → proj₁ ∘ cB , (λ x → proj₂ (cB _) (g x)))
    , (λ _ _ → extendable (⇒≡ 0 ∘ cB) n)

-- The zero modality is topological.
--
-- This result is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

Zero-topological : Topological (Zero-modality {ℓ = ℓ})
Zero-topological {ℓ} =
    ( ↑ ℓ ⊤
    , (λ _ → ⊥)
    , (λ _ → record { to = to; from = from })
    )
  , (λ _ → ⊥-propositional)
  where
  open Modality (Zero-modality {ℓ = ℓ})

  to :
    Zero-modal A →
    ↑ ℓ ⊤ → Is-∞-extendable-along-[ η {A = ⊥} ] (λ _ → A)
  to cA _ zero    = _
  to cA _ (suc n) =
      (λ _ → (λ _ → proj₁ cA) , (λ ()))
    , (λ _ _ → to (⇒≡ 0 cA) _ n)

  from :
    (↑ ℓ ⊤ → Is-∞-extendable-along-[ η ] (λ _ → A)) →
    Zero-modal A
  from {A} ext =
      inh
    , (λ x →
         ext _ 2 .proj₂ (const inh) (const x) .proj₁ ⊥-elim .proj₁ _)
    where
    inh : A
    inh = ext _ 1 .proj₁ ⊥-elim .proj₁ _

-- The zero modality is very modal.

Zero-very-modal : Very-modal (Zero-modality {ℓ = ℓ})
Zero-very-modal {ℓ} {A} =
                         $⟨ _ ⟩
  ↑ ℓ ⊤                  →⟨ id ⟩□
  Zero (Contractible A)  □

------------------------------------------------------------------------
-- Some properties that hold for Erased do not hold for every
-- topological modality

-- The zero modality is not empty-modal.
--
-- Compare with Erased.Stability.[]-cong₁.Erased-empty-modal.

Zero-not-empty-modal : ¬ Empty-modal (Zero-modality {ℓ = ℓ})
Zero-not-empty-modal {ℓ} =
  Zero-modal ⊥    ↔⟨⟩
  Contractible ⊥  →⟨ ⊥-elim ∘ proj₁ ⟩□
  ⊥               □

-- The zero modality is not W-modal.
--
-- Compare with Erased.Stability.[]-cong₁.Erased-W-modal.

Zero-not-W-modal : ¬ W-modal (Zero-modality {ℓ = ℓ})
Zero-not-W-modal {ℓ} =
  W-modal Zero-modality      →⟨ W-modal→Empty-modal ⟩
  Empty-modal Zero-modality  →⟨ Zero-not-empty-modal ⟩□
  ⊥                          □
  where
  open Modality (Zero-modality {ℓ = ℓ})

-- The Zero modality is not accessibility-modal for any relation.

¬-Zero-accessibility-modal-for :
  {_<_ : A → A → Type ℓ} →
  ¬ Modality.Accessibility-modal-for Zero-modality _<_
¬-Zero-accessibility-modal-for {ℓ} {_<_} =
  Accessibility-modal-for _<_           →⟨ Stable-Acc-[]◯ ⟩
  Stable (A.Acc _[ _<_ ]◯_ (lift tt))   →⟨ Stable-respects-⇔ record
                                             { to   = λ acc → A.Acc-map _ acc
                                             ; from = λ acc → A.Acc-map _ acc
                                             } ⟩
  Stable (A.Acc (λ _ _ → ⊤) (lift tt))  →⟨ _$ _ ⟩
  A.Acc (λ _ _ → ⊤) (lift tt)           →⟨ A.<→¬-Acc _ ⟩□
  ⊥                                     □
  where
  open Modality (Zero-modality {ℓ = ℓ})

-- The zero modality is not accessibility-modal.
--
-- Compare with Erased.Stability.[]-cong₁.Erased-accessibility-modal.

¬-Zero-accessibility-modal :
  ¬ Modality.Accessibility-modal (Zero-modality {ℓ = ℓ})
¬-Zero-accessibility-modal acc =
  ¬-Zero-accessibility-modal-for
    {A = ↑ _ ⊤}
    {_<_ = λ _ _ → ↑ _ ⊤}
    acc

-- It is not the case that Zero ⊥ is isomorphic to ⊥.
--
-- Compare with Erased.Level-1.Erased-⊥↔⊥.

¬[Zero-⊥↔⊥] : ¬ (Zero (⊥ {ℓ = ℓ}) ↔ ⊥ {ℓ = ℓ})
¬[Zero-⊥↔⊥] hyp =
         $⟨ _ ⟩
  ↑ _ ⊤  ↝⟨ hyp ⟩
  ⊥      ↝⟨ ⊥↔⊥ ⟩□
  ⊥₀     □

-- It is not the case that Zero A implies ¬ ¬ A for all types A.
--
-- Compare with Erased.Stability.Erased→¬¬.

¬[Zero→¬¬] : ¬ ({A : Type a} → Zero A → ¬ ¬ A)
¬[Zero→¬¬] hyp =
          $⟨ _ ⟩
  Zero ⊥  ↝⟨ hyp ⟩
  ¬ ¬ ⊥   ↝⟨ ⊥-elim ∘ (_$ ⊥-elim) ⟩□
  ⊥       □

-- It is not the case that, for all types A, if A is stable for
-- double-negation, then A is Zero-stable.
--
-- Compare with Erased.Stability.¬¬-stable→Stable.

¬[¬¬-stable→Zero-stable] :
  ¬ ({A : Type a} → (¬ ¬ A → A) → Zero-stable A)
¬[¬¬-stable→Zero-stable] hyp =
                $⟨ ⊥-elim ∘ (_$ ⊥-elim) ⟩
  (¬ ¬ ⊥ → ⊥)   ↝⟨ hyp ⟩
  (Zero ⊥ → ⊥)  ↝⟨ _$ _ ⟩
  ⊥             ↔⟨ ⊥↔⊥ ⟩□
  ⊥₀            □

-- It is not the case that, for all types A, if A is decided, then A
-- is Zero-stable.
--
-- Compare with Erased.Stability.Dec→Stable.

¬[Dec→Zero-stable] : ¬ ({A : Type a} → Dec A → Zero-stable A)
¬[Dec→Zero-stable] hyp =
                $⟨ inj₂ ⊥-elim ⟩
  Dec ⊥         ↝⟨ hyp ⟩
  (Zero ⊥ → ⊥)  ↝⟨ _$ _ ⟩
  ⊥             ↔⟨ ⊥↔⊥ ⟩□
  ⊥₀            □

-- It is not the case that, for all types A, if equality is decidable
-- for A, then equality for A is Zero-stable.

¬[Decidable-equality→Zero-stable-≡] :
  ¬ ({A : Type a} → Decidable-equality A → Zero-stable-≡ A)
¬[Decidable-equality→Zero-stable-≡] {a} hyp =
                                                            $⟨ ↑.Dec._≟_ Bool._≟_ ⟩
  Decidable-equality (↑ a Bool)                             ↝⟨ (λ dec → hyp dec _ _) ⟩
  (Zero (lift true ≡ lift false) → lift true ≡ lift false)  ↝⟨ _$ _ ⟩
  lift true ≡ lift false                                    ↝⟨ Bool.true≢false ∘ cong lower ⟩□
  ⊥₀                                                        □

-- It is not the case that, for all types A, if equality is decidable
-- for A, then equality for A is Zero-modal.
--
-- Compare with
-- Erased.Stability.[]-cong₁.Decidable-equality→Very-stable-≡.

¬[Decidable-equality→Zero-modal-≡] :
  ¬ ({A : Type a} → Decidable-equality A → Zero-modal-≡ A)
¬[Decidable-equality→Zero-modal-≡] {a} =
  ({A : Type a} →
   Decidable-equality A → Zero-modal-≡ A)   ↝⟨ (implicit-∀-cong _ $ ∀-cong _ λ _ → ∀-cong _ λ _ → ∀-cong _ λ _ →
                                                Zero-modal→Zero-stable) ⟩
  ({A : Type a} →
   Decidable-equality A → Zero-stable-≡ A)  ↝⟨ ¬[Decidable-equality→Zero-stable-≡] ⟩□

  ⊥                                         □

-- It is not the case that the empty types are Zero-modal.
--
-- Compare with Erased.Stability.Very-stable-⊥.

¬[Zero-modal-⊥] : ¬ Zero-modal (⊥ {ℓ = ℓ})
¬[Zero-modal-⊥] =
  Contractible ⊥  ↝⟨ proj₁ ⟩
  ⊥               ↔⟨ ⊥↔⊥ ⟩□
  ⊥₀              □

-- It is not the case that, for any type A and type family P over A,
-- if A is Zero-modal, then W A P is Zero-modal.
--
-- Compare with Erased.Stability.[]-cong₂-⊔₁.Very-stable-W, which is
-- proved under the assumption of function extensionality.

¬[Zero-modal-W] :
  ¬ ({A : Type a} {P : A → Type p} → Zero-modal A → Zero-modal (W A P))
¬[Zero-modal-W] hyp =                   $⟨ ↑-closure 0 ⊤-contractible ⟩
  Zero-modal (↑ _ ⊤)                    ↝⟨ hyp ⟩
  Zero-modal (W (↑ _ ⊤) (λ _ → ↑ _ ⊤))  ↝⟨ proj₁ ⟩
  W (↑ _ ⊤) (λ _ → ↑ _ ⊤)               ↝⟨ inhabited⇒W-empty _ ⟩□
  ⊥                                     □

-- It is not the case that, for all types A and B, if equality is
-- Zero-stable for A and B, then equality is Zero-stable for A ⊎ B.
--
-- Compare with Erased.Stability.Stable-≡-⊎.

¬[Zero-stable-≡-⊎] :
  ¬ ({A : Type a} {B : Type b} →
     Zero-stable-≡ A →
     Zero-stable-≡ B →
     Zero-stable-≡ (A ⊎ B))
¬[Zero-stable-≡-⊎] hyp =                         $⟨ (λ _ _ _ → refl _)
                                                  , (λ _ _ _ → refl _)
                                                  ⟩
  Zero-stable-≡ (↑ _ ⊤) × Zero-stable-≡ (↑ _ ⊤)  ↝⟨ uncurry hyp ⟩
  Zero-stable-≡ (↑ _ ⊤ ⊎ ↑ _ ⊤)                  ↝⟨ (_$ _) ∘ (_$ _) ∘ (_$ _) ⟩
  inj₁ _ ≡ inj₂ _                                ↝⟨ ⊎.inj₁≢inj₂ ⟩□
  ⊥                                              □

-- It is not the case that, for all types A and B, if equality is
-- Zero-modal for A and B, then equality is Zero-modal for A ⊎ B.
--
-- Compare with Erased.Stability.[]-cong₂-⊔₂.Very-stable-≡-⊎.

¬[Zero-modal-≡-⊎] :
  ¬ ({A : Type a} {B : Type b} →
     Zero-modal-≡ A →
     Zero-modal-≡ B →
     Zero-modal-≡ (A ⊎ B))
¬[Zero-modal-≡-⊎] hyp =                        $⟨ (λ _ _ → +⇒≡ (mono₁ 0 (↑-closure 0 ⊤-contractible)))
                                                , (λ _ _ → +⇒≡ (mono₁ 0 (↑-closure 0 ⊤-contractible)))
                                                ⟩
  Zero-modal-≡ (↑ _ ⊤) × Zero-modal-≡ (↑ _ ⊤)  ↝⟨ uncurry hyp ⟩
  Zero-modal-≡ (↑ _ ⊤ ⊎ ↑ _ ⊤)                 ↝⟨ proj₁ ∘ (_$ _) ∘ (_$ _) ⟩
  inj₁ _ ≡ inj₂ _                              ↝⟨ ⊎.inj₁≢inj₂ ⟩□
  ⊥                                            □

-- It is not the case that, for all types A, if equality is
-- Zero-stable for A, then equality is Zero-stable for List A.
--
-- Compare with Erased.Stability.Stable-≡-List.

¬[Zero-stable-≡-List] :
  ¬ ({A : Type a} → Zero-stable-≡ A → Zero-stable-≡ (List A))
¬[Zero-stable-≡-List] hyp =     $⟨ (λ _ _ _ → refl _) ⟩
  Zero-stable-≡ (↑ _ ⊤)         ↝⟨ hyp ⟩
  Zero-stable-≡ (List (↑ _ ⊤))  ↝⟨ (_$ _) ∘ (_$ _) ∘ (_$ _) ⟩
  [] ≡ _ ∷ []                   ↝⟨ List.[]≢∷ ⟩□
  ⊥                             □

-- It is not the case that, for all types A, if equality is Zero-modal
-- for A, then equality is Zero-modal for List A.
--
-- Compare with Erased.Stability.[]-cong₁.Very-stable-≡-List.

¬[Zero-modal-≡-List] :
  ¬ ({A : Type a} → Zero-modal-≡ A → Zero-modal-≡ (List A))
¬[Zero-modal-≡-List] hyp =     $⟨ (λ _ _ → +⇒≡ (mono₁ 0 (↑-closure 0 ⊤-contractible))) ⟩
  Zero-modal-≡ (↑ _ ⊤)         ↝⟨ hyp ⟩
  Zero-modal-≡ (List (↑ _ ⊤))  ↝⟨ proj₁ ∘ (_$ _) ∘ (_$ _) ⟩
  [] ≡ _ ∷ []                  ↝⟨ List.[]≢∷ ⟩□
  ⊥                            □
