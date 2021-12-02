------------------------------------------------------------------------
-- Some results related to modalities that hold if the []-cong axioms
-- can be instantiated
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Erased.Level-1
import Modality.Basics

module Modality.Box-cong
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (open Erased.Level-1 eq using (Erased; []-cong-axiomatisation))
  {a}
  (ax : []-cong-axiomatisation a)
  (open Modality.Basics eq)
  (M : Modality a)
  where

open Derived-definitions-and-properties eq
open Modality M

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equivalence eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq
  using (Contractibleᴱ; _⁻¹ᴱ_)
open import Function-universe eq

private
  variable
    ℓ   : Level
    A B : Type ℓ
    k   : A

private
  module E  = Erased.Level-1 eq
  module BC = E.[]-cong₁ ax

-- If A is modal, then Erased A is modal.

Is-modal-Erased :
  {@0 A : Type a} → @0 Is-modal A → Is-modal (Erased A)
Is-modal-Erased {A = A} m =
  Stable→left-inverse→Is-modal
    (Stable-Erased (Is-modal→Stable m))
    (λ x →
       Stable-Erased (Is-modal→Stable m) (η x)         ≡⟨⟩
       E.[ Is-modal→Stable m (◯-map E.erased (η x)) ]  ≡⟨ BC.[]-cong E.[ cong (Is-modal→Stable m) ◯-map-η ] ⟩
       E.[ Is-modal→Stable m (η (E.erased x)) ]        ≡⟨ BC.[]-cong E.[ _≃_.left-inverse-of (Is-modal→≃◯ m) _ ] ⟩∎
       E.[ E.erased x ]                                ∎)

-- If f has type A → B, where A is modal and B is separated, then
-- Is-equivalenceᴱ f is stable.

Is-modal→Stable-Is-equivalenceᴱ :
  {@0 f : A → B} →
  Is-modal A → @0 Separated B →
  Stable (Is-equivalenceᴱ f)
Is-modal→Stable-Is-equivalenceᴱ {f = f} m s =
                                          $⟨ s′ ⟩
  Stable (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  →⟨ Stable-respects-⇔ $ inverse $
                                             EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP ⟩□
  Stable (Is-equivalenceᴱ f)              □
  where
  s′ =
    Stable-Π λ y →
    let m′ : Is-modal (f ⁻¹ᴱ y)
        m′ = Is-modal-Σ m λ _ → Is-modal-Erased (s _ _) in
    Stable-Σ m′ λ _ →
    Stable-Erased (
    Stable-Π λ _ →
    Is-modal→Stable (Is-modal→Separated m′ _ _))

-- ◯ (A ≃ᴱ B) implies ◯ A ≃ᴱ ◯ B.

◯-cong-≃ᴱ-◯ : ◯ (A ≃ᴱ B) → ◯ A ≃ᴱ ◯ B
◯-cong-≃ᴱ-◯ =
  ◯↝→◯↝◯
    (from-equivalence EEq.≃ᴱ-as-Σ)
    ◯-Is-equivalenceᴱ→Is-equivalenceᴱ
    (λ p → _⇔_.to $ EEq.Is-equivalenceᴱ-cong-⇔ p)
    (Is-modal→Stable-Is-equivalenceᴱ Is-modal-◯ Separated-◯)

-- If the modality is left exact, then ◯ (A ↝[ k ] B) implies
-- ◯ A ↝[ k ] ◯ B.

◯-cong-◯ :
  Left-exact-η-cong →
  ◯ (A ↝[ k ] B) → ◯ A ↝[ k ] ◯ B
◯-cong-◯ {k = implication}         _   = ◯-map-◯
◯-cong-◯ {k = logical-equivalence} _   = ◯-cong-⇔-◯
◯-cong-◯ {k = injection}           lex = ◯-cong-↣-◯ lex
◯-cong-◯ {k = embedding}           lex = ◯-cong-Embedding-◯ lex
◯-cong-◯ {k = surjection}          _   = ◯-cong-↠-◯
◯-cong-◯ {k = bijection}           _   = ◯-cong-↔-◯
◯-cong-◯ {k = equivalence}         _   = ◯-cong-≃-◯
◯-cong-◯ {k = equivalenceᴱ}        _   = ◯-cong-≃ᴱ-◯

-- Some variants of Stable-respects-≃.

Stable-respects-↝-↜ :
  Left-exact-η-cong →
  A ↝[ k ] B → B ↝[ k ] A → Stable-[ k ] A → Stable-[ k ] B
Stable-respects-↝-↜ {A = A} {B = B} lex A↝B B↝A s =
  ◯ B  ↝⟨ ◯-cong-◯ lex (η B↝A) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A↝B ⟩□
  B    □

Stable-respects-↝-sym :
  A ↝[ ⌊ k ⌋-sym ] B →
  Stable-[ ⌊ k ⌋-sym ] A → Stable-[ ⌊ k ⌋-sym ] B
Stable-respects-↝-sym
  {A = A} {k = logical-equivalence} {B = B} A⇔B s =
  ◯ B  ↝⟨ ◯-cong-⇔-◯ (η (inverse A⇔B)) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A⇔B ⟩□
  B    □
Stable-respects-↝-sym {A = A} {k = bijection} {B = B} A↔B s =
  ◯ B  ↝⟨ ◯-cong-↔-◯ (η (inverse A↔B)) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A↔B ⟩□
  B    □
Stable-respects-↝-sym {A = A} {k = equivalence} {B = B} A≃B s =
  ◯ B  ↝⟨ ◯-cong-≃-◯ (η (inverse A≃B)) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A≃B ⟩□
  B    □
Stable-respects-↝-sym {A = A} {k = equivalenceᴱ} {B = B} A≃ᴱB s =
  ◯ B  ↝⟨ ◯-cong-≃ᴱ-◯ (η (inverse A≃ᴱB)) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A≃ᴱB ⟩□
  B    □
