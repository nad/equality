------------------------------------------------------------------------
-- Some results related to modalities that hold if the []-cong axioms
-- can be instantiated
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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

open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq
  using (Contractibleᴱ; _⁻¹ᴱ_)
import Erased.Level-2 eq as E₂
open import Extensionality eq
open import Function-universe eq hiding (_∘_)
import Modality.Left-exact eq M as Lex

private
  variable
    ℓ   : Level
    A B : Type ℓ
    k   : A

private
  module E  = Erased.Level-1 eq
  module BC = E.[]-cong₁ ax

-- If A is modal, then Erased A is modal.

Modal-Erased :
  {@0 A : Type a} → @0 Modal A → Modal (Erased A)
Modal-Erased {A} m =
  Stable→left-inverse→Modal
    (Stable-Erased (Modal→Stable m))
    (λ x →
       Stable-Erased (Modal→Stable m) (η x)         ≡⟨⟩
       E.[ Modal→Stable m (◯-map E.erased (η x)) ]  ≡⟨ BC.[]-cong E.[ cong (Modal→Stable m) ◯-map-η ] ⟩
       E.[ Modal→Stable m (η (E.erased x)) ]        ≡⟨ BC.[]-cong E.[ _≃_.left-inverse-of (Modal→≃◯ m) _ ] ⟩∎
       E.[ E.erased x ]                             ∎)

-- If f has type A → B, where A is modal and B is separated, then
-- f ⁻¹ᴱ y is modal.

Modal-⁻¹ᴱ :
  {@0 B : Type a} {@0 f : A → B} {@0 y : B} →
  Modal A →
  @0 Separated B →
  Modal (f ⁻¹ᴱ y)
Modal-⁻¹ᴱ m s = Modal-Σ m λ _ → Modal-Erased (s _ _)

-- If f has type A → B, where A is modal and B is separated, then
-- Is-equivalenceᴱ f is stable.

Modal→Stable-Is-equivalenceᴱ :
  {@0 f : A → B} →
  Modal A → @0 Separated B →
  Stable (Is-equivalenceᴱ f)
Modal→Stable-Is-equivalenceᴱ {f} m s =    $⟨ s′ ⟩
  Stable (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  →⟨ Stable-respects-⇔ $ inverse $
                                             EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP ⟩□
  Stable (Is-equivalenceᴱ f)              □
  where
  s′ =
    Stable-Π λ y →
    let m′ : Modal (f ⁻¹ᴱ y)
        m′ = Modal-⁻¹ᴱ m s in
    Stable-Σ m′ λ _ →
    Stable-Erased (
    Stable-Π λ _ →
    Modal→Stable (Modal→Separated m′ _ _))

-- If f has type A → B, where A is modal and B is separated, then
-- Is-equivalenceᴱ f is modal (assuming function extensionality).

Modal-Is-equivalenceᴱ :
  {@0 f : A → B} →
  Extensionality a a →
  Modal A → @0 Separated B →
  Modal (Is-equivalenceᴱ f)
Modal-Is-equivalenceᴱ ext m s =
  Modal-Σ (Modal-Π ext λ _ → m) λ _ →
  Modal-Erased (
  Modal-Half-adjoint-proofs ext (Modal→Separated m) s)

-- ◯ (A ≃ᴱ B) implies ◯ A ≃ᴱ ◯ B.

◯-cong-≃ᴱ-◯ : ◯ (A ≃ᴱ B) → ◯ A ≃ᴱ ◯ B
◯-cong-≃ᴱ-◯ =
  ◯↝→◯↝◯
    (from-equivalence EEq.≃ᴱ-as-Σ)
    ◯-Is-equivalenceᴱ→Is-equivalenceᴱ
    (λ p → _⇔_.to $ EEq.Is-equivalenceᴱ-cong-⇔ p)
    (Modal→Stable-Is-equivalenceᴱ Modal-◯ Separated-◯)

-- If the modality is left exact, then ◯ (A ↝[ k ] B) implies
-- ◯ A ↝[ k ] ◯ B.

◯-cong-◯ :
  Left-exact-η-cong →
  ◯ (A ↝[ k ] B) → ◯ A ↝[ k ] ◯ B
◯-cong-◯ {k = implication}         _   = ◯-map-◯
◯-cong-◯ {k = logical-equivalence} _   = ◯-cong-⇔-◯
◯-cong-◯ {k = injection}           lex = Lex.◯-cong-↣-◯ lex
◯-cong-◯ {k = embedding}           lex = Lex.◯-cong-Embedding-◯ lex
◯-cong-◯ {k = surjection}          _   = ◯-cong-↠-◯
◯-cong-◯ {k = bijection}           _   = ◯-cong-↔-◯
◯-cong-◯ {k = equivalence}         _   = ◯-cong-≃-◯
◯-cong-◯ {k = equivalenceᴱ}        _   = ◯-cong-≃ᴱ-◯

-- Some variants of Stable-respects-≃.

Stable-respects-↝-↜ :
  Left-exact-η-cong →
  A ↝[ k ] B → B ↝[ k ] A → Stable-[ k ] A → Stable-[ k ] B
Stable-respects-↝-↜ {A} {B} lex A↝B B↝A s =
  ◯ B  ↝⟨ ◯-cong-◯ lex (η B↝A) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A↝B ⟩□
  B    □

Stable-respects-↝-sym :
  A ↝[ ⌊ k ⌋-sym ] B →
  Stable-[ ⌊ k ⌋-sym ] A → Stable-[ ⌊ k ⌋-sym ] B
Stable-respects-↝-sym {A} {k = logical-equivalence} {B} A⇔B s =
  ◯ B  ↝⟨ ◯-cong-⇔-◯ (η (inverse A⇔B)) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A⇔B ⟩□
  B    □
Stable-respects-↝-sym {A} {k = bijection} {B} A↔B s =
  ◯ B  ↝⟨ ◯-cong-↔-◯ (η (inverse A↔B)) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A↔B ⟩□
  B    □
Stable-respects-↝-sym {A} {k = equivalence} {B} A≃B s =
  ◯ B  ↝⟨ ◯-cong-≃-◯ (η (inverse A≃B)) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A≃B ⟩□
  B    □
Stable-respects-↝-sym {A} {k = equivalenceᴱ} {B} A≃ᴱB s =
  ◯ B  ↝⟨ ◯-cong-≃ᴱ-◯ (η (inverse A≃ᴱB)) ⟩
  ◯ A  ↝⟨ s ⟩
  A    ↝⟨ A≃ᴱB ⟩□
  B    □

-- If the modality commutes with Σ, then ◯ (η ∘ f ⁻¹ᴱ y) is equivalent
-- to ◯-map f ⁻¹ᴱ y.

◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ :
  {A : Type a} {@0 B : Type a} {@0 f : A → B} {y : ◯ B} →
  Commutes-with-Σ →
  ◯ (η ∘ f ⁻¹ᴱ y) ≃ ◯-map f ⁻¹ᴱ y
◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ {f} {y} comm =
  ◯ (∃ λ x → Erased (η (f x) ≡ y))        ↝⟨ (◯-cong-≃ $ ∃-cong λ _ →
                                              E₂.[]-cong₂-⊔.Erased-cong ax ax ax (
                                              ≡⇒↝ _ $ cong (_≡ _) $ sym ◯-map-η)) ⟩
  ◯ (∃ λ x → Erased (◯-map f (η x) ≡ y))  ↝⟨ Eq.⟨ _ , comm ⟩ ⟩
  (∃ λ x → ◯ (Erased (◯-map f x ≡ y)))    ↝⟨ (∃-cong λ _ → inverse $ Modal→≃◯ (Modal-Erased (Separated-◯ _ _))) ⟩□
  (∃ λ x → Erased (◯-map f x ≡ y))        □
