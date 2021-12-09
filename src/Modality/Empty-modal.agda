------------------------------------------------------------------------
-- Some results that hold for every empty-modal modality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Modality.Basics

module Modality.Empty-modal
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (open Modality.Basics eq)
  {a}
  (M : Modality a)
  (Modal-⊥ : Empty-modal M)
  where

open Derived-definitions-and-properties eq

open Modality M

open import Prelude

open import Bijection eq as Bijection using (_↔_)
open import Equality.Decidable-UIP eq
open import Equivalence eq as Eq using (_≃_)
open import For-iterated-equality eq
open import Function-universe eq hiding (_∘_)
open import H-level eq as H-level
open import H-level.Closure eq

private
  variable
    ℓ   : Level
    A B : Type ℓ
    k   : A

-- ◯ ⊥ is equivalent to ⊥₀.

◯⊥≃⊥ : ◯ ⊥ ≃ ⊥₀
◯⊥≃⊥ =
  ◯ ⊥  ↝⟨ inverse $ Modal→≃◯ Modal-⊥ ⟩
  ⊥    ↔⟨ ⊥↔⊥ ⟩□
  ⊥₀   □

-- ◯ commutes with ¬_ (assuming extensionality).

◯¬≃¬ : ◯ (¬ A) ↝[ a ∣ lzero ] ¬ ◯ A
◯¬≃¬ {A = A} = generalise-ext?
  (record
     { to = λ f x →   $⟨ _≃_.from ◯×≃ (f , x) ⟩
         ◯ (¬ A × A)  →⟨ ◯-map (_↔_.to ⊥↔⊥ ∘ uncurry _$_) ⟩
         ◯ ⊥          ↔⟨ ◯⊥≃⊥ ⟩□
         ⊥₀           □
     ; from = λ hyp → η (hyp ∘ η)
     })
  (λ ext →
       (λ f → apply-ext ext λ x →
          ⊥-elim (f x))
     , ◯-elim
         (λ _ → Separated-◯ _ _)
         (λ f → cong η $ apply-ext ext λ x →
            ⊥-elim (f x)))

-- ◯ can be dropped under ¬_ (assuming extensionality).

¬◯≃¬ : ¬ ◯ A ↝[ a ∣ lzero ] ¬ A
¬◯≃¬ {A = A} =
  generalise-ext?-prop
    (record
       { to   = _∘ η
       ; from = λ f → ⊥-elim ∘ ◯-rec Modal-⊥ (⊥-elim ∘ f)
       })
    ¬-propositional
    ¬-propositional

-- Dec A implies Dec (◯ A).
--
-- This result appears in (at least one version of) the Coq code
-- accompanying "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.

Dec→Dec-◯ : Dec A → Dec (◯ A)
Dec→Dec-◯ (yes x)    = yes (η x)
Dec→Dec-◯ (no empty) =
  no (⊥-elim ∘ ◯-rec Modal-⊥ (⊥-elim ∘ empty))

-- ◯ A implies ¬ ¬ A.

◯→¬¬ : ◯ A → ¬ ¬ A
◯→¬¬ x f = _≃_.to ◯⊥≃⊥ (◯-map (⊥-elim ∘ f) x)

-- Types that are stable for double negation are stable.

¬¬-stable→Stable : (¬ ¬ A → A) → Stable A
¬¬-stable→Stable = _∘ ◯→¬¬

-- Types for which it is known whether or not they are inhabited are
-- stable.

Dec→Stable : Dec A → Stable A
Dec→Stable         (yes x)    = λ _ → x
Dec→Stable {A = A} (no empty) =
  ◯ A    →⟨ ◯→¬¬ ⟩
  ¬ ¬ A  →⟨ _$ empty ⟩
  ⊥      →⟨ ⊥-elim ⟩□
  A      □

-- If equality is decidable for A, then A is separated.

Decidable-equality→Separated :
  Decidable-equality A → Separated A
Decidable-equality→Separated dec x y =
  Stable→Is-proposition→Modal
    (Dec→Stable (dec x y))
    (decidable⇒set dec)

-- The type ¬ A is k-stable (perhaps assuming function
-- extensionality).

Stable-¬ :
  Extensionality? k a lzero →
  Stable-[ k ] (¬ A)
Stable-¬ {A = A} ext =
  ◯ (¬ A)  ↝⟨ ◯¬≃¬ ext ⟩
  ¬ (◯ A)  ↝⟨ ¬◯≃¬ ext ⟩□
  ¬ A      □

-- ¬ A is modal (assuming function extensionality).

Modal-¬ :
  Extensionality a lzero →
  Modal (¬ A)
Modal-¬ {A = A} ext =
  Is-equivalence-η→Modal $
  _≃_.is-equivalence $
  Eq.with-other-function
    (inverse $ Stable-¬ ext)
    η
    (λ empty → cong η $ apply-ext ext (⊥-elim ∘ empty))

-- If equality is k-stable for A and B, then equality is k-stable
-- for A ⊎ B. (The lemma is more general.)

Stable-≡-⊎ :
  ∀ n →
  For-iterated-equality (1 + n) Stable-[ k ] A →
  For-iterated-equality (1 + n) Stable-[ k ] B →
  For-iterated-equality (1 + n) Stable-[ k ] (A ⊎ B)
Stable-≡-⊎ n sA sB =
  For-iterated-equality-⊎-suc
    n
    lemma
    (Modal→Stable Modal-⊥)
    (For-iterated-equality-↑ _ (1 + n) lemma sA)
    (For-iterated-equality-↑ _ (1 + n) lemma sB)
  where
  lemma : A ↔ B → Stable-[ k ] A → Stable-[ k ] B
  lemma = Stable-respects-≃ ∘ from-isomorphism

-- If A and B are separated, then A ⊎ B is separated. (The lemma is
-- more general.)

Separated-⊎ :
  ∀ n →
  For-iterated-equality (1 + n) Modal A →
  For-iterated-equality (1 + n) Modal B →
  For-iterated-equality (1 + n) Modal (A ⊎ B)
Separated-⊎ n sA sB =
  For-iterated-equality-⊎-suc
    n
    lemma
    Modal-⊥
    (For-iterated-equality-↑ _ (1 + n) lemma sA)
    (For-iterated-equality-↑ _ (1 + n) lemma sB)
  where
  lemma : A ↔ B → Modal A → Modal B
  lemma = Modal-respects-≃ ∘ from-isomorphism

-- If equality is k-stable for A, then it is k-stable for List A.
-- (The lemma is more general.)

Stable-≡-List :
  ∀ n →
  For-iterated-equality (1 + n) Stable-[ k ] A →
  For-iterated-equality (1 + n) Stable-[ k ] (List A)
Stable-≡-List n =
  For-iterated-equality-List-suc
    n
    (Stable-respects-≃ ∘ from-isomorphism)
    (Modal→Stable Modal-⊤)
    (Modal→Stable Modal-⊥)
    Stable-×

-- If A is separated, then List A is separated. (The lemma is more
-- general.)

Separated-List :
  ∀ n →
  For-iterated-equality (1 + n) Modal A →
  For-iterated-equality (1 + n) Modal (List A)
Separated-List n =
  For-iterated-equality-List-suc
    n
    (Modal-respects-≃ ∘ from-isomorphism)
    Modal-⊤
    Modal-⊥
    (λ mA mB → Modal-Σ mA λ _ → mB)
