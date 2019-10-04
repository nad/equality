------------------------------------------------------------------------
-- Erased singletons
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Erased.Cubical.Singleton
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude hiding ([_,_])

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Erased.Cubical eq
open import Function-universe eq as F hiding (_∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc using (∥_∥)
open import Monad eq
open import Surjection eq using (_↠_)

private
  variable
    a   : Level
    A B : Set a
    x   : A
    A↠B : A ↠ B
    s   : Very-stable-≡ A

-- A variant of the Singleton type family with erased equality proofs.

Erased-singleton : {A : Set a} → @0 A → Set a
Erased-singleton x = ∃ λ y → Erased (y ≡ x)

-- The type of triples consisting of two values of type A, one erased,
-- and an erased proof of equality of the two values is isomorphic to
-- A.

Σ-Erased-Erased-singleton↔ :
  (∃ λ (x : Erased A) → Erased-singleton (erased x)) ↔ A
Σ-Erased-Erased-singleton↔ {A = A} =
  (∃ λ (x : Erased A) → ∃ λ y → Erased (y ≡ erased x))  ↝⟨ ∃-comm ⟩
  (∃ λ y → ∃ λ (x : Erased A) → Erased (y ≡ erased x))  ↝⟨ (∃-cong λ _ → inverse Erased-Σ↔Σ) ⟩
  (∃ λ y → Erased (∃ λ (x : A) → y ≡ x))                ↝⟨ (∃-cong λ _ → Erased-cong (_⇔_.to contractible⇔↔⊤ (other-singleton-contractible _))) ⟩
  A × Erased ⊤                                          ↝⟨ drop-⊤-right (λ _ → Erased-⊤↔⊤) ⟩□
  A                                                     □

-- If equality is very stable for A, then Erased-singleton x is
-- contractible for x : A.

erased-singleton-contractible :
  {x : A} →
  Very-stable-≡ A →
  Contractible (Erased-singleton x)
erased-singleton-contractible {x = x} s =
                                     $⟨ singleton-contractible x ⟩
  Contractible (Singleton x)         ↝⟨ H-level-cong _ 0 (∃-cong λ _ → Eq.⟨ _ , s _ _ ⟩) ⦂ (_ → _) ⟩□
  Contractible (Erased-singleton x)  □

-- If equality is very stable for A, and x : A is erased, then
-- Erased-singleton x is a proposition.

erased-singleton-with-erased-center-propositional :
  {@0 x : A} →
  Very-stable-≡ A →
  Is-proposition (Erased-singleton x)
erased-singleton-with-erased-center-propositional {x = x} s =
                                                 $⟨ [ erased-singleton-contractible s ] ⟩
  Erased (Contractible (Erased-singleton x))     ↝⟨ Erased-cong (mono₁ 0) ⟩
  Erased (Is-proposition (Erased-singleton x))   ↝⟨ (Stable-H-level _ 0 $ Very-stable→Stable 1 $
                                                     Very-stable-Σⁿ 1 s λ _ → Very-stable→Very-stable-≡ 0 Very-stable-Erased) ⟩□
  Is-proposition (Erased-singleton x)            □

-- If A is very stable, and x : A is erased, then Erased-singleton x
-- is contractible.

erased-singleton-with-erased-center-contractible :
  {@0 x : A} →
  Very-stable A →
  Contractible (Erased-singleton x)
erased-singleton-with-erased-center-contractible {x = x} s =
                                     $⟨ [ x , [ refl _ ] ] ⟩
  Erased (Erased-singleton x)        ↝⟨ Very-stable→Stable 0 (Very-stable-Σ s λ _ → Very-stable-Erased) ⟩
  Erased-singleton x                 ↝⟨ propositional⇒inhabited⇒contractible $
                                        erased-singleton-with-erased-center-propositional $
                                        Very-stable→Very-stable-≡ 0 s ⟩□
  Contractible (Erased-singleton x)  □

-- A corollary of erased-singleton-with-erased-center-propositional.

↠→↔Erased-singleton :
  {@0 y : B}
  (A↠B : A ↠ B) →
  Very-stable-≡ B →
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ ↔ Erased-singleton y
↠→↔Erased-singleton {A = A} {y = y} A↠B s =
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥  ↝⟨ Trunc.∥∥-cong-⇔ (Eq.∃-preserves-logical-equivalences A↠B λ _ → F.id) ⟩
  ∥ Erased-singleton y ∥                         ↝⟨ Trunc.∥∥↔ (erased-singleton-with-erased-center-propositional s) ⟩□
  Erased-singleton y                             □

mutual

  -- The right-to-left direction of the previous lemma does not depend
  -- on the assumption of stability.

  ↠→Erased-singleton→ :
    {@0 y : B}
    (A↠B : A ↠ B) →
    Erased-singleton y →
    ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥
  ↠→Erased-singleton→ = _  -- Agda can infer the definition.

  _ : _↔_.from (↠→↔Erased-singleton A↠B s) x ≡
      ↠→Erased-singleton→ A↠B x
  _ = refl _

-- A corollary of Σ-Erased-Erased-singleton↔ and ↠→↔Erased-singleton.

Σ-Erased-∥-Σ-Erased-≡-∥↔ :
  (A↠B : A ↠ B) →
  Very-stable-≡ B →
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥) ↔
  B
Σ-Erased-∥-Σ-Erased-≡-∥↔ {A = A} {B = B} A↠B s =
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥)  ↝⟨ (∃-cong λ _ → ↠→↔Erased-singleton A↠B s) ⟩

  (∃ λ (x : Erased B) → Erased-singleton (erased x))        ↝⟨ Σ-Erased-Erased-singleton↔ ⟩□

  B                                                         □

mutual

  -- Again the right-to-left direction of the previous lemma does not
  -- depend on the assumption of stability.

  →Σ-Erased-∥-Σ-Erased-≡-∥ :
    (A↠B : A ↠ B) →
    B →
    ∃ λ (x : Erased B) →
      ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥
  →Σ-Erased-∥-Σ-Erased-≡-∥ = _  -- Agda can infer the definition.

  _ : _↔_.from (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) x ≡
      →Σ-Erased-∥-Σ-Erased-≡-∥ A↠B x
  _ = refl _

-- In an erased context the left-to-right direction of
-- Σ-Erased-∥-Σ-Erased-≡-∥↔ returns the erased first component.

@0 to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ :
  ∀ (A↠B : A ↠ B) (s : Very-stable-≡ B) x →
  _↔_.to (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) x ≡ erased (proj₁ x)
to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ A↠B s (x , y) =
  _↔_.to (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) (x , y)  ≡⟨⟩
  proj₁ (_↔_.to (↠→↔Erased-singleton A↠B s) y)     ≡⟨ erased (proj₂ (_↔_.to (↠→↔Erased-singleton A↠B s) y)) ⟩∎
  erased x                                         ∎
