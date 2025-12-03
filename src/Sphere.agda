------------------------------------------------------------------------
-- Spheres
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe #-}

-- This module follows the HoTT book rather closely (unless otherwise
-- noted).

import Equality.Path as P

module Sphere
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Path-split equality-with-J as PS using (_-Null_)
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Nat equality-with-J as Nat
open import Pointed-type equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Suspension eq as Suspension

private
  variable
    a b : Level
    A B : Type a
    C   : Pointed-type a
    x   : A
    n   : ℕ

-- Spheres.

𝕊[_-1] : ℕ → Type
𝕊[ zero  -1] = ⊥
𝕊[ suc n -1] = Susp 𝕊[ n -1]

-- Spheres with non-negative dimensions.

𝕊 : ℕ → Type
𝕊 n = 𝕊[ 1 + n -1]

-- The booleans are isomorphic to the 0-dimensional sphere.

Bool↔𝕊⁰ : Bool ↔ 𝕊 0
Bool↔𝕊⁰ = Bool↔Susp-⊥

-- Based maps from spheres with non-negative dimensions (using north
-- as the point) are isomorphic to iterated loop spaces.

𝕊→ᴮ↔ : ∀ n → (𝕊 n , north) →ᴮ C ↔ proj₁ (Ω[ n ] C)
𝕊→ᴮ↔ {C} = lemma zero
  where
  lemma : ∀ m n → (𝕊 n , north) →ᴮ Ω[ m ] C ↔ proj₁ (Ω[ m + n ] C)
  lemma m zero =
    (𝕊 0 , north) →ᴮ Ω[ m ] C  ↝⟨ Σ-cong (→-cong ext (inverse Bool↔𝕊⁰) F.id) (λ _ → F.id) ⟩
    (Bool , true) →ᴮ Ω[ m ] C  ↝⟨ Bool→ᴮ↔ ext ⟩
    proj₁ (Ω[ m ] C)           ↝⟨ ≡⇒↝ _ $ cong (λ n → proj₁ (Ω[ n ] C)) $ sym $ Nat.+-right-identity {n = m} ⟩□
    proj₁ (Ω[ m + 0 ] C)       □

  lemma m (suc n) =
    (𝕊 (suc n) , north) →ᴮ Ω[ m ] C  ↝⟨ Susp→ᴮ↔ ⟩
    (𝕊 n , north) →ᴮ Ω[ suc m ] C    ↝⟨ lemma (suc m) n ⟩
    proj₁ (Ω[ suc m + n ] C)         ↝⟨ ≡⇒↝ _ $ cong (λ n → proj₁ (Ω[ n ] C)) $ Nat.suc+≡+suc m ⟩□
    proj₁ (Ω[ m + suc n ] C)         □

-- A corollary.

+↔∀contractible𝕊→ᴮ :
  H-level (1 + n) A ↔
  (∀ x → Contractible ((𝕊 n , north) →ᴮ (A , x)))
+↔∀contractible𝕊→ᴮ {n} {A} =
  H-level (1 + n) A                                ↔⟨ _↔_.to (Eq.⇔↔≃ ext (H-level-propositional ext _)
                                                                         (Π-closure ext 1 λ _ →
                                                                          H-level-propositional ext _))
                                                             (+⇔∀contractible-Ω[] _) ⟩
  (∀ x → Contractible (proj₁ $ Ω[ n ] (A , x)))    ↝⟨ (∀-cong ext λ _ → H-level-cong ext 0 (inverse $ 𝕊→ᴮ↔ _)) ⟩□
  (∀ x → Contractible ((𝕊 n , north) →ᴮ (A , x)))  □

-- There is an equivalence between (λ (_ : ⊤) → 𝕊[ n -1]) -Null A and
-- H-level n A.
--
-- This lemma is taken from "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

𝕊-1-Null≃H-level : ((λ (_ : ⊤) → 𝕊[ n -1]) -Null A) ≃ H-level n A
𝕊-1-Null≃H-level {n = zero} =
  PS.⊥-Null≃Contractible ext _ ext
𝕊-1-Null≃H-level {n = suc n} {A} =
  _↠_.from
    (Eq.≃↠⇔
       (PS.Null-propositional ext)
       (H-level-propositional ext (1 + n)))
    ((λ _ → 𝕊 n) -Null A                              ↝⟨ record { to = _$ _; from = const } ⟩
     Is-equivalence (const ⦂ (A → 𝕊 n → A))           ↝⟨ record { to = to; from = from } ⟩
     (∀ x → Contractible ((𝕊 n , north) →ᴮ (A , x)))  ↔⟨ inverse +↔∀contractible𝕊→ᴮ ⟩□
     H-level (1 + n) A                                □)
  where
  from = λ c →
    _≃_.is-equivalence $
    Eq.with-other-function
      (A                                                ↔⟨ (inverse $ drop-⊤-right λ x →
                                                            _⇔_.to contractible⇔↔⊤ $ c x) ⟩
       (∃ λ (x : A) → (𝕊 n , north) →ᴮ (A , x))         ↔⟨⟩
       (∃ λ (x : A) → ∃ λ (f : 𝕊 n → A) → f north ≡ x)  ↔⟨ ∃-comm ⟩
       (∃ λ (f : 𝕊 n → A) → ∃ λ (x : A) → f north ≡ x)  ↔⟨ (drop-⊤-right λ _ →
                                                            _⇔_.to contractible⇔↔⊤ $
                                                            other-singleton-contractible _) ⟩□
       (𝕊 n → A)                                        □)
      const
      (λ x → ⟨ext⟩ λ y →
         c x .proj₁ .proj₁ y  ≡⟨ cong (λ f → f .proj₁ y) $
                                 c x .proj₂ (const x , refl _) ⟩∎
         x                    ∎)

  to = λ eq x →
      (const x , refl x)
    , (λ (f , f-north≡x) → Σ-≡,≡→≡
         (⟨ext⟩ λ y →
          x                                                 ≡⟨ sym f-north≡x ⟩
          f north                                           ≡⟨ sym $ cong (_$ north) $ _≃_.right-inverse-of Eq.⟨ _ , eq ⟩ _ ⟩
          const {B = 𝕊 n} (_≃_.from Eq.⟨ _ , eq ⟩ f) north  ≡⟨⟩
          _≃_.from Eq.⟨ _ , eq ⟩ f                          ≡⟨⟩
          const {B = 𝕊 n} (_≃_.from Eq.⟨ _ , eq ⟩ f) y      ≡⟨ cong (_$ y) $ _≃_.right-inverse-of Eq.⟨ _ , eq ⟩ _ ⟩∎
          f y                                               ∎)
         (let rinv = _≃_.right-inverse-of Eq.⟨ _ , eq ⟩ f in
          subst (λ f → f north ≡ x)
            (⟨ext⟩ λ y →
             trans (sym f-north≡x)
               (trans (sym $ cong (_$ north) rinv)
                  (cong (_$ y) rinv)))
            (refl x)                                ≡⟨ subst-∘ _ _ _ ⟩

          subst (_≡ x)
            (cong (_$ north) $ ⟨ext⟩ λ y →
             trans (sym f-north≡x)
               (trans (sym $ cong (_$ north) rinv)
                  (cong (_$ y) rinv)))
            (refl x)                                ≡⟨ subst-trans-sym ⟩

          trans
            (sym $ cong (_$ north) $ ⟨ext⟩ λ y →
             trans (sym f-north≡x)
               (trans (sym $ cong (_$ north) rinv)
                  (cong (_$ y) rinv)))
            (refl x)                                ≡⟨ trans-reflʳ _ ⟩

          (sym $ cong (_$ north) $ ⟨ext⟩ λ y →
           trans (sym f-north≡x)
             (trans (sym $ cong (_$ north) rinv)
                (cong (_$ y) rinv)))                ≡⟨ cong sym $ cong-ext ext ⟩

          sym $
          trans (sym f-north≡x)
            (trans (sym $ cong (_$ north) rinv)
               (cong (_$ north) rinv))              ≡⟨ cong sym $
                                                       trans (cong (trans _) $ trans-symˡ _) $
                                                       trans-reflʳ _ ⟩

          sym (sym f-north≡x)                       ≡⟨ sym-sym _ ⟩∎

          f-north≡x                                 ∎))
