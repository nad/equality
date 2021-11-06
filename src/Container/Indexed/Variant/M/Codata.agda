------------------------------------------------------------------------
-- M-types for indexed containers, defined coinductively (in Cubical
-- Agda)
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe --guardedness #-}

import Equality.Path as P

module Container.Indexed.Variant.M.Codata
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Container.Indexed equality-with-J using (_⇾_; _∘⇾_)
open import Container.Indexed.Variant equality-with-J
  hiding (Final′≃Final′)
import Container.Indexed.Variant P.equality-with-J as PC
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J
open import H-level equality-with-J

private
  variable
    a iℓ s  : Level
    A I     : Type a
    i p q x : A
    C       : Container I s p
    n       : ℕ

-- An M-type for a given container.
--
-- This definition is similar to one in "Indexed containers" by
-- Altenkirch, Ghani, Hancock, McBride and Morris.

record M {I : Type iℓ} (C : Container I s p) (i : I) :
         Type (iℓ ⊔ s ⊔ p) where
  coinductive
  constructor in-M
  field
    out-M : ⟦ C ⟧ (M C) i

open M public

-- An η-law.

η : in-M (out-M x) ≡ x
η = _↔_.from ≡↔≡ η′
  where
  η′ : in-M (out-M x) P.≡ x
  η′ {x = x} _ .out-M = x .out-M

-- M C is, in a certain sense, a fixpoint of ⟦ C ⟧.

M-fixpoint : ⟦ C ⟧ (M C) i ≃ M C i
M-fixpoint = Eq.↔→≃ in-M out-M (λ _ → η) refl

-- A coalgebra defined using M and out-M.

M-coalgebra : (C : Container I s p) → Coalgebra C
M-coalgebra C = M C , λ _ → out-M

private

  -- M-coalgebra C is a final coalgebra.
  --
  -- This code is based on code written by Andrea Vezzosi for the
  -- cubical library.

  M-final′′ : PC.Final′ (M-coalgebra C)
  M-final′′ {C = C@(S ◁ P)} Y@(Q , f) = unfold , unique
    where
    g : Q ⇾ M C
    g i q .out-M .proj₁     = f i q .proj₁
    g i q .out-M .proj₂ j p = g j (f i q .proj₂ j p)

    g-ok : (λ _ → out-M) ∘⇾ g P.≡ map C g ∘⇾ f
    g-ok i j q .proj₁            = f j q .proj₁
    g-ok i j q .proj₂ k p .out-M = g-ok i k (f j q .proj₂ k p)

    unfold : Y PC.⇨ M-coalgebra C
    unfold = g , g-ok

    module _ (u : Y PC.⇨ M-coalgebra C) where

      lemma₁ :
        x P.≡ u .proj₁ i q →
        x .out-M .proj₁ P.≡
        (map C (u .proj₁) ∘⇾ f) i q .proj₁
      lemma₁ {i = i} {x = x} {q = q} eq =
        x .out-M .proj₁                     P.≡⟨ P.cong (λ x → x .out-M .proj₁) eq ⟩
        u .proj₁ i q .out-M .proj₁          P.≡⟨ P.cong (λ f → f i q .proj₁) (u .proj₂) ⟩∎
        (map C (u .proj₁) ∘⇾ f) i q .proj₁  ∎

      lemma₂ :
        (eq : x P.≡ u .proj₁ i q) →
        P.[ (λ l → P (lemma₁ eq l) ⇾ M C) ]
          x .out-M .proj₂ ≡
          (map C (u .proj₁) ∘⇾ f) i q .proj₂
      lemma₂ {i = i} {x = x} {q = q} eq =
        x .out-M .proj₂                     P.≡⟨ P.hcong (λ x → x .out-M .proj₂) eq ⟩[ (λ p → P p ⇾ M C) ]
        u .proj₁ i q .out-M .proj₂          P.≡⟨ P.hcong (λ f → f i q .proj₂) (u .proj₂) ⟩∎h
        (map C (u .proj₁) ∘⇾ f) i q .proj₂  ∎

      unique′ : ∀ i q x → x P.≡ u .proj₁ i q → x P.≡ g i q
      unique′ _ _ _ eq j .out-M .proj₁     = lemma₁ eq j
      unique′ i q x eq j .out-M .proj₂ k p =
        unique′ k (f i q .proj₂ k p₁) (x .out-M .proj₂ k p₀) lemma₂′ j
        where
        lem₁ = lemma₁ eq

        p₀ : P (lem₁ P.0̲) k
        p₁ : P (lem₁ P.1̲) k
        p₀ = P.transport (λ l → P (lem₁ (P.min j (P.- l))) k) (P.- j) p
        p₁ = P.transport (λ l → P (lem₁ (P.max j      l )) k)      j  p

        p₀≡p₁ : P.[ (λ l → P (lem₁ l) k) ] p₀ ≡ p₁
        p₀≡p₁ = P.elim¹
          (λ eq →
             ∀ p →
             P.[ (λ l → eq l) ]
               P.transport (λ l → eq (P.min j (P.- l))) (P.- j) p ≡
               P.transport (λ l → eq (P.max j      l ))      j  p)
          (λ p →
             P.transport (λ _ → P (x .out-M .proj₁) k) (P.- j) p  P.≡⟨ P.cong (_$ p) $ P.transport-refl (P.- j) ⟩
             p                                                    P.≡⟨ P.cong (_$ p) $ P.sym $ P.transport-refl j ⟩∎
             P.transport (λ _ → P (x .out-M .proj₁) k) j p        ∎)
          (P.cong (λ s → P s k) lem₁)
          p

        lemma₂′ :
          x .out-M .proj₂ k p₀ P.≡
          (map C (u .proj₁) ∘⇾ f) i q .proj₂ k p₁
        lemma₂′ l = lemma₂ eq l k (p₀≡p₁ l)

      unique : unfold .proj₁ P.≡ u .proj₁
      unique =
        P.⟨ext⟩ λ _ → P.⟨ext⟩ λ _ → P.sym $
        unique′ _ _ _ P.refl

  -- Finality expressed using equality is equivalent to finality
  -- expressed using paths.

  Final′≃Final′ :
    (X : Coalgebra C) →
    Final′ X ≃ PC.Final′ X
  Final′≃Final′ X =
    (∀ Y → ∃ λ (m : Y    ⇨ X) → (m′ : Y    ⇨ X) → proj₁ m ≡ proj₁ m′)    ↔⟨ (∀-cong ext λ _ →
                                                                             Σ-cong (lemma _) λ _ →
                                                                             Π-cong ext (lemma _) λ _ →
                                                                             ≡↔≡) ⟩□
    (∀ Y → ∃ λ (m : Y PC.⇨ X) → (m′ : Y PC.⇨ X) → proj₁ m P.≡ proj₁ m′)  □
    where
    lemma : ∀ Y → (Y ⇨ X) ↔ (Y PC.⇨ X)
    lemma Y = ∃-cong λ _ → ≡↔≡

-- M-coalgebra C is a final coalgebra.
--
-- The lemma M-final′′ is based on code written by Andrea Vezzosi for
-- the cubical library.

M-final′ :
  (C : Container I s p) →
  Final′ (M-coalgebra C)
M-final′ C = _≃_.from (Final′≃Final′ (M-coalgebra C)) M-final′′
