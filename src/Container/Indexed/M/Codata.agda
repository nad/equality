------------------------------------------------------------------------
-- M-types for indexed containers, defined coinductively (in Cubical
-- Agda)
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe --guardedness #-}

import Equality.Path as P

module Container.Indexed.M.Codata
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Container.Indexed equality-with-J
open import Container.Indexed.Coalgebra equality-with-J
import Container.Indexed.M.Function equality-with-J as F
import Container.Indexed.Variant equality-with-J as V
import Container.Indexed.Variant.Coalgebra equality-with-J as VC
open import Container.Indexed.Variant.M.Codata eq as VM using (out-M)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Extensionality equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Univalence-axiom equality-with-J

private
  variable
    a iℓ s p : Level
    A I      : Type a
    i x      : A
    C        : Container I s p
    n        : ℕ

------------------------------------------------------------------------
-- The M-type and some basic results

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
  η′ {x} _ .out-M = x .out-M

-- M C is, in a certain sense, a fixpoint of ⟦ C ⟧.

M-fixpoint : ⟦ C ⟧ (M C) i ≃ M C i
M-fixpoint = Eq.↔→≃ in-M out-M (λ _ → η) refl

-- A coalgebra defined using M and out-M.

M-coalgebra : (C : Container I s p) → Coalgebra C
M-coalgebra C = M C , λ _ → out-M

------------------------------------------------------------------------
-- Some conversion lemmas

-- One can convert between M and VM.M.

M≃M :
  ∀ p {I : Type i} {C : V.Container I s (i ⊔ p)} {i} →
  M (_⇔_.to (V.Container⇔Container p) C) i ≃ VM.M C i
M≃M p {C} =
  Eq.↔→≃ to from
    (λ c → _↔_.from ≡↔≡ (to-from c))
    (λ c → _↔_.from ≡↔≡ (from-to c))
  where
  to : M (_⇔_.to (V.Container⇔Container p) C) i → VM.M C i
  to x .out-M .proj₁     = x .out-M .proj₁
  to x .out-M .proj₂ i p = to (x .out-M .proj₂ (i , p))

  from : VM.M C i → M (_⇔_.to (V.Container⇔Container p) C) i
  from x .out-M .proj₁         = x .out-M .proj₁
  from x .out-M .proj₂ (i , p) = from (x .out-M .proj₂ i p)

  to-from : (x : VM.M C i) → to (from x) P.≡ x
  to-from x i .out-M .proj₁     = x .out-M .proj₁
  to-from x i .out-M .proj₂ j p = to-from (x .out-M .proj₂ j p) i

  from-to :
    (x : M (_⇔_.to (V.Container⇔Container p) C) i) →
    from (to x) P.≡ x
  from-to x i .out-M .proj₁   = x .out-M .proj₁
  from-to x i .out-M .proj₂ p = from-to (x .out-M .proj₂ p) i

-- M-coalgebra is related to VM.M-coalgebra (assuming univalence).

M-coalgebra≡M-coalgebra :
  ∀ p {I : Type i} (C : V.Container I s (i ⊔ p)) →
  Univalence (i ⊔ s ⊔ p) →
  M-coalgebra (_⇔_.to (V.Container⇔Container p) C) ≡
  _≃_.to (VC.Coalgebra≃Coalgebra p C ext) (VM.M-coalgebra C)
M-coalgebra≡M-coalgebra p C univ =
  Σ-≡,≡→≡
    (⟨ext⟩ lemma₁)
    (⟨ext⟩ λ i → ⟨ext⟩ λ x →

     subst (λ P → P ⇾ ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P)
       (⟨ext⟩ lemma₁) (λ _ → out-M) i x                                ≡⟨ cong (_$ x) $ sym $
                                                                          push-subst-application _ _ ⟩
     subst (λ P → P i → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i)
       (⟨ext⟩ lemma₁) out-M x                                          ≡⟨ subst-→ ⟩

     subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i)
       (⟨ext⟩ lemma₁)
       (subst (_$ i) (sym (⟨ext⟩ lemma₁)) x .out-M)                    ≡⟨ cong (subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i) _) $
                                                                          cong out-M $
                                                                          cong (flip (subst (_$ i)) _) $ sym $
                                                                          ext-sym {f≡g = lemma₁} ext ⟩
     subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i)
       (⟨ext⟩ lemma₁)
       (subst (_$ i) (⟨ext⟩ (sym ∘ lemma₁)) x .out-M)                  ≡⟨ cong (subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i) _) $
                                                                          cong out-M $
                                                                          subst-ext {Q = id} {f≡g = sym ∘ lemma₁} ext ⟩
     subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i)
       (⟨ext⟩ lemma₁)
       (subst id (sym (lemma₁ i)) x .out-M)                            ≡⟨ cong (subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i) _) $
                                                                          cong out-M $
                                                                          subst-id-in-terms-of-inverse∘≡⇒↝ equivalence {A≡B = lemma₁ i} ⟩
     subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i)
       (⟨ext⟩ lemma₁)
       (_≃_.from (≡⇒≃ (lemma₁ i)) x .out-M)                            ≡⟨ cong (subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i) _) $
                                                                          cong (λ (eq : M (_⇔_.to (V.Container⇔Container p) C) i ≃ VM.M C i) →
                                                                                  _≃_.from eq x .out-M) $
                                                                          _≃_.right-inverse-of (≡≃≃ univ) _ ⟩
     subst (λ P → ⟦ _⇔_.to (V.Container⇔Container p) C ⟧ P i)
       (⟨ext⟩ lemma₁)
       (_≃_.from (M≃M p {i = i}) x .out-M)                             ≡⟨⟩

     subst (λ P → ∃ λ (s : V.Shape C i) →
                    ((i , _) : ∃ (V.Position C s)) → P i)
       (⟨ext⟩ lemma₁)
       (_≃_.from (M≃M p {i = i}) x .out-M)                             ≡⟨ push-subst-pair-× _ _ ⟩

     ( x .out-M .proj₁
     , subst (λ P → ((i , _) : ∃ (V.Position C (x .out-M .proj₁))) →
                    P i)
       (⟨ext⟩ lemma₁)
       (_≃_.from (M≃M p {i = i}) x .out-M .proj₂)
     )                                                                 ≡⟨ cong (x .out-M .proj₁ ,_) $
                                                                          ⟨ext⟩ (lemma₃ i x) ⟩∎
     Σ-map id uncurry (x .out-M)                                       ∎)
  where
  lemma₁ = λ _ → ≃⇒≡ univ (M≃M p)

  lemma₂ : ∀ _ _ _ → _
  lemma₂ _ _ p =
    sym (Σ-≡,≡→≡ (sym (⟨ext⟩ lemma₁)) (refl p′))                ≡⟨ cong sym $ cong (Σ-≡,≡→≡ (sym (⟨ext⟩ lemma₁))) $ sym $
                                                                   trans-symʳ _ ⟩
    sym (Σ-≡,≡→≡ (sym (⟨ext⟩ lemma₁))
           (trans (subst-const _) (sym (subst-const _))))       ≡⟨ cong sym $ Σ-≡,≡→≡-subst-const _ _ ⟩

    sym (cong₂ _,_ (sym (⟨ext⟩ lemma₁)) (sym (subst-const _)))  ≡⟨ cong sym cong₂-sym ⟩

    sym (sym (cong₂ _,_ (⟨ext⟩ lemma₁) (subst-const _)))        ≡⟨ sym-sym _ ⟩∎

    cong₂ _,_ (⟨ext⟩ lemma₁) (subst-const _)                    ∎
    where
    p′ = subst (const _) (sym (⟨ext⟩ lemma₁)) p

  lemma₃ : ∀ _ _ _ → _
  lemma₃ i x (i′ , p′) =
    subst (λ P → ((i , _) : ∃ _) → P i)
    (⟨ext⟩ lemma₁)
    (_≃_.from (M≃M p {i = i}) x .out-M .proj₂)
    (i′ , p′)                                               ≡⟨ subst-∀ ⟩

    subst (λ ((P , i , _) : _ × ∃ _) → P i)
      (sym $ Σ-≡,≡→≡ (sym (⟨ext⟩ lemma₁)) (refl _))
      (_≃_.from (M≃M p {i = i}) x .out-M .proj₂ $
       subst (const _) (sym (⟨ext⟩ lemma₁)) (i′ , p′))      ≡⟨ cong (flip (subst (λ ((P , i , _) : _ × ∃ _) → P i)) _) $
                                                               lemma₂ i x _ ⟩
    subst (λ ((P , i , _) : _ × ∃ _) → P i)
      (cong₂ _,_ (⟨ext⟩ lemma₁) (subst-const _))
      (_≃_.from (M≃M p {i = i}) x .out-M .proj₂ $
       subst (const _) (sym (⟨ext⟩ lemma₁)) (i′ , p′))      ≡⟨ elim₁
                                                                 (λ {q} eq →
                                                                    subst (λ ((P , i , _) : _ × ∃ _) → P i)
                                                                      (cong₂ _,_ (⟨ext⟩ lemma₁) eq)
                                                                      (_≃_.from (M≃M p {i = i}) x .out-M .proj₂ q) ≡
                                                                    subst (λ ((P , i , _) : _ × ∃ (V.Position C (x .out-M .proj₁))) → P i)
                                                                      (cong₂ {u = i′ , p′} _,_ (⟨ext⟩ lemma₁) (refl _))
                                                                      (_≃_.from (M≃M p {i = i}) x .out-M .proj₂ (i′ , p′)))
                                                                 (refl _)
                                                                 _ ⟩
    subst (λ ((P , i , _) : _ × ∃ _) → P i)
      (cong₂ _,_ (⟨ext⟩ lemma₁) (refl _))
      (_≃_.from (M≃M p {i = i}) x .out-M .proj₂ (i′ , p′))  ≡⟨ cong (flip (subst (λ ((P , i , _) : _ × ∃ _) → P i)) _) $
                                                               cong₂-reflʳ _ ⟩
    subst (λ ((P , i , _) : _ × ∃ _) → P i)
      (cong (_, i′ , p′) (⟨ext⟩ lemma₁))
      (_≃_.from (M≃M p {i = i}) x .out-M .proj₂ (i′ , p′))  ≡⟨ sym $ subst-∘ _ _ _ ⟩

    subst (_$ i′) (⟨ext⟩ lemma₁)
      (_≃_.from (M≃M p {i = i}) x .out-M .proj₂ (i′ , p′))  ≡⟨ subst-ext ext ⟩

    subst id (lemma₁ i′)
      (_≃_.from (M≃M p {i = i}) x .out-M .proj₂ (i′ , p′))  ≡⟨⟩

    subst id (≃⇒≡ univ (M≃M p {i = i′}))
      (_≃_.from (M≃M p {i = i′}) (x .out-M .proj₂ i′ p′))   ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence ⟩

    _≃_.to (≡⇒≃ (≃⇒≡ univ (M≃M p {i = i′})))
      (_≃_.from (M≃M p {i = i′}) (x .out-M .proj₂ i′ p′))   ≡⟨ cong (λ eq → _≃_.to eq (_≃_.from (M≃M p {i = i′}) (x .out-M .proj₂ i′ p′))) $
                                                               _≃_.right-inverse-of (≡≃≃ univ) _ ⟩
    _≃_.to (M≃M p {i = i′})
      (_≃_.from (M≃M p {i = i′}) (x .out-M .proj₂ i′ p′))   ≡⟨ _≃_.right-inverse-of (M≃M p {i = i′}) _ ⟩

    x .out-M .proj₂ i′ p′                                   ≡⟨⟩

    Σ-map id uncurry (x .out-M) .proj₂ (i′ , p′)            ∎

------------------------------------------------------------------------
-- Lemmas related to lift-positions

-- Lifting the position type family using lift-positions does not
-- affect the resulting M type (up to pointwise equivalence).

M≃M-lift-positions : M C i ≃ M (lift-positions C) i
M≃M-lift-positions =
  Eq.↔→≃ to from
    (λ c → _↔_.from ≡↔≡ (to-from c))
    (λ c → _↔_.from ≡↔≡ (from-to c))
  where
  to : M C i → M (lift-positions C) i
  to x .out-M .proj₁          = x .out-M .proj₁
  to x .out-M .proj₂ (lift p) = to (x .out-M .proj₂ p)

  from : M (lift-positions C) i → M C i
  from x .out-M .proj₁   = x .out-M .proj₁
  from x .out-M .proj₂ p = from (x .out-M .proj₂ (lift p))

  to-from : (x : M (lift-positions C) i) → to (from x) P.≡ x
  to-from x i .out-M .proj₁   = x .out-M .proj₁
  to-from x i .out-M .proj₂ p = to-from (x .out-M .proj₂ p) i

  from-to : (x : M C i) → from (to x) P.≡ x
  from-to x i .out-M .proj₁   = x .out-M .proj₁
  from-to x i .out-M .proj₂ p = from-to (x .out-M .proj₂ p) i

-- M-coalgebra C is related to M-coalgebra (lift-positions C)
-- (assuming univalence).

≡M-coalgebra-lift-positions :
  {I : Type i} {C : Container I s p} →
  Univalence (i ⊔ s ⊔ p) →
  Coalgebra≃Coalgebra-lift-positions _ (M-coalgebra C) ≡
  M-coalgebra (lift-positions C)
≡M-coalgebra-lift-positions {C} univ =
  Σ-≡,≡→≡
    (⟨ext⟩ lemma)
    (⟨ext⟩ λ i → ⟨ext⟩ λ x →

     subst (λ P → P ⇾ ⟦ lift-positions C ⟧ P)
       (⟨ext⟩ lemma)
       ((Σ-map id (_∘ lower) ∘_) ∘ (λ _ → out-M))
       i x                                                             ≡⟨ cong (_$ x) $ sym $
                                                                          push-subst-application _ _ ⟩
     subst (λ P → P i → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma) (Σ-map id (_∘ lower) ∘ out-M) x                   ≡⟨ subst-→ ⟩

     subst (λ P → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma)
       (Σ-map id (_∘ lower) $
        subst (_$ i) (sym (⟨ext⟩ lemma)) x .out-M)                     ≡⟨ cong (subst (λ P → ⟦ lift-positions C ⟧ P i) _) $
                                                                          cong (Σ-map id (_∘ lower)) $ cong out-M $
                                                                          cong (flip (subst (_$ i)) _) $ sym $
                                                                          ext-sym {f≡g = lemma} ext ⟩
     subst (λ P → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma)
       (Σ-map id (_∘ lower) $
        subst (_$ i) (⟨ext⟩ (sym ∘ lemma)) x .out-M)                   ≡⟨ cong (subst (λ P → ⟦ lift-positions C ⟧ P i) _) $
                                                                          cong (Σ-map id (_∘ lower)) $ cong out-M $
                                                                          subst-ext {Q = id} {f≡g = sym ∘ lemma} ext ⟩
     subst (λ P → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma)
       (Σ-map id (_∘ lower) $
        subst id (sym (lemma i)) x .out-M)                             ≡⟨ cong (subst (λ P → ⟦ lift-positions C ⟧ P i) _) $
                                                                          cong (Σ-map id (_∘ lower)) $ cong out-M $
                                                                          subst-id-in-terms-of-inverse∘≡⇒↝ equivalence {A≡B = lemma i} ⟩
     subst (λ P → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma)
       (Σ-map id (_∘ lower) $
        _≃_.from (≡⇒≃ (lemma i)) x .out-M)                             ≡⟨ cong (subst (λ P → ⟦ lift-positions C ⟧ P i) _) $
                                                                          cong (λ (eq : M C i ≃ M (lift-positions C) i) →
                                                                                  Σ-map id (_∘ lower) (_≃_.from eq x .out-M)) $
                                                                          _≃_.right-inverse-of (≡≃≃ univ) _ ⟩
     subst (λ P → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma)
       (Σ-map id (_∘ lower) $
        _≃_.from M≃M-lift-positions x .out-M)                          ≡⟨⟩

     subst (λ P → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma)
       ( x .out-M .proj₁
       , _≃_.from M≃M-lift-positions ∘ x .out-M .proj₂
       )                                                               ≡⟨ (cong (subst (λ P → ⟦ lift-positions C ⟧ P i) _) $ cong (_ ,_) $
                                                                           ⟨ext⟩ λ p →
                                                                           cong (λ eq → _≃_.from eq (x .out-M .proj₂ p)) $ sym $
                                                                           _≃_.right-inverse-of (≡≃≃ univ) _) ⟩
     subst (λ P → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma)
       ( x .out-M .proj₁
       , _≃_.from (≡⇒≃ (lemma _)) ∘ x .out-M .proj₂
       )                                                               ≡⟨ (cong (subst (λ P → ⟦ lift-positions C ⟧ P i) _) $ cong (_ ,_) $
                                                                           ⟨ext⟩ λ p →
                                                                           cong (λ (f : ∀ i → M C i ≡ M (lift-positions C) i) →
                                                                                   _≃_.from (≡⇒≃ (f _)) (x .out-M .proj₂ p)) $ sym $
                                                                           _≃_.left-inverse-of Π≡≃≡ _) ⟩
     subst (λ P → ⟦ lift-positions C ⟧ P i)
       (⟨ext⟩ lemma)
       ( x .out-M .proj₁
       , _≃_.from (≡⇒≃ (ext⁻¹ (⟨ext⟩ lemma) _)) ∘ x .out-M .proj₂
       )                                                               ≡⟨ elim₁
                                                                            (λ eq →
                                                                               subst (λ P → ⟦ lift-positions C ⟧ P i)
                                                                                 eq
                                                                                 ( x .out-M .proj₁
                                                                                 , _≃_.from (≡⇒≃ (ext⁻¹ eq _)) ∘ x .out-M .proj₂
                                                                                 ) ≡
                                                                               x .out-M)
                                                                            (
         subst (λ P → ⟦ lift-positions C ⟧ P i)
           (refl _)
           ( x .out-M .proj₁
           , _≃_.from (≡⇒≃ (ext⁻¹ (refl (M (lift-positions C))) _)) ∘
             x .out-M .proj₂
           )                                                                 ≡⟨ subst-refl _ _ ⟩

           x .out-M .proj₁
         , _≃_.from (≡⇒≃ (ext⁻¹ (refl (M (lift-positions C))) _)) ∘
           x .out-M .proj₂                                                   ≡⟨ (cong (_ ,_) $ ⟨ext⟩ λ p →
                                                                                 cong (λ eq → _≃_.from eq (x .out-M .proj₂ p)) $
                                                                                 trans (cong ≡⇒≃ $ ext⁻¹-refl (M (lift-positions C))) $
                                                                                 ≡⇒↝-refl) ⟩∎
         x .out-M                                                            ∎)
                                                                            (⟨ext⟩ lemma) ⟩∎
     x .out-M                                                          ∎)
  where
  lemma = λ _ → ≃⇒≡ univ M≃M-lift-positions

------------------------------------------------------------------------
-- Finality

private

  -- M-coalgebra C is sometimes a final coalgebra (assuming
  -- univalence). Note that the last index argument of C is not
  -- unrestricted.

  M-final′ :
    ∀ p {I : Type i} {C : Container I s (i ⊔ p)} →
    Univalence (i ⊔ s ⊔ p) →
    Univalence (i ⊔ p) →
    Final′ (M-coalgebra C)
  M-final′ p {C} univ₁ univ₂ =                                        $⟨ VM.M-final′ C′ ⟩
    VC.Final′ (VM.M-coalgebra C′)                                     ↝⟨ subst VC.Final′ $ sym $ _≃_.to-from C≃C $ sym $
                                                                         M-coalgebra≡M-coalgebra p C′ univ₁ ⟩
    VC.Final′ (_≃_.from C≃C (M-coalgebra (_⇔_.to C⇔C C′)))            ↔⟨ VC.Final′≃Final′ p C′ ext ext
                                                                           (_≃_.from C≃C (M-coalgebra (_⇔_.to C⇔C C′))) ⟩
    Final′ (_≃_.to C≃C $ _≃_.from C≃C $ M-coalgebra (_⇔_.to C⇔C C′))  ↝⟨ subst Final′ (_≃_.right-inverse-of C≃C (M-coalgebra (_⇔_.to C⇔C C′))) ⟩
    Final′ (M-coalgebra (_⇔_.to C⇔C C′))                              ↝⟨ subst (Final′ ∘ M-coalgebra) $
                                                                         _≃_.right-inverse-of (V.Container≃Container p ext univ₂) _ ⟩□
    Final′ (M-coalgebra C)                                            □
    where
    C⇔C = V.Container⇔Container p
    C′  = _⇔_.from C⇔C C
    C≃C = VC.Coalgebra≃Coalgebra p C′ ext

  -- M-coalgebra C is sometimes a final coalgebra (assuming univalence).
  -- Note that the last index argument of C is not unrestricted.

  M-final″ :
    ∀ p {I : Type i} {C : Container I s (i ⊔ p)} →
    Univalence (i ⊔ s ⊔ p) →
    Univalence (i ⊔ p) →
    Final (M-coalgebra C)
  M-final″ p {C} univ₁ univ₂ =
    block λ b →
    Final′→Final
      ext
      ( F.M-coalgebra b ext C
      , F.M-final b ext ext
      )
      ( M-coalgebra C
      , M-final′ p univ₁ univ₂
      )

-- M-coalgebra C is a final coalgebra (assuming univalence).
--
-- TODO: Can this be proved directly, without using VM.M-final′ or
-- univalence?

M-final :
  {I : Type i} {C : Container I s p} →
  Univalence (i ⊔ s ⊔ p) →
  Univalence (i ⊔ p) →
  Final (M-coalgebra C)
M-final {p} {C} univ₁ univ₂ =                                $⟨ M-final″ p univ₁ univ₂ ⟩
  Final (M-coalgebra (lift-positions C))                     ↔⟨⟩

  (∀ Y → Contractible (Y ⇨ M-coalgebra (lift-positions C)))  ↝⟨ (Π-cong-contra-→ (Coalgebra≃Coalgebra-lift-positions _) λ Y →
                                                                 H-level-cong _ 0 (
      Coalgebra≃Coalgebra-lift-positions _ Y ⇨
      M-coalgebra (lift-positions C)                               ↝⟨ ≡⇒↝ _ $ cong (Coalgebra≃Coalgebra-lift-positions _ Y ⇨_) $ sym $
                                                                      ≡M-coalgebra-lift-positions univ₁ ⟩
      Coalgebra≃Coalgebra-lift-positions _ Y ⇨
      Coalgebra≃Coalgebra-lift-positions _ (M-coalgebra C)         ↝⟨ inverse $ ⇨≃⇨-lift-positions ext _ (M-coalgebra C) ⟩□

      Y ⇨ M-coalgebra C                                            □)) ⟩

  (∀ Y → Contractible (Y ⇨ M-coalgebra C))                   ↔⟨⟩

  Final (M-coalgebra C)                                      □

------------------------------------------------------------------------
-- H-levels

-- If the shape types of C have h-level n, then M C i has h-level n
-- (assuming univalence).

H-level-M :
  {I : Type i} {C : Container I s p} →
  Univalence (i ⊔ s ⊔ p) →
  Univalence (i ⊔ p) →
  (∀ i → H-level n (Shape C i)) →
  ∀ {i} → H-level n (M C i)
H-level-M {C} univ₁ univ₂ h =
  F.H-level-final-coalgebra
    ext
    (M-coalgebra C , M-final univ₁ univ₂)
    h
