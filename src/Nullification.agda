------------------------------------------------------------------------
-- Nullification
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- Partly based on "Modalities in Homotopy Type Theory" by Rijke,
-- Shulman and Spitters.

import Equality.Path as P

module Nullification
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude as P

open import Equality.Path.Isomorphisms eq as I hiding (ext)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Path-split equality-with-J using (_-Null_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level.Closure equality-with-J
open import Localisation eq
import Pushout eq as PO
open import Surjection equality-with-J using (_↠_)
open import Suspension eq as Susp using (Susp)

private
  variable
    a a₁ a₂ p : Level
    A B       : Type a
    P         : A → Type p
    y         : A

------------------------------------------------------------------------
-- Nullification

-- The function _-Null_ can be expressed using _-Local_.

Null≃Local : P -Null B ≃ (λ x (_ : P x) → tt) -Local B
Null≃Local {P = P} {B = B} =
  P -Null B                                                ↔⟨⟩
  (∀ x → Is-equivalence (const ⦂ (B → P x → B)))           ↝⟨ (∀-cong I.ext λ _ →
                                                               Is-equivalence≃Is-equivalence-∘ʳ
                                                                 (_≃_.is-equivalence $ Eq.↔⇒≃ Π-left-identity) I.ext) ⟩
  (∀ x → Is-equivalence (λ (g : ⊤ → B) (_ : P x) → g tt))  ↔⟨⟩
  (λ x (_ : P x) → tt) -Local B                            □

-- Nullification.

Nullification : {A : Type a} → (A → Type a) → Type a → Type a
Nullification {A = A} P =
  Localisation′ {A = A ⊎ A} {P = P.[ P , Susp ∘ P ]} {Q = λ _ → ⊤} _

-- Nullification is a special case of localisation.

Nullification≃Localisation :
  Nullification P B ≃
  Localisation {P = P} {Q = λ _ → ⊤} _ B
Nullification≃Localisation {P = P} {B = B} =

  -- The proof is quite repetitive: to and from are rather similar, as
  -- are the two round-trip proofs. Perhaps it would make sense to
  -- prove something like Localisation′-cong (for a fixed "A"), and
  -- use that to prove this lemma.

  Eq.↔→≃ to from
    (elim λ where
       .[]ʳ → refl ∘ [_]

       .extʳ {x = inj₁ x} {g = f} hyp _ →
         to (from (ext (inj₁ x) f _))    ≡⟨⟩
         ext (inj₁ x) (to ∘ from ∘ f) _  ≡⟨ cong (flip (ext _) _) $ ⟨ext⟩ hyp ⟩∎
         ext (inj₁ x) f _                ∎

       .extʳ {x = inj₂ x} {g = f} hyp _ →
         to (from (ext (inj₂ x) f _))                                     ≡⟨⟩

         ext (inj₂ x)
           (to ∘ from ∘ f ∘ _≃_.from PO.Susp≃Susp ∘ _≃_.to PO.Susp≃Susp)
           _                                                              ≡⟨ (cong (flip (ext _) _) $ ⟨ext⟩ λ y → cong (to ∘ from ∘ f) $
                                                                              _≃_.left-inverse-of PO.Susp≃Susp y) ⟩

         ext (inj₂ x) (to ∘ from ∘ f) _                                   ≡⟨ cong (flip (ext _) _) $ ⟨ext⟩ hyp ⟩∎

         ext (inj₂ x) f _                                                 ∎

       .ext≡ʳ {x = inj₁ x} {g = f} {y = y} hyp →
         subst (λ x → to (from x) ≡ x)
           (ext≡ {x = inj₁ x} {y = y} {g = f})
           (cong (flip (ext _) _) $ ⟨ext⟩ hyp)                    ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans
           (sym $ cong (to ∘ from) $
            ext≡ {x = inj₁ x} {y = y} {g = f})
           (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
              (cong id (ext≡ {x = inj₁ x} {y = y} {g = f})))      ≡⟨ cong₂ (trans ∘ sym)
                                                                       (sym $ cong-∘ _ _ _)
                                                                       (cong (trans _) $ sym $ cong-id _) ⟩
         trans
           (sym $ cong to $ cong from $
            ext≡ {x = inj₁ x} {y = y} {g = f})
           (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
              (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ cong (flip trans _) $ cong sym $
                                                                     trans (cong (cong to) $ rec-ext≡ {r = from′}) $
                                                                     rec-ext≡ {r = to′} ⟩
         trans
           (sym $ ext≡ {x = inj₁ x} {y = y} {g = to ∘ from ∘ f})
           (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
              (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ elim₁
                                                                       (λ {g} eq →
                                                                          trans
                                                                            (sym $ ext≡ {x = inj₁ x} {y = y} {g = g})
                                                                            (trans (cong (flip (ext _) _) eq)
                                                                               (ext≡ {x = inj₁ x} {y = y} {g = f})) ≡
                                                                          ext⁻¹ eq y)
                                                                       (
           trans (sym ext≡)
             (trans (cong (flip (ext _) _) (refl f)) ext≡)              ≡⟨ cong (trans _) $
                                                                           trans (cong (flip trans _) $ cong-refl _) $
                                                                           trans-reflˡ _ ⟩

           trans (sym ext≡) ext≡                                        ≡⟨ trans-symˡ _ ⟩

           refl (f y)                                                   ≡⟨ sym $ ext⁻¹-refl _ ⟩∎

           ext⁻¹ (refl f) y                                             ∎)
                                                                       _ ⟩

         ext⁻¹ (⟨ext⟩ hyp) y                                      ≡⟨ cong-ext _ ⟩∎

         hyp y                                                    ∎

       .ext≡ʳ {x = inj₂ x} {g = f} {y = y} hyp →
         subst (λ x → to (from x) ≡ x)
           (ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (cong (flip (ext _) _) $
               ⟨ext⟩ λ y → cong (to ∘ from ∘ f) $
               _≃_.left-inverse-of PO.Susp≃Susp y)
              (cong (flip (ext _) _) $ ⟨ext⟩ hyp))                        ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans
           (sym $ cong (to ∘ from) $
            ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (cong id (ext≡ {x = inj₂ x} {y = y} {g = f})))              ≡⟨ cong₂ (trans ∘ sym)
                                                                               (sym $ cong-∘ _ _ _)
                                                                               (cong (trans _) $ sym $ cong-id _) ⟩
         trans
           (sym $ cong to $ cong from $
            ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = inj₂ x} {y = y} {g = f}))                        ≡⟨ cong (flip trans _) $ cong (sym ∘ cong to) $
                                                                             rec-ext≡ {r = from′} ⟩
         trans
           (sym $ cong to $
            trans
              (ext≡ {x = inj₂ x} {y = _≃_.to PO.Susp≃Susp y}
                 {g = from ∘ f ∘ _≃_.from PO.Susp≃Susp})
              (cong (from ∘ f) $ _≃_.left-inverse-of PO.Susp≃Susp y))
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = inj₂ x} {y = y} {g = f}))                        ≡⟨ cong (flip trans _) $ cong sym $
                                                                             trans (cong-trans _ _ _) $
                                                                             cong (trans _) $ cong-∘ _ _ _ ⟩
         trans
           (sym $
            trans
              (cong to $
               ext≡ {x = inj₂ x} {y = _≃_.to PO.Susp≃Susp y}
                 {g = from ∘ f ∘ _≃_.from PO.Susp≃Susp})
              (cong (to ∘ from ∘ f) $
               _≃_.left-inverse-of PO.Susp≃Susp y))
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = inj₂ x} {y = y} {g = f}))                        ≡⟨ cong (flip trans _) $ cong sym $ cong (flip trans _) $
                                                                             rec-ext≡ {r = to′} ⟩
         trans
           (sym $
            trans
              (trans
                 (ext≡ {x = inj₂ x}
                    {y = _≃_.from PO.Susp≃Susp (_≃_.to PO.Susp≃Susp y)}
                    {g = to ∘ from ∘ f ∘
                         _≃_.from PO.Susp≃Susp ∘ _≃_.to PO.Susp≃Susp})
                 (cong (to ∘ from ∘ f ∘ _≃_.from PO.Susp≃Susp) $
                  _≃_.right-inverse-of PO.Susp≃Susp
                    (_≃_.to PO.Susp≃Susp y)))
              (cong (to ∘ from ∘ f) $
               _≃_.left-inverse-of PO.Susp≃Susp y))
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = inj₂ x} {y = y} {g = f}))                        ≡⟨ trans (cong (flip trans _) $ cong sym $
                                                                                    cong (flip trans _) $ cong (trans _) $
                                                                                    trans (sym $ cong-∘ _ _ _) $
                                                                                    cong (cong (to ∘ from ∘ f)) $
                                                                                    _≃_.right-left-lemma PO.Susp≃Susp _) $
                                                                             cong₂ trans
                                                                               (cong sym $
                                                                                cong₂ trans
                                                                                  (cong (trans _) $ cong (cong _) left-lemma)
                                                                                  (cong (cong _) left-lemma))
                                                                               (cong (flip trans _) $ cong (flip trans _) $
                                                                                cong (cong _) $ cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                                                cong (cong _) left-lemma) ⟩
         (let eq = ⟨ext⟩ (_≃_.left-inverse-of PO.Susp≃Susp) in
          trans
            (sym $
             trans
               (trans
                  (ext≡ {x = inj₂ x}
                     {y = _≃_.from PO.Susp≃Susp (_≃_.to PO.Susp≃Susp y)}
                     {g = to ∘ from ∘ f ∘
                          _≃_.from PO.Susp≃Susp ∘ _≃_.to PO.Susp≃Susp})
                  (cong (to ∘ from ∘ f) $
                   ext⁻¹ eq
                     (_≃_.from PO.Susp≃Susp (_≃_.to PO.Susp≃Susp y))))
               (cong (to ∘ from ∘ f) $ ext⁻¹ eq y))
            (trans
               (trans
                  (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                   cong (to ∘ from ∘ f) $ ext⁻¹ eq y)
                  (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
               (ext≡ {x = inj₂ x} {y = y} {g = f})))                      ≡⟨ elim₁
                                                                               (λ {g} eq →
                                                                                  trans
                                                                                    (sym $
                                                                                     trans
                                                                                       (trans
                                                                                          (ext≡ {x = inj₂ x} {y = g y} {g = to ∘ from ∘ f ∘ g})
                                                                                          (cong (to ∘ from ∘ f) $ ext⁻¹ eq (g y)))
                                                                                       (cong (to ∘ from ∘ f) $ ext⁻¹ eq y))
                                                                                    (trans
                                                                                       (trans
                                                                                          (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                                                                                           cong (to ∘ from ∘ f) $ ext⁻¹ eq y)
                                                                                          (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
                                                                                       (ext≡ {x = inj₂ x} {y = y} {g = f})) ≡
                                                                                  hyp y)
                                                                               (
           trans
             (sym $
              trans
                (trans
                   (ext≡ {x = inj₂ x} {y = y} {g = to ∘ from ∘ f})
                   (cong (to ∘ from ∘ f) $ ext⁻¹ (refl id) y))
                (cong (to ∘ from ∘ f) $ ext⁻¹ (refl id) y))
             (trans
                (trans
                   (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                    cong (to ∘ from ∘ f) $ ext⁻¹ (refl id) y)
                   (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
                (ext≡ {x = inj₂ x} {y = y} {g = f}))                            ≡⟨ cong₂ trans
                                                                                     (cong sym $
                                                                                      trans (cong₂ trans
                                                                                               (trans (cong (trans _) $
                                                                                                       trans (cong (cong _) $ ext⁻¹-refl _) $
                                                                                                       cong-refl _) $
                                                                                                trans-reflʳ _)
                                                                                               (trans (cong (cong _) $ ext⁻¹-refl _) $
                                                                                                cong-refl _)) $
                                                                                      trans-reflʳ _)
                                                                                     (cong (flip trans _) $
                                                                                      trans (cong (flip trans _) $
                                                                                             trans (cong (cong _) $
                                                                                                    trans (cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                                                                           trans (cong (cong _) $ ext⁻¹-refl _) $
                                                                                                           cong-refl _)
                                                                                                    ext-refl) $
                                                                                             cong-refl _) $
                                                                                      trans-reflˡ _) ⟩
           trans
             (sym $ ext≡ {x = inj₂ x} {y = y} {g = to ∘ from ∘ f})
             (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
                (ext≡ {x = inj₂ x} {y = y} {g = f}))                            ≡⟨ elim₁
                                                                                     (λ {g} eq →
                                                                                      trans
                                                                                        (sym $ ext≡ {x = inj₂ x} {y = y} {g = g})
                                                                                        (trans (cong (flip (ext _) _) eq)
                                                                                           (ext≡ {x = inj₂ x} {y = y} {g = f})) ≡
                                                                                      ext⁻¹ eq y)
                                                                                     (trans (cong (trans _) $
                                                                                             trans (cong (flip trans _) $ cong-refl _) $
                                                                                             trans-reflˡ _) $
                                                                                      trans (trans-symˡ _) $
                                                                                      sym $ ext⁻¹-refl _)
                                                                                     _ ⟩

           ext⁻¹ (⟨ext⟩ hyp) y                                                  ≡⟨ cong-ext _ ⟩∎

           hyp y                                                                ∎)
                                                                               _ ⟩∎
         hyp y                                                            ∎)
    (elim λ where
       .[]ʳ → refl ∘ [_]

       .extʳ {x = inj₁ x} {g = f} hyp _ →
         from (to (ext (inj₁ x) f _))    ≡⟨⟩
         ext (inj₁ x) (from ∘ to ∘ f) _  ≡⟨ cong (flip (ext _) _) $ ⟨ext⟩ hyp ⟩∎
         ext (inj₁ x) f _                ∎

       .extʳ {x = inj₂ x} {g = f} hyp _ →
         from (to (ext (inj₂ x) f _))                                     ≡⟨⟩

         ext (inj₂ x)
           (from ∘ to ∘ f ∘ _≃_.to PO.Susp≃Susp ∘ _≃_.from PO.Susp≃Susp)
           _                                                              ≡⟨ (cong (flip (ext _) _) $ ⟨ext⟩ λ y → cong (from ∘ to ∘ f) $
                                                                              _≃_.right-inverse-of PO.Susp≃Susp y) ⟩

         ext (inj₂ x) (from ∘ to ∘ f) _                                   ≡⟨ cong (flip (ext _) _) $ ⟨ext⟩ hyp ⟩∎

         ext (inj₂ x) f _                                                 ∎

       .ext≡ʳ {x = inj₁ x} {g = f} {y = y} hyp →
         subst (λ x → from (to x) ≡ x)
           (ext≡ {x = inj₁ x} {y = y} {g = f})
           (cong (flip (ext _) _) $ ⟨ext⟩ hyp)                    ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans
           (sym $ cong (from ∘ to) $
            ext≡ {x = inj₁ x} {y = y} {g = f})
           (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
              (cong id (ext≡ {x = inj₁ x} {y = y} {g = f})))      ≡⟨ cong₂ (trans ∘ sym)
                                                                       (sym $ cong-∘ _ _ _)
                                                                       (cong (trans _) $ sym $ cong-id _) ⟩
         trans
           (sym $ cong from $ cong to $
            ext≡ {x = inj₁ x} {y = y} {g = f})
           (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
              (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ cong (flip trans _) $ cong sym $
                                                                     trans (cong (cong from) $ rec-ext≡ {r = to′}) $
                                                                     rec-ext≡ {r = from′} ⟩
         trans
           (sym $ ext≡ {x = inj₁ x} {y = y} {g = from ∘ to ∘ f})
           (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
              (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ elim₁
                                                                       (λ {g} eq →
                                                                          trans
                                                                            (sym $ ext≡ {x = inj₁ x} {y = y} {g = g})
                                                                            (trans (cong (flip (ext _) _) eq)
                                                                               (ext≡ {x = inj₁ x} {y = y} {g = f})) ≡
                                                                          ext⁻¹ eq y)
                                                                       (
           trans (sym ext≡)
             (trans (cong (flip (ext _) _) (refl f)) ext≡)              ≡⟨ cong (trans _) $
                                                                           trans (cong (flip trans _) $ cong-refl _) $
                                                                           trans-reflˡ _ ⟩

           trans (sym ext≡) ext≡                                        ≡⟨ trans-symˡ _ ⟩

           refl (f y)                                                   ≡⟨ sym $ ext⁻¹-refl _ ⟩∎

           ext⁻¹ (refl f) y                                             ∎)
                                                                       _ ⟩

         ext⁻¹ (⟨ext⟩ hyp) y                                      ≡⟨ cong-ext _ ⟩∎

         hyp y                                                    ∎

       .ext≡ʳ {x = inj₂ x} {g = f} {y = y} hyp →
         subst (λ x → from (to x) ≡ x)
           (ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (cong (flip (ext _) _) $
               ⟨ext⟩ λ y → cong (from ∘ to ∘ f) $
               _≃_.right-inverse-of PO.Susp≃Susp y)
              (cong (flip (ext _) _) $ ⟨ext⟩ hyp))                        ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans
           (sym $ cong (from ∘ to) $
            ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (cong id (ext≡ {x = inj₂ x} {y = y} {g = f})))              ≡⟨ cong₂ (trans ∘ sym)
                                                                               (sym $ cong-∘ _ _ _)
                                                                               (cong (trans _) $ sym $ cong-id _) ⟩
         trans
           (sym $ cong from $ cong to $
            ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = inj₂ x} {y = y} {g = f}))                        ≡⟨ cong (flip trans _) $ cong (sym ∘ cong from) $
                                                                             rec-ext≡ {r = to′} ⟩
         trans
           (sym $ cong from $
            trans
              (ext≡ {x = inj₂ x} {y = _≃_.from PO.Susp≃Susp y}
                 {g = to ∘ f ∘ _≃_.to PO.Susp≃Susp})
              (cong (to ∘ f) $ _≃_.right-inverse-of PO.Susp≃Susp y))
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = inj₂ x} {y = y} {g = f}))                        ≡⟨ cong (flip trans _) $ cong sym $
                                                                             trans (cong-trans _ _ _) $
                                                                             cong (trans _) $ cong-∘ _ _ _ ⟩
         trans
           (sym $
            trans
              (cong from $
               ext≡ {x = inj₂ x} {y = _≃_.from PO.Susp≃Susp y}
                 {g = to ∘ f ∘ _≃_.to PO.Susp≃Susp})
              (cong (from ∘ to ∘ f) $
               _≃_.right-inverse-of PO.Susp≃Susp y))
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = inj₂ x} {y = y} {g = f}))                        ≡⟨ cong (flip trans _) $ cong sym $ cong (flip trans _) $
                                                                             rec-ext≡ {r = from′} ⟩
         trans
           (sym $
            trans
              (trans
                 (ext≡ {x = inj₂ x}
                    {y = _≃_.to PO.Susp≃Susp (_≃_.from PO.Susp≃Susp y)}
                    {g = from ∘ to ∘ f ∘
                         _≃_.to PO.Susp≃Susp ∘ _≃_.from PO.Susp≃Susp})
                 (cong (from ∘ to ∘ f ∘ _≃_.to PO.Susp≃Susp) $
                  _≃_.left-inverse-of PO.Susp≃Susp
                    (_≃_.from PO.Susp≃Susp y)))
              (cong (from ∘ to ∘ f) $
               _≃_.right-inverse-of PO.Susp≃Susp y))
           (trans
              (trans
                 (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = inj₂ x} {y = y} {g = f}))                        ≡⟨ trans (cong (flip trans _) $ cong sym $
                                                                                    cong (flip trans _) $ cong (trans _) $
                                                                                    trans (sym $ cong-∘ _ _ _) $
                                                                                    cong (cong (from ∘ to ∘ f)) $
                                                                                    _≃_.left-right-lemma PO.Susp≃Susp _) $
                                                                             cong₂ trans
                                                                               (cong sym $
                                                                                cong₂ trans
                                                                                  (cong (trans _) $ cong (cong _) right-lemma)
                                                                                  (cong (cong _) right-lemma))
                                                                               (cong (flip trans _) $ cong (flip trans _) $
                                                                                cong (cong _) $ cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                                                cong (cong _) right-lemma) ⟩
         (let eq = ⟨ext⟩ (_≃_.right-inverse-of PO.Susp≃Susp) in
          trans
            (sym $
             trans
               (trans
                  (ext≡ {x = inj₂ x}
                     {y = _≃_.to PO.Susp≃Susp (_≃_.from PO.Susp≃Susp y)}
                     {g = from ∘ to ∘ f ∘
                          _≃_.to PO.Susp≃Susp ∘ _≃_.from PO.Susp≃Susp})
                  (cong (from ∘ to ∘ f) $
                   ext⁻¹ eq
                     (_≃_.to PO.Susp≃Susp (_≃_.from PO.Susp≃Susp y))))
               (cong (from ∘ to ∘ f) $ ext⁻¹ eq y))
            (trans
               (trans
                  (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                   cong (from ∘ to ∘ f) $ ext⁻¹ eq y)
                  (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
               (ext≡ {x = inj₂ x} {y = y} {g = f})))                      ≡⟨ elim₁
                                                                               (λ {g} eq →
                                                                                  trans
                                                                                    (sym $
                                                                                     trans
                                                                                       (trans
                                                                                          (ext≡ {x = inj₂ x} {y = g y} {g = from ∘ to ∘ f ∘ g})
                                                                                          (cong (from ∘ to ∘ f) $ ext⁻¹ eq (g y)))
                                                                                       (cong (from ∘ to ∘ f) $ ext⁻¹ eq y))
                                                                                    (trans
                                                                                       (trans
                                                                                          (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                                                                                           cong (from ∘ to ∘ f) $ ext⁻¹ eq y)
                                                                                          (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
                                                                                       (ext≡ {x = inj₂ x} {y = y} {g = f})) ≡
                                                                                  hyp y)
                                                                               (
           trans
             (sym $
              trans
                (trans
                   (ext≡ {x = inj₂ x} {y = y} {g = from ∘ to ∘ f})
                   (cong (from ∘ to ∘ f) $ ext⁻¹ (refl id) y))
                (cong (from ∘ to ∘ f) $ ext⁻¹ (refl id) y))
             (trans
                (trans
                   (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
                    cong (from ∘ to ∘ f) $ ext⁻¹ (refl id) y)
                   (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
                (ext≡ {x = inj₂ x} {y = y} {g = f}))                            ≡⟨ cong₂ trans
                                                                                     (cong sym $
                                                                                      trans (cong₂ trans
                                                                                               (trans (cong (trans _) $
                                                                                                       trans (cong (cong _) $ ext⁻¹-refl _) $
                                                                                                       cong-refl _) $
                                                                                                trans-reflʳ _)
                                                                                               (trans (cong (cong _) $ ext⁻¹-refl _) $
                                                                                                cong-refl _)) $
                                                                                      trans-reflʳ _)
                                                                                     (cong (flip trans _) $
                                                                                      trans (cong (flip trans _) $
                                                                                             trans (cong (cong _) $
                                                                                                    trans (cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                                                                           trans (cong (cong _) $ ext⁻¹-refl _) $
                                                                                                           cong-refl _)
                                                                                                    ext-refl) $
                                                                                             cong-refl _) $
                                                                                      trans-reflˡ _) ⟩
           trans
             (sym $ ext≡ {x = inj₂ x} {y = y} {g = from ∘ to ∘ f})
             (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
                (ext≡ {x = inj₂ x} {y = y} {g = f}))                            ≡⟨ elim₁
                                                                                     (λ {g} eq →
                                                                                      trans
                                                                                        (sym $ ext≡ {x = inj₂ x} {y = y} {g = g})
                                                                                        (trans (cong (flip (ext _) _) eq)
                                                                                           (ext≡ {x = inj₂ x} {y = y} {g = f})) ≡
                                                                                      ext⁻¹ eq y)
                                                                                     (trans (cong (trans _) $
                                                                                             trans (cong (flip trans _) $ cong-refl _) $
                                                                                             trans-reflˡ _) $
                                                                                      trans (trans-symˡ _) $
                                                                                      sym $ ext⁻¹-refl _)
                                                                                     _ ⟩

           ext⁻¹ (⟨ext⟩ hyp) y                                                  ≡⟨ cong-ext _ ⟩∎

           hyp y                                                                ∎)
                                                                               _ ⟩∎
         hyp y                                                            ∎)
  where
  to′ = λ where
    .[]ʳ → [_]

    .extʳ {x = inj₁ x} f _ → ext (inj₁ x) (f ∘ lower) _

    .extʳ {x = inj₂ x} f _ → ext (inj₂ x) (f ∘ _≃_.to PO.Susp≃Susp) _

    .ext≡ʳ {x = inj₁ x} {y = y} f →
      ext (inj₁ x) (f ∘ lower) _  ≡⟨ ext≡ {x = inj₁ x} {y = lift y} {g = f ∘ lower} ⟩∎
      f y                         ∎

    .ext≡ʳ {x = inj₂ x} {y = y} f →
      ext (inj₂ x) (f ∘ _≃_.to PO.Susp≃Susp) _           ≡⟨ ext≡ {x = inj₂ x} {y = _≃_.from PO.Susp≃Susp y} {g = f ∘ _≃_.to PO.Susp≃Susp} ⟩
      f (_≃_.to PO.Susp≃Susp (_≃_.from PO.Susp≃Susp y))  ≡⟨ cong f $ _≃_.right-inverse-of PO.Susp≃Susp y ⟩∎
      f y                                                ∎

  from′ = λ where
    .[]ʳ → [_]

    .extʳ {x = inj₁ x} f _ → ext (inj₁ x) (f ∘ lift) _

    .extʳ {x = inj₂ x} f _ → ext (inj₂ x) (f ∘ _≃_.from PO.Susp≃Susp) _

    .ext≡ʳ {x = inj₁ x} {y = y} f →
      ext (inj₁ x) (f ∘ lift) _  ≡⟨ ext≡ {x = inj₁ x} {y = lower y} {g = f ∘ lift} ⟩∎
      f y                        ∎

    .ext≡ʳ {x = inj₂ x} {y = y} f →
      ext (inj₂ x) (f ∘ _≃_.from PO.Susp≃Susp) _         ≡⟨ ext≡ {x = inj₂ x} {y = _≃_.to PO.Susp≃Susp y} {g = f ∘ _≃_.from PO.Susp≃Susp} ⟩
      f (_≃_.from PO.Susp≃Susp (_≃_.to PO.Susp≃Susp y))  ≡⟨ cong f $ _≃_.left-inverse-of PO.Susp≃Susp y ⟩∎
      f y                                                ∎

  to : Nullification P B → Localisation {P = P} {Q = λ _ → ⊤} _ B
  to = rec to′

  from : Localisation {P = P} {Q = λ _ → ⊤} _ B → Nullification P B
  from = rec from′

  left-lemma :
    _≃_.left-inverse-of PO.Susp≃Susp y ≡
    ext⁻¹ (⟨ext⟩ (_≃_.left-inverse-of PO.Susp≃Susp)) y
  left-lemma = sym $ cong-ext (_≃_.left-inverse-of PO.Susp≃Susp)

  right-lemma :
    _≃_.right-inverse-of PO.Susp≃Susp y ≡
    ext⁻¹ (⟨ext⟩ (_≃_.right-inverse-of PO.Susp≃Susp)) y
  right-lemma = sym $ cong-ext (_≃_.right-inverse-of PO.Susp≃Susp)

------------------------------------------------------------------------
-- A map function

private

  -- A first approximation to nullification.

  Nullification′ : {A : Type a} → (A → Type a) → Type a → Type a
  Nullification′ P = Localisation′ {P = P} {Q = λ _ → ⊤} _

  -- The body of Nullification′-map.

  Nullification′-map-body :
    {A₁ : Type a₁} {P₁ : A₁ → Type a₁} {B₁ : Type a₁}
    {A₂ : Type a₂} {P₂ : A₂ → Type a₂} {B₂ : Type a₂} →
    (f : A₁ → A₂) → (∀ x → P₂ (f x) ↠ P₁ x) → (B₁ → B₂) →
    Rec {P = P₁} {Q = λ _ → ⊤} _ B₁ (Nullification′ P₂ B₂)
  Nullification′-map-body A₁→A₂ P₂↠P₁ B₁→B₂ = λ where
    .[]ʳ → [_] ∘ B₁→B₂

    .extʳ {x = x} f _ → ext (A₁→A₂ x) (f ∘ _↠_.to (P₂↠P₁ x)) _

    .ext≡ʳ {x = x} {y = y} f →
      ext (A₁→A₂ x) (f ∘ _↠_.to (P₂↠P₁ x)) _       ≡⟨ ext≡ ⟩
      f (_↠_.to (P₂↠P₁ x) (_↠_.from (P₂↠P₁ x) y))  ≡⟨ cong f $ _↠_.right-inverse-of (P₂↠P₁ x) _ ⟩∎
      f y                                          ∎

  -- A map function for Nullification′.

  Nullification′-map :
    {A₁ : Type a₁} {P₁ : A₁ → Type a₁} {B₁ : Type a₁}
    {A₂ : Type a₂} {P₂ : A₂ → Type a₂} {B₂ : Type a₂} →
    (f : A₁ → A₂) → (∀ x → P₂ (f x) ↠ P₁ x) → (B₁ → B₂) →
    Nullification′ P₁ B₁ → Nullification′ P₂ B₂
  Nullification′-map A₁→A₂ P₂↠P₁ B₁→B₂ =
    rec (Nullification′-map-body A₁→A₂ P₂↠P₁ B₁→B₂)

  -- The body of Nullification-map.

  Nullification-map-body :
    {A₁ : Type a₁} {P₁ : A₁ → Type a₁} {B₁ : Type a₁}
    {A₂ : Type a₂} {P₂ : A₂ → Type a₂} {B₂ : Type a₂} →
    (f : A₁ → A₂) → (∀ x → P₂ (f x) ↠ P₁ x) → (B₁ → B₂) →
    Rec {P = P.[ P₁ , Susp ∘ P₁ ]} {Q = λ _ → ⊤} _ B₁
      (Nullification P₂ B₂)
  Nullification-map-body A₁→A₂ P₂↠P₁ =
    Nullification′-map-body
      (⊎-map A₁→A₂ A₁→A₂)
      P.[ P₂↠P₁ , Susp.cong-↠ ∘ P₂↠P₁ ]

-- A map function for Nullification.

Nullification-map :
  {A₁ : Type a₁} {P₁ : A₁ → Type a₁} {B₁ : Type a₁}
  {A₂ : Type a₂} {P₂ : A₂ → Type a₂} {B₂ : Type a₂} →
  (f : A₁ → A₂) → (∀ x → P₂ (f x) ↠ P₁ x) → (B₁ → B₂) →
  Nullification P₁ B₁ → Nullification P₂ B₂
Nullification-map A₁→A₂ P₂↠P₁ B₁→B₂ =
  rec (Nullification-map-body A₁→A₂ P₂↠P₁ B₁→B₂)
