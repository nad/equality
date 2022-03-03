------------------------------------------------------------------------
-- Nullification
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe --save-metas #-}

-- Partly based on "Modalities in Homotopy Type Theory" by Rijke,
-- Shulman and Spitters.

import Equality.Path as P

module Nullification
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude as P

import Bijection equality-with-J as B
open import Equality.Path.Isomorphisms eq as I hiding (ext)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Path-split equality-with-J as PS using (_-Null_)
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level.Closure equality-with-J
open import Localisation eq
import Pushout eq as PO
open import Surjection equality-with-J using (_↠_)
open import Suspension eq as Susp using (Susp)

private
  variable
    a a₁ a₂ ℓ p : Level
    A B         : Type a
    P Q         : A → Type p
    f g h x y   : A

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

private abstract

  -- A lemma used below.

  sym-ext≡-ext≡ :
    {g≡h : ∀ y → g y ≡ h y} →
    trans
      (sym (ext≡ {P = P} {Q = Q} {x = x} {y = y} {f = f} {g = g}))
      (trans (cong (flip (ext x) _) $ ⟨ext⟩ g≡h)
         (ext≡ {x = x} {y = y} {g = h})) ≡
    g≡h y
  sym-ext≡-ext≡ {x = x} {g = g} {h = h} {y = y} {g≡h = g≡h} =
    trans
      (sym (ext≡ {x = x} {y = y} {g = g}))
      (trans (cong (flip (ext x) _) $ ⟨ext⟩ g≡h)
         (ext≡ {x = x} {y = y} {g = h}))               ≡⟨ elim₁
                                                            (λ {g} eq →
                                                               trans
                                                                 (sym $ ext≡ {x = x} {y = y} {g = g})
                                                                 (trans (cong (flip (ext _) _) eq)
                                                                    (ext≡ {x = x} {y = y} {g = h})) ≡
                                                               ext⁻¹ eq y)
                                                            (
      trans (sym ext≡)
        (trans (cong (flip (ext _) _) (refl h)) ext≡)        ≡⟨ cong (trans _) $
                                                                trans (cong (flip trans _) $ cong-refl _) $
                                                                trans-reflˡ _ ⟩

      trans (sym ext≡) ext≡                                  ≡⟨ trans-symˡ _ ⟩

      refl (h y)                                             ≡⟨ sym $ ext⁻¹-refl _ ⟩∎

      ext⁻¹ (refl h) y                                       ∎)
                                                            _ ⟩

    ext⁻¹ (⟨ext⟩ g≡h) y                                ≡⟨ cong-ext I.ext ⟩∎

    g≡h y                                              ∎

-- Nullification is a special case of localisation.

Nullification≃Localisation :
  Nullification P B ≃
  Localisation {P = P} {Q = λ _ → ⊤} _ B
Nullification≃Localisation {P = P} {B = B} =

  -- The proof is quite repetitive: to and from are rather similar, as
  -- are the two round-trip proofs. Perhaps it would make sense to
  -- prove something like Localisation′-cong (for a fixed "A"), and
  -- use that to prove this lemma.

  Eq.↔→≃ to from to-from from-to

  where
  to′ : Rec _ _ _
  to′ .[]ʳ =
    [_]

  to′ .extʳ {x = inj₁ x} f _ =
    ext (inj₁ x) (f ∘ lower) _

  to′ .extʳ {x = inj₂ x} f _ =
    ext (inj₂ x) (f ∘ _≃_.to PO.Susp≃Susp) _

  to′ .ext≡ʳ {x = inj₁ x} {y = y} f =
    ext (inj₁ x) (f ∘ lower) _  ≡⟨ ext≡ {x = inj₁ x} {y = lift y} {g = f ∘ lower} ⟩∎
    f y                         ∎

  to′ .ext≡ʳ {x = inj₂ x} {y = y} f =
    ext (inj₂ x) (f ∘ _≃_.to PO.Susp≃Susp) _           ≡⟨ ext≡ {x = inj₂ x} {y = _≃_.from PO.Susp≃Susp y} {g = f ∘ _≃_.to PO.Susp≃Susp} ⟩
    f (_≃_.to PO.Susp≃Susp (_≃_.from PO.Susp≃Susp y))  ≡⟨ cong f $ _≃_.right-inverse-of PO.Susp≃Susp y ⟩∎
    f y                                                ∎

  from′ : Rec _ _ _
  from′ .[]ʳ =
    [_]

  from′ .extʳ {x = inj₁ x} f _ =
    ext (inj₁ x) (f ∘ lift) _

  from′ .extʳ {x = inj₂ x} f _ =
    ext (inj₂ x) (f ∘ _≃_.from PO.Susp≃Susp) _

  from′ .ext≡ʳ {x = inj₁ x} {y = y} f =
    ext (inj₁ x) (f ∘ lift) _  ≡⟨ ext≡ {x = inj₁ x} {y = lower y} {g = f ∘ lift} ⟩∎
    f y                        ∎

  from′ .ext≡ʳ {x = inj₂ x} {y = y} f =
    ext (inj₂ x) (f ∘ _≃_.from PO.Susp≃Susp) _         ≡⟨ ext≡ {x = inj₂ x} {y = _≃_.to PO.Susp≃Susp y} {g = f ∘ _≃_.from PO.Susp≃Susp} ⟩
    f (_≃_.from PO.Susp≃Susp (_≃_.to PO.Susp≃Susp y))  ≡⟨ cong f $ _≃_.left-inverse-of PO.Susp≃Susp y ⟩∎
    f y                                                ∎

  to : Nullification P B → Localisation {P = P} {Q = λ _ → ⊤} _ B
  to = rec to′

  from : Localisation {P = P} {Q = λ _ → ⊤} _ B → Nullification P B
  from = rec from′

  abstract

    left-eq :
      _≃_.from PO.Susp≃Susp ∘ _≃_.to PO.Susp≃Susp ≡ id {A = PO.Susp A}
    left-eq = ⟨ext⟩ (_≃_.left-inverse-of PO.Susp≃Susp)

    left-lemma :
      _≃_.left-inverse-of PO.Susp≃Susp y ≡ ext⁻¹ left-eq y
    left-lemma = sym $ cong-ext I.ext

    right-eq :
      _≃_.to PO.Susp≃Susp ∘ _≃_.from PO.Susp≃Susp ≡ id {A = Susp A}
    right-eq = ⟨ext⟩ (_≃_.right-inverse-of PO.Susp≃Susp)

    right-lemma :
      _≃_.right-inverse-of PO.Susp≃Susp y ≡
      ext⁻¹ (⟨ext⟩ (_≃_.right-inverse-of PO.Susp≃Susp)) y
    right-lemma = sym $ cong-ext I.ext

    to-from′ : Elim (λ x → to (from x) ≡ x)
    to-from′ .[]ʳ =
      refl ∘ [_]

    to-from′ .extʳ {x = inj₁ x} {g = f} hyp _ =
      to (from (ext (inj₁ x) f _))    ≡⟨⟩
      ext (inj₁ x) (to ∘ from ∘ f) _  ≡⟨ cong (flip (ext _) _) $ ⟨ext⟩ hyp ⟩∎
      ext (inj₁ x) f _                ∎

    to-from′ .extʳ {x = inj₂ x} {g = f} hyp _ =
      to (from (ext (inj₂ x) f _))                                     ≡⟨⟩

      ext (inj₂ x)
        (to ∘ from ∘ f ∘ _≃_.from PO.Susp≃Susp ∘ _≃_.to PO.Susp≃Susp)
        _                                                              ≡⟨ (cong (flip (ext _) _) $ ⟨ext⟩ λ y → cong (to ∘ from ∘ f) $
                                                                           _≃_.left-inverse-of PO.Susp≃Susp y) ⟩

      ext (inj₂ x) (to ∘ from ∘ f) _                                   ≡⟨ cong (flip (ext _) _) $ ⟨ext⟩ hyp ⟩∎

      ext (inj₂ x) f _                                                 ∎

    to-from′ .ext≡ʳ {x = inj₁ x} {g = f} {y = y} hyp =
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
           (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ sym-ext≡-ext≡ ⟩∎

      hyp y                                                    ∎

    to-from′ .ext≡ʳ {x = inj₂ x} {g = f} {y = y} hyp =
      subst (λ x → to (from x) ≡ x)
        (ext≡ {x = inj₂ x} {y = y} {g = f})
        (trans
           (cong (flip (ext _) _) $
            ⟨ext⟩ λ y → cong (to ∘ from ∘ f) $
            _≃_.left-inverse-of PO.Susp≃Susp y)
           (cong (flip (ext _) _) $ ⟨ext⟩ hyp))                       ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans
        (sym $ cong (to ∘ from) $
         ext≡ {x = inj₂ x} {y = y} {g = f})
        (trans
           (trans
              (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
               cong (to ∘ from ∘ f) $
               _≃_.left-inverse-of PO.Susp≃Susp y)
              (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
           (cong id (ext≡ {x = inj₂ x} {y = y} {g = f})))             ≡⟨ cong₂ (trans ∘ sym)
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
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong (sym ∘ cong to) $
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
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $
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
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (flip trans _) $
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
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ trans (cong (flip trans _) $ cong sym $
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
      trans
        (sym $
         trans
           (trans
              (ext≡ {x = inj₂ x}
                 {y = _≃_.from PO.Susp≃Susp (_≃_.to PO.Susp≃Susp y)}
                 {g = to ∘ from ∘ f ∘
                      _≃_.from PO.Susp≃Susp ∘ _≃_.to PO.Susp≃Susp})
              (cong (to ∘ from ∘ f) $
               ext⁻¹ left-eq
                 (_≃_.from PO.Susp≃Susp (_≃_.to PO.Susp≃Susp y))))
           (cong (to ∘ from ∘ f) $ ext⁻¹ left-eq y))
        (trans
           (trans
              (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
               cong (to ∘ from ∘ f) $ ext⁻¹ left-eq y)
              (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ elim₁
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
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                           ≡⟨ cong₂ trans
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
                                                                                                       cong-refl _) $
                                                                                                ext-refl I.ext) $
                                                                                         cong-refl _) $
                                                                                  trans-reflˡ _) ⟩
        trans
          (sym $ ext≡ {x = inj₂ x} {y = y} {g = to ∘ from ∘ f})
          (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                           ≡⟨ sym-ext≡-ext≡ ⟩∎

        hyp y                                                               ∎)
                                                                           _ ⟩∎
      hyp y                                                           ∎

    from-to′ : Elim (λ x → from (to x) ≡ x)
    from-to′ .[]ʳ =
      refl ∘ [_]

    from-to′ .extʳ {x = inj₁ x} {g = f} hyp _ =
      from (to (ext (inj₁ x) f _))    ≡⟨⟩
      ext (inj₁ x) (from ∘ to ∘ f) _  ≡⟨ cong (flip (ext _) _) $ ⟨ext⟩ hyp ⟩∎
      ext (inj₁ x) f _                ∎

    from-to′ .extʳ {x = inj₂ x} {g = f} hyp _ =
      from (to (ext (inj₂ x) f _))                                     ≡⟨⟩

      ext (inj₂ x)
        (from ∘ to ∘ f ∘ _≃_.to PO.Susp≃Susp ∘ _≃_.from PO.Susp≃Susp)
        _                                                              ≡⟨ (cong (flip (ext _) _) $ ⟨ext⟩ λ y → cong (from ∘ to ∘ f) $
                                                                           _≃_.right-inverse-of PO.Susp≃Susp y) ⟩

      ext (inj₂ x) (from ∘ to ∘ f) _                                   ≡⟨ cong (flip (ext _) _) $ ⟨ext⟩ hyp ⟩∎

      ext (inj₂ x) f _                                                 ∎

    from-to′ .ext≡ʳ {x = inj₁ x} {g = f} {y = y} hyp =
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
           (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ sym-ext≡-ext≡ ⟩∎

      hyp y                                                    ∎

    from-to′ .ext≡ʳ {x = inj₂ x} {g = f} {y = y} hyp =
      subst (λ x → from (to x) ≡ x)
        (ext≡ {x = inj₂ x} {y = y} {g = f})
        (trans
           (cong (flip (ext _) _) $
            ⟨ext⟩ λ y → cong (from ∘ to ∘ f) $
            _≃_.right-inverse-of PO.Susp≃Susp y)
           (cong (flip (ext _) _) $ ⟨ext⟩ hyp))                       ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans
        (sym $ cong (from ∘ to) $
         ext≡ {x = inj₂ x} {y = y} {g = f})
        (trans
           (trans
              (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
               cong (from ∘ to ∘ f) $
               _≃_.right-inverse-of PO.Susp≃Susp y)
              (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
           (cong id (ext≡ {x = inj₂ x} {y = y} {g = f})))             ≡⟨ cong₂ (trans ∘ sym)
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
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong (sym ∘ cong from) $
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
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $
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
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (flip trans _) $
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
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ trans (cong (flip trans _) $ cong sym $
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
      trans
        (sym $
         trans
           (trans
              (ext≡ {x = inj₂ x}
                 {y = _≃_.to PO.Susp≃Susp (_≃_.from PO.Susp≃Susp y)}
                 {g = from ∘ to ∘ f ∘
                      _≃_.to PO.Susp≃Susp ∘ _≃_.from PO.Susp≃Susp})
              (cong (from ∘ to ∘ f) $
               ext⁻¹ right-eq
                 (_≃_.to PO.Susp≃Susp (_≃_.from PO.Susp≃Susp y))))
           (cong (from ∘ to ∘ f) $ ext⁻¹ right-eq y))
        (trans
           (trans
              (cong (flip (ext _) _) $ ⟨ext⟩ λ y →
               cong (from ∘ to ∘ f) $ ext⁻¹ right-eq y)
              (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
           (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ elim₁
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
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                           ≡⟨ cong₂ trans
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
                                                                                                       cong-refl _) $
                                                                                                ext-refl I.ext) $
                                                                                         cong-refl _) $
                                                                                  trans-reflˡ _) ⟩
        trans
          (sym $ ext≡ {x = inj₂ x} {y = y} {g = from ∘ to ∘ f})
          (trans (cong (flip (ext _) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                           ≡⟨ sym-ext≡-ext≡ ⟩∎

        hyp y                                                               ∎)
                                                                           _ ⟩∎
      hyp y                                                           ∎

    to-from : ∀ x → to (from x) ≡ x
    to-from = elim to-from′

    from-to : ∀ x → from (to x) ≡ x
    from-to = elim from-to′

-- If B is P-null, then λ (f : Nullification P A → B) → f ∘ [_] is an
-- equivalence.

Null→Is-equivalence-∘[] :
  P -Null B →
  Is-equivalence (λ (f : Nullification P A → B) → f ∘ [_])
Null→Is-equivalence-∘[] {P = P} {B = B} {A = A} =
  P -Null B                                                         ↔⟨ Null≃Local ⟩

  (λ x (_ : P x) → tt) -Local B                                     →⟨ Local→Is-equivalence-[] ⟩

  Is-equivalence
    (λ (f : Localisation {P = P} {Q = λ _ → ⊤} _ A → B) → f ∘ [_])  →⟨ Is-equivalence≃Is-equivalence-∘ʳ
                                                                         (_≃_.is-equivalence $
                                                                          →-cong I.ext Nullification≃Localisation F.id)
                                                                         _ ⟩□
  Is-equivalence (λ (f : Nullification P A → B) → f ∘ [_])          □

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
  Nullification′-map-body A₁→A₂ P₂↠P₁ B₁→B₂ = body
    where
    body : Rec _ _ _
    body .[]ʳ = [_] ∘ B₁→B₂

    body .extʳ {x = x} f _ = ext (A₁→A₂ x) (f ∘ _↠_.to (P₂↠P₁ x)) _

    body .ext≡ʳ {x = x} {y = y} f =
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

------------------------------------------------------------------------
-- The lemma Nullification-↑-↑-≃

private abstract

  -- A lemma used below.

  sym-ext≡-ext≡′ :
    {f : P x → Nullification′ P B}
    {eq : h ≡ id}
    (g : Nullification′ P B → Nullification′ P B)
    (hyp : ∀ x → g (f x) ≡ f x) →
    trans
      (sym $
       trans
         (trans
            (ext≡ {x = x} {y = h y} {g = g ∘ f ∘ h})
            (cong (g ∘ f) $ ext⁻¹ eq (h y)))
         (cong (g ∘ f) $ ext⁻¹ eq y))
      (trans
         (trans
            (cong (flip (ext _) _) $ cong ((g ∘ f) ∘_) eq)
            (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
         (ext≡ {x = x} {y = y} {g = f})) ≡
    hyp y
  sym-ext≡-ext≡′ {x = x} {y = y} {f = f} g hyp =
    elim₁
      (λ {h} eq →
         trans
           (sym $
            trans
              (trans (ext≡ {x = x} {y = h y} {g = g ∘ f ∘ h})
                 (cong (g ∘ f) $ ext⁻¹ eq (h y)))
              (cong (g ∘ f) $ ext⁻¹ eq y))
           (trans
              (trans
                 (cong (flip (ext _) _) $ cong ((g ∘ f) ∘_) eq)
                 (cong (flip (ext _) _) $ ⟨ext⟩ hyp))
              (ext≡ {x = x} {y = y} {g = f})) ≡
         hyp y)
      (trans
         (sym $
          trans
            (trans
               (ext≡ {x = x} {y = y} {g = g ∘ f})
               (cong (g ∘ f) $ ext⁻¹ (refl id) y))
            (cong (g ∘ f) $ ext⁻¹ (refl id) y))
         (trans
            (trans
               (cong (flip (ext x) _) $
                cong ((g ∘ f) ∘_) $ refl id)
               (cong (flip (ext x) _) $ ⟨ext⟩ hyp))
            (ext≡ {x = x} {y = y} {g = f}))          ≡⟨ cong₂ trans
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
                                                                  trans (cong (cong _) $ cong-refl _) $
                                                                  cong-refl _) $
                                                           trans-reflˡ _) ⟩
       trans
         (sym $ ext≡ {x = x} {y = y} {g = g ∘ f})
         (trans (cong (flip (ext x) _) $ ⟨ext⟩ hyp)
            (ext≡ {x = x} {y = y} {g = f}))          ≡⟨ sym-ext≡-ext≡ ⟩∎

       hyp y                                         ∎)
      _

-- Helper functions used to implement Nullification-↑-↑-≃.

private
  module Nullification-↑-↑-≃
    {ℓ : Level} {A B : Type a} {P : A → Type a} where

    ↑≃ : {A : Type a} → ↑ ℓ A ≃ A
    ↑≃ = Eq.↔⇒≃ B.↑↔

    mutual

      to″ =
        Nullification′-map-body
          (⊎-map lower lower)
          P.[ (λ _ → _≃_.surjection $ inverse ↑≃)
            , (λ _ → _≃_.surjection $ inverse $ Susp.cong-≃ ↑≃)
            ]
          lower

      -- The proof to′ is a variant of to″ that is partly blocked.

      to′ : Block "to" → Rec _ _ _
      to′ _ .[]ʳ                   = to″ .[]ʳ
      to′ _ .extʳ {x = x}          = to″ .extʳ {x = x}
      to′ ⊠ .ext≡ʳ {x = x} {y = y} = to″ .ext≡ʳ {x = x} {y = y}

      to :
        Block "to" →
        Nullification {A = ↑ ℓ A} (↑ ℓ ∘ P ∘ lower) (↑ ℓ B) →
        Nullification P B
      to b = rec (to′ b)

    mutual

      from″ =
        Nullification-map-body
          lift
          (λ _ → _≃_.surjection ↑≃)
          lift

      -- The proof from′ is a variant of from″ that is partly blocked.

      from′ : Block "from" → Rec _ _ _
      from′ _ .[]ʳ                   = from″ .[]ʳ
      from′ _ .extʳ {x = x}          = from″ .extʳ {x = x}
      from′ ⊠ .ext≡ʳ {x = x} {y = y} = from″ .ext≡ʳ {x = x} {y = y}

      from :
        Block "from" →
        Nullification P B →
        Nullification {A = ↑ ℓ A} (↑ ℓ ∘ P ∘ lower) (↑ ℓ B)
      from b = rec (from′ b)

    abstract

      right-eq :
        {A : Type a} →
        Susp.map lower ∘ Susp.map (lift {ℓ = ℓ}) ≡ id {A = Susp A}
      right-eq = ⟨ext⟩ (_≃_.right-inverse-of (Susp.cong-≃ ↑≃))

      right-lemma :
        _≃_.right-inverse-of (Susp.cong-≃ ↑≃) y ≡ ext⁻¹ right-eq y
      right-lemma = sym $ cong-ext I.ext

      to-from-ext :
        ∀ b x f →
        (∀ y → to b (from b (f y)) ≡ f y) →
        to b (from b (ext x f _)) ≡ ext x f _
      to-from-ext b (inj₁ x) f hyp =
        ext (inj₁ x) (to b ∘ from b ∘ f) _  ≡⟨ cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp ⟩∎
        ext (inj₁ x) f _                    ∎
      to-from-ext b (inj₂ x) f hyp =
        ext (inj₂ x)
          (to b ∘ from b ∘ f ∘ Susp.map lower ∘ Susp.map lift)
          _                                                     ≡⟨ cong (flip (ext (inj₂ x)) _) $ cong ((to b ∘ from b ∘ f) ∘_)
                                                                   right-eq ⟩

        ext (inj₂ x) (to b ∘ from b ∘ f) _                      ≡⟨ cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp ⟩∎

        ext (inj₂ x) f _                                        ∎

      to-from-ext≡ :
        ∀ b x f y (hyp : ∀ y → to b (from b (f y)) ≡ f y) →
        subst (λ x → to b (from b x) ≡ x) ext≡ (to-from-ext b x f hyp) ≡
        hyp y
      to-from-ext≡ b (inj₁ x) f y hyp =
        subst (λ x → to b (from b x) ≡ x)
          (ext≡ {x = inj₁ x} {y = y} {g = f})
          (to-from-ext b (inj₁ x) f hyp)                                ≡⟨⟩

        subst (λ x → to b (from b x) ≡ x)
          (ext≡ {x = inj₁ x} {y = y} {g = f})
          (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)                    ≡⟨ subst-in-terms-of-trans-and-cong ⟩

        trans
          (sym $ cong (to b ∘ from b) $
           ext≡ {x = inj₁ x} {y = y} {g = f})
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (cong id $ ext≡ {x = inj₁ x} {y = y} {g = f}))             ≡⟨ cong₂ trans
                                                                             (cong sym $ sym $ cong-∘ _ _ _)
                                                                             (cong (trans _) $ sym $ cong-id _) ⟩
        trans
          (sym $ cong (to b) $ cong (from b) $
           ext≡ {x = inj₁ x} {y = y} {g = f})
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (cong (to b)) $
                                                                           unblock b
                                                                             (λ b →
                                                                                cong (from b) ext≡ ≡
                                                                                trans ext≡ (cong (from b ∘ f) (refl y))) $
                                                                           rec-ext≡ {r = from′ ⊠} ⟩
        trans
          (sym $ cong (to b) $
           trans
             (ext≡ {x = inj₁ (lift x)} {y = lift y}
                {g = from b ∘ f ∘ lower {ℓ = ℓ}}) $
           cong (from b ∘ f) $ refl y)
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (cong _) $
                                                                           trans (cong (trans _) $ cong-refl _) $
                                                                           trans-reflʳ _ ⟩
        trans
          (sym $ cong (to b) $
           ext≡ {x = inj₁ (lift x)} {y = lift y}
             {g = from b ∘ f ∘ lower {ℓ = ℓ}})
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $
                                                                           unblock b
                                                                             (λ b →
                                                                                cong (to b)
                                                                                  (ext≡ {x = inj₁ (lift x)} {y = lift y}
                                                                                     {g = from b ∘ f ∘ lower {ℓ = ℓ}}) ≡
                                                                                trans (ext≡ {x = inj₁ x} {y = y} {g = to b ∘ from b ∘ f})
                                                                                  (cong (to b ∘ from b ∘ f ∘ lower {ℓ = ℓ}) $
                                                                                   _≃_.left-inverse-of ↑≃ (lift y))) $
                                                                           rec-ext≡ {r = to′ ⊠} ⟩
        trans
          (sym $
           trans (ext≡ {x = inj₁ x} {y = y} {g = to b ∘ from b ∘ f}) $
           cong (to b ∘ from b ∘ f ∘ lower {ℓ = ℓ}) $
           _≃_.left-inverse-of ↑≃ (lift y))
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (trans _) $
                                                                           trans (sym $ cong-∘ _ _ _) $
                                                                           cong (cong _) $
                                                                           _≃_.left-right-lemma ↑≃ _ ⟩
        trans
          (sym $
           trans (ext≡ {x = inj₁ x} {y = y} {g = to b ∘ from b ∘ f}) $
           cong (to b ∘ from b ∘ f) $ _≃_.right-inverse-of ↑≃ y)
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨⟩
        trans
          (sym $
           trans (ext≡ {x = inj₁ x} {y = y} {g = to b ∘ from b ∘ f}) $
           cong (to b ∘ from b ∘ f) $ refl y)
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $
                                                                           trans (cong (trans _) $ cong-refl _) $
                                                                           trans-reflʳ _ ⟩
        trans
          (sym $ ext≡ {x = inj₁ x} {y = y} {g = to b ∘ from b ∘ f})
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ sym-ext≡-ext≡ ⟩∎

        hyp y                                                           ∎

      to-from-ext≡ b (inj₂ x) f y hyp =
        subst (λ x → to b (from b x) ≡ x)
          (ext≡ {x = inj₂ x} {y = y} {g = f})
          (to-from-ext b (inj₂ x) f hyp)                                ≡⟨⟩

        subst (λ x → to b (from b x) ≡ x)
          (ext≡ {x = inj₂ x} {y = y} {g = f})
          (trans
             (cong (flip (ext (inj₂ x)) _) $
              cong ((to b ∘ from b ∘ f) ∘_) right-eq)
             (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))                ≡⟨ subst-in-terms-of-trans-and-cong ⟩

        trans
          (sym $ cong (to b ∘ from b) $
           ext≡ {x = inj₂ x} {y = y} {g = f})
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((to b ∘ from b ∘ f) ∘_) right-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (cong id (ext≡ {x = inj₂ x} {y = y} {g = f})))             ≡⟨ cong₂ (trans ∘ sym)
                                                                             (sym $ cong-∘ _ _ _)
                                                                             (cong (trans _) $ sym $ cong-id _) ⟩
        trans
          (sym $ cong (to b) $ cong (from b) $
           ext≡ {x = inj₂ x} {y = y} {g = f})
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((to b ∘ from b ∘ f) ∘_) right-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong (sym ∘ cong (to b)) $
                                                                           unblock b
                                                                             (λ b →
                                                                                cong (from b)
                                                                                  (ext≡ {x = inj₂ x} {y = y} {g = f}) ≡
                                                                                trans
                                                                                  (ext≡
                                                                                     {x = inj₂ (lift x)}
                                                                                     {y = Susp.map (lift {ℓ = ℓ}) y}
                                                                                     {g = from b ∘ f ∘ Susp.map (lower {ℓ = ℓ})})
                                                                                  (cong (from b ∘ f) $
                                                                                   _≃_.right-inverse-of (Susp.cong-≃ ↑≃) y)) $
                                                                           rec-ext≡ {r = from′ ⊠} ⟩
        trans
          (sym $ cong (to b) $
           trans
             (ext≡
                {x = inj₂ (lift x)}
                {y = Susp.map (lift {ℓ = ℓ}) y}
                {g = from b ∘ f ∘ Susp.map (lower {ℓ = ℓ})})
             (cong (from b ∘ f) $
              _≃_.right-inverse-of (Susp.cong-≃ ↑≃) y))
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((to b ∘ from b ∘ f) ∘_) right-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $
                                                                           trans (cong-trans _ _ _) $
                                                                           cong (trans _) $ cong-∘ _ _ _ ⟩
        trans
          (sym $
           trans
             (cong (to b) $
              ext≡
                {x = inj₂ (lift x)}
                {y = Susp.map (lift {ℓ = ℓ}) y}
                {g = from b ∘ f ∘ Susp.map (lower {ℓ = ℓ})})
             (cong (to b ∘ from b ∘ f) $
              _≃_.right-inverse-of (Susp.cong-≃ ↑≃) y))
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((to b ∘ from b ∘ f) ∘_) right-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (flip trans _) $
                                                                           unblock b
                                                                             (λ b →
                                                                                cong (to b)
                                                                                  (ext≡
                                                                                     {x = inj₂ (lift x)}
                                                                                     {y = Susp.map (lift {ℓ = ℓ}) y}
                                                                                     {g = from b ∘ f ∘ Susp.map (lower {ℓ = ℓ})}) ≡
                                                                                trans
                                                                                  (ext≡
                                                                                     {x = inj₂ x}
                                                                                     {y = Susp.map (lower {ℓ = ℓ}) (Susp.map lift y)}
                                                                                     {g = to b ∘ from b ∘ f ∘
                                                                                          Susp.map (lower {ℓ = ℓ}) ∘ Susp.map lift})
                                                                                  (cong (to b ∘ from b ∘ f ∘ Susp.map (lower {ℓ = ℓ})) $
                                                                                   _≃_.left-inverse-of (Susp.cong-≃ ↑≃) (Susp.map lift y))) $
                                                                           rec-ext≡ {r = to′ ⊠} ⟩
        trans
          (sym $
           trans
             (trans
                (ext≡
                   {x = inj₂ x}
                   {y = Susp.map (lower {ℓ = ℓ}) (Susp.map lift y)}
                   {g = to b ∘ from b ∘ f ∘
                        Susp.map (lower {ℓ = ℓ}) ∘ Susp.map lift})
                (cong (to b ∘ from b ∘ f ∘ Susp.map (lower {ℓ = ℓ})) $
                 _≃_.left-inverse-of (Susp.cong-≃ ↑≃)
                   (Susp.map lift y)))
             (cong (to b ∘ from b ∘ f) $
              _≃_.right-inverse-of (Susp.cong-≃ ↑≃) y))
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((to b ∘ from b ∘ f) ∘_) right-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $
                                                                           cong₂ trans
                                                                             (cong (trans _) $
                                                                              trans (sym $ cong-∘ _ _ _) $
                                                                              cong (cong (to b ∘ from b ∘ f)) $
                                                                              trans (_≃_.left-right-lemma (Susp.cong-≃ ↑≃) _)
                                                                              right-lemma)
                                                                             (cong (cong _) right-lemma) ⟩
        trans
          (sym $
           trans
             (trans
                (ext≡
                   {x = inj₂ x}
                   {y = Susp.map (lower {ℓ = ℓ}) (Susp.map lift y)}
                   {g = to b ∘ from b ∘ f ∘
                        Susp.map (lower {ℓ = ℓ}) ∘ Susp.map lift})
                (cong (to b ∘ from b ∘ f) $
                 ext⁻¹ right-eq
                   (Susp.map (lower {ℓ = ℓ}) (Susp.map lift y))))
             (cong (to b ∘ from b ∘ f) $ ext⁻¹ right-eq y))
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((to b ∘ from b ∘ f) ∘_) right-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                       ≡⟨ sym-ext≡-ext≡′ (to b ∘ from b) hyp ⟩∎

        hyp y                                                           ∎

      to-from : ∀ b x → to b (from b x) ≡ x
      to-from b = elim λ where
        .[]ʳ        → refl ∘ [_]
        .extʳ hyp _ → to-from-ext b _ _ hyp
        .ext≡ʳ hyp  → to-from-ext≡ b _ _ _ hyp

      left-eq :
        {A : Type a} →
        Susp.map lift ∘ Susp.map lower ≡ id {A = Susp (↑ ℓ A)}
      left-eq = ⟨ext⟩ (_≃_.left-inverse-of (Susp.cong-≃ ↑≃))

      left-lemma :
        _≃_.left-inverse-of (Susp.cong-≃ ↑≃) y ≡ ext⁻¹ left-eq y
      left-lemma = sym $ cong-ext I.ext

      from-to-ext :
        ∀ b x f →
        (∀ y → from b (to b (f y)) ≡ f y) →
        from b (to b (ext x f _)) ≡ ext x f _
      from-to-ext b (inj₁ x) f hyp =
        ext (inj₁ x) (from b ∘ to b ∘ f) _  ≡⟨ cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp ⟩∎
        ext (inj₁ x) f _                    ∎
      from-to-ext b (inj₂ x) f hyp =
        ext (inj₂ x)
          (from b ∘ to b ∘ f ∘ Susp.map lift ∘ Susp.map lower)
          _                                                     ≡⟨ cong (flip (ext (inj₂ x)) _) $ cong ((from b ∘ to b ∘ f) ∘_)
                                                                   left-eq ⟩

        ext (inj₂ x) (from b ∘ to b ∘ f) _                      ≡⟨ cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp ⟩∎

        ext (inj₂ x) f _                                        ∎

      cong-to-ext≡-inj₁ :
        ∀ b →
        cong (to b) (ext≡ {x = inj₁ x} {y = y} {g = f}) ≡
        trans
          (ext≡ {x = inj₁ (lower x)} {y = lower y}
             {g = to b ∘ f ∘ lift {ℓ = ℓ}})
          (cong (to b ∘ f) $ _≃_.left-inverse-of ↑≃ y)
      cong-to-ext≡-inj₁ ⊠ = rec-ext≡ {r = to′ ⊠}

      cong-from-ext≡-inj₁ :
        ∀ b f →
        cong (from b)
          (ext≡ {x = inj₁ (lower x)} {y = lower y}
             {g = to b ∘ f ∘ lift {ℓ = ℓ}}) ≡
        trans
          (ext≡ {x = inj₁ x} {y = y} {g = from b ∘ to b ∘ f})
          (cong (from b ∘ to b ∘ f ∘ lift {ℓ = ℓ}) $
           refl (lower y))
      cong-from-ext≡-inj₁ ⊠ _ = rec-ext≡ {r = from′ ⊠}

      cong-to-ext≡-inj₂ :
        ∀ b →
        cong (to b) (ext≡ {x = inj₂ x} {y = y} {g = f}) ≡
        trans
          (ext≡
             {x = inj₂ (lower x)}
             {y = Susp.map (lower {ℓ = ℓ}) y}
             {g = to b ∘ f ∘ Susp.map (lift {ℓ = ℓ})})
          (cong (to b ∘ f) $ _≃_.left-inverse-of (Susp.cong-≃ ↑≃) y)
      cong-to-ext≡-inj₂ ⊠ = rec-ext≡ {r = to′ ⊠}

      cong-from-ext≡-inj₂ :
        ∀ b f y →
        cong (from b)
          (ext≡
             {x = inj₂ (lower x)}
             {y = Susp.map (lower {ℓ = ℓ}) y}
             {g = to b ∘ f ∘ Susp.map (lift {ℓ = ℓ})}) ≡
        trans
          (ext≡
             {x = inj₂ x}
             {y = Susp.map (lift {ℓ = ℓ}) (Susp.map lower y)}
             {g = from b ∘ to b ∘ f ∘
                  Susp.map (lift {ℓ = ℓ}) ∘ Susp.map lower})
          (cong (from b ∘ to b ∘ f ∘ Susp.map (lift {ℓ = ℓ})) $
           _≃_.right-inverse-of (Susp.cong-≃ ↑≃) (Susp.map lower y))
      cong-from-ext≡-inj₂ ⊠ _ _ = rec-ext≡ {r = from′ ⊠}

      from-to-ext≡ :
        ∀ b x f y (hyp : ∀ y → from b (to b (f y)) ≡ f y) →
        subst (λ x → from b (to b x) ≡ x) ext≡ (from-to-ext b x f hyp) ≡
        hyp y
      from-to-ext≡ b (inj₁ x) f y hyp =
        subst (λ x → from b (to b x) ≡ x)
          (ext≡ {x = inj₁ x} {y = y} {g = f})
          (from-to-ext b (inj₁ x) f hyp)                                ≡⟨⟩

        subst (λ x → from b (to b x) ≡ x)
          (ext≡ {x = inj₁ x} {y = y} {g = f})
          (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)                    ≡⟨ subst-in-terms-of-trans-and-cong ⟩

        trans
          (sym $ cong (from b ∘ to b) $
           ext≡ {x = inj₁ x} {y = y} {g = f})
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (cong id $ ext≡ {x = inj₁ x} {y = y} {g = f}))             ≡⟨ cong₂ trans
                                                                             (cong sym $ sym $ cong-∘ _ _ _)
                                                                             (cong (trans _) $ sym $ cong-id _) ⟩
        trans
          (sym $ cong (from b) $ cong (to b) $
           ext≡ {x = inj₁ x} {y = y} {g = f})
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (cong (from b)) $
                                                                           cong-to-ext≡-inj₁ b ⟩
        trans
          (sym $ cong (from b) $
           trans
             (ext≡ {x = inj₁ (lower x)} {y = lower y}
                {g = to b ∘ f ∘ lift {ℓ = ℓ}}) $
           cong (to b ∘ f) $ _≃_.left-inverse-of ↑≃ y)
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨⟩

        trans
          (sym $ cong (from b) $
           trans
             (ext≡ {x = inj₁ (lower x)} {y = lower y}
                {g = to b ∘ f ∘ lift {ℓ = ℓ}}) $
           cong (to b ∘ f ∘ lift ∘ lower) $
           _≃_.left-inverse-of ↑≃ y)
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (cong _) $ cong (trans _) $
                                                                           trans (sym $ cong-∘ _ _ _) $
                                                                           cong (cong _) $
                                                                           _≃_.left-right-lemma ↑≃ _ ⟩
        trans
          (sym $ cong (from b) $
           trans
             (ext≡ {x = inj₁ (lower x)} {y = lower y}
                {g = to b ∘ f ∘ lift {ℓ = ℓ}}) $
           cong (to b ∘ f ∘ lift) $
           _≃_.right-inverse-of ↑≃ (lower y))
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨⟩

        trans
          (sym $ cong (from b) $
           trans
             (ext≡ {x = inj₁ (lower x)} {y = lower y}
                {g = to b ∘ f ∘ lift {ℓ = ℓ}}) $
           cong (to b ∘ f ∘ lift) $ refl (lower y))
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $ cong (cong _) $
                                                                           trans (cong (trans _) $ cong-refl _) $
                                                                           trans-reflʳ _ ⟩
        trans
          (sym $ cong (from b) $
           ext≡ {x = inj₁ (lower x)} {y = lower y}
             {g = to b ∘ f ∘ lift {ℓ = ℓ}})
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $
                                                                           cong-from-ext≡-inj₁ b f ⟩
        trans
          (sym $
           trans (ext≡ {x = inj₁ x} {y = y} {g = from b ∘ to b ∘ f}) $
           cong (from b ∘ to b ∘ f ∘ lift {ℓ = ℓ}) $ refl (lower y))
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ cong (flip trans _) $ cong sym $
                                                                           trans (cong (trans _) $ cong-refl _) $
                                                                           trans-reflʳ _ ⟩
        trans
          (sym (ext≡ {x = inj₁ x} {y = y} {g = from b ∘ to b ∘ f}))
          (trans (cong (flip (ext (inj₁ x)) _) $ ⟨ext⟩ hyp)
             (ext≡ {x = inj₁ x} {y = y} {g = f}))                       ≡⟨ sym-ext≡-ext≡ ⟩∎

        hyp y                                                           ∎

      from-to-ext≡ b (inj₂ x) f y hyp =
        subst (λ x → from b (to b x) ≡ x)
          (ext≡ {x = inj₂ x} {y = y} {g = f})
          (from-to-ext b (inj₂ x) f hyp)                             ≡⟨⟩

        subst (λ x → from b (to b x) ≡ x)
          (ext≡ {x = inj₂ x} {y = y} {g = f})
          (trans
             (cong (flip (ext (inj₂ x)) _) $
              cong ((from b ∘ to b ∘ f) ∘_) left-eq)
             (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))             ≡⟨ subst-in-terms-of-trans-and-cong ⟩

        trans
          (sym $ cong (from b ∘ to b) $
           ext≡ {x = inj₂ x} {y = y} {g = f})
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((from b ∘ to b ∘ f) ∘_) left-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (cong id (ext≡ {x = inj₂ x} {y = y} {g = f})))          ≡⟨ cong₂ (trans ∘ sym)
                                                                          (sym $ cong-∘ _ _ _)
                                                                          (cong (trans _) $ sym $ cong-id _) ⟩
        trans
          (sym $ cong (from b) $ cong (to b) $
           ext≡ {x = inj₂ x} {y = y} {g = f})
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((from b ∘ to b ∘ f) ∘_) left-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                    ≡⟨ cong (flip trans _) $ cong sym $ cong (cong (from b)) $
                                                                        cong-to-ext≡-inj₂ b ⟩
        trans
          (sym $ cong (from b) $
           trans
             (ext≡
                {x = inj₂ (lower x)}
                {y = Susp.map (lower {ℓ = ℓ}) y}
                {g = to b ∘ f ∘ Susp.map (lift {ℓ = ℓ})})
             (cong (to b ∘ f) $
              _≃_.left-inverse-of (Susp.cong-≃ ↑≃) y))
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((from b ∘ to b ∘ f) ∘_) left-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                    ≡⟨ cong (flip trans _) $ cong sym $
                                                                        trans (cong-trans _ _ _) $
                                                                        cong (trans _) $ cong-∘ _ _ _ ⟩
        trans
          (sym $
           trans
             (cong (from b) $
              ext≡
                {x = inj₂ (lower x)}
                {y = Susp.map (lower {ℓ = ℓ}) y}
                {g = to b ∘ f ∘ Susp.map (lift {ℓ = ℓ})})
             (cong (from b ∘ to b ∘ f) $
              _≃_.left-inverse-of (Susp.cong-≃ ↑≃) y))
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((from b ∘ to b ∘ f) ∘_) left-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                    ≡⟨ cong (flip trans _) $ cong sym $ cong (flip trans _) $
                                                                        cong-from-ext≡-inj₂ b f y ⟩
        trans
          (sym $
           trans
             (trans
                (ext≡
                   {x = inj₂ x}
                   {y = Susp.map (lift {ℓ = ℓ}) (Susp.map lower y)}
                   {g = from b ∘ to b ∘ f ∘
                        Susp.map (lift {ℓ = ℓ}) ∘ Susp.map lower})
                (cong (from b ∘ to b ∘ f ∘ Susp.map (lift {ℓ = ℓ})) $
                 _≃_.right-inverse-of (Susp.cong-≃ ↑≃)
                   (Susp.map lower y)))
             (cong (from b ∘ to b ∘ f) $
              _≃_.left-inverse-of (Susp.cong-≃ ↑≃) y))
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((from b ∘ to b ∘ f) ∘_) left-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                    ≡⟨ cong (flip trans _) $ cong sym $
                                                                        cong₂ trans
                                                                          (cong (trans _) $
                                                                           trans (sym $ cong-∘ _ _ _) $
                                                                           cong (cong (from b ∘ to b ∘ f)) $
                                                                           trans (_≃_.right-left-lemma (Susp.cong-≃ ↑≃) _)
                                                                           left-lemma)
                                                                          (cong (cong _) left-lemma) ⟩
        trans
          (sym $
           trans
             (trans
                (ext≡
                   {x = inj₂ x}
                   {y = Susp.map (lift {ℓ = ℓ}) (Susp.map lower y)}
                   {g = from b ∘ to b ∘ f ∘
                        Susp.map (lift {ℓ = ℓ}) ∘ Susp.map lower})
                (cong (from b ∘ to b ∘ f) $
                 ext⁻¹ left-eq
                   (Susp.map (lift {ℓ = ℓ}) (Susp.map lower y))))
             (cong (from b ∘ to b ∘ f) $ ext⁻¹ left-eq y))
          (trans
             (trans
                (cong (flip (ext (inj₂ x)) _) $
                 cong ((from b ∘ to b ∘ f) ∘_) left-eq)
                (cong (flip (ext (inj₂ x)) _) $ ⟨ext⟩ hyp))
             (ext≡ {x = inj₂ x} {y = y} {g = f}))                    ≡⟨ sym-ext≡-ext≡′ (from b ∘ to b) hyp ⟩∎

        hyp y                                                        ∎

      from-to : ∀ b x → from b (to b x) ≡ x
      from-to b = elim λ where
        .[]ʳ        → refl ∘ [_]
        .extʳ hyp _ → from-to-ext b _ _ hyp
        .ext≡ʳ hyp  → from-to-ext≡ b _ _ _ hyp

-- Nullification {A = ↑ ℓ A} (↑ ℓ ∘ P ∘ lower) (↑ ℓ B) is equivalent
-- to Nullification {A = A} P B.
--
-- This lemma could be replaced by
--
--   Nullification-cong
--     (Eq.↔⇒≃ B.↑↔) (λ _ → Eq.↔⇒≃ B.↑↔) (Eq.↔⇒≃ B.↑↔),
--
-- given a suitable implementation of Nullification-cong.

Nullification-↑-↑-≃ :
  Nullification {A = ↑ ℓ A} (↑ ℓ ∘ P ∘ lower) (↑ ℓ B) ≃
  Nullification {A = A} P B
Nullification-↑-↑-≃ =
  block λ b → Eq.↔→≃ (to b) (from b) (to-from b) (from-to b)
  where
  open Nullification-↑-↑-≃

_ :
  _≃_.to (Nullification-↑-↑-≃ {ℓ = ℓ} {P = P} {B = B}) ∘ [_] ≡
  [_] ∘ lower
_ = refl _

_ :
  _≃_.from (Nullification-↑-↑-≃ {ℓ = ℓ} {P = P} {B = B}) ∘ [_] ≡
  [_] ∘ lift
_ = refl _
