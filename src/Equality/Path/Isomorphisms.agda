------------------------------------------------------------------------
-- Isomorphisms and equalities relating an arbitrary "equality with J"
-- to path equality, along with proofs of extensionality and
-- univalence for the "equality with J"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Equality

module Equality.Path.Isomorphisms
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Equality.Instances-related
import Equality.Path as P
open import Prelude

import Bijection
import Equivalence
import Function-universe
import H-level
import Univalence-axiom

open Bijection eq using (_↔_)
open Equivalence eq hiding (id; _∘_; inverse)
open Function-universe eq hiding (id; _∘_)
open H-level eq
open Univalence-axiom eq

private
  module PB = Bijection P.equality-with-J
  module PE = Equivalence P.equality-with-J
  module PF = Function-universe P.equality-with-J
  module PH = H-level P.equality-with-J
  module PU = Univalence-axiom P.equality-with-J

private
  variable
    a b c p q ℓ : Level
    A           : Set a
    B           : A → Set b
    u v x y z   : A
    f g h       : (x : A) → B x
    n           : ℕ

------------------------------------------------------------------------
-- An isomorphism

private

  ≡↔≡′ :
    ∃ λ (iso : {x y : A} → x ≡ y ↔ x P.≡ y) →
      (∀ {x} → _↔_.to   iso (refl x) P.≡ P.refl) ×
      (∀ {x} → _↔_.from iso P.refl     ≡ refl x)
  ≡↔≡′ = all-equality-types-isomorphic _ P.equality-with-J

-- Equality is pointwise isomorphic to path equality.

≡↔≡ : x ≡ y ↔ x P.≡ y
≡↔≡ = proj₁ ≡↔≡′

-- The isomorphism maps reflexivity to reflexivity.

to-≡↔≡-refl : _↔_.to ≡↔≡ (refl c) ≡ P.refl
to-≡↔≡-refl = _↔_.from ≡↔≡ $ proj₁ $ proj₂ ≡↔≡′

from-≡↔≡-refl : _↔_.from ≡↔≡ P.refl ≡ refl x
from-≡↔≡-refl = proj₂ $ proj₂ ≡↔≡′

------------------------------------------------------------------------
-- Extensionality

-- The proof bad-ext is perhaps not less "good" than ext (I don't
-- know), it is called this simply because it is not defined using
-- good-ext.

bad-ext : Extensionality a b
apply-ext bad-ext {f = f} {g = g} =
  (∀ x → f x ≡ g x)    ↝⟨ (λ p x → _↔_.to ≡↔≡ (p x)) ⟩
  (∀ x → f x P.≡ g x)  ↝⟨ P.apply-ext P.ext ⟩
  f P.≡ g              ↔⟨ inverse ≡↔≡ ⟩□
  f ≡ g                □

-- Extensionality.

ext : Extensionality a b
ext = good-ext bad-ext

⟨ext⟩ : Extensionality′ A B
⟨ext⟩ = apply-ext ext

abstract

  -- The function ⟨ext⟩ is an equivalence.

  ext-is-equivalence : Is-equivalence {A = ∀ x → f x ≡ g x} ⟨ext⟩
  ext-is-equivalence = good-ext-is-equivalence bad-ext

  -- Equality rearrangement lemmas for ⟨ext⟩.

  ext-refl : ⟨ext⟩ (λ x → refl (f x)) ≡ refl f
  ext-refl = good-ext-refl bad-ext _

  cong-ext :
    ∀ (f≡g : ∀ x → f x ≡ g x) {x} →
    cong (_$ x) (⟨ext⟩ f≡g) ≡ f≡g x
  cong-ext = cong-good-ext bad-ext

  subst-ext :
    ∀ {f g : (x : A) → B x}
    (P : B x → Set p) {p} (f≡g : ∀ x → f x ≡ g x) →
    subst (λ f → P (f x)) (⟨ext⟩ f≡g) p ≡ subst P (f≡g x) p
  subst-ext = subst-good-ext bad-ext

  elim-ext :
    (P : B x → B x → Set p)
    (p : (y : B x) → P y y)
    {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) →
    elim (λ {f g} _ → P (f x) (g x)) (p ∘ (_$ x)) (⟨ext⟩ f≡g) ≡
    elim (λ {x y} _ → P x y) p (f≡g x)
  elim-ext = elim-good-ext bad-ext

  -- I based the statements of the following three lemmas on code in
  -- the Lean Homotopy Type Theory Library with Jakob von Raumer and
  -- Floris van Doorn listed as authors. The file was claimed to have
  -- been ported from the Coq HoTT library. (The third lemma has later
  -- been generalised.)

  ext-sym :
    (f≡g : ∀ x → f x ≡ g x) →
    ⟨ext⟩ (sym ∘ f≡g) ≡ sym (⟨ext⟩ f≡g)
  ext-sym = good-ext-sym bad-ext

  ext-trans :
    (f≡g : ∀ x → f x ≡ g x) (g≡h : ∀ x → g x ≡ h x) →
    ⟨ext⟩ (λ x → trans (f≡g x) (g≡h x)) ≡ trans (⟨ext⟩ f≡g) (⟨ext⟩ g≡h)
  ext-trans = good-ext-trans bad-ext

  cong-post-∘-ext :
    (f≡g : ∀ x → f x ≡ g x) →
    cong (h ∘_) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (cong h ∘ f≡g)
  cong-post-∘-ext = cong-post-∘-good-ext bad-ext bad-ext

  cong-pre-∘-ext :
    (f≡g : ∀ x → f x ≡ g x) →
    cong (_∘ h) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (f≡g ∘ h)
  cong-pre-∘-ext = cong-pre-∘-good-ext bad-ext bad-ext

------------------------------------------------------------------------
-- More isomorphisms and related properties

private

  -- Bijections expressed using paths can be converted into bijections
  -- expressed using equality.

  ↔→↔ : {A B : Set ℓ} → A PB.↔ B → A ↔ B
  ↔→↔ A↔B = record
    { surjection = record
      { logical-equivalence = record
        { to   = PB._↔_.to   A↔B
        ; from = PB._↔_.from A↔B
        }
      ; right-inverse-of = _↔_.from ≡↔≡ ∘ PB._↔_.right-inverse-of A↔B
      }
    ; left-inverse-of = _↔_.from ≡↔≡ ∘ PB._↔_.left-inverse-of A↔B
    }

-- H-level expressed using equality is isomorphic to H-level expressed
-- using paths.

H-level↔H-level : ∀ n → H-level n A ↔ PH.H-level n A
H-level↔H-level {A = A} zero =
  H-level 0 A                    ↔⟨⟩
  (∃ λ (x : A) → ∀ y → x ≡ y)    ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ≡↔≡) ⟩
  (∃ λ (x : A) → ∀ y → x P.≡ y)  ↔⟨⟩
  PH.H-level 0 A                 □

H-level↔H-level {A = A} (suc n) =
  H-level (suc n) A                 ↔⟨⟩
  (∀ x y → H-level n (x ≡ y))       ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → H-level-cong ext _ ≡↔≡) ⟩
  (∀ x y → H-level n (x P.≡ y))     ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → H-level↔H-level n) ⟩
  (∀ x y → PH.H-level n (x P.≡ y))  ↔⟨⟩
  PH.H-level (suc n) A              □

abstract

  -- Is-equivalence expressed using equality is isomorphic to
  -- Is-equivalence expressed using paths.

  Is-equivalence↔Is-equivalence :
    Is-equivalence f ↔ PE.Is-equivalence f
  Is-equivalence↔Is-equivalence {f = f} =
    Is-equivalence f                            ↔⟨⟩
    (∀ y →   Contractible (∃ λ x → f x   ≡ y))  ↝⟨ (∀-cong ext λ _ → H-level-cong ext _ $ ∃-cong λ _ → ≡↔≡) ⟩
    (∀ y →   Contractible (∃ λ x → f x P.≡ y))  ↝⟨ (∀-cong ext λ _ → H-level↔H-level _) ⟩
    (∀ y → P.Contractible (∃ λ x → f x P.≡ y))  ↔⟨⟩
    PE.Is-equivalence f                         □

-- The cong function for paths can be expressed in terms of the cong
-- function for equality.

cong≡cong :
  {A : Set a} {B : Set b} {f : A → B} {x y : A} {x≡y : x P.≡ y} →
  cong f (_↔_.from ≡↔≡ x≡y) ≡ _↔_.from ≡↔≡ (P.cong f x≡y)
cong≡cong {f = f} {x≡y = x≡y} = P.elim
  (λ x≡y → cong f (_↔_.from ≡↔≡ x≡y) ≡ _↔_.from ≡↔≡ (P.cong f x≡y))
  (λ x →
     cong f (_↔_.from ≡↔≡ P.refl)    ≡⟨ cong (cong f) from-≡↔≡-refl ⟩
     cong f (refl x)                 ≡⟨ cong-refl _ ⟩
     refl (f x)                      ≡⟨ sym $ from-≡↔≡-refl ⟩
     _↔_.from ≡↔≡ P.refl             ≡⟨ cong (_↔_.from ≡↔≡) $ sym $ _↔_.from ≡↔≡ $ P.cong-refl f ⟩∎
     _↔_.from ≡↔≡ (P.cong f P.refl)  ∎)
  x≡y

-- The subst function for paths can be expressed in terms of the subst
-- function for equality.

subst≡subst :
  ∀ {P : A → Set p} {x≡y : x P.≡ y} {p} →
  subst P (_↔_.from ≡↔≡ x≡y) p ≡ P.subst P x≡y p
subst≡subst {P = P} {x≡y} = P.elim
  (λ x≡y → ∀ {p} → subst P (_↔_.from ≡↔≡ x≡y) p ≡ P.subst P x≡y p)
  (λ x {p} →
     subst P (_↔_.from ≡↔≡ P.refl) p  ≡⟨ cong (λ eq → subst P eq p) from-≡↔≡-refl ⟩
     subst P (refl x) p               ≡⟨ subst-refl _ _ ⟩
     p                                ≡⟨ sym $ _↔_.from ≡↔≡ $ P.subst-refl P _ ⟩∎
     P.subst P P.refl p               ∎)
  x≡y

-- A "computation" rule for subst≡subst.

subst≡subst-refl :
  ∀ {P : A → Set p} {p : P x} →
  subst≡subst {x≡y = P.refl} ≡
  trans (cong (λ eq → subst P eq p) from-≡↔≡-refl)
    (trans (subst-refl _ _) (sym $ _↔_.from ≡↔≡ $ P.subst-refl P _))
subst≡subst-refl {P = P} = cong (λ f → f {p = _}) $ _↔_.from ≡↔≡ $
  P.elim-refl
    (λ x≡y → ∀ {p} → subst P (_↔_.from ≡↔≡ x≡y) p ≡ P.subst P x≡y p)
    (λ _ → trans (cong (λ eq → subst P eq _) from-≡↔≡-refl)
             (trans (subst-refl _ _)
                (sym $ _↔_.from ≡↔≡ $ P.subst-refl P _)))

-- A corollary.

subst≡↔subst≡ :
  ∀ {eq : x P.≡ y} →
  subst B (_↔_.from ≡↔≡ eq) u ≡ v ↔
  P.subst B eq u P.≡ v
subst≡↔subst≡ {B = B} {u = u} {v = v} {eq = eq} =
  subst B (_↔_.from ≡↔≡ eq) u ≡ v  ↝⟨ ≡⇒↝ _ $ cong (_≡ _) subst≡subst ⟩
  P.subst B eq u ≡ v               ↝⟨ ≡↔≡ ⟩□
  P.subst B eq u P.≡ v             □

-- The dependent-cong function for paths can be expressed using
-- dependent-cong for equality.

dependent-cong≡dependent-cong :
  {f : (x : A) → B x} {x≡y : x P.≡ y} →
  _↔_.to subst≡↔subst≡ (dependent-cong f (_↔_.from ≡↔≡ x≡y)) ≡
  P.dependent-cong f x≡y
dependent-cong≡dependent-cong {B = B} {f = f} {x≡y} = P.elim
  (λ x≡y → _↔_.to subst≡↔subst≡
             (dependent-cong f (_↔_.from ≡↔≡ x≡y)) ≡
           P.dependent-cong f x≡y)
  (λ x →
     _↔_.to subst≡↔subst≡ (dependent-cong f (_↔_.from ≡↔≡ P.refl))  ≡⟨⟩

     _↔_.to ≡↔≡ (_↔_.to (≡⇒↝ _ $ cong (_≡ _) subst≡subst) $
       dependent-cong f (_↔_.from ≡↔≡ P.refl))                      ≡⟨ cong (_↔_.to ≡↔≡) $ lemma x ⟩

     _↔_.to ≡↔≡ (_↔_.from ≡↔≡ $ P.subst-refl B (f x))               ≡⟨ _↔_.right-inverse-of ≡↔≡ _ ⟩

     P.subst-refl B (f x)                                           ≡⟨ sym $ _↔_.from ≡↔≡ $ P.dependent-cong-refl f ⟩∎

     P.dependent-cong f P.refl                                      ∎)
  x≡y
  where
  lemma : ∀ _ → _
  lemma _ =
     _↔_.to (≡⇒↝ _ $ cong (_≡ _) subst≡subst)
       (dependent-cong f (_↔_.from ≡↔≡ P.refl))                         ≡⟨ sym $ subst-in-terms-of-≡⇒↝ bijection _ _ _ ⟩

     subst (_≡ _) subst≡subst (dependent-cong f (_↔_.from ≡↔≡ P.refl))  ≡⟨ cong (λ p → subst (_≡ _) p $ dependent-cong f _) $ sym $ sym-sym _ ⟩

     subst (_≡ _) (sym $ sym subst≡subst)
       (dependent-cong f (_↔_.from ≡↔≡ P.refl))                         ≡⟨ subst-trans _ ⟩

     trans (sym (subst≡subst {x≡y = P.refl}))
       (dependent-cong f (_↔_.from ≡↔≡ P.refl))                         ≡⟨ cong (λ p → trans (sym p) (dependent-cong f (_↔_.from ≡↔≡ P.refl)))
                                                                           subst≡subst-refl ⟩
     trans
       (sym $ trans (cong (λ eq → subst B eq _) from-≡↔≡-refl)
                (trans (subst-refl _ _)
                   (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
       (dependent-cong f (_↔_.from ≡↔≡ P.refl))                         ≡⟨ elim₁ (λ {x} p →
                                                                                    trans (sym $ trans (cong (λ eq → subst B eq _) p)
                                                                                                   (trans (subst-refl _ _)
                                                                                                      (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
                                                                                      (dependent-cong f x) ≡
                                                                                    trans (sym $ trans (cong (λ eq → subst B eq _) (refl _))
                                                                                                   (trans (subst-refl _ _)
                                                                                                      (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
                                                                                      (dependent-cong f (refl _)))
                                                                                 (refl _)
                                                                                 from-≡↔≡-refl ⟩
     trans
       (sym $ trans (cong (λ eq → subst B eq _) (refl _))
                (trans (subst-refl _ _)
                   (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
       (dependent-cong f (refl _))                                      ≡⟨ cong₂ (λ p → trans $ sym $ trans p $ trans (subst-refl _ _) $ sym $
                                                                                          _↔_.from ≡↔≡ $ P.subst-refl B _)
                                                                             (cong-refl _)
                                                                             (dependent-cong-refl _) ⟩
     trans
       (sym $ trans (refl _)
                (trans (subst-refl _ _)
                   (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
       (subst-refl B _)                                                 ≡⟨ cong (λ p → trans (sym p) (subst-refl _ _)) $ trans-reflˡ _ ⟩

     trans
       (sym $ trans (subst-refl _ _)
                (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _))
       (subst-refl B _)                                                 ≡⟨ cong (λ p → trans p (subst-refl _ _)) $ sym-trans _ _ ⟩

     trans
       (trans (sym $ sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)
              (sym $ subst-refl _ _))
       (subst-refl B _)                                                 ≡⟨ trans-[trans-sym]- _ _ ⟩

     sym $ sym $ _↔_.from ≡↔≡ $ P.subst-refl B _                        ≡⟨ sym-sym _ ⟩∎

     _↔_.from ≡↔≡ $ P.subst-refl B _                                    ∎

-- Three corollaries, intended to be used in the implementation of
-- eliminators for HITs. For some examples, see Interval and
-- Quotient.HIT.

subst≡→[]≡ :
  {eq : x P.≡ y} →
  subst B (_↔_.from ≡↔≡ eq) u ≡ v →
  P.[ (λ i → B (eq i)) ] u ≡ v
subst≡→[]≡ {B = B} {u = u} {v = v} {eq = eq} =
  subst B (_↔_.from ≡↔≡ eq) u ≡ v  ↝⟨ _↔_.to subst≡↔subst≡ ⟩
  P.subst B eq u P.≡ v             ↝⟨ PB._↔_.from (P.heterogeneous↔homogeneous _) ⟩□
  P.[ (λ i → B (eq i)) ] u ≡ v     □

dependent-cong-subst≡→[]≡ :
  {eq₁ : x P.≡ y} {eq₂ : subst B (_↔_.from ≡↔≡ eq₁) (f x) ≡ f y} →
  P.hcong f eq₁ ≡ subst≡→[]≡ eq₂ →
  dependent-cong f (_↔_.from ≡↔≡ eq₁) ≡ eq₂
dependent-cong-subst≡→[]≡ {B = B} {f = f} {eq₁} {eq₂} hyp =
  dependent-cong f (_↔_.from ≡↔≡ eq₁)                         ≡⟨ sym $ _↔_.left-inverse-of subst≡↔subst≡ _ ⟩

  _↔_.from subst≡↔subst≡ $ _↔_.to subst≡↔subst≡ $
    dependent-cong f (_↔_.from ≡↔≡ eq₁)                       ≡⟨ cong (_↔_.from subst≡↔subst≡) dependent-cong≡dependent-cong ⟩

  _↔_.from subst≡↔subst≡ $ P.dependent-cong f eq₁             ≡⟨⟩

  _↔_.from subst≡↔subst≡ $ PB._↔_.to h↔h $ P.hcong f eq₁      ≡⟨ cong (_↔_.from subst≡↔subst≡ ∘ PB._↔_.to h↔h) hyp ⟩

  _↔_.from subst≡↔subst≡ $ PB._↔_.to h↔h $ PB._↔_.from h↔h $
    _↔_.to subst≡↔subst≡ eq₂                                  ≡⟨ cong (_↔_.from subst≡↔subst≡) $ _↔_.from ≡↔≡ $
                                                                 PB._↔_.right-inverse-of h↔h _ ⟩

  _↔_.from subst≡↔subst≡ $ _↔_.to subst≡↔subst≡ eq₂           ≡⟨ _↔_.left-inverse-of subst≡↔subst≡ _ ⟩∎

  eq₂                                                         ∎
  where
  h↔h = P.heterogeneous↔homogeneous (λ i → B (eq₁ i))

cong-≡↔≡ :
  {eq₁ : x P.≡ y} {eq₂ : f x ≡ f y} →
  P.cong f eq₁ ≡ _↔_.to ≡↔≡ eq₂ →
  cong f (_↔_.from ≡↔≡ eq₁) ≡ eq₂
cong-≡↔≡ {f = f} {eq₁ = eq₁} {eq₂} hyp =
  cong f (_↔_.from ≡↔≡ eq₁)      ≡⟨ cong≡cong ⟩
  _↔_.from ≡↔≡ $ P.cong f eq₁    ≡⟨ cong (_↔_.from ≡↔≡) hyp ⟩
  _↔_.from ≡↔≡ $ _↔_.to ≡↔≡ eq₂  ≡⟨ _↔_.left-inverse-of ≡↔≡ _ ⟩∎
  eq₂                            ∎

-- There is an isomorphism between Is-proposition A (as defined using
-- equality) and Proof-irrelevant A (as defined using paths).

propositional↔irrelevant :
  Is-proposition A ↔ P.Proof-irrelevant A
propositional↔irrelevant {A = A} =
  Is-proposition A      ↝⟨ H-level↔H-level _ ⟩
  PH.Is-proposition A   ↝⟨ ↔→↔ $ PE._≃_.bijection $ PF.propositional≃irrelevant P.ext ⟩□
  P.Proof-irrelevant A  □

-- There is an isomorphism between Is-set A (as defined using
-- equality) and Uniqueness-of-identity-proofs A (as defined using
-- paths).

set↔UIP : Is-set A ↔ P.Uniqueness-of-identity-proofs A
set↔UIP {A = A} =
  Is-set A                           ↝⟨ H-level↔H-level _ ⟩
  PH.Is-set A                        ↝⟨ ↔→↔ $ PE._≃_.bijection $ PF.set≃UIP P.ext ⟩□
  P.Uniqueness-of-identity-proofs A  □

------------------------------------------------------------------------
-- Univalence

-- Univalence.

univ : ∀ {ℓ} → Univalence ℓ
univ {ℓ} {A = A} {B = B} = lemma P.univ
  where
  lemma₄ : {A B : Set ℓ} → (A PE.≃ B) ≃ (A ≃ B)
  lemma₄ {A} {B} =
    A PE.≃ B                       ↔⟨ ↔→↔ PE.≃-as-Σ ⟩
    (∃ λ f → PE.Is-equivalence f)  ↔⟨ ∃-cong (λ _ → inverse Is-equivalence↔Is-equivalence) ⟩
    (∃ λ f → Is-equivalence f)     ↔⟨ inverse ≃-as-Σ ⟩□
    A ≃ B                          □

  lemma₃ : ∀ A≡B → _≃_.to lemma₄ (PU.≡⇒≃ A≡B) ≡ ≡⇒≃ (_↔_.from ≡↔≡ A≡B)
  lemma₃ = P.elim¹
    (λ A≡B → _≃_.to lemma₄ (PU.≡⇒≃ A≡B) ≡ ≡⇒≃ (_↔_.from ≡↔≡ A≡B))
    (_≃_.to lemma₄ (PU.≡⇒≃ P.refl)  ≡⟨ cong (_≃_.to lemma₄) (_↔_.from ≡↔≡ PU.≡⇒≃-refl) ⟩
     _≃_.to lemma₄ PE.id            ≡⟨ lift-equality ext (refl _) ⟩
     Equivalence.id eq              ≡⟨ sym ≡⇒≃-refl ⟩
     ≡⇒≃ (refl _)                   ≡⟨ sym $ cong ≡⇒≃ from-≡↔≡-refl ⟩∎
     ≡⇒≃ (_↔_.from ≡↔≡ P.refl)      ∎)

  lemma₂ : ∀ _ _ → _ ≃ _
  lemma₂ A≡B (f , f-eq) =
    PU.≡⇒≃ A≡B ≡ PE.⟨ f , f-eq ⟩                         ↝⟨ inverse $ ≃-≡ lemma₄ ⟩

    _≃_.to lemma₄ (PU.≡⇒≃ A≡B) ≡
    ⟨ f , _↔_.from Is-equivalence↔Is-equivalence f-eq ⟩  ↝⟨ ≡⇒≃ $ cong (_≡ ⟨ f , _↔_.from Is-equivalence↔Is-equivalence f-eq ⟩) $
                                                            lemma₃ A≡B ⟩□
    ≡⇒≃ (_↔_.from ≡↔≡ A≡B) ≡
    ⟨ f , _↔_.from Is-equivalence↔Is-equivalence f-eq ⟩  □

  lemma₁ :
    ∀ A≃B →
    (∃ λ A≡B → PU.≡⇒≃ A≡B ≡ PB._↔_.from PE.≃-as-Σ A≃B) ≃
    (∃ λ A≡B → ≡⇒≃ A≡B ≡
               ⟨ proj₁ A≃B
               , _↔_.from Is-equivalence↔Is-equivalence (proj₂ A≃B)
               ⟩)
  lemma₁ A≃B = Σ-cong (inverse ≡↔≡) λ A≡B → lemma₂ A≡B A≃B

  lemma =
    ((A≃B : A PE.≃ B) →
     ∃ λ (x : ∃ λ A≡B → PU.≡⇒≃ A≡B P.≡ A≃B) → ∀ y → x P.≡ y)           ↔⟨ inverse Is-equivalence↔Is-equivalence ⟩

    ((A≃B : A PE.≃ B) →
     ∃ λ (x : ∃ λ A≡B → PU.≡⇒≃ A≡B ≡ A≃B) → ∀ y → x ≡ y)               ↝⟨ PF.Π-cong _ PE.≃-as-Σ (λ _ → id) ⟩

    ((A≃B : ∃ λ (f : A → B) → PE.Is-equivalence f) →
     ∃ λ (x : ∃ λ A≡B → PU.≡⇒≃ A≡B ≡ PB._↔_.from PE.≃-as-Σ A≃B) →
     ∀ y → x ≡ y)                                                      ↝⟨ Π-cong _ (∃-cong λ _ → inverse Is-equivalence↔Is-equivalence) (λ A≃B →
                                                                          Σ-cong (lemma₁ A≃B) λ _ →
                                                                          Π-cong _ (lemma₁ A≃B) λ _ →
                                                                          cong (_≃_.to (lemma₁ A≃B))) ⟩
    ((A≃B : ∃ λ (f : A → B) → Is-equivalence f) →
     ∃ λ (x : ∃ λ A≡B → ≡⇒≃ A≡B ≡ _↔_.from ≃-as-Σ A≃B) →
     ∀ y → x ≡ y)                                                      ↝⟨ Π-cong _ (inverse ≃-as-Σ) (λ _ → id) ⟩□

    ((A≃B : A ≃ B) → ∃ λ (x : ∃ λ A≡B → ≡⇒≃ A≡B ≡ A≃B) → ∀ y → x ≡ y)  □

-- Propositional extensionality.

prop-ext : ∀ {ℓ} → Propositional-extensionality ℓ
prop-ext =
  _≃_.from
    (Propositional-extensionality-is-univalence-for-propositions ext)
    (λ _ _ → univ)
