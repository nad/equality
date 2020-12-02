------------------------------------------------------------------------
-- Isomorphisms and equalities relating an arbitrary "equality with J"
-- to path equality, along with proofs of extensionality and
-- univalence for the "equality with J"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Equality.Path.Isomorphisms
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

import Bijection
import Embedding
import Equivalence
import Function-universe
import H-level
import Univalence-axiom

private
  module F  = Function-universe equality-with-J

  module PB = Bijection P.equality-with-J
  module PM = Embedding P.equality-with-J
  module PE = Equivalence P.equality-with-J
  module PF = Function-universe P.equality-with-J
  module PH = H-level P.equality-with-J
  module PU = Univalence-axiom P.equality-with-J

open Bijection equality-with-J using (_↔_)
open Embedding equality-with-J hiding (id; _∘_)
open Equivalence equality-with-J hiding (id; _∘_; inverse)
open F hiding (id; _∘_)
open H-level equality-with-J
open Univalence-axiom equality-with-J

private
  variable
    a b c p q ℓ : Level
    A           : Type a
    B           : A → Type b
    u v x y z   : A
    f g h       : (x : A) → B x
    n           : ℕ

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

  ext-const :
    (x≡y : x ≡ y) →
    ⟨ext⟩ (const {B = A} x≡y) ≡ cong const x≡y
  ext-const = good-ext-const bad-ext

  cong-ext :
    ∀ (f≡g : ∀ x → f x ≡ g x) {x} →
    cong (_$ x) (⟨ext⟩ f≡g) ≡ f≡g x
  cong-ext = cong-good-ext bad-ext

  subst-ext :
    ∀ {f g : (x : A) → B x}
    (P : B x → Type p) {p} (f≡g : ∀ x → f x ≡ g x) →
    subst (λ f → P (f x)) (⟨ext⟩ f≡g) p ≡ subst P (f≡g x) p
  subst-ext = subst-good-ext bad-ext

  elim-ext :
    (P : B x → B x → Type p)
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

  ↔→↔ : {A B : Type ℓ} → A PB.↔ B → A ↔ B
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
  H-level (suc n) A                 ↝⟨ inverse $ ≡↔+ _ ext ⟩
  (∀ x y → H-level n (x ≡ y))       ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → H-level-cong ext _ ≡↔≡) ⟩
  (∀ x y → H-level n (x P.≡ y))     ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → H-level↔H-level n) ⟩
  (∀ x y → PH.H-level n (x P.≡ y))  ↝⟨ ↔→↔ $ PF.≡↔+ _ P.ext ⟩
  PH.H-level (suc n) A              □

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

-- The type of equivalences, expressed using equality, is isomorphic
-- to the type of equivalences, expressed using paths.

≃↔≃ :
  {A : Type a} {B : Type b} →
  A ≃ B ↔ A PE.≃ B
≃↔≃ {A = A} {B = B} =
  A ≃ B                ↝⟨ ≃-as-Σ ⟩
  ∃ Is-equivalence     ↝⟨ (∃-cong λ _ → Is-equivalence↔Is-equivalence) ⟩
  ∃ PE.Is-equivalence  ↝⟨ inverse $ ↔→↔ PE.≃-as-Σ ⟩□
  A PE.≃ B             □

private

  -- ≃↔≃ computes in the "right" way.

  to-≃↔≃ :
    {A : Type a} {B : Type b} {A≃B : A ≃ B} →
    PE._≃_.logical-equivalence (_↔_.to ≃↔≃ A≃B) ≡
    _≃_.logical-equivalence A≃B
  to-≃↔≃ = refl _

  from-≃↔≃ :
    {A : Type a} {B : Type b} {A≃B : A PE.≃ B} →
    _≃_.logical-equivalence (_↔_.from ≃↔≃ A≃B) ≡
    PE._≃_.logical-equivalence A≃B
  from-≃↔≃ = refl _

-- The cong function for paths can be expressed in terms of the cong
-- function for equality.

cong≡cong :
  {A : Type a} {B : Type b} {f : A → B} {x y : A} {x≡y : x P.≡ y} →
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

-- The sym function for paths can be expressed in terms of the sym
-- function for equality.

sym≡sym :
  {x≡y : x P.≡ y} →
  sym (_↔_.from ≡↔≡ x≡y) ≡ _↔_.from ≡↔≡ (P.sym x≡y)
sym≡sym {x≡y = x≡y} = P.elim₁
  (λ x≡y → sym (_↔_.from ≡↔≡ x≡y) ≡ _↔_.from ≡↔≡ (P.sym x≡y))
  (sym (_↔_.from ≡↔≡ P.refl)    ≡⟨ cong sym from-≡↔≡-refl ⟩
   sym (refl _)                 ≡⟨ sym-refl ⟩
   refl _                       ≡⟨ sym from-≡↔≡-refl ⟩
   _↔_.from ≡↔≡ P.refl          ≡⟨ cong (_↔_.from ≡↔≡) $ sym $ _↔_.from ≡↔≡ P.sym-refl ⟩∎
   _↔_.from ≡↔≡ (P.sym P.refl)  ∎)
  x≡y

-- The trans function for paths can be expressed in terms of the trans
-- function for equality.

trans≡trans :
  {x≡y : x P.≡ y} {y≡z : y P.≡ z} →
  trans (_↔_.from ≡↔≡ x≡y) (_↔_.from ≡↔≡ y≡z) ≡
  _↔_.from ≡↔≡ (P.trans x≡y y≡z)
trans≡trans {x≡y = x≡y} {y≡z = y≡z} = P.elim₁
  (λ x≡y → trans (_↔_.from ≡↔≡ x≡y) (_↔_.from ≡↔≡ y≡z) ≡
           _↔_.from ≡↔≡ (P.trans x≡y y≡z))
  (trans (_↔_.from ≡↔≡ P.refl) (_↔_.from ≡↔≡ y≡z)  ≡⟨ cong (flip trans _) from-≡↔≡-refl ⟩
   trans (refl _) (_↔_.from ≡↔≡ y≡z)               ≡⟨ trans-reflˡ _ ⟩
   _↔_.from ≡↔≡ y≡z                                ≡⟨ cong (_↔_.from ≡↔≡) $ sym $ _↔_.from ≡↔≡ $ P.trans-reflˡ _ ⟩∎
   _↔_.from ≡↔≡ (P.trans P.refl y≡z)               ∎)
  x≡y

-- The type of embeddings, expressed using equality, is isomorphic to
-- the type of embeddings, expressed using paths.

Embedding↔Embedding :
  {A : Type a} {B : Type b} →
  Embedding A B ↔ PM.Embedding A B
Embedding↔Embedding {A = A} {B = B} =
  Embedding A B                                   ↝⟨ Embedding-as-Σ ⟩
  (∃ λ f → ∀ x y → Is-equivalence (cong f))       ↔⟨ (∃-cong λ f → ∀-cong ext λ x → ∀-cong ext λ y →
                                                      _↔_.to (⇔↔≃ ext (propositional ext _) (propositional ext _)) $
                                                        record { to   = λ is → _≃_.is-equivalence $
                                                                               with-other-function
                                                                                 (
      x P.≡ y                                                                      ↔⟨ inverse ≡↔≡ ⟩
      x ≡ y                                                                        ↝⟨ ⟨ _ , is ⟩ ⟩
      f x ≡ f y                                                                    ↔⟨ ≡↔≡ ⟩□
      f x P.≡ f y                                                                  □)
                                                                                 (P.cong f)
                                                                                 (λ eq →
      _↔_.to ≡↔≡ (cong f (_↔_.from ≡↔≡ eq))                                         ≡⟨ cong (_↔_.to ≡↔≡) cong≡cong ⟩
      _↔_.to ≡↔≡ (_↔_.from ≡↔≡ (P.cong f eq))                                       ≡⟨ _↔_.right-inverse-of ≡↔≡ _ ⟩∎
      P.cong f eq                                                                   ∎)
                                                               ; from = λ is → _≃_.is-equivalence $
                                                                               with-other-function
                                                                                 (
      x ≡ y                                                                        ↔⟨ ≡↔≡ ⟩
      x P.≡ y                                                                      ↝⟨ ⟨ _ , is ⟩ ⟩
      f x P.≡ f y                                                                  ↔⟨ inverse ≡↔≡ ⟩□
      f x ≡ f y                                                                    □)
                                                                                 (cong f)
                                                                                 (λ eq →
      _↔_.from ≡↔≡ (P.cong f (_↔_.to ≡↔≡ eq))                                       ≡⟨ sym cong≡cong ⟩
      cong f (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ eq))                                         ≡⟨ cong (cong f) $ _↔_.left-inverse-of ≡↔≡ _ ⟩∎
      cong f eq                                                                     ∎)
                                                               }) ⟩
  (∃ λ f → ∀ x y → Is-equivalence (P.cong f))     ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → Is-equivalence↔Is-equivalence) ⟩
  (∃ λ f → ∀ x y → PE.Is-equivalence (P.cong f))  ↝⟨ inverse $ ↔→↔ PM.Embedding-as-Σ ⟩□
  PM.Embedding A B                                □

-- The subst function for paths can be expressed in terms of the subst
-- function for equality.

subst≡subst :
  ∀ {P : A → Type p} {x≡y : x P.≡ y} {p} →
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
  ∀ {P : A → Type p} {p : P x} →
  subst≡subst {x≡y = P.refl} ≡
  trans (cong (λ eq → subst P eq p) from-≡↔≡-refl)
    (trans (subst-refl _ _) (sym $ _↔_.from ≡↔≡ $ P.subst-refl P _))
subst≡subst-refl {P = P} = cong (λ f → f {p = _}) $ _↔_.from ≡↔≡ $
  P.elim-refl
    (λ x≡y → ∀ {p} → subst P (_↔_.from ≡↔≡ x≡y) p ≡ P.subst P x≡y p)
    (λ _ → trans (cong (λ eq → subst P eq _) from-≡↔≡-refl)
             (trans (subst-refl _ _)
                (sym $ _↔_.from ≡↔≡ $ P.subst-refl P _)))

-- Some corollaries.

subst≡↔subst≡ :
  ∀ {eq : x P.≡ y} →
  subst B (_↔_.from ≡↔≡ eq) u ≡ v ↔
  P.subst B eq u P.≡ v
subst≡↔subst≡ {B = B} {u = u} {v = v} {eq = eq} =
  subst B (_↔_.from ≡↔≡ eq) u ≡ v  ↝⟨ ≡⇒↝ _ $ cong (_≡ _) subst≡subst ⟩
  P.subst B eq u ≡ v               ↝⟨ ≡↔≡ ⟩□
  P.subst B eq u P.≡ v             □

subst≡↔[]≡ :
  {eq : x P.≡ y} →
  subst B (_↔_.from ≡↔≡ eq) u ≡ v ↔
  P.[ (λ i → B (eq i)) ] u ≡ v
subst≡↔[]≡ {B = B} {u = u} {v = v} {eq = eq} =
  subst B (_↔_.from ≡↔≡ eq) u ≡ v  ↝⟨ subst≡↔subst≡ ⟩
  P.subst B eq u P.≡ v             ↝⟨ ↔→↔ $ PB.inverse $ P.heterogeneous↔homogeneous _ ⟩□
  P.[ (λ i → B (eq i)) ] u ≡ v     □

-- The dcong function for paths can be expressed using dcong for
-- equality (up to pointwise equality).

dcong≡dcong :
  {f : (x : A) → B x} {x≡y : x P.≡ y} →
  _↔_.to subst≡↔subst≡ (dcong f (_↔_.from ≡↔≡ x≡y)) ≡
  P.dcong f x≡y
dcong≡dcong {B = B} {f = f} {x≡y} = P.elim
  (λ x≡y → _↔_.to subst≡↔subst≡ (dcong f (_↔_.from ≡↔≡ x≡y)) ≡
           P.dcong f x≡y)
  (λ x →
     _↔_.to subst≡↔subst≡ (dcong f (_↔_.from ≡↔≡ P.refl))    ≡⟨⟩

     _↔_.to ≡↔≡ (_↔_.to (≡⇒↝ _ $ cong (_≡ _) subst≡subst) $
       dcong f (_↔_.from ≡↔≡ P.refl))                        ≡⟨ cong (_↔_.to ≡↔≡) $ lemma x ⟩

     _↔_.to ≡↔≡ (_↔_.from ≡↔≡ $ P.subst-refl B (f x))        ≡⟨ _↔_.right-inverse-of ≡↔≡ _ ⟩

     P.subst-refl B (f x)                                    ≡⟨ sym $ _↔_.from ≡↔≡ $ P.dcong-refl f ⟩∎

     P.dcong f P.refl                                        ∎)
  x≡y
  where
  lemma : ∀ _ → _
  lemma _ =
     _↔_.to (≡⇒↝ _ $ cong (_≡ _) subst≡subst)
       (dcong f (_↔_.from ≡↔≡ P.refl))                         ≡⟨ sym $ subst-in-terms-of-≡⇒↝ bijection _ _ _ ⟩

     subst (_≡ _) subst≡subst (dcong f (_↔_.from ≡↔≡ P.refl))  ≡⟨ cong (λ p → subst (_≡ _) p $ dcong f _) $ sym $ sym-sym _ ⟩

     subst (_≡ _) (sym $ sym subst≡subst)
       (dcong f (_↔_.from ≡↔≡ P.refl))                         ≡⟨ subst-trans _ ⟩

     trans (sym (subst≡subst {x≡y = P.refl}))
       (dcong f (_↔_.from ≡↔≡ P.refl))                         ≡⟨ cong (λ p → trans (sym p) (dcong f (_↔_.from ≡↔≡ P.refl)))
                                                                  subst≡subst-refl ⟩
     trans
       (sym $ trans (cong (λ eq → subst B eq _) from-≡↔≡-refl)
                (trans (subst-refl _ _)
                   (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
       (dcong f (_↔_.from ≡↔≡ P.refl))                         ≡⟨ elim₁ (λ {x} p →
                                                                           trans (sym $ trans (cong (λ eq → subst B eq _) p)
                                                                                          (trans (subst-refl _ _)
                                                                                             (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
                                                                             (dcong f x) ≡
                                                                           trans (sym $ trans (cong (λ eq → subst B eq _) (refl _))
                                                                                          (trans (subst-refl _ _)
                                                                                             (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
                                                                             (dcong f (refl _)))
                                                                        (refl _)
                                                                        from-≡↔≡-refl ⟩
     trans
       (sym $ trans (cong (λ eq → subst B eq _) (refl _))
                (trans (subst-refl _ _)
                   (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
       (dcong f (refl _))                                      ≡⟨ cong₂ (λ p → trans $ sym $ trans p $ trans (subst-refl _ _) $ sym $
                                                                                 _↔_.from ≡↔≡ $ P.subst-refl B _)
                                                                    (cong-refl _)
                                                                    (dcong-refl _) ⟩
     trans
       (sym $ trans (refl _)
                (trans (subst-refl _ _)
                   (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)))
       (subst-refl B _)                                        ≡⟨ cong (λ p → trans (sym p) (subst-refl _ _)) $ trans-reflˡ _ ⟩

     trans
       (sym $ trans (subst-refl _ _)
                (sym $ _↔_.from ≡↔≡ $ P.subst-refl B _))
       (subst-refl B _)                                        ≡⟨ cong (λ p → trans p (subst-refl _ _)) $ sym-trans _ _ ⟩

     trans
       (trans (sym $ sym $ _↔_.from ≡↔≡ $ P.subst-refl B _)
              (sym $ subst-refl _ _))
       (subst-refl B _)                                        ≡⟨ trans-[trans-sym]- _ _ ⟩

     sym $ sym $ _↔_.from ≡↔≡ $ P.subst-refl B _               ≡⟨ sym-sym _ ⟩∎

     _↔_.from ≡↔≡ $ P.subst-refl B _                           ∎

-- A lemma relating dcong and hcong (for paths).

dcong≡hcong :
  {x≡y : x P.≡ y} (f : (x : A) → B x) →
  dcong f (_↔_.from ≡↔≡ x≡y) ≡ _↔_.from subst≡↔[]≡ (P.hcong f x≡y)
dcong≡hcong {x≡y = x≡y} f =
  dcong f (_↔_.from ≡↔≡ x≡y)                                     ≡⟨ sym $ _↔_.from-to (inverse subst≡↔subst≡) dcong≡dcong ⟩

  _↔_.from subst≡↔subst≡ (P.dcong f x≡y)                         ≡⟨ cong (_↔_.from subst≡↔subst≡) $ _↔_.from ≡↔≡ $ P.dcong≡hcong f ⟩

  _↔_.from subst≡↔subst≡
    (PB._↔_.to (P.heterogeneous↔homogeneous _) (P.hcong f x≡y))  ≡⟨⟩

  _↔_.from subst≡↔[]≡ (P.hcong f x≡y)                            ∎

-- Three corollaries, intended to be used in the implementation of
-- eliminators for HITs. For some examples, see Interval and
-- Quotient.HIT.

subst≡→[]≡ :
  {eq : x P.≡ y} →
  subst B (_↔_.from ≡↔≡ eq) u ≡ v →
  P.[ (λ i → B (eq i)) ] u ≡ v
subst≡→[]≡ = _↔_.to subst≡↔[]≡

dcong-subst≡→[]≡ :
  {eq₁ : x P.≡ y} {eq₂ : subst B (_↔_.from ≡↔≡ eq₁) (f x) ≡ f y} →
  P.hcong f eq₁ ≡ subst≡→[]≡ eq₂ →
  dcong f (_↔_.from ≡↔≡ eq₁) ≡ eq₂
dcong-subst≡→[]≡ {B = B} {f = f} {eq₁} {eq₂} hyp =
  dcong f (_↔_.from ≡↔≡ eq₁)                   ≡⟨ dcong≡hcong f ⟩
  _↔_.from subst≡↔[]≡ (P.hcong f eq₁)          ≡⟨ cong (_↔_.from subst≡↔[]≡) hyp ⟩
  _↔_.from subst≡↔[]≡ (_↔_.to subst≡↔[]≡ eq₂)  ≡⟨ _↔_.left-inverse-of subst≡↔[]≡ _ ⟩∎
  eq₂                                          ∎

cong-≡↔≡ :
  {eq₁ : x P.≡ y} {eq₂ : f x ≡ f y} →
  P.cong f eq₁ ≡ _↔_.to ≡↔≡ eq₂ →
  cong f (_↔_.from ≡↔≡ eq₁) ≡ eq₂
cong-≡↔≡ {f = f} {eq₁ = eq₁} {eq₂} hyp =
  cong f (_↔_.from ≡↔≡ eq₁)      ≡⟨ cong≡cong ⟩
  _↔_.from ≡↔≡ $ P.cong f eq₁    ≡⟨ cong (_↔_.from ≡↔≡) hyp ⟩
  _↔_.from ≡↔≡ $ _↔_.to ≡↔≡ eq₂  ≡⟨ _↔_.left-inverse-of ≡↔≡ _ ⟩∎
  eq₂                            ∎

------------------------------------------------------------------------
-- Univalence

-- Univalence′ expressed using equality is equivalent to Univalence′
-- expressed using paths.

Univalence′≃Univalence′ :
  {A B : Type ℓ} →
  Univalence′ A B ≃ PU.Univalence′ A B
Univalence′≃Univalence′ {ℓ = ℓ} {A = A} {B = B} =
  ((A≃B : A ≃ B) → ∃ λ (x : ∃ λ A≡B → ≡⇒≃ A≡B ≡ A≃B) → ∀ y → x ≡ y)  ↝⟨ Π-cong ext ≃-as-Σ (λ _ → F.id) ⟩

  ((A≃B : ∃ λ (f : A → B) → Is-equivalence f) →
   ∃ λ (x : ∃ λ A≡B → ≡⇒≃ A≡B ≡ _↔_.from ≃-as-Σ A≃B) →
   ∀ y → x ≡ y)                                                      ↝⟨ (Π-cong ext (∃-cong λ _ → Is-equivalence↔Is-equivalence) λ A≃B →
                                                                         Σ-cong (lemma₁ A≃B) λ _ →
                                                                         Π-cong ext (lemma₁ A≃B) λ _ →
                                                                         inverse $ ≃-≡ (lemma₁ A≃B)) ⟩
  ((A≃B : ∃ λ (f : A → B) → PE.Is-equivalence f) →
   ∃ λ (x : ∃ λ A≡B → PU.≡⇒≃ A≡B ≡ PB._↔_.from PE.≃-as-Σ A≃B) →
   ∀ y → x ≡ y)                                                      ↔⟨ ↔→↔ $ PF.Π-cong P.ext (PF.inverse PE.≃-as-Σ) (λ _ → PF.id) ⟩

  ((A≃B : A PE.≃ B) →
   ∃ λ (x : ∃ λ A≡B → PU.≡⇒≃ A≡B ≡ A≃B) → ∀ y → x ≡ y)               ↔⟨ Is-equivalence↔Is-equivalence ⟩□

  ((A≃B : A PE.≃ B) →
   ∃ λ (x : ∃ λ A≡B → PU.≡⇒≃ A≡B P.≡ A≃B) → ∀ y → x P.≡ y)           □
  where
  lemma₃ :
    (A≡B : A ≡ B) →
    _↔_.to ≃↔≃ (≡⇒≃ A≡B) ≡ PU.≡⇒≃ (_↔_.to ≡↔≡ A≡B)
  lemma₃ = elim¹
    (λ A≡B → _↔_.to ≃↔≃ (≡⇒≃ A≡B) ≡ PU.≡⇒≃ (_↔_.to ≡↔≡ A≡B))
    (_↔_.to ≃↔≃ (≡⇒≃ (refl _))     ≡⟨ cong (_↔_.to ≃↔≃) ≡⇒≃-refl ⟩
     _↔_.to ≃↔≃ F.id               ≡⟨ _↔_.from ≡↔≡ $ PE.lift-equality P.ext P.refl ⟩
     PE.id                         ≡⟨ sym $ _↔_.from ≡↔≡ PU.≡⇒≃-refl ⟩
     PU.≡⇒≃ P.refl                 ≡⟨ sym $ cong PU.≡⇒≃ to-≡↔≡-refl ⟩∎
     PU.≡⇒≃ (_↔_.to ≡↔≡ (refl _))  ∎)

  lemma₂ : ∀ _ _ → _ ≃ _
  lemma₂ A≡B (f , f-eq) =
    ≡⇒≃ A≡B ≡ ⟨ f , f-eq ⟩                                ↝⟨ inverse $ ≃-≡ (↔⇒≃ ≃↔≃) ⟩

    _↔_.to ≃↔≃ (≡⇒≃ A≡B) ≡
    PE.⟨ f , _↔_.to Is-equivalence↔Is-equivalence f-eq ⟩  ↝⟨ ≡⇒≃ $ cong (_≡ PE.⟨ f , _↔_.to Is-equivalence↔Is-equivalence f-eq ⟩) $
                                                             lemma₃ A≡B ⟩□
    PU.≡⇒≃ (_↔_.to ≡↔≡ A≡B) ≡
    PE.⟨ f , _↔_.to Is-equivalence↔Is-equivalence f-eq ⟩  □

  lemma₁ :
    ∀ A≃B →
    (∃ λ A≡B → ≡⇒≃ A≡B ≡ _↔_.from ≃-as-Σ A≃B) ≃
    (∃ λ A≡B → PU.≡⇒≃ A≡B ≡
               PE.⟨ proj₁ A≃B
                  , _↔_.to Is-equivalence↔Is-equivalence (proj₂ A≃B)
                  ⟩)
  lemma₁ A≃B = Σ-cong ≡↔≡ λ A≡B → lemma₂ A≡B A≃B

-- Univalence expressed using equality is equivalent to univalence
-- expressed using paths.

Univalence≃Univalence : Univalence ℓ ≃ PU.Univalence ℓ
Univalence≃Univalence {ℓ = ℓ} =
  ({A B : Type ℓ} → Univalence′ A B)     ↝⟨ implicit-∀-cong ext $ implicit-∀-cong ext Univalence′≃Univalence′ ⟩□
  ({A B : Type ℓ} → PU.Univalence′ A B)  □

-- Univalence.

univ : ∀ {ℓ} → Univalence ℓ
univ = _≃_.from Univalence≃Univalence P.univ

-- Propositional extensionality.

prop-ext : ∀ {ℓ} → Propositional-extensionality ℓ
prop-ext =
  _≃_.from
    (Propositional-extensionality-is-univalence-for-propositions ext)
    (λ _ _ → univ)
