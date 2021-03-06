------------------------------------------------------------------------
-- Isomorphisms and equalities relating an arbitrary "equality with J"
-- to path equality, along with a proof of extensionality for the
-- "equality with J"
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
import Equivalence.Contractible-preimages
import Equivalence.Half-adjoint
import Function-universe
import H-level
import Surjection
import Univalence-axiom

private
  module B  = Bijection equality-with-J
  module CP = Equivalence.Contractible-preimages equality-with-J
  module HA = Equivalence.Half-adjoint equality-with-J
  module Eq = Equivalence equality-with-J
  module F  = Function-universe equality-with-J

  module PB  = Bijection P.equality-with-J
  module PM  = Embedding P.equality-with-J
  module PE  = Equivalence P.equality-with-J
  module PCP = Equivalence.Contractible-preimages P.equality-with-J
  module PHA = Equivalence.Half-adjoint P.equality-with-J
  module PF  = Function-universe P.equality-with-J
  module PH  = H-level P.equality-with-J
  module PS  = Surjection P.equality-with-J
  module PU  = Univalence-axiom P.equality-with-J

open B using (_↔_)
open Embedding equality-with-J hiding (id; _∘_)
open Eq using (_≃_; Is-equivalence)
open F hiding (id; _∘_)
open H-level equality-with-J
open Surjection equality-with-J using (_↠_)
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
ext = Eq.good-ext bad-ext

⟨ext⟩ : Extensionality′ A B
⟨ext⟩ = apply-ext ext

abstract

  -- The function ⟨ext⟩ is an equivalence.

  ext-is-equivalence : Is-equivalence {A = ∀ x → f x ≡ g x} ⟨ext⟩
  ext-is-equivalence = Eq.good-ext-is-equivalence bad-ext

  -- Equality rearrangement lemmas for ⟨ext⟩.

  ext-refl : ⟨ext⟩ (λ x → refl (f x)) ≡ refl f
  ext-refl = Eq.good-ext-refl bad-ext _

  ext-const :
    (x≡y : x ≡ y) →
    ⟨ext⟩ (const {B = A} x≡y) ≡ cong const x≡y
  ext-const = Eq.good-ext-const bad-ext

  cong-ext :
    ∀ (f≡g : ∀ x → f x ≡ g x) {x} →
    cong (_$ x) (⟨ext⟩ f≡g) ≡ f≡g x
  cong-ext = Eq.cong-good-ext bad-ext

  subst-ext :
    ∀ {f g : (x : A) → B x}
    (P : B x → Type p) {p} (f≡g : ∀ x → f x ≡ g x) →
    subst (λ f → P (f x)) (⟨ext⟩ f≡g) p ≡ subst P (f≡g x) p
  subst-ext = Eq.subst-good-ext bad-ext

  elim-ext :
    (P : B x → B x → Type p)
    (p : (y : B x) → P y y)
    {f g : (x : A) → B x}
    (f≡g : ∀ x → f x ≡ g x) →
    elim (λ {f g} _ → P (f x) (g x)) (p ∘ (_$ x)) (⟨ext⟩ f≡g) ≡
    elim (λ {x y} _ → P x y) p (f≡g x)
  elim-ext = Eq.elim-good-ext bad-ext

  -- I based the statements of the following three lemmas on code in
  -- the Lean Homotopy Type Theory Library with Jakob von Raumer and
  -- Floris van Doorn listed as authors. The file was claimed to have
  -- been ported from the Coq HoTT library. (The third lemma has later
  -- been generalised.)

  ext-sym :
    (f≡g : ∀ x → f x ≡ g x) →
    ⟨ext⟩ (sym ∘ f≡g) ≡ sym (⟨ext⟩ f≡g)
  ext-sym = Eq.good-ext-sym bad-ext

  ext-trans :
    (f≡g : ∀ x → f x ≡ g x) (g≡h : ∀ x → g x ≡ h x) →
    ⟨ext⟩ (λ x → trans (f≡g x) (g≡h x)) ≡ trans (⟨ext⟩ f≡g) (⟨ext⟩ g≡h)
  ext-trans = Eq.good-ext-trans bad-ext

  cong-post-∘-ext :
    (f≡g : ∀ x → f x ≡ g x) →
    cong (h ∘_) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (cong h ∘ f≡g)
  cong-post-∘-ext = Eq.cong-post-∘-good-ext bad-ext bad-ext

  cong-pre-∘-ext :
    (f≡g : ∀ x → f x ≡ g x) →
    cong (_∘ h) (⟨ext⟩ f≡g) ≡ ⟨ext⟩ (f≡g ∘ h)
  cong-pre-∘-ext = Eq.cong-pre-∘-good-ext bad-ext bad-ext

  cong-∘-ext :
    {A : Type a} {B : Type b} {C : Type c} {f g : B → C}
    (f≡g : ∀ x → f x ≡ g x) →
    cong {B = (A → B) → (A → C)}
         (λ f → f ∘_) (⟨ext⟩ f≡g) ≡
    ⟨ext⟩ λ h → ⟨ext⟩ λ x → f≡g (h x)
  cong-∘-ext = Eq.cong-∘-good-ext bad-ext bad-ext bad-ext

------------------------------------------------------------------------
-- More isomorphisms and related properties

-- Split surjections expressed using equality are equivalent to split
-- surjections expressed using paths.

↠≃↠ :
  {A : Type a} {B : Type b} →
  (A ↠ B) ≃ (A PS.↠ B)
↠≃↠ = Eq.↔→≃
  (λ A↠B → record
     { logical-equivalence = _↠_.logical-equivalence A↠B
     ; right-inverse-of    = _↔_.to ≡↔≡ ∘ _↠_.right-inverse-of A↠B
     })
  (λ A↠B → record
     { logical-equivalence = PS._↠_.logical-equivalence A↠B
     ; right-inverse-of    = _↔_.from ≡↔≡ ∘ PS._↠_.right-inverse-of A↠B
     })
  (λ A↠B →
     cong (λ r → record
             { logical-equivalence = PS._↠_.logical-equivalence A↠B
             ; right-inverse-of    = r
             }) $
     ⟨ext⟩ λ _ → _↔_.right-inverse-of ≡↔≡ _)
  (λ A↠B →
     cong (λ r → record
             { logical-equivalence = _↠_.logical-equivalence A↠B
             ; right-inverse-of    = r
             }) $
     ⟨ext⟩ λ _ → _↔_.left-inverse-of ≡↔≡ _)

private

  -- Bijections expressed using paths can be converted into bijections
  -- expressed using equality.

  ↔→↔ : {A B : Type ℓ} → A PB.↔ B → A ↔ B
  ↔→↔ A↔B = record
    { surjection      = _≃_.from ↠≃↠ $ PB._↔_.surjection      A↔B
    ; left-inverse-of = _↔_.from ≡↔≡ ∘ PB._↔_.left-inverse-of A↔B
    }

-- Bijections expressed using equality are equivalent to bijections
-- expressed using paths.

↔≃↔ :
  {A : Type a} {B : Type b} →
  (A ↔ B) ≃ (A PB.↔ B)
↔≃↔ {A = A} {B = B} =
  A ↔ B                                                 ↔⟨ B.↔-as-Σ ⟩

  (∃ λ (f : A → B) → ∃ λ (f⁻¹ : B → A) →
    (∀ x → f (f⁻¹ x) ≡ x) × (∀ x → f⁻¹ (f x) ≡ x))      ↔⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                            (∀-cong ext λ _ → ≡↔≡)
                                                              ×-cong
                                                            (∀-cong ext λ _ → ≡↔≡)) ⟩
  (∃ λ (f : A → B) → ∃ λ (f⁻¹ : B → A) →
    (∀ x → f (f⁻¹ x) P.≡ x) × (∀ x → f⁻¹ (f x) P.≡ x))  ↔⟨ inverse $ ↔→↔ $ PB.↔-as-Σ ⟩□

  A PB.↔ B                                              □

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

-- CP.Is-equivalence is isomorphic to PCP.Is-equivalence.

Is-equivalence-CP↔Is-equivalence-CP :
  CP.Is-equivalence f ↔ PCP.Is-equivalence f
Is-equivalence-CP↔Is-equivalence-CP {f = f} =
  CP.Is-equivalence f                         ↔⟨⟩
  (∀ y →   Contractible (∃ λ x → f x   ≡ y))  ↝⟨ (∀-cong ext λ _ → H-level-cong ext _ $ ∃-cong λ _ → ≡↔≡) ⟩
  (∀ y →   Contractible (∃ λ x → f x P.≡ y))  ↝⟨ (∀-cong ext λ _ → H-level↔H-level _) ⟩
  (∀ y → P.Contractible (∃ λ x → f x P.≡ y))  ↔⟨⟩
  PCP.Is-equivalence f                        □

-- Is-equivalence expressed using equality is isomorphic to
-- Is-equivalence expressed using paths.

Is-equivalence↔Is-equivalence :
  Is-equivalence f ↔ PE.Is-equivalence f
Is-equivalence↔Is-equivalence {f = f} =
  Is-equivalence f      ↝⟨ HA.Is-equivalence↔Is-equivalence-CP ext ⟩
  CP.Is-equivalence f   ↝⟨ Is-equivalence-CP↔Is-equivalence-CP ⟩
  PCP.Is-equivalence f  ↝⟨ inverse $ ↔→↔ $ PHA.Is-equivalence↔Is-equivalence-CP P.ext ⟩□
  PE.Is-equivalence f   □

-- The type of equivalences, expressed using equality, is isomorphic
-- to the type of equivalences, expressed using paths.

≃↔≃ :
  {A : Type a} {B : Type b} →
  A ≃ B ↔ A PE.≃ B
≃↔≃ {A = A} {B = B} =
  A ≃ B                ↝⟨ Eq.≃-as-Σ ⟩
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

-- The type of equivalences, expressed using "contractible preimages"
-- and equality, is isomorphic to the type of equivalences, expressed
-- using contractible preimages and paths.

≃-CP↔≃-CP :
  {A : Type a} {B : Type b} →
  A CP.≃ B ↔ A PCP.≃ B
≃-CP↔≃-CP {A = A} {B = B} =
  ∃ CP.Is-equivalence   ↝⟨ (∃-cong λ _ → Is-equivalence-CP↔Is-equivalence-CP) ⟩□
  ∃ PCP.Is-equivalence  □

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
                                                      Eq.⇔→≃ (Eq.propositional ext _) (Eq.propositional ext _)
                                                        (λ is → _≃_.is-equivalence $
                                                           Eq.with-other-function
                                                             (
      x P.≡ y                                                  ↔⟨ inverse ≡↔≡ ⟩
      x ≡ y                                                    ↝⟨ Eq.⟨ _ , is ⟩ ⟩
      f x ≡ f y                                                ↔⟨ ≡↔≡ ⟩□
      f x P.≡ f y                                              □)
                                                             (P.cong f)
                                                             (λ eq →
      _↔_.to ≡↔≡ (cong f (_↔_.from ≡↔≡ eq))                     ≡⟨ cong (_↔_.to ≡↔≡) cong≡cong ⟩
      _↔_.to ≡↔≡ (_↔_.from ≡↔≡ (P.cong f eq))                   ≡⟨ _↔_.right-inverse-of ≡↔≡ _ ⟩∎
      P.cong f eq                                               ∎))
                                                        (λ is → _≃_.is-equivalence $
                                                           Eq.with-other-function
                                                             (
      x ≡ y                                                    ↔⟨ ≡↔≡ ⟩
      x P.≡ y                                                  ↝⟨ Eq.⟨ _ , is ⟩ ⟩
      f x P.≡ f y                                              ↔⟨ inverse ≡↔≡ ⟩□
      f x ≡ f y                                                □)
                                                             (cong f)
                                                             (λ eq →
      _↔_.from ≡↔≡ (P.cong f (_↔_.to ≡↔≡ eq))                   ≡⟨ sym cong≡cong ⟩
      cong f (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ eq))                     ≡⟨ cong (cong f) $ _↔_.left-inverse-of ≡↔≡ _ ⟩∎
      cong f eq                                                 ∎))) ⟩
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

-- CP.Univalence′ is pointwise equivalent to PCP.Univalence′.

Univalence′-CP≃Univalence′-CP :
  {A B : Type ℓ} →
  CP.Univalence′ A B ≃ PCP.Univalence′ A B
Univalence′-CP≃Univalence′-CP {A = A} {B = B} =
  ((A≃B : A CP.≃ B) →
   ∃ λ (x : ∃ λ A≡B → CP.≡⇒≃ A≡B ≡ A≃B) → ∀ y → x ≡ y)       ↔⟨⟩

  ((A≃B : ∃ λ (f : A → B) → CP.Is-equivalence f) →
   ∃ λ (x : ∃ λ A≡B → CP.≡⇒≃ A≡B ≡ A≃B) →
   ∀ y → x ≡ y)                                              ↝⟨ (Π-cong ext (∃-cong λ _ → Is-equivalence-CP↔Is-equivalence-CP) λ A≃B →
                                                                 Σ-cong (lemma₁ A≃B) λ _ →
                                                                 Π-cong ext (lemma₁ A≃B) λ _ →
                                                                 inverse $ Eq.≃-≡ (lemma₁ A≃B)) ⟩
  ((A≃B : ∃ λ (f : A → B) → PCP.Is-equivalence f) →
   ∃ λ (x : ∃ λ A≡B → PCP.≡⇒≃ A≡B ≡ A≃B) →
   ∀ y → x ≡ y)                                              ↔⟨⟩

  ((A≃B : A PCP.≃ B) →
   ∃ λ (x : ∃ λ A≡B → PCP.≡⇒≃ A≡B ≡ A≃B) → ∀ y → x ≡ y)      ↔⟨ Is-equivalence-CP↔Is-equivalence-CP ⟩□

  ((A≃B : A PCP.≃ B) →
   ∃ λ (x : ∃ λ A≡B → PCP.≡⇒≃ A≡B P.≡ A≃B) → ∀ y → x P.≡ y)  □
  where
  lemma₃ :
    (A≡B : A ≡ B) →
    _↔_.to ≃-CP↔≃-CP (CP.≡⇒≃ A≡B) ≡ PCP.≡⇒≃ (_↔_.to ≡↔≡ A≡B)
  lemma₃ = elim¹
    (λ A≡B → _↔_.to ≃-CP↔≃-CP (CP.≡⇒≃ A≡B) ≡ PCP.≡⇒≃ (_↔_.to ≡↔≡ A≡B))
    (_↔_.to ≃-CP↔≃-CP (CP.≡⇒≃ (refl _))  ≡⟨ cong (_↔_.to ≃-CP↔≃-CP) CP.≡⇒≃-refl ⟩
     _↔_.to ≃-CP↔≃-CP CP.id              ≡⟨ _↔_.from ≡↔≡ $ P.Σ-≡,≡→≡ P.refl (PCP.propositional P.ext _ _ _) ⟩
     PCP.id                              ≡⟨ sym $ _↔_.from ≡↔≡ PCP.≡⇒≃-refl ⟩
     PCP.≡⇒≃ P.refl                      ≡⟨ sym $ cong PCP.≡⇒≃ to-≡↔≡-refl ⟩∎
     PCP.≡⇒≃ (_↔_.to ≡↔≡ (refl _))       ∎)

  lemma₂ : ∀ _ _ → _ ≃ _
  lemma₂ A≡B (f , f-eq) =
    CP.≡⇒≃ A≡B ≡ (f , f-eq)                                ↝⟨ inverse $ Eq.≃-≡ (Eq.↔⇒≃ ≃-CP↔≃-CP) ⟩

    _↔_.to ≃-CP↔≃-CP (CP.≡⇒≃ A≡B) ≡
    (f , _↔_.to Is-equivalence-CP↔Is-equivalence-CP f-eq)  ↝⟨ ≡⇒≃ $ cong (_≡ (f , _↔_.to Is-equivalence-CP↔Is-equivalence-CP f-eq)) $
                                                              lemma₃ A≡B ⟩□
    PCP.≡⇒≃ (_↔_.to ≡↔≡ A≡B) ≡
    (f , _↔_.to Is-equivalence-CP↔Is-equivalence-CP f-eq)  □

  lemma₁ :
    ∀ A≃B →
    (∃ λ A≡B → CP.≡⇒≃ A≡B ≡ A≃B) ≃
    (∃ λ A≡B →
         PCP.≡⇒≃ A≡B ≡
         ( proj₁ A≃B
         , _↔_.to Is-equivalence-CP↔Is-equivalence-CP (proj₂ A≃B)
         ))
  lemma₁ A≃B = Σ-cong ≡↔≡ λ A≡B → lemma₂ A≡B A≃B

-- Univalence′ expressed using equality is equivalent to Univalence′
-- expressed using paths.

Univalence′≃Univalence′ :
  {A B : Type ℓ} →
  Univalence′ A B ≃ PU.Univalence′ A B
Univalence′≃Univalence′ {A = A} {B = B} =
  Univalence′ A B      ↝⟨ Univalence′≃Univalence′-CP ext ⟩
  CP.Univalence′ A B   ↝⟨ Univalence′-CP≃Univalence′-CP ⟩
  PCP.Univalence′ A B  ↝⟨ inverse $ _↔_.from ≃↔≃ $ PU.Univalence′≃Univalence′-CP P.ext ⟩□
  PU.Univalence′ A B   □

-- Univalence expressed using equality is equivalent to univalence
-- expressed using paths.

Univalence≃Univalence : Univalence ℓ ≃ PU.Univalence ℓ
Univalence≃Univalence {ℓ = ℓ} =
  ({A B : Type ℓ} → Univalence′ A B)     ↝⟨ implicit-∀-cong ext $ implicit-∀-cong ext Univalence′≃Univalence′ ⟩□
  ({A B : Type ℓ} → PU.Univalence′ A B)  □
