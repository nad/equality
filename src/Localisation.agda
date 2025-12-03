------------------------------------------------------------------------
-- Localisation
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe #-}

-- Following "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining (a first approximation to)
-- localisation use path equality, but the supplied notion of equality
-- is used for many other things.

import Equality.Path as P

module Localisation
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude as P

open import Bijection equality-with-J as B using (_↔_)
open import Equality.Path.Isomorphisms eq as I hiding (ext)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Path-split equality-with-J as PS
  using (Path-split)
open import Extensionality equality-with-J
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Pullback equality-with-J as PB using (∆)
open import Pushout eq as PO using (Pushout; ∇; Pushout→≃Pullback)
open import Surjection equality-with-J using (_↠_; Split-surjective)

private
  variable
    a b c p q r : Level
    A B C       : Type a
    P Q R       : A → Type p
    e f g x y   : A

------------------------------------------------------------------------
-- Local types

-- A type B is f-local (for a family of functions f : ∀ x → P x → Q x)
-- if precomposition with f x (where the codomain of the composition
-- operation is B) is an equivalence for all x.

_-Local_ :
  {A : Type a} {P : A → Type p} {Q : A → Type q} →
  (f : ∀ x → P x → Q x) → Type b → Type (a ⊔ b ⊔ p ⊔ q)
_-Local_ {Q} f B =
  ∀ x → Is-equivalence (λ (g : Q x → B) → g ∘ f x)

-- Locality can be expressed in another way.

Local≃Split-surjective-∘×Split-surjective-∘∇ :
  {f : (x : A) → P x → Q x} →
  f -Local B ≃
  (∀ x → Split-surjective ((_∘ f x)     ⦂ ((_ → B) → _)) ×
         Split-surjective ((_∘ ∇ (f x)) ⦂ ((_ → B) → _)))
Local≃Split-surjective-∘×Split-surjective-∘∇ {P} {Q} {B} {f} =
  f -Local B                                                         ↔⟨⟩
  (∀ x → Is-equivalence (_∘ f x))                                    ↝⟨ (∀-cong I.ext λ x → lemma (f x)) ⟩□
  (∀ x → Split-surjective (_∘ f x) × Split-surjective (_∘ ∇ (f x)))  □
  where
  lemma : (g : P x → Q x) → _
  lemma g =
    Is-equivalence (_∘ g)                                   ↝⟨ inverse $ PS.Path-split↔Is-equivalence I.ext ⟩

    Path-split 2 (_∘ g)                                     ↝⟨ PS.Path-split-2≃Split-surjective×Split-surjective-∆ I.ext ⟩

    Split-surjective (_∘ g) × Split-surjective (∆ (_∘ g))   ↝⟨ (∃-cong λ _ → inverse $ Split-surjective-cong I.ext $ ext⁻¹
                                                                PO.∘∇≡∆∘) ⟩
    Split-surjective (_∘ g) ×
    Split-surjective (_≃_.to Pushout→≃Pullback ∘ (_∘ ∇ g))  ↝⟨ (∃-cong λ _ → inverse $
                                                                Split-surjective≃Split-surjective-∘ˡ I.ext
                                                                  (_≃_.is-equivalence Pushout→≃Pullback)) ⟩□
    Split-surjective (_∘ g) × Split-surjective (_∘ ∇ g)     □

-- Locality can be expressed in a third way.

Local≃Is-equivalence-∘×Is-equivalence-∘∇ :
  {f : (x : A) → P x → Q x} →
  f -Local B ≃
  (∀ x → Is-equivalence ((_∘ f x)     ⦂ ((_ → B) → _)) ×
         Is-equivalence ((_∘ ∇ (f x)) ⦂ ((_ → B) → _)))
Local≃Is-equivalence-∘×Is-equivalence-∘∇ {P} {Q} {B} {f} =
  f -Local B                                                     ↔⟨⟩
  (∀ x → Is-equivalence (_∘ f x))                                ↝⟨ (∀-cong I.ext λ x → lemma (f x)) ⟩□
  (∀ x → Is-equivalence (_∘ f x) × Is-equivalence (_∘ ∇ (f x)))  □
  where
  lemma : (g : P x → Q x) → _
  lemma g =
    Is-equivalence (_∘ g)                              ↔⟨ (inverse $ drop-⊤-right λ ∘-f-eq →
                                                           _⇔_.to contractible⇔↔⊤ $
                                                           propositional⇒inhabited⇒contractible
                                                             (Is-equivalence-propositional I.ext)
                                                             (PB.Is-equivalence-∆ ∘-f-eq)) ⟩
    Is-equivalence (_∘ g) × Is-equivalence (∆ (_∘ g))  ↝⟨ (∃-cong λ _ → PO.Is-equivalence-∆∘≃Is-equivalence-∘∇) ⟩□
    Is-equivalence (_∘ g) × Is-equivalence (_∘ ∇ g)    □

------------------------------------------------------------------------
-- Localisation′

-- A first approximation to localisation.
--
-- This is a slight generalisation of the HIT that Rijke et al. call
-- 𝓙: they require all types to live in the same universe.

data Localisation′
       {A : Type a} {P : A → Type p} {Q : A → Type q}
       (f : ∀ x → P x → Q x) (B : Type b) :
       Type (a ⊔ b ⊔ p ⊔ q) where
  [_]   : B → Localisation′ f B
  ext   : ∀ x → (P x → Localisation′ f B) → (Q x → Localisation′ f B)
  ext≡ᴾ : ext x g (f x y) P.≡ g y

-- A variant of ext≡ᴾ.

ext≡ :
  {f : (x : A) → P x → Q x} {g : P x → Localisation′ f B} →
  ext x g (f x y) ≡ g y
ext≡ = _↔_.from ≡↔≡ ext≡ᴾ

------------------------------------------------------------------------
-- Some eliminators for Localisation′

-- A dependent eliminator, expressed using paths.

record Elimᴾ
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         {f : ∀ x → P x → Q x} {B : Type b}
         (R : Localisation′ f B → Type r) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ r) where
  no-eta-equality
  field
    []ʳ   : ∀ x → R [ x ]
    extʳ  : ((y : P x) → R (g y)) → ∀ y → R (ext x g y)
    ext≡ʳ : (h : (y : P x) → R (g y)) →
            P.[ (λ i → R (ext≡ᴾ {g = g} {y = y} i)) ] extʳ h (f x y) ≡
            h y

open Elimᴾ public

elimᴾ : Elimᴾ R → (x : Localisation′ f B) → R x
elimᴾ {f} {B} {R} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Localisation′ f B) → R x
  helper [ x ]         = E.[]ʳ x
  helper (ext _ g y)   = E.extʳ (λ y → helper (g y)) y
  helper (ext≡ᴾ {g} i) = E.ext≡ʳ (λ y → helper (g y)) i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         (f : ∀ x → P x → Q x) (B : Type b)
         (C : Type c) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ c) where
  no-eta-equality
  field
    []ʳ   : B → C
    extʳ  : (P x → C) → Q x → C
    ext≡ʳ : (g : P x → C) → extʳ g (f x y) P.≡ g y

open Recᴾ public

recᴾ : Recᴾ f B C → Localisation′ f B → C
recᴾ r = elimᴾ λ where
    .[]ʳ   → R.[]ʳ
    .extʳ  → R.extʳ
    .ext≡ʳ → R.ext≡ʳ
  where
  module R = Recᴾ r

-- A dependent eliminator.

record Elim
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         {f : ∀ x → P x → Q x} {B : Type b}
         (R : Localisation′ f B → Type r) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ r) where
  no-eta-equality
  field
    []ʳ   : ∀ x → R [ x ]
    extʳ  : ((y : P x) → R (g y)) → ∀ y → R (ext x g y)
    ext≡ʳ : (h : (y : P x) → R (g y)) →
            subst R (ext≡ {y = y} {g = g}) (extʳ h (f x y)) ≡ h y

open Elim public

elim : Elim R → (x : Localisation′ f B) → R x
elim {R} e = elimᴾ eᴾ
  where
  module E = Elim e

  eᴾ : Elimᴾ R
  eᴾ .[]ʳ   = E.[]ʳ
  eᴾ .extʳ  = E.extʳ
  eᴾ .ext≡ʳ = subst≡→[]≡ ∘ E.ext≡ʳ

-- A "computation rule".

elim-ext≡ :
  dcong (elim e) (ext≡ {y = y} {g = g}) ≡
  e .ext≡ʳ (elim e ∘ g)
elim-ext≡ = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         (f : ∀ x → P x → Q x) (B : Type b)
         (C : Type c) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ c) where
  no-eta-equality
  field
    []ʳ   : B → C
    extʳ  : (P x → C) → Q x → C
    ext≡ʳ : (g : P x → C) → extʳ g (f x y) ≡ g y

open Rec public

rec : Rec f B C → Localisation′ f B → C
rec {f} {B} {C} r = recᴾ rᴾ
  where
  module R = Rec r

  rᴾ : Recᴾ f B C
  rᴾ .[]ʳ   = R.[]ʳ
  rᴾ .extʳ  = R.extʳ
  rᴾ .ext≡ʳ = _↔_.to ≡↔≡ ∘ R.ext≡ʳ

-- A "computation rule".

rec-ext≡ :
  {f : ∀ x → P x → Q x}
  {r : Rec f B C}
  {g : P x → Localisation′ f B} →
  cong (rec r) (ext≡ {x = x} {y = y} {g = g}) ≡
  r .ext≡ʳ (rec r ∘ g)
rec-ext≡ = cong-≡↔≡ (refl _)

------------------------------------------------------------------------
-- Some lemmas related to Localisation′

-- If C is f-local, then precomposition with [_] (at a certain type)
-- is an equivalence.

Local→Is-equivalence-∘[] :
  {f : ∀ x → P x → Q x} →
  f -Local C →
  Is-equivalence (λ (g : Localisation′ f B → C) → g ∘ [_])
Local→Is-equivalence-∘[] {P} {Q} {C} {B} {f} local =
                           $⟨ (λ g → from g , from-[])
                            , (λ g h →
                                   (λ g∘[]≡h∘[] →
                                        drop-∘[] g h g∘[]≡h∘[]
                                      , cong-∘[]-drop-∘[] g∘[]≡h∘[])
                                 , _)
                            ⟩
  Path-split 2 (_∘ [_])    →⟨ PS.Path-split↔Is-equivalence _ ⟩□
  Is-equivalence (_∘ [_])  □
  where
  Q→C≃P→C : ∀ x → (Q x → C) ≃ (P x → C)
  Q→C≃P→C x = Eq.⟨ _∘ f x , local x ⟩

  from : (B → C) → (Localisation′ f B → C)
  from g = elim λ where
    .[]ʳ      → g
    .extʳ {x} →
      (P x → C)  ↔⟨ inverse $ Q→C≃P→C x ⟩□
      (Q x → C)  □
    .ext≡ʳ {x} {y} h →
      subst (λ _ → C) ext≡ (_≃_.from (Q→C≃P→C x) h (f x y))  ≡⟨ subst-const _ ⟩
      _≃_.from (Q→C≃P→C x) h (f x y)                         ≡⟨⟩
      _≃_.to (Q→C≃P→C x) (_≃_.from (Q→C≃P→C x) h) y          ≡⟨ cong (_$ y) $ _≃_.right-inverse-of (Q→C≃P→C x) _ ⟩∎
      h y                                                    ∎

  from-[] : from g ∘ [_] ≡ g
  from-[] = refl _

  drop-∘[]′ :
    (g h : Localisation′ f B → C) →
    g ∘ [_] ≡ h ∘ [_] → ∀ x → g x ≡ h x
  drop-∘[]′ g h g∘[]≡h∘[] = elim λ where
      .[]ʳ x → cong (_$ x) g∘[]≡h∘[]

      .extʳ {g = k} → _≃_.to (lemma k)

      .ext≡ʳ {x} {g = k} {y} g∘k≡h∘k →
        subst (λ x → g x ≡ h x) ext≡ (_≃_.to (lemma k) g∘k≡h∘k (f x y))  ≡⟨ sym $ from-lemma _ _ ⟩
        _≃_.from (lemma k) (_≃_.to (lemma k) g∘k≡h∘k) y                  ≡⟨ cong (_$ y) $ _≃_.left-inverse-of (lemma k) _ ⟩∎
        g∘k≡h∘k y                                                        ∎
    where
    lemma : ∀ {x} (k : P x → Localisation′ f B) → _ ≃ _
    lemma {x} k =
      ((y : P x) → g (k y) ≡ h (k y))              ↔⟨ Π≡≃≡ ⟩
      g ∘ k ≡ h ∘ k                                ↔⟨ (≡⇒↝ equivalence $ cong (λ f → g ∘ f ≡ h ∘ f) $ ⟨ext⟩ λ _ → sym ext≡) ⟩
      g ∘ ext x k ∘ f x ≡ h ∘ ext x k ∘ f x        ↔⟨ Eq.≃-≡ $ Q→C≃P→C x ⟩
      g ∘ ext x k ≡ h ∘ ext x k                    ↔⟨ inverse Π≡≃≡ ⟩□
      ((y : Q x) → g (ext x k y) ≡ h (ext x k y))  □

    from-lemma :
      ∀ {x y}
      (k : P x → Localisation′ f B)
      (eq : ∀ y → g (ext x k y) ≡ h (ext x k y)) →
      _
    from-lemma {x} {y} k eq =
      _≃_.from (lemma k) eq y                          ≡⟨⟩

      cong (_$ y)
        (_≃_.from (≡⇒↝ _ $ cong (λ f → g ∘ f ≡ h ∘ f)
                             (⟨ext⟩ λ _ → sym ext≡))
           (cong (_∘ f x) (⟨ext⟩ eq)))                 ≡⟨ cong (cong _) $ sym $
                                                          subst-in-terms-of-inverse∘≡⇒↝ equivalence _ _ _ ⟩
      cong (_$ y)
        (subst (λ f → g ∘ f ≡ h ∘ f)
           (sym $ ⟨ext⟩ λ _ → sym ext≡)
           (cong (_∘ f x) (⟨ext⟩ eq)))                 ≡⟨ (cong (cong _) $ cong (flip (subst _) _) $
                                                           trans (sym $ ext-sym I.ext) $
                                                           cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                           sym-sym _) ⟩
      cong (_$ y)
        (subst (λ f → g ∘ f ≡ h ∘ f)
           (⟨ext⟩ λ _ → ext≡)
           (cong (_∘ f x) (⟨ext⟩ eq)))                 ≡⟨ cong (cong _) $ cong (subst _ _) $
                                                          cong-pre-∘-ext I.ext I.ext ⟩
      cong (_$ y)
        (subst (λ f → g ∘ f ≡ h ∘ f)
           (⟨ext⟩ λ _ → ext≡)
           (⟨ext⟩ (eq ∘ f x)))                         ≡⟨ cong (cong _)
                                                          subst-in-terms-of-trans-and-cong ⟩
      cong (_$ y)
        (trans (sym (cong (g ∘_) (⟨ext⟩ λ _ → ext≡)))
           (trans (⟨ext⟩ (eq ∘ f x))
              (cong (h ∘_) (⟨ext⟩ λ _ → ext≡))))       ≡⟨ cong (cong _) $
                                                          trans (cong₂ trans
                                                                   (trans (cong sym $ cong-post-∘-ext I.ext I.ext) $
                                                                    sym $ ext-sym I.ext)
                                                                   (trans (cong (trans _) $ cong-post-∘-ext I.ext I.ext) $
                                                                    sym $ ext-trans I.ext)) $
                                                          sym $ ext-trans I.ext ⟩
      (cong (_$ y) $ ⟨ext⟩ λ y →
       trans (sym (cong g ext≡))
         (trans (eq (f x y)) (cong h ext≡)))           ≡⟨ cong-ext I.ext ⟩

      trans (sym (cong g ext≡))
        (trans (eq (f x y)) (cong h ext≡))             ≡⟨ sym subst-in-terms-of-trans-and-cong ⟩∎

      subst (λ x → g x ≡ h x) ext≡ (eq (f x y))        ∎

  drop-∘[] :
    (g h : Localisation′ f B → C) →
    g ∘ [_] ≡ h ∘ [_] → g ≡ h
  drop-∘[] g h g∘[]≡h∘[] = ⟨ext⟩ $ drop-∘[]′ g h g∘[]≡h∘[]

  cong-∘[]-drop-∘[] :
    {g h : Localisation′ f B → C}
    (g∘[]≡h∘[] : g ∘ [_] ≡ h ∘ [_]) →
    cong (_∘ [_]) (drop-∘[] g h g∘[]≡h∘[]) ≡ g∘[]≡h∘[]
  cong-∘[]-drop-∘[] {g} {h} g∘[]≡h∘[] =
    cong (_∘ [_]) (drop-∘[] g h g∘[]≡h∘[])           ≡⟨⟩
    cong (_∘ [_]) (⟨ext⟩ $ drop-∘[]′ g h g∘[]≡h∘[])  ≡⟨ cong-pre-∘-ext I.ext I.ext ⟩
    ⟨ext⟩ (drop-∘[]′ g h g∘[]≡h∘[] ∘ [_])            ≡⟨⟩
    ⟨ext⟩ (ext⁻¹ g∘[]≡h∘[])                          ≡⟨ _≃_.right-inverse-of Π≡≃≡ _ ⟩∎
    g∘[]≡h∘[]                                        ∎

-- If f x is split surjective for each x, then Localisation′ f B is
-- f-local.

Split-surjective→Local-Localisation′ :
  {f : (x : A) → P x → Q x} →
  (∀ x → Split-surjective (f x)) →
  f -Local Localisation′ f B
Split-surjective→Local-Localisation′ {P} {Q} {f} f-surj x =
  _≃_.is-equivalence $
  Eq.↔→≃
    _
    (ext x)
    (λ _ → ⟨ext⟩ λ _ → ext≡)
    (λ g → ⟨ext⟩ λ y →
       ext x (g ∘ f x) y                         ≡⟨ cong (ext _ _) $ sym $ _↠_.right-inverse-of Px↠Qx _ ⟩
       ext x (g ∘ f x) (f x (_↠_.from Px↠Qx y))  ≡⟨ ext≡ ⟩
       g (f x (_↠_.from Px↠Qx y))                ≡⟨ cong g $ _↠_.right-inverse-of Px↠Qx _ ⟩∎
       g y                                       ∎)
  where
  Px↠Qx : P x ↠ Q x
  Px↠Qx = _↔_.from ↠↔∃-Split-surjective (f x , f-surj x)

------------------------------------------------------------------------
-- Localisation

-- The localisation operation.

Localisation :
  {A : Type a} {P : A → Type p} {Q : A → Type q} →
  (∀ x → P x → Q x) →
  Type b → Type (a ⊔ b ⊔ p ⊔ q)
Localisation {p} {q} {A} {P} {Q} f =
  Localisation′ f̂
  where
  P̂ : A ⊎ A → Type (p ⊔ q)
  P̂ = P.[ ↑ q ∘ P
        , (λ x → Pushout (record { left = f x; right = f x }))
        ]

  Q̂ : A ⊎ A → Type q
  Q̂ = P.[ Q , Q ]

  f̂ : (x : A ⊎ A) → P̂ x → Q̂ x
  f̂ = P.[ (λ x → f x ∘ lower)
        , (λ x → ∇ (f x))
        ]

-- Localisation f B is f-local.

Local-Localisation : f -Local Localisation f B
Local-Localisation {f} {B} =
  _≃_.from Local≃Split-surjective-∘×Split-surjective-∘∇ λ x →
    (λ g → ext (inj₁ x) (g ∘ lower)
         , ⟨ext⟩ λ y →
             ext (inj₁ x) (g ∘ lower) (f x y)  ≡⟨ ext≡ ⟩∎
             g y                               ∎)
  , (λ g → ext (inj₂ x) g
         , (⟨ext⟩ $ PO.elim
              (λ y → ext (inj₂ x) g (∇ (f x) y) ≡ g y)
              (λ _ → ext≡)
              (λ _ → ext≡)
              (lemma x g)))
  where
  lemma :
    ∀ x g y →
    subst (λ y → ext (inj₂ x) g (∇ (f x) y) ≡ g y) (PO.glue y) ext≡ ≡
    ext≡
  lemma x g _ =
    elim¹
      (λ eq →
         subst (λ y → ext (inj₂ x) g (∇ (f x) y) ≡ g y) eq ext≡ ≡
         ext≡ {x = inj₂ x})
      (subst-refl _ _)
      _

-- If C is f-local, then λ (g : Localisation f B → C) → g ∘ [_] is an
-- equivalence.

Local→Is-equivalence-[] :
  f -Local C →
  Is-equivalence (λ (g : Localisation f B → C) → g ∘ [_])
Local→Is-equivalence-[] {f} local =
  Local→Is-equivalence-∘[] $
  _≃_.from Local≃Is-equivalence-∘×Is-equivalence-∘∇ $
  P.[ (_≃_.to Local≃Is-equivalence-∘×Is-equivalence-∘∇ λ x →
                                          $⟨ local x ⟩
       Is-equivalence (_∘ f x)            →⟨ Is-equivalence≃Is-equivalence-∘ˡ
                                               (_≃_.is-equivalence $ →-cong I.ext (Eq.↔⇒≃ $ inverse B.↑↔) F.id) _ ⟩□
       Is-equivalence (_∘ (f x ∘ lower))  □)
    , (λ x →
           (                             $⟨ local x ⟩
            Is-equivalence (_∘ f x)      →⟨ PO.Is-equivalence-∘∇ ⟩□
            Is-equivalence (_∘ ∇ (f x))  □)
         , (                                 $⟨ local x ⟩
            Is-equivalence (_∘ f x)          →⟨ PO.Is-equivalence-∘∇ ⟩
            Is-equivalence (_∘ ∇ (f x))      →⟨ PO.Is-equivalence-∘∇ ⟩□
            Is-equivalence (_∘ ∇ (∇ (f x)))  □))
    ]
