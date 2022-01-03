------------------------------------------------------------------------
-- Localisation
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

-- Following "Modalities in Homotopy Type Theory" by Rijke, Shulman
-- and Spitters.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining localisation use path equality,
-- but the supplied notion of equality is used for many other things.

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
  using (Path-split; _-Null_; Is-∞-extendable-along-[_])
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Modality.Basics equality-with-J
open import Pullback equality-with-J as PB using (∆)
open import Pushout eq as PO using (Pushout; ∇; Pushout→≃Pullback)
open import Surjection equality-with-J using (_↠_; Split-surjective)
open import Suspension eq (Susp)
open import Univalence-axiom equality-with-J

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
_-Local_ {Q = Q} f B =
  ∀ x → Is-equivalence (λ (g : Q x → B) → g ∘ f x)

-- The function _-Null_ can be expressed using _-Local_.

Null≃Local : P -Null B ≃ (λ x (_ : P x) → tt) -Local B
Null≃Local {P = P} {B = B} =
  P -Null B                                                ↔⟨⟩
  (∀ x → Is-equivalence (const ⦂ (B → P x → B)))           ↝⟨ (∀-cong I.ext λ _ →
                                                               Is-equivalence≃Is-equivalence-∘ʳ
                                                                 (_≃_.is-equivalence $ Eq.↔⇒≃ Π-left-identity) I.ext) ⟩
  (∀ x → Is-equivalence (λ (g : ⊤ → B) (_ : P x) → g tt))  ↔⟨⟩
  (λ x (_ : P x) → tt) -Local B                            □

-- Locality can be expressed in another way.

Local≃Split-surjective-∘×Split-surjective-∘∇ :
  {f : (x : A) → P x → Q x} →
  f -Local B ≃
  (∀ x → Split-surjective ((_∘ f x)     ⦂ ((_ → B) → _)) ×
         Split-surjective ((_∘ ∇ (f x)) ⦂ ((_ → B) → _)))
Local≃Split-surjective-∘×Split-surjective-∘∇
  {P = P} {Q = Q} {B = B} {f = f} =
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
Local≃Is-equivalence-∘×Is-equivalence-∘∇ {P = P} {Q = Q} {B = B} {f = f} =
  f -Local B                                                     ↔⟨⟩
  (∀ x → Is-equivalence (_∘ f x))                                ↝⟨ (∀-cong I.ext λ x → lemma (f x)) ⟩□
  (∀ x → Is-equivalence (_∘ f x) × Is-equivalence (_∘ ∇ (f x)))  □
  where
  lemma : (g : P x → Q x) → _
  lemma g =
    Is-equivalence (_∘ g)                              ↔⟨ (inverse $ drop-⊤-right λ ∘-f-eq →
                                                           _⇔_.to contractible⇔↔⊤ $
                                                           propositional⇒inhabited⇒contractible
                                                             (Eq.propositional I.ext _)
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
  ext   : (P x → Localisation′ f B) →
          (Q x → Localisation′ f B)
  ext≡ᴾ : ext g (f x y) P.≡ g y

-- A variant of ext≡ᴾ.

ext≡ :
  {f : (x : A) → P x → Q x} {g : P x → Localisation′ f B} →
  ext g (f x y) ≡ g y
ext≡ = _↔_.from ≡↔≡ ext≡ᴾ

------------------------------------------------------------------------
-- Some eliminators for Localisation′

-- A dependent eliminator, expressed using paths.

record Elimᴾ
         {A : Type a} {P : A → Type p} {Q : A → Type q}
         (f : ∀ x → P x → Q x) (B : Type b)
         (R : Localisation′ f B → Type r) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ r) where
  no-eta-equality
  field
    []ʳ   : ∀ x → R [ x ]
    extʳ  : ((y : P x) → R (g y)) → ∀ y → R (ext g y)
    ext≡ʳ : (h : (y : P x) → R (g y)) →
            P.[ (λ i → R (ext≡ᴾ {g = g} {y = y} i)) ] extʳ h (f x y) ≡
            h y

open Elimᴾ public

elimᴾ : Elimᴾ f B R → (x : Localisation′ f B) → R x
elimᴾ {f = f} {B = B} {R = R} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Localisation′ f B) → R x
  helper [ x ]             = E.[]ʳ x
  helper (ext g y)         = E.extʳ (λ y → helper (g y)) y
  helper (ext≡ᴾ {g = g} i) = E.ext≡ʳ (λ y → helper (g y)) i

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
         (f : ∀ x → P x → Q x) (B : Type b)
         (R : Localisation′ f B → Type r) :
         Type (a ⊔ b ⊔ p ⊔ q ⊔ r) where
  no-eta-equality
  field
    []ʳ   : ∀ x → R [ x ]
    extʳ  : ((y : P x) → R (g y)) → ∀ y → R (ext g y)
    ext≡ʳ : (h : (y : P x) → R (g y)) →
            subst R (ext≡ {y = y} {g = g}) (extʳ h (f x y)) ≡ h y

open Elim public

elim : Elim f B R → (x : Localisation′ f B) → R x
elim e = elimᴾ λ where
    .[]ʳ   → E.[]ʳ
    .extʳ  → E.extʳ
    .ext≡ʳ → subst≡→[]≡ ∘ E.ext≡ʳ
  where
  module E = Elim e

-- A "computation" rule.

elim-ext≡ :
  dcong (elim e) (ext≡ {y = y} {g = g}) ≡
  Elim.ext≡ʳ e (elim e ∘ g)
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
rec r = recᴾ λ where
    .[]ʳ   → R.[]ʳ
    .extʳ  → R.extʳ
    .ext≡ʳ → _↔_.to ≡↔≡ ∘ R.ext≡ʳ
  where
  module R = Rec r

-- A "computation" rule.

rec-ext≡ :
  {f : ∀ x → P x → Q x}
  {r : Rec f B C}
  {g : P x → Localisation′ f B} →
  cong (rec r) (ext≡ {y = y} {g = g}) ≡
  Rec.ext≡ʳ r (rec r ∘ g)
rec-ext≡ = cong-≡↔≡ (refl _)

------------------------------------------------------------------------
-- Some lemmas related to Localisation′

-- If C is f-local, then precomposition with [_] (at a certain type)
-- is an equivalence.

Local→Is-equivalence-∘[] :
  {f : ∀ x → P x → Q x} →
  f -Local C →
  Is-equivalence (λ (g : Localisation′ f B → C) → g ∘ [_])
Local→Is-equivalence-∘[] {P = P} {Q = Q} {C = C} {B = B} {f = f} local =
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
    .[]ʳ          → g
    .extʳ {x = x} →
      (P x → C)  ↔⟨ inverse $ Q→C≃P→C x ⟩□
      (Q x → C)  □
    .ext≡ʳ {x = x} {y = y} h →
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

      .ext≡ʳ {x = x} {g = k} {y = y} g∘k≡h∘k →
        subst (λ x → g x ≡ h x) ext≡ (_≃_.to (lemma k) g∘k≡h∘k (f x y))  ≡⟨ sym $ from-lemma _ _ ⟩
        _≃_.from (lemma k) (_≃_.to (lemma k) g∘k≡h∘k) y                  ≡⟨ cong (_$ y) $ _≃_.left-inverse-of (lemma k) _ ⟩∎
        g∘k≡h∘k y                                                        ∎
    where
    lemma : ∀ {x} (k : P x → Localisation′ f B) → _ ≃ _
    lemma {x = x} k =
      ((y : P x) → g (k y) ≡ h (k y))          ↔⟨ Π≡≃≡ ⟩
      g ∘ k ≡ h ∘ k                            ↔⟨ (≡⇒↝ equivalence $ cong (λ f → g ∘ f ≡ h ∘ f) $ ⟨ext⟩ λ _ → sym ext≡) ⟩
      g ∘ ext k ∘ f x ≡ h ∘ ext k ∘ f x        ↔⟨ Eq.≃-≡ $ Q→C≃P→C x ⟩
      g ∘ ext k ≡ h ∘ ext k                    ↔⟨ inverse Π≡≃≡ ⟩□
      ((y : Q x) → g (ext k y) ≡ h (ext k y))  □

    from-lemma :
      ∀ {x y}
      (k : P x → Localisation′ f B)
      (eq : ∀ y → g (ext k y) ≡ h (ext k y)) →
      _
    from-lemma {x = x} {y = y} k eq =
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
                                                           trans (sym $ ext-sym _) $
                                                           cong ⟨ext⟩ $ ⟨ext⟩ λ _ →
                                                           sym-sym _) ⟩
      cong (_$ y)
        (subst (λ f → g ∘ f ≡ h ∘ f)
           (⟨ext⟩ λ _ → ext≡)
           (cong (_∘ f x) (⟨ext⟩ eq)))                 ≡⟨ cong (cong _) $ cong (subst _ _) $
                                                          cong-pre-∘-ext _ ⟩
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
                                                                   (trans (cong sym $ cong-post-∘-ext _) $
                                                                    sym $ ext-sym _)
                                                                   (trans (cong (trans _) $ cong-post-∘-ext _) $
                                                                    sym $ ext-trans _ _)) $
                                                          sym $ ext-trans _ _ ⟩
      (cong (_$ y) $ ⟨ext⟩ λ y →
       trans (sym (cong g ext≡))
         (trans (eq (f x y)) (cong h ext≡)))           ≡⟨ cong-ext _ ⟩

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
  cong-∘[]-drop-∘[] {g = g} {h = h} g∘[]≡h∘[] =
    cong (_∘ [_]) (drop-∘[] g h g∘[]≡h∘[])           ≡⟨⟩
    cong (_∘ [_]) (⟨ext⟩ $ drop-∘[]′ g h g∘[]≡h∘[])  ≡⟨ cong-pre-∘-ext _ ⟩
    ⟨ext⟩ (drop-∘[]′ g h g∘[]≡h∘[] ∘ [_])            ≡⟨⟩
    ⟨ext⟩ (ext⁻¹ g∘[]≡h∘[])                          ≡⟨ _≃_.right-inverse-of Π≡≃≡ _ ⟩∎
    g∘[]≡h∘[]                                        ∎

-- If f x is split surjective for each x, then Localisation′ f B is
-- f-local.

Split-surjective→Local-Localisation′ :
  {f : (x : A) → P x → Q x} →
  (∀ x → Split-surjective (f x)) →
  f -Local Localisation′ f B
Split-surjective→Local-Localisation′ {P = P} {Q = Q} {f = f} f-surj x =
  _≃_.is-equivalence $
  Eq.↔→≃
    _
    ext
    (λ _ → ⟨ext⟩ λ _ → ext≡)
    (λ g → ⟨ext⟩ λ y →
       ext (g ∘ f x) y                         ≡⟨ cong (ext _) $ sym $ _↠_.right-inverse-of Px↠Qx _ ⟩
       ext (g ∘ f x) (f x (_↠_.from Px↠Qx y))  ≡⟨ ext≡ ⟩
       g (f x (_↠_.from Px↠Qx y))              ≡⟨ cong g $ _↠_.right-inverse-of Px↠Qx _ ⟩∎
       g y                                     ∎)
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
Localisation {p = p} {q = q} {A = A} {P = P} {Q = Q} f =
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
Local-Localisation {f = f} {B = B} =
  _≃_.from Local≃Split-surjective-∘×Split-surjective-∘∇ λ x →
    (λ g → ext {x = inj₁ x} (g ∘ lower)
         , ⟨ext⟩ λ y →
             ext (g ∘ lower) (f x y)  ≡⟨ ext≡ ⟩∎
             g y                      ∎)
  , (λ g → ext {x = inj₂ x} g
         , (⟨ext⟩ $ PO.elim
              (λ y → ext g (∇ (f x) y) ≡ g y)
              (λ _ → ext≡)
              (λ _ → ext≡)
              (lemma x g)))
  where
  lemma :
    ∀ x g y →
    subst (λ y → ext g (∇ (f x) y) ≡ g y) (PO.glue y) ext≡ ≡ ext≡
  lemma x g _ =
    elim¹
      (λ eq →
         subst (λ y → ext g (∇ (f x) y) ≡ g y) eq ext≡ ≡
         ext≡ {x = inj₂ x})
      (subst-refl _ _)
      _

-- If C is f-local, then λ (g : Localisation f B → C) → g ∘ [_] is an
-- equivalence.

Local→Is-equivalence-[] :
  f -Local C →
  Is-equivalence (λ (g : Localisation f B → C) → g ∘ [_])
Local→Is-equivalence-[] {f = f} local =
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

------------------------------------------------------------------------
-- Nullification

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
         to (from (ext {x = inj₁ x} f _))    ≡⟨⟩
         ext {x = inj₁ x} (to ∘ from ∘ f) _  ≡⟨ cong (flip ext _) $ ⟨ext⟩ hyp ⟩∎
         ext {x = inj₁ x} f _                ∎

       .extʳ {x = inj₂ x} {g = f} hyp _ →
         to (from (ext {x = inj₂ x} f _))                                 ≡⟨⟩

         ext {x = inj₂ x}
           (to ∘ from ∘ f ∘ _≃_.from PO.Susp≃Susp ∘ _≃_.to PO.Susp≃Susp)
           _                                                              ≡⟨ (cong (flip ext _) $ ⟨ext⟩ λ y → cong (to ∘ from ∘ f) $
                                                                              _≃_.left-inverse-of PO.Susp≃Susp y) ⟩

         ext {x = inj₂ x} (to ∘ from ∘ f) _                               ≡⟨ cong (flip ext _) $ ⟨ext⟩ hyp ⟩∎

         ext {x = inj₂ x} f _                                             ∎

       .ext≡ʳ {x = inj₁ x} {g = f} {y = y} hyp →
         subst (λ x → to (from x) ≡ x)
           (ext≡ {x = inj₁ x} {y = y} {g = f})
           (cong (flip ext _) $ ⟨ext⟩ hyp)                        ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans
           (sym $ cong (to ∘ from) $
            ext≡ {x = inj₁ x} {y = y} {g = f})
           (trans (cong (flip ext _) $ ⟨ext⟩ hyp)
              (cong id (ext≡ {x = inj₁ x} {y = y} {g = f})))      ≡⟨ cong₂ (trans ∘ sym)
                                                                       (sym $ cong-∘ _ _ _)
                                                                       (cong (trans _) $ sym $ cong-id _) ⟩
         trans
           (sym $ cong to $ cong from $
            ext≡ {x = inj₁ x} {y = y} {g = f})
           (trans (cong (flip ext _) $ ⟨ext⟩ hyp)
              (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ cong (flip trans _) $ cong sym $
                                                                     trans (cong (cong to) $ rec-ext≡ {r = from′}) $
                                                                     rec-ext≡ {r = to′} ⟩
         trans
           (sym $ ext≡ {x = inj₁ x} {y = y} {g = to ∘ from ∘ f})
           (trans (cong (flip ext _) $ ⟨ext⟩ hyp)
              (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ elim₁
                                                                       (λ {g} eq →
                                                                          trans
                                                                            (sym $ ext≡ {x = inj₁ x} {y = y} {g = g})
                                                                            (trans (cong (flip ext _) eq)
                                                                               (ext≡ {x = inj₁ x} {y = y} {g = f})) ≡
                                                                          ext⁻¹ eq y)
                                                                       (
           trans (sym ext≡)
             (trans (cong (flip ext _) (refl f)) ext≡)                  ≡⟨ cong (trans _) $
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
              (cong (flip ext _) $ ⟨ext⟩ λ y → cong (to ∘ from ∘ f) $
               _≃_.left-inverse-of PO.Susp≃Susp y)
              (cong (flip ext _) $ ⟨ext⟩ hyp))                            ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans
           (sym $ cong (to ∘ from) $
            ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (trans
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
              (cong id (ext≡ {x = inj₂ x} {y = y} {g = f})))              ≡⟨ cong₂ (trans ∘ sym)
                                                                               (sym $ cong-∘ _ _ _)
                                                                               (cong (trans _) $ sym $ cong-id _) ⟩
         trans
           (sym $ cong to $ cong from $
            ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (trans
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (to ∘ from ∘ f) $
                  _≃_.left-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                  (cong (flip ext _) $ ⟨ext⟩ λ y →
                   cong (to ∘ from ∘ f) $ ext⁻¹ eq y)
                  (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                                                                                          (cong (flip ext _) $ ⟨ext⟩ λ y →
                                                                                           cong (to ∘ from ∘ f) $ ext⁻¹ eq y)
                                                                                          (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                   (cong (flip ext _) $ ⟨ext⟩ λ y →
                    cong (to ∘ from ∘ f) $ ext⁻¹ (refl id) y)
                   (cong (flip ext _) $ ⟨ext⟩ hyp))
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
             (trans (cong (flip ext _) $ ⟨ext⟩ hyp)
                (ext≡ {x = inj₂ x} {y = y} {g = f}))                            ≡⟨ elim₁
                                                                                     (λ {g} eq →
                                                                                      trans
                                                                                        (sym $ ext≡ {x = inj₂ x} {y = y} {g = g})
                                                                                        (trans (cong (flip ext _) eq)
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
         from (to (ext {x = inj₁ x} f _))    ≡⟨⟩
         ext {x = inj₁ x} (from ∘ to ∘ f) _  ≡⟨ cong (flip ext _) $ ⟨ext⟩ hyp ⟩∎
         ext {x = inj₁ x} f _                ∎

       .extʳ {x = inj₂ x} {g = f} hyp _ →
         from (to (ext {x = inj₂ x} f _))                                 ≡⟨⟩

         ext {x = inj₂ x}
           (from ∘ to ∘ f ∘ _≃_.to PO.Susp≃Susp ∘ _≃_.from PO.Susp≃Susp)
           _                                                              ≡⟨ (cong (flip ext _) $ ⟨ext⟩ λ y → cong (from ∘ to ∘ f) $
                                                                              _≃_.right-inverse-of PO.Susp≃Susp y) ⟩

         ext {x = inj₂ x} (from ∘ to ∘ f) _                               ≡⟨ cong (flip ext _) $ ⟨ext⟩ hyp ⟩∎

         ext {x = inj₂ x} f _                                             ∎

       .ext≡ʳ {x = inj₁ x} {g = f} {y = y} hyp →
         subst (λ x → from (to x) ≡ x)
           (ext≡ {x = inj₁ x} {y = y} {g = f})
           (cong (flip ext _) $ ⟨ext⟩ hyp)                        ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans
           (sym $ cong (from ∘ to) $
            ext≡ {x = inj₁ x} {y = y} {g = f})
           (trans (cong (flip ext _) $ ⟨ext⟩ hyp)
              (cong id (ext≡ {x = inj₁ x} {y = y} {g = f})))      ≡⟨ cong₂ (trans ∘ sym)
                                                                       (sym $ cong-∘ _ _ _)
                                                                       (cong (trans _) $ sym $ cong-id _) ⟩
         trans
           (sym $ cong from $ cong to $
            ext≡ {x = inj₁ x} {y = y} {g = f})
           (trans (cong (flip ext _) $ ⟨ext⟩ hyp)
              (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ cong (flip trans _) $ cong sym $
                                                                     trans (cong (cong from) $ rec-ext≡ {r = to′}) $
                                                                     rec-ext≡ {r = from′} ⟩
         trans
           (sym $ ext≡ {x = inj₁ x} {y = y} {g = from ∘ to ∘ f})
           (trans (cong (flip ext _) $ ⟨ext⟩ hyp)
              (ext≡ {x = inj₁ x} {y = y} {g = f}))                ≡⟨ elim₁
                                                                       (λ {g} eq →
                                                                          trans
                                                                            (sym $ ext≡ {x = inj₁ x} {y = y} {g = g})
                                                                            (trans (cong (flip ext _) eq)
                                                                               (ext≡ {x = inj₁ x} {y = y} {g = f})) ≡
                                                                          ext⁻¹ eq y)
                                                                       (
           trans (sym ext≡)
             (trans (cong (flip ext _) (refl f)) ext≡)                  ≡⟨ cong (trans _) $
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
              (cong (flip ext _) $ ⟨ext⟩ λ y → cong (from ∘ to ∘ f) $
               _≃_.right-inverse-of PO.Susp≃Susp y)
              (cong (flip ext _) $ ⟨ext⟩ hyp))                            ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans
           (sym $ cong (from ∘ to) $
            ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (trans
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
              (cong id (ext≡ {x = inj₂ x} {y = y} {g = f})))              ≡⟨ cong₂ (trans ∘ sym)
                                                                               (sym $ cong-∘ _ _ _)
                                                                               (cong (trans _) $ sym $ cong-id _) ⟩
         trans
           (sym $ cong from $ cong to $
            ext≡ {x = inj₂ x} {y = y} {g = f})
           (trans
              (trans
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                 (cong (flip ext _) $ ⟨ext⟩ λ y →
                  cong (from ∘ to ∘ f) $
                  _≃_.right-inverse-of PO.Susp≃Susp y)
                 (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                  (cong (flip ext _) $ ⟨ext⟩ λ y →
                   cong (from ∘ to ∘ f) $ ext⁻¹ eq y)
                  (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                                                                                          (cong (flip ext _) $ ⟨ext⟩ λ y →
                                                                                           cong (from ∘ to ∘ f) $ ext⁻¹ eq y)
                                                                                          (cong (flip ext _) $ ⟨ext⟩ hyp))
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
                   (cong (flip ext _) $ ⟨ext⟩ λ y →
                    cong (from ∘ to ∘ f) $ ext⁻¹ (refl id) y)
                   (cong (flip ext _) $ ⟨ext⟩ hyp))
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
             (trans (cong (flip ext _) $ ⟨ext⟩ hyp)
                (ext≡ {x = inj₂ x} {y = y} {g = f}))                            ≡⟨ elim₁
                                                                                     (λ {g} eq →
                                                                                      trans
                                                                                        (sym $ ext≡ {x = inj₂ x} {y = y} {g = g})
                                                                                        (trans (cong (flip ext _) eq)
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

    .extʳ {x = inj₁ x} f _ → ext {x = inj₁ x} (f ∘ lower) _

    .extʳ {x = inj₂ x} f _ →
      ext {x = inj₂ x} (f ∘ _≃_.to PO.Susp≃Susp) _

    .ext≡ʳ {x = inj₁ x} {y = y} f →
      ext (f ∘ lower) _  ≡⟨ ext≡ {x = inj₁ x} {y = lift y} {g = f ∘ lower} ⟩∎
      f y                ∎

    .ext≡ʳ {x = inj₂ x} {y = y} f →
      ext (f ∘ _≃_.to PO.Susp≃Susp) _                    ≡⟨ ext≡ {x = inj₂ x} {y = _≃_.from PO.Susp≃Susp y} {g = f ∘ _≃_.to PO.Susp≃Susp} ⟩
      f (_≃_.to PO.Susp≃Susp (_≃_.from PO.Susp≃Susp y))  ≡⟨ cong f $ _≃_.right-inverse-of PO.Susp≃Susp y ⟩∎
      f y                                                ∎

  from′ = λ where
    .[]ʳ → [_]

    .extʳ {x = inj₁ x} f _ → ext {x = inj₁ x} (f ∘ lift) _

    .extʳ {x = inj₂ x} f _ →
      ext {x = inj₂ x} (f ∘ _≃_.from PO.Susp≃Susp) _

    .ext≡ʳ {x = inj₁ x} {y = y} f →
      ext (f ∘ lift) _  ≡⟨ ext≡ {x = inj₁ x} {y = lower y} {g = f ∘ lift} ⟩∎
      f y               ∎

    .ext≡ʳ {x = inj₂ x} {y = y} f →
      ext (f ∘ _≃_.from PO.Susp≃Susp) _                  ≡⟨ ext≡ {x = inj₂ x} {y = _≃_.to PO.Susp≃Susp y} {g = f ∘ _≃_.from PO.Susp≃Susp} ⟩
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
-- The nullification modality

-- The nullification modality for a given type family.

Nullification-modality :
  {A : Type a} (P : A → Type a) →
  Modality a
Nullification-modality {a = a} P =
  Σ-closed-reflective-subuniverse.modality λ where
    .Σ-closed-reflective-subuniverse.◯ → Nullification P

    .Σ-closed-reflective-subuniverse.η → [_]

    .Σ-closed-reflective-subuniverse.Modal A → P -Null A

    .Σ-closed-reflective-subuniverse.Modal-propositional _ →
      Π-closure I.ext 1 λ _ →
      Eq.propositional I.ext _

    .Σ-closed-reflective-subuniverse.Modal-◯ {A = A} →
                                                                          $⟨ Local-Localisation ⟩
      (λ x (_ : P x) → tt) -Local Localisation {P = P} {Q = λ _ → ⊤} _ A  ↝⟨ inverse Null≃Local ⟩
      P -Null Localisation {P = P} {Q = λ _ → ⊤} _ A                      ↝⟨ PS.Null-cong I.ext (λ _ → F.id) (inverse Nullification≃Localisation) ⟩□
      P -Null Nullification P A                                           □

    .Σ-closed-reflective-subuniverse.Modal-respects-≃
      {A = A} {B = B} A≃B →
      P -Null A  ↔⟨ PS.Null-cong I.ext (λ _ → F.id) A≃B ⟩□
      P -Null B  □

    .Σ-closed-reflective-subuniverse.extendable-along-η
      {B = B} {A = A} →
      P -Null B                                                         ↔⟨ Null≃Local ⟩

      (λ x (_ : P x) → tt) -Local B                                     →⟨ Local→Is-equivalence-[] ⟩

      Is-equivalence
        (λ (f : Localisation {P = P} {Q = λ _ → ⊤} _ A → B) → f ∘ [_])  ↔⟨ Is-equivalence≃Is-equivalence-∘ʳ
                                                                             (_≃_.is-equivalence $
                                                                              →-cong I.ext Nullification≃Localisation F.id)
                                                                             {k = equivalence}
                                                                             I.ext ⟩
      Is-equivalence
        ((_∘ [_]) ∘ (_∘ _≃_.from Nullification≃Localisation))           ↔⟨⟩

      Is-equivalence (λ (f : Nullification P A → B) → f ∘ [_])          ↔⟨ inverse $ PS.Is-∞-extendable-along≃Is-equivalence I.ext ⟩□

      Is-∞-extendable-along-[ [_] ] (λ (_ : Nullification P A) → B)     □

    .Σ-closed-reflective-subuniverse.Σ-closed {A = B} {P = Q} mB mQ x →
      _≃_.is-equivalence
        ((∃ λ (y : B) → Q y)                        ↝⟨ (∃-cong λ y → Eq.⟨ _ , mQ y x ⟩) ⟩
         (∃ λ (y : B) → P x → Q y)                  ↝⟨ (Σ-cong Eq.⟨ _ , mB x ⟩ λ _ → F.id) ⟩
         (∃ λ (f : P x → B) → (y : P x) → Q (f y))  ↔⟨ inverse ΠΣ-comm ⟩□
         (P x → ∃ λ (y : B) → Q y)                  □)

-- The nullification modality for P is accessible.

Nullification-accessible :
  {P : A → Type a} →
  Accessible (Nullification-modality P)
Nullification-accessible {a = a} {P = P} =
    _
  , P
  , (λ A →
       Modal A                                               ↔⟨⟩
       P -Null A                                             ↔⟨ inverse $ PS.Π-Is-∞-extendable-along≃Null I.ext ⟩□
       (∀ x →
          Is-∞-extendable-along-[ (λ (_ : P x) → lift tt) ]
            (λ (_ : ↑ a ⊤) → A))                             □)
  where
  open Modality (Nullification-modality P)

-- If P is pointwise propositional, then the nullification modality
-- for P is topological.

Nullification-topological :
  (∀ x → Is-proposition (P x)) →
  Topological (Nullification-modality P)
Nullification-topological prop =
  Nullification-accessible , prop

-- An alternative characterisation of "accessible".

Accessible≃≃ :
  (M : Modality a) →
  Accessible M ≃
  ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
  ∃ λ (eq : ∀ B → Modality.◯ M B ≃ Nullification P B) →
    ∀ B → _≃_.to (eq B) ∘ Modality.η M ≡ [_]
Accessible≃≃ {a = a} M =
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     (B : Type a) →
     Modal B ⇔
     ∀ x →
     Is-∞-extendable-along-[ (λ (_ : P x) → lift tt) ]
       (λ (_ : ↑ a ⊤) → B))                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong I.ext λ _ →
                                                            ⇔-cong I.ext F.id (PS.Π-Is-∞-extendable-along≃Null I.ext)) ⟩
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     (B : Type a) → Modal B ⇔ P -Null B)                ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                            Modal⇔Modal≃◯≃◯ I.ext M (Nullification-modality _) I.ext) ⟩□
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
   ∃ λ (eq : ∀ B → ◯ B ≃ Nullification P B) →
     ∀ B → _≃_.to (eq B) ∘ η ≡ [_])                     □
  where
  open Modality M

-- If a modality is accessible, then it is related to nullification in
-- a certain way.

Accessible→≃Nullification :
  (M : Modality a)
  ((_ , P , _) : Accessible M) →
  ∃ λ (eq : ∀ B → Modality.◯ M B ≃ Nullification P B) →
    ∀ B → _≃_.to (eq B) ∘ Modality.η M ≡ [_]
Accessible→≃Nullification M acc =
  _≃_.to (Accessible≃≃ M) acc .proj₂ .proj₂

-- Another alternative characterisation of "accessible".

Accessible≃≡ :
  Univalence a →
  (M : Modality a) →
  Accessible M ≃
  ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
    M ≡ Nullification-modality P
Accessible≃≡ {a = a} univ M =
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     (B : Type a) →
     Modal B ⇔
     ∀ x →
     Is-∞-extendable-along-[ (λ (_ : P x) → lift tt) ]
       (λ (_ : ↑ a ⊤) → B))                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong I.ext λ _ →
                                                            ⇔-cong I.ext F.id (PS.Π-Is-∞-extendable-along≃Null I.ext)) ⟩
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     (B : Type a) → Modal B ⇔ P -Null B)                ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                            Modal⇔Modal≃≡ I.ext univ) ⟩□
  (∃ λ (A : Type a) →
   ∃ λ (P : A → Type a) →
     M ≡ Nullification-modality P)                      □
  where
  open Modality M

-- An alternative characterisation of "topological".

Topological≃≃ :
  (M : Modality a) →
  Topological M ≃
  ∃ λ ((_ , P , _) :
       ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
       ∃ λ (eq : ∀ B → Modality.◯ M B ≃ Nullification P B) →
         (∀ B → _≃_.to (eq B) ∘ Modality.η M ≡ [_])) →
    ∀ x → Is-proposition (P x)
Topological≃≃ M = Σ-cong (Accessible≃≃ M) λ _ → F.id

-- Another alternative characterisation of "topological".

Topological≃≡ :
  Univalence a →
  (M : Modality a) →
  Topological M ≃
  ∃ λ ((_ , P , _) :
       ∃ λ (A : Type a) → ∃ λ (P : A → Type a) →
         M ≡ Nullification-modality P) →
    ∀ x → Is-proposition (P x)
Topological≃≡ univ M = Σ-cong (Accessible≃≡ univ M) λ _ → F.id
