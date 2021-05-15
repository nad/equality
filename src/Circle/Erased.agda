------------------------------------------------------------------------
-- The circle with an erased higher constructor
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly following the HoTT book.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the circle uses path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Circle.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Circle eq as C using (𝕊¹)
open import Equality.Groupoid equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence P.equality-with-J as PE
open import Erased.Cubical eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import Group equality-with-J as G using (_≃ᴳ_)
open import H-level equality-with-J
open import H-level.Truncation.Propositional.Erased eq as T using (∥_∥ᴱ)
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹)
open import H-level.Truncation.Propositional.One-step.Erased eq as OE
  using (∥_∥¹ᴱ)
open import Integer equality-with-J using (ℤ; +_; ℤ-group)
open import Nat equality-with-J
open import Pointed-type equality-with-J as PT using (_≃ᴮ_)
open import Pointed-type.Homotopy-group eq

private
  variable
    a p : Level
    A   : Type p
    P   : A → Type p
    b ℓ : A

------------------------------------------------------------------------
-- The type and some eliminators

-- The circle.

data 𝕊¹ᴱ : Type where
  base     : 𝕊¹ᴱ
  @0 loopᴾ : base P.≡ base

@0 loop : base ≡ base
loop = _↔_.from ≡↔≡ loopᴾ

-- A dependent eliminator, expressed using paths.

elimᴾ :
  (P : 𝕊¹ᴱ → Type p)
  (b : P base) →
  @0 P.[ (λ i → P (loopᴾ i)) ] b ≡ b →
  (x : 𝕊¹ᴱ) → P x
elimᴾ P b ℓ base      = b
elimᴾ P b ℓ (loopᴾ i) = ℓ i

-- A non-dependent eliminator, expressed using paths.

recᴾ : (b : A) → @0 b P.≡ b → 𝕊¹ᴱ → A
recᴾ = elimᴾ _

-- A dependent eliminator.

elim :
  (P : 𝕊¹ᴱ → Type p)
  (b : P base) →
  @0 subst P loop b ≡ b →
  (x : 𝕊¹ᴱ) → P x
elim P b ℓ = elimᴾ P b (subst≡→[]≡ ℓ)

-- A "computation" rule.

@0 elim-loop :
  dcong (elim P b ℓ) loop ≡ ℓ
elim-loop = dcong-subst≡→[]≡ (refl _)

-- Every dependent function of type (x : 𝕊¹ᴱ) → P x can be expressed
-- using elim.

η-elim :
  {f : (x : 𝕊¹ᴱ) → P x} →
  f ≡ elim P (f base) (dcong f loop)
η-elim {P = P} {f = f} =
  ⟨ext⟩ $ elim _ (refl _)
    (subst (λ x → f x ≡ elim P (f base) (dcong f loop) x) loop (refl _)  ≡⟨ subst-in-terms-of-trans-and-dcong ⟩

     trans (sym (dcong f loop))
       (trans (cong (subst P loop) (refl _))
          (dcong (elim P (f base) (dcong f loop)) loop))                 ≡⟨ cong (trans (sym (dcong f loop))) $
                                                                            trans (cong (flip trans _) $ cong-refl _) $
                                                                            trans-reflˡ _ ⟩
     trans (sym (dcong f loop))
       (dcong (elim P (f base) (dcong f loop)) loop)                     ≡⟨ cong (trans (sym (dcong f loop))) elim-loop ⟩

     trans (sym (dcong f loop)) (dcong f loop)                           ≡⟨ trans-symˡ _ ⟩∎

     refl _                                                              ∎)

-- A non-dependent eliminator.

rec : (b : A) → @0 b ≡ b → 𝕊¹ᴱ → A
rec b ℓ = recᴾ b (_↔_.to ≡↔≡ ℓ)

-- A "computation" rule.

@0 rec-loop : cong (rec b ℓ) loop ≡ ℓ
rec-loop = cong-≡↔≡ (refl _)

-- Every function from 𝕊¹ᴱ to A can be expressed using rec.

η-rec : {f : 𝕊¹ᴱ → A} → f ≡ rec (f base) (cong f loop)
η-rec {f = f} =
  ⟨ext⟩ $ elim _ (refl _)
    (subst (λ x → f x ≡ rec (f base) (cong f loop) x) loop (refl _)      ≡⟨ subst-in-terms-of-trans-and-cong ⟩

     trans (sym (cong f loop))
       (trans (refl _) (cong (rec (f base) (cong f loop)) loop))         ≡⟨ cong (trans (sym (cong f loop))) $ trans-reflˡ _ ⟩

     trans (sym (cong f loop)) (cong (rec (f base) (cong f loop)) loop)  ≡⟨ cong (trans (sym (cong f loop))) rec-loop ⟩

     trans (sym (cong f loop)) (cong f loop)                             ≡⟨ trans-symˡ _ ⟩∎

     refl _                                                              ∎)

------------------------------------------------------------------------
-- Conversion functions

-- There is a function from 𝕊¹ᴱ to 𝕊¹.

𝕊¹ᴱ→𝕊¹ : 𝕊¹ᴱ → 𝕊¹
𝕊¹ᴱ→𝕊¹ = rec C.base C.loop

-- In erased contexts 𝕊¹ is equivalent to 𝕊¹ᴱ.

@0 𝕊¹≃𝕊¹ᴱ : 𝕊¹ ≃ 𝕊¹ᴱ
𝕊¹≃𝕊¹ᴱ = Eq.↔→≃
  (C.rec base loop)
  𝕊¹ᴱ→𝕊¹
  (elim _ (refl _)
     (subst (λ x → C.rec base loop (𝕊¹ᴱ→𝕊¹ x) ≡ x) loop (refl _)  ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans (sym (cong (C.rec base loop ∘ 𝕊¹ᴱ→𝕊¹) loop))
        (trans (refl _) (cong id loop))                           ≡⟨ cong (trans _) $
                                                                     trans (trans-reflˡ _) $
                                                                     sym $ cong-id _ ⟩

      trans (sym (cong (C.rec base loop ∘ 𝕊¹ᴱ→𝕊¹) loop)) loop     ≡⟨ cong (flip trans _) $ cong sym $
                                                                     trans (sym $ cong-∘ _ _ _) $
                                                                     trans (cong (cong (C.rec base loop))
                                                                            rec-loop) $
                                                                     C.rec-loop ⟩

      trans (sym loop) loop                                       ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                      ∎))
  (C.elim _ (refl _)
     (subst (λ x → 𝕊¹ᴱ→𝕊¹ (C.rec base loop x) ≡ x) C.loop (refl _)  ≡⟨ subst-in-terms-of-trans-and-cong ⟩

      trans (sym (cong (𝕊¹ᴱ→𝕊¹ ∘ C.rec base loop) C.loop))
        (trans (refl _) (cong id C.loop))                           ≡⟨ cong (trans _) $
                                                                       trans (trans-reflˡ _) $
                                                                       sym $ cong-id _ ⟩

      trans (sym (cong (𝕊¹ᴱ→𝕊¹ ∘ C.rec base loop) C.loop)) C.loop   ≡⟨ cong (flip trans _) $ cong sym $
                                                                       trans (sym $ cong-∘ _ _ _) $
                                                                       trans (cong (cong 𝕊¹ᴱ→𝕊¹)
                                                                              C.rec-loop) $
                                                                       rec-loop ⟩

      trans (sym C.loop) C.loop                                     ≡⟨ trans-symˡ _ ⟩∎

      refl _                                                        ∎))

-- In erased contexts there is a based equivalence between 𝕊¹ , C.base
-- and 𝕊¹ᴱ , base.

@0 𝕊¹≃ᴮ𝕊¹ᴱ : (𝕊¹ , C.base) ≃ᴮ (𝕊¹ᴱ , base)
𝕊¹≃ᴮ𝕊¹ᴱ = 𝕊¹≃𝕊¹ᴱ , refl _

-- The one-step truncation of the unit type is equivalent to 𝕊¹ᴱ.
--
-- Paolo Capriotti informed me about the corresponding result without
-- erasure.

∥⊤∥¹ᴱ≃𝕊¹ᴱ : ∥ ⊤ ∥¹ᴱ ≃ 𝕊¹ᴱ
∥⊤∥¹ᴱ≃𝕊¹ᴱ = _↔_.from ≃↔≃ $ PE.↔→≃
  (OE.recᴾ λ where
     .OE.∣∣ʳ _            → base
     .OE.∣∣-constantʳ _ _ → loopᴾ)
  (recᴾ OE.∣ _ ∣ (OE.∣∣-constantᴾ _ _))
  (elimᴾ _ P.refl (λ _ → P.refl))
  (OE.elimᴾ λ where
     .OE.∣∣ʳ _              → P.refl
     .OE.∣∣-constantʳ _ _ _ → P.refl)

------------------------------------------------------------------------
-- The loop space of 𝕊¹ᴱ

-- The function trans is commutative for the loop space of 𝕊¹ᴱ.

trans-commutative : (p q : base ≡ base) → trans p q ≡ trans q p
trans-commutative =
  flip $ Transitivity-commutative.commutative base _∙_ ∙-base base-∙
  where
  _∙_ : 𝕊¹ᴱ → 𝕊¹ᴱ → 𝕊¹ᴱ
  x ∙ y = rec x (elim (λ x → x ≡ x) loop lemma x) y
    where
    @0 lemma : subst (λ x → x ≡ x) loop loop ≡ loop
    lemma = ≡⇒↝ _ (sym [subst≡]≡[trans≡trans]) (refl _)

  base-∙ : ∀ x → x ∙ base ≡ x
  base-∙ _ = refl _

  ∙-base : ∀ y → base ∙ y ≡ y
  ∙-base =
    elim _ (refl _)
      (subst (λ x → rec base loop x ≡ x) loop (refl _)         ≡⟨ subst-in-terms-of-trans-and-cong ⟩

       trans (sym (cong (rec base loop) loop))
         (trans (refl _) (cong id loop))                       ≡⟨ cong (trans _) $ trans-reflˡ _ ⟩

       trans (sym (cong (rec base loop) loop)) (cong id loop)  ≡⟨ cong₂ (trans ∘ sym)
                                                                    rec-loop
                                                                    (sym $ cong-id _) ⟩

       trans (sym loop) loop                                   ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                  ∎)

-- The loop space is equivalent to x ≡ x, for any x : 𝕊¹ᴱ.

base≡base≃≡ : {x : 𝕊¹ᴱ} → (base ≡ base) ≃ (x ≡ x)
base≡base≃≡ = elim
  (λ x → (base ≡ base) ≃ (x ≡ x))
  Eq.id
  (Eq.lift-equality ext $ ⟨ext⟩ λ eq →
   _≃_.to (subst (λ x → (base ≡ base) ≃ (x ≡ x)) loop Eq.id) eq        ≡⟨ cong (_$ eq) Eq.to-subst ⟩
   subst (λ x → base ≡ base → x ≡ x) loop id eq                        ≡⟨ subst-→ ⟩
   subst (λ x → x ≡ x) loop (subst (λ _ → base ≡ base) (sym loop) eq)  ≡⟨ cong (subst (λ x → x ≡ x) loop) $ subst-const _ ⟩
   subst (λ x → x ≡ x) loop eq                                         ≡⟨ ≡⇒↝ _ (sym [subst≡]≡[trans≡trans]) (

       trans eq loop                                                        ≡⟨ trans-commutative _ _ ⟩∎
       trans loop eq                                                        ∎) ⟩∎

   eq                                                                  ∎)
  _

-- In erased contexts the loop space of 𝕊¹ᴱ is equivalent to the type
-- of integers.

@0 base≡base≃ℤ : (base ≡ base) ≃ ℤ
base≡base≃ℤ =
  base ≡ base      ↝⟨ Eq.≃-≡ 𝕊¹≃𝕊¹ᴱ ⟩
  C.base ≡ C.base  ↝⟨ C.base≡base≃ℤ ⟩□
  ℤ                □

-- In erased contexts the fundamental group of 𝕊¹ᴱ is equivalent to
-- the group of integers.

@0 Fundamental-group≃ℤ : Fundamental-group (𝕊¹ᴱ , base) ≃ᴳ ℤ-group
Fundamental-group≃ℤ =
  G.↝ᴳ-trans (G.≃ᴳ-sym $ ≃ᴮ→≃ᴳ _ _ 0 𝕊¹≃ᴮ𝕊¹ᴱ) C.Fundamental-group≃ℤ

-- 𝕊¹ᴱ is a groupoid (in erased contexts).

@0 𝕊¹ᴱ-groupoid : H-level 3 𝕊¹ᴱ
𝕊¹ᴱ-groupoid =   $⟨ (λ {_ _ _ _} → C.𝕊¹-groupoid) ⟩
  H-level 3 𝕊¹   ↝⟨ H-level-cong _ 3 𝕊¹≃𝕊¹ᴱ ⦂ (_ → _) ⟩□
  H-level 3 𝕊¹ᴱ  □

-- The type of endofunctions on 𝕊¹ᴱ is equivalent to
-- ∃ λ (x : 𝕊¹ᴱ) → Erased (x ≡ x).

𝕊¹ᴱ→𝕊¹ᴱ≃Σ𝕊¹ᴱ-Erased≡ : (𝕊¹ᴱ → 𝕊¹ᴱ) ≃ ∃ λ (x : 𝕊¹ᴱ) → Erased (x ≡ x)
𝕊¹ᴱ→𝕊¹ᴱ≃Σ𝕊¹ᴱ-Erased≡ = Eq.↔→≃ to from to-from from-to
  where
  to : (𝕊¹ᴱ → 𝕊¹ᴱ) → ∃ λ (x : 𝕊¹ᴱ) → Erased (x ≡ x)
  to f = f base , [ cong f loop ]

  from : (∃ λ (x : 𝕊¹ᴱ) → Erased (x ≡ x)) → (𝕊¹ᴱ → 𝕊¹ᴱ)
  from (x , [ eq ]) = rec x eq

  to-from : ∀ p → to (from p) ≡ p
  to-from (x , [ eq ]) = cong (x ,_)
    ([ cong (rec x eq) loop ]  ≡⟨ []-cong [ rec-loop ] ⟩∎
     [ eq ]                    ∎)

  from-to : ∀ f → from (to f) ≡ f
  from-to f =
    rec (f base) (cong f loop)  ≡⟨ sym η-rec ⟩∎
    f                           ∎

-- The type of endofunctions on 𝕊¹ᴱ is equivalent to 𝕊¹ᴱ × Erased ℤ.

𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ : (𝕊¹ᴱ → 𝕊¹ᴱ) ≃ (𝕊¹ᴱ × Erased ℤ)
𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ =
  (𝕊¹ᴱ → 𝕊¹ᴱ)                       ↝⟨ 𝕊¹ᴱ→𝕊¹ᴱ≃Σ𝕊¹ᴱ-Erased≡ ⟩
  (∃ λ (x : 𝕊¹ᴱ) → Erased (x ≡ x))  ↝⟨ (∃-cong λ _ → Erased-cong (inverse base≡base≃≡)) ⟩
  𝕊¹ᴱ × Erased (base ≡ base)        ↝⟨ (∃-cong λ _ → Erased-cong base≡base≃ℤ) ⟩□
  𝕊¹ᴱ × Erased ℤ                    □

-- The forward direction of 𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ maps the identity
-- function to base , [ + 1 ].

𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ-id :
  _≃_.to 𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ id ≡ (base , [ + 1 ])
𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ-id = _≃_.from-to 𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ
  (rec base (cong (_≃_.to 𝕊¹≃𝕊¹ᴱ) (trans (refl C.base) C.loop))  ≡⟨ cong (λ ([ ℓ ]) → rec base ℓ) $ []-cong [ lemma ] ⟩
   rec base (cong id loop)                                       ≡⟨ sym η-rec ⟩∎
   id                                                            ∎)
  where
  @0 lemma : _
  lemma =
    cong (_≃_.to 𝕊¹≃𝕊¹ᴱ) (trans (refl C.base) C.loop)  ≡⟨ cong (cong (_≃_.to 𝕊¹≃𝕊¹ᴱ)) $ trans-reflˡ _ ⟩
    cong (_≃_.to 𝕊¹≃𝕊¹ᴱ) C.loop                        ≡⟨ C.rec-loop ⟩
    loop                                               ≡⟨ cong-id _ ⟩∎
    cong id loop                                       ∎

-- The forward direction of 𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ maps the constant
-- function returning base to base , [ + 0 ].

𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ-const :
  _≃_.to 𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ (const base) ≡ (base , [ + 0 ])
𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ-const = _≃_.from-to 𝕊¹ᴱ→𝕊¹ᴱ≃𝕊¹ᴱ×Erased-ℤ
  (rec base (cong (_≃_.to 𝕊¹≃𝕊¹ᴱ) (refl C.base))  ≡⟨ cong (λ ([ ℓ ]) → rec base ℓ) $ []-cong [ lemma ] ⟩
   rec base (cong (const base) loop)              ≡⟨ sym η-rec ⟩∎
   const base                                     ∎)
  where
  @0 lemma : _
  lemma =
    cong (_≃_.to 𝕊¹≃𝕊¹ᴱ) (refl C.base)  ≡⟨ cong-refl _ ⟩
    refl _                              ≡⟨ sym $ cong-const _ ⟩∎
    cong (const base) loop              ∎

------------------------------------------------------------------------
-- Some negative results

-- The equality loop is not equal to refl base.

loop≢refl : loop ≢ refl base
loop≢refl =
  Stable-¬
    [ loop ≡ refl base                                                  ↔⟨ inverse $ Eq.≃-≡ $ inverse $ Eq.≃-≡ $ inverse 𝕊¹≃𝕊¹ᴱ ⟩
      cong (_≃_.from 𝕊¹≃𝕊¹ᴱ) loop ≡ cong (_≃_.from 𝕊¹≃𝕊¹ᴱ) (refl base)  ↝⟨ trans (sym rec-loop) ∘ flip trans (cong-refl _) ⟩
      C.loop ≡ refl C.base                                              ↝⟨ C.loop≢refl ⟩□
      ⊥                                                                 □
    ]

-- 𝕊¹ᴱ is not a set.

¬-𝕊¹ᴱ-set : ¬ Is-set 𝕊¹ᴱ
¬-𝕊¹ᴱ-set =
  Stable-¬
    [ Is-set 𝕊¹ᴱ  ↝⟨ H-level-cong _ 2 $ inverse 𝕊¹≃𝕊¹ᴱ ⟩
      Is-set 𝕊¹   ↝⟨ C.¬-𝕊¹-set ⟩□
      ⊥           □
    ]

-- It is not necessarily the case that the one-step truncation of a
-- proposition is a proposition.

¬-Is-proposition-∥∥¹ᴱ :
  ¬ ({A : Type a} → Is-proposition A → Is-proposition ∥ A ∥¹ᴱ)
¬-Is-proposition-∥∥¹ᴱ {a = a} =
  Stable-¬
    [ ({A : Type a} → Is-proposition A → Is-proposition ∥ A ∥¹ᴱ)  ↝⟨ (implicit-∀-cong _ $ ∀-cong _ λ _ → H-level-cong _ 1 O.∥∥¹ᴱ≃∥∥¹) ⟩
      ({A : Type a} → Is-proposition A → Is-proposition ∥ A ∥¹)   ↝⟨ C.¬-Is-proposition-∥∥¹ ⟩□
      ⊥                                                           □
    ]

-- A function with the type of refl (for 𝕊¹ᴱ) that is not equal to
-- refl. The function is available in erased contexts.

@0 not-refl : (x : 𝕊¹ᴱ) → x ≡ x
not-refl x =           $⟨ C.not-refl (𝕊¹ᴱ→𝕊¹ x) ⟩
  𝕊¹ᴱ→𝕊¹ x ≡ 𝕊¹ᴱ→𝕊¹ x  ↝⟨ Eq.≃-≡ $ inverse 𝕊¹≃𝕊¹ᴱ ⟩□
  x ≡ x                □

-- The function not-refl is not equal to refl.

not-refl≢refl : not-refl ≢ refl
not-refl≢refl =
  Stable-¬
    [ not-refl ≡ refl                                                ↔⟨⟩

      _≃_.to (Eq.≃-≡ $ inverse 𝕊¹≃𝕊¹ᴱ) ∘ C.not-refl ∘ 𝕊¹ᴱ→𝕊¹ ≡ refl  ↝⟨ flip trans (⟨ext⟩ lemma) ⟩

      _≃_.to (Eq.≃-≡ $ inverse 𝕊¹≃𝕊¹ᴱ) ∘ C.not-refl ∘ 𝕊¹ᴱ→𝕊¹ ≡
      _≃_.to (Eq.≃-≡ $ inverse 𝕊¹≃𝕊¹ᴱ) ∘ refl ∘ 𝕊¹ᴱ→𝕊¹               ↔⟨ (Eq.≃-≡ $ inverse $
                                                                         Π-cong ext (inverse 𝕊¹≃𝕊¹ᴱ) λ _ →
                                                                         inverse $ Eq.≃-≡ $ inverse 𝕊¹≃𝕊¹ᴱ) ⟩

      C.not-refl ≡ refl                                              ↝⟨ C.not-refl≢refl ⟩□

      ⊥                                                              □
    ]
  where
  @0 lemma : _
  lemma x = sym $ _≃_.from-to (Eq.≃-≡ $ Eq.inverse 𝕊¹≃𝕊¹ᴱ)
    (_≃_.from (Eq.≃-≡ $ Eq.inverse 𝕊¹≃𝕊¹ᴱ) (refl x)  ≡⟨⟩
     cong 𝕊¹ᴱ→𝕊¹ (refl x)                            ≡⟨ cong-refl _ ⟩∎
     refl (𝕊¹ᴱ→𝕊¹ x)                                 ∎)

-- For every universe level there is a type A such that
-- (x : A) → x ≡ x is not a proposition.

¬-type-of-refl-propositional :
  ∃ λ (A : Type a) → ¬ Is-proposition ((x : A) → x ≡ x)
¬-type-of-refl-propositional {a = a} =
    ↑ _ 𝕊¹ᴱ
  , Stable-¬
      [ Is-proposition ((x : ↑ _ 𝕊¹ᴱ) → x ≡ x)  ↝⟨ (H-level-cong _ 1 $
                                                    Π-cong ext (↑-cong $ inverse 𝕊¹≃𝕊¹ᴱ) λ _ →
                                                    inverse $ Eq.≃-≡ $ ↑-cong $ inverse 𝕊¹≃𝕊¹ᴱ) ⟩
        Is-proposition ((x : ↑ _ 𝕊¹) → x ≡ x)   ↝⟨ proj₂ C.¬-type-of-refl-propositional ⟩□
        ⊥                                       □
      ]

-- Every value of type 𝕊¹ᴱ is merely equal to the base point (using
-- ∥_∥ᴱ to express "merely").
--
-- A variant of this lemma was mentioned by Mike Shulman in a blog
-- post (http://homotopytypetheory.org/2013/07/24/cohomology/).

all-points-on-the-circle-are-merely-equal :
  (x : 𝕊¹ᴱ) → ∥ x ≡ base ∥ᴱ
all-points-on-the-circle-are-merely-equal =
  elim _
       T.∣ refl base ∣
       (T.truncation-is-proposition _ _)

-- Every value of type 𝕊¹ᴱ is not not equal to the base point.

all-points-on-the-circle-are-¬¬-equal :
  (x : 𝕊¹ᴱ) → ¬ ¬ x ≡ base
all-points-on-the-circle-are-¬¬-equal x =
  Stable-¬
    [ x ≢ base           ↔⟨ →-cong ext (inverse $ Eq.≃-≡ $ inverse 𝕊¹≃𝕊¹ᴱ) Eq.id ⟩
      𝕊¹ᴱ→𝕊¹ x ≢ C.base  ↝⟨ C.all-points-on-the-circle-are-¬¬-equal _ ⟩□
      ⊥                  □
    ]

-- It is not the case that every value of type 𝕊¹ᴱ is equal to the
-- base point.

¬-all-points-on-the-circle-are-equal :
  ¬ ((x : 𝕊¹ᴱ) → x ≡ base)
¬-all-points-on-the-circle-are-equal =
  Stable-¬
    [ ((x : 𝕊¹ᴱ) → x ≡ base)   ↔⟨ (Π-cong ext (inverse 𝕊¹≃𝕊¹ᴱ) λ _ →
                                   inverse $ Eq.≃-≡ $ Eq.inverse 𝕊¹≃𝕊¹ᴱ) ⟩
      ((x : 𝕊¹) → x ≡ C.base)  ↝⟨ C.¬-all-points-on-the-circle-are-equal ⟩□
      ⊥                        □
    ]

-- Double-negation shift for Type-valued predicates over 𝕊¹ᴱ does not
-- hold in general.

¬-double-negation-shift :
  ¬ ({P : 𝕊¹ᴱ → Type} → ((x : 𝕊¹ᴱ) → ¬ ¬ P x) → ¬ ¬ ((x : 𝕊¹ᴱ) → P x))
¬-double-negation-shift =
  Stable-¬
    [ ({P : 𝕊¹ᴱ → Type} → ((x : 𝕊¹ᴱ) → ¬ ¬ P x) → ¬ ¬ ((x : 𝕊¹ᴱ) → P x))  ↔⟨ (implicit-Π-cong ext
                                                                                (→-cong₁ {k₂ = equivalence} ext $ inverse 𝕊¹≃𝕊¹ᴱ) λ _ →
                                                                              →-cong ext (inverse $ Π-cong ext 𝕊¹≃𝕊¹ᴱ λ _ → Eq.id) $
                                                                              ¬-cong ext $ ¬-cong ext $ inverse $ Π-cong ext 𝕊¹≃𝕊¹ᴱ λ _ → Eq.id) ⟩
      ({P : 𝕊¹ → Type} → ((x : 𝕊¹) → ¬ ¬ P x) → ¬ ¬ ((x : 𝕊¹) → P x))     ↝⟨ C.¬-double-negation-shift ⟩□
      ⊥                                                                   □
    ]

-- H-level.Closure.proj₁-closure cannot be generalised by replacing
-- the assumption ∀ a → B a with ∀ a → ∥ B a ∥ᴱ.
--
-- A variant of this observation is due to Andrea Vezzosi.

¬-generalised-proj₁-closure :
  ¬ ({A : Type} {B : A → Type} →
     (∀ a → ∥ B a ∥ᴱ) →
     ∀ n → H-level n (Σ A B) → H-level n A)
¬-generalised-proj₁-closure generalised-proj₁-closure =
                                  $⟨ singleton-contractible _ ⟩
  Contractible (Σ 𝕊¹ᴱ (_≡ base))  ↝⟨ generalised-proj₁-closure
                                       all-points-on-the-circle-are-merely-equal
                                       0 ⟩
  Contractible 𝕊¹ᴱ                ↝⟨ ¬-𝕊¹ᴱ-set ∘ mono (zero≤ 2) ⟩□
  ⊥                               □

-- There is no based equivalence between 𝕊¹ᴱ and the product of 𝕊¹ᴱ
-- with itself.

𝕊¹ᴱ≄ᴮ𝕊¹ᴱ×𝕊¹ᴱ : ¬ (𝕊¹ᴱ , base) ≃ᴮ ((𝕊¹ᴱ , base) PT.× (𝕊¹ᴱ , base))
𝕊¹ᴱ≄ᴮ𝕊¹ᴱ×𝕊¹ᴱ =
  Stable-¬
    [ (𝕊¹ᴱ , base) ≃ᴮ ((𝕊¹ᴱ , base) PT.× (𝕊¹ᴱ , base))     ↝⟨ PT.↝ᴮ-trans 𝕊¹≃ᴮ𝕊¹ᴱ ∘
                                                              flip PT.↝ᴮ-trans (PT.≃ᴮ-sym (𝕊¹≃ᴮ𝕊¹ᴱ PT.×-cong-≃ᴮ 𝕊¹≃ᴮ𝕊¹ᴱ)) ⟩
      (𝕊¹ , C.base) ≃ᴮ ((𝕊¹ , C.base) PT.× (𝕊¹ , C.base))  ↝⟨ C.𝕊¹≄ᴮ𝕊¹×𝕊¹ ⟩□
      ⊥                                                    □
    ]

-- 𝕊¹ᴱ is not equivalent to 𝕊¹ᴱ × 𝕊¹ᴱ.

𝕊¹ᴱ≄𝕊¹ᴱ×𝕊¹ᴱ : ¬ 𝕊¹ᴱ ≃ (𝕊¹ᴱ × 𝕊¹ᴱ)
𝕊¹ᴱ≄𝕊¹ᴱ×𝕊¹ᴱ =
  Stable-¬
    [ 𝕊¹ᴱ ≃ (𝕊¹ᴱ × 𝕊¹ᴱ)  ↔⟨ Eq.≃-preserves ext (inverse 𝕊¹≃𝕊¹ᴱ) (inverse $ 𝕊¹≃𝕊¹ᴱ ×-cong 𝕊¹≃𝕊¹ᴱ) ⟩
      𝕊¹ ≃ (𝕊¹ × 𝕊¹)     ↝⟨ C.𝕊¹≄𝕊¹×𝕊¹ ⟩□
      ⊥                  □
    ]
