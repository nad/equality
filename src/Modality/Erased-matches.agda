------------------------------------------------------------------------
-- Some results that hold for a modality, implemented using
-- --erased-matches
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --erased-matches #-}

open import Equality
import Modality.Basics

module Modality.Erased-matches
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (open Modality.Basics eq)
  {a}
  (M : Modality a)
  where

open Derived-definitions-and-properties eq
open Modality M hiding (◯Wη→W◯; ◯Wη→W◯-η; Stable-W)

import Modality.Has-choice
open import Prelude

open import Accessibility eq as A using (Acc; _<W_)
import Accessibility.Erased-matches eq as AE
open import Equivalence eq as Eq using (_≃_)
open import Erased.Box-cong-axiomatisation eq
  using ([]-cong-axiomatisation)
import Erased.Level-1 eq as E
open import Extensionality eq
open import Function-universe eq hiding (id; _∘_)

private variable
  ℓ   : Level
  A   : Type ℓ
  P   : A → Type ℓ
  k x : A

------------------------------------------------------------------------
-- Accessibility-modal modalities

-- Accessibility-modal-for _<_ is "erasure-stable".

Accessibility-modal-for-erasure-stable :
  {@0 A : Type a} {@0 _<_ : A → A → Type a} →
  E.Stable (Accessibility-modal-for _<_)
Accessibility-modal-for-erasure-stable E.[ acc₁ , acc₂ ] =
    (λ acc → AE.Acc-erasure-stable E.[ acc₁ acc ])
  , (λ acc → AE.Acc-erasure-stable E.[ acc₂ acc ])

-- Accessibility-modal is "erasure-stable".

Accessibility-modal-erasure-stable :
  E.Stable Accessibility-modal
Accessibility-modal-erasure-stable E.[ acc ] =
  Accessibility-modal-for-erasure-stable E.[ acc ]

private

  -- A lemma used in the implementation of ◯Wη→W◯.

  ◯Wη→W◯-Acc :
    @0 Extensionality a a →
    (x : ◯ (W A (P ∘ η))) →
    @0 Acc _[ _<W_ ]◯_ x →
    W (◯ A) P
  ◯Wη→W◯-Acc {P} ext w (A.acc a) =
    sup x′ λ y → ◯Wη→W◯-Acc ext (f′ y) (a (f′ y) (f′<w y))
    where
    p′ = ◯Wη→Σ◯Π◯Wη {P = P} w

    x′ = p′ .proj₁
    f′ = p′ .proj₂

    @0 f′<w : ∀ y → f′ y [ _<W_ ]◯ w
    f′<w =
      ◯-elim′
        {P = λ w →
               let (x′ , f′) = ◯Wη→Σ◯Π◯Wη {P = P} w in
               ∀ y → f′ y [ _<W_ ]◯ w}
        (λ _ → Stable-Π λ _ → Modal→Stable Modal-◯)
        (λ @0 where
           w@(sup x f) y →
             let x′ , f′ = ◯Wη→Σ◯Π◯Wη (η w)

                 @0 lemma : (x′ , f′) ≡ (η x , η ∘ f)
                 lemma = ◯Wη→Σ◯Π◯Wη-η ext
             in
             η ( f (subst (P ∘ proj₁) lemma y)
               , w
               , (f′ y                               ≡⟨ elim₁
                                                          (λ {(x′ , f′)} eq →
                                                             (y : P x′) → f′ y ≡ η (f (subst (P ∘ proj₁) eq y)))
                                                          (λ _ → cong (η ∘ f) $ sym $ subst-refl _ _)
                                                          lemma y ⟩∎
                  η (f (subst (P ∘ proj₁) lemma y))  ∎)
               , (η w  ∎)
               , (_ , refl _)
               ))
        w

  -- A "computation rule" for ◯Wη→W◯-Acc.

  ◯Wη→W◯-Acc-η :
    (@0 ext : Extensionality a a) →
    Extensionality a a →
    []-cong-axiomatisation a →
    (x : W A (P ∘ η))
    (@0 acc : Acc _[ _<W_ ]◯_ (η x)) →
    ◯Wη→W◯-Acc {P = P} ext (η x) acc ≡ W-map η id x
  ◯Wη→W◯-Acc-η {A} {P} ext ext′ ax (sup x f) (A.acc acc) =
    cong (uncurry sup) $
    Σ-≡,≡→≡
      (cong proj₁ lemma)
      (apply-ext ext′ λ y →
         let @0 acc₁ : ∀ y → Acc _[ _<W_ ]◯_ (p′ .proj₂ y)
             acc₁ = _
         in
         subst (λ y → P y → W (◯ A) P)
           (cong proj₁ lemma)
           (λ y → ◯Wη→W◯-Acc ext (p′ .proj₂ y) (acc₁ y))
           y
                                                          ≡⟨ elim₁
                                                               (λ {(x′ , f′)} lemma →
                                                                  (y : P (η x))
                                                                  (@0 acc₁ : (y : P x′) → Acc _[ _<W_ ]◯_ (f′ y)) →
                                                                  subst (λ y → P y → W (◯ A) P)
                                                                    (cong proj₁ lemma)
                                                                    (λ y → ◯Wη→W◯-Acc ext (f′ y) (acc₁ y))
                                                                    y ≡
                                                                  ◯Wη→W◯-Acc ext (η (f y)) (acc₂ y))
                                                               (λ y (@0 acc₁) →
           subst (λ y → P y → W (◯ A) P)
             (cong proj₁ (refl _))
             (λ y → ◯Wη→W◯-Acc ext (η (f y)) (acc₁ y))
             y                                                    ≡⟨ cong (_$ y) $ cong (flip (subst (λ y → P y → W (◯ A) P)) _) $
                                                                     cong-refl _ ⟩
           subst (λ y → P y → W (◯ A) P)
             (refl _)
             (λ y → ◯Wη→W◯-Acc ext (η (f y)) (acc₁ y))
             y                                                    ≡⟨ cong (_$ y) $ subst-refl _ _ ⟩

           ◯Wη→W◯-Acc ext (η (f y)) (acc₁ y)                      ≡⟨ cong (λ acc → ◯Wη→W◯-Acc ext (η (f y)) (E.erased acc)) $
                                                                     []-cong-axiomatisation.[]-cong ax E.[ A.Acc-propositional ext _ _ ] ⟩∎
           ◯Wη→W◯-Acc ext (η (f y)) (acc₂ y)                      ∎)
                                                               lemma y acc₁ ⟩

         ◯Wη→W◯-Acc ext (η (f y)) (acc₂ y)                ≡⟨ ◯Wη→W◯-Acc-η ext ext′ ax (f y) (acc₂ y) ⟩∎

         W-map η id (f y)                                 ∎)
    where
    p′ = ◯Wη→Σ◯Π◯Wη {P = P} (η (sup x f))

    lemma : p′ ≡ (η x , η ∘ f)
    lemma = ◯Wη→Σ◯Π◯Wη-η ext′

    @0 acc₂ : ∀ y → Acc _[ _<W_ ]◯_ (η (f y))
    acc₂ y =
      acc (η (f y)) (η (_ , _ , refl _ , refl _ , _ , refl _))

-- If the modality is accessibility-modal for a certain relation,
-- then ◯ (W A (P ∘ η)) implies W (◯ A) P (assuming function
-- extensionality).
--
-- See also W◯→◯Wη in Modality.Has-choice and ◯Wη≃W◯ below.

◯Wη→W◯ :
  {P : ◯ A → Type a} →
  @0 Accessibility-modal-for (_<W_ {A = A} {P = P ∘ η}) →
  @0 Extensionality a a →
  ◯ (W A (P ∘ η)) → W (◯ A) P
◯Wη→W◯ {A} {P} acc ext =
  ◯ (W A (P ∘ η))                                      →⟨ ◯-map (λ x → x , A.Well-founded-W x) ⟩
  ◯ (∃ λ (x : W A (P ∘ η)) → Acc _<W_ x)               →⟨ ◯-map (Σ-map id (acc′ .proj₁)) ⟩
  ◯ (∃ λ (x : W A (P ∘ η)) → Acc _[ _<W_ ]◯_ (η x))    →⟨ ◯Ση≃Σ◯◯ _ ⟩
  (∃ λ (x : ◯ (W A (P ∘ η))) → ◯ (Acc _[ _<W_ ]◯_ x))  →⟨ Σ-map id (acc′ .proj₂) ⟩
  (∃ λ (x : ◯ (W A (P ∘ η))) → Acc _[ _<W_ ]◯_ x)      →⟨ (λ (x , a) → ◯Wη→W◯-Acc ext x a) ⟩□
  W (◯ A) P                                            □
  where
  acc′ = Accessibility-modal-for-erasure-stable E.[ acc ]

-- A "computation rule" for ◯Wη→W◯.
--
-- Note that the final argument can be proved using the previous
-- one, see Erased.Level-1.Extensionality→[]-cong-axiomatisation.

◯Wη→W◯-η :
  {x : W A (P ∘ η)}
  (@0 acc : Accessibility-modal-for _<W_)
  (@0 ext : Extensionality a a) →
  Extensionality a a →
  []-cong-axiomatisation a →
  ◯Wη→W◯ {P = P} acc ext (η x) ≡ W-map η id x
◯Wη→W◯-η {A} {P} {x} acc ext ext′ ax =
  (λ (x , a) → ◯Wη→W◯-Acc ext x (acc′ .proj₂ a))
    (◯Ση≃Σ◯◯ _
       (◯-map (Σ-map id (acc′ .proj₁))
          (◯-map (λ x → x , A.Well-founded-W x) (η x))))  ≡⟨ cong (λ (x , a) → ◯Wη→W◯-Acc ext x (acc′ .proj₂ a)) $
                                                             trans (cong (◯Ση≃Σ◯◯ _) $
                                                                    trans (cong (◯-map _) ◯-map-η)
                                                                    ◯-map-η)
                                                             ◯-rec-η ⟩
  (λ (x , a) → ◯Wη→W◯-Acc ext x (acc′ .proj₂ a))
    (η x , η (acc′ .proj₁ (A.Well-founded-W x)))          ≡⟨⟩

  ◯Wη→W◯-Acc ext (η x)
    (acc′ .proj₂ (η (acc′ .proj₁ (A.Well-founded-W x))))  ≡⟨ ◯Wη→W◯-Acc-η ext ext′ ax _ _ ⟩∎

  W-map η id x                                            ∎
  where
  acc′ = Accessibility-modal-for-erasure-stable E.[ acc ]

-- If the modality is accessibility-modal for a certain relation and
-- A is modal, then W A P is stable (assuming function
-- extensionality).

Stable-W :
  @0 Accessibility-modal-for (_<W_ {A = A} {P = P}) →
  @0 Extensionality a a →
  Modal A →
  Stable (W A P)
Stable-W {A} {P} acc ext m =
  ◯ (W A P)                         →⟨ ◯-map $ W-map id (subst P Modal→Stable-η) ⟩
  ◯ (W A (P ∘ Modal→Stable m ∘ η))  →⟨ ◯Wη→W◯ acc′ ext ⟩
  W (◯ A) (P ∘ Modal→Stable m)      →⟨ W-map (Modal→Stable m) id ⟩□
  W A P                             □
  where
  @0 acc′ :
    Accessibility-modal-for
      (_<W_ {A = A} {P = P ∘ Modal→Stable m ∘ η})
  acc′ =
    subst
      (λ f → Accessibility-modal-for (_<W_ {A = A} {P = P ∘ f}))
      (apply-ext ext λ _ → sym Modal→Stable-η)
      acc

------------------------------------------------------------------------
-- Some results that hold for modalities that satisfy a choice
-- principle

-- The choice principle is only required to hold for "valid" domains.

module Has-choice
  (Valid-domain : Type a → Type a)
  (has-choice :
   {A : Type a} →
   Valid-domain A → Modality.Has-choice-for M A)
  where

  private
    open module H = Modality.Has-choice eq M Valid-domain has-choice
      hiding (module Valid-domain-Π◯;
              module Valid-domain-Π;
              module Valid-domain)

  -- A result that holds if a given family of types is valid
  -- (pointwise).

  module Valid-domain-Π◯
    (P : ◯ A → Type a)
    (v : ∀ x → Valid-domain (P x))
    where

    private
      open module V₁ {x} = Valid-domain₁ (v x)
      open H.Valid-domain-Π◯ _ v hiding (◯Wη≃W◯)

    -- If the modality has choice and is accessibility-modal for a
    -- certain relation, then ◯ commutes with W in a certain way
    -- (assuming function extensionality).

    ◯Wη≃W◯ :
      @0 Accessibility-modal-for (_<W_ {A = A} {P = P ∘ η}) →
      @0 Extensionality a a →
      ◯ (W A (P ∘ η)) ↝[ a ∣ a ] W (◯ A) P
    ◯Wη≃W◯ acc ext =
      generalise-ext?
        (record { to = ◯Wη→W◯ acc ext; from = W◯→◯Wη })
        (λ ext′ → to-from ext′ , from-to ext′)
      where
      module _ (ext′ : Extensionality a a) where
        ax = E.Extensionality→[]-cong-axiomatisation ext′

        from-to : ∀ x → W◯→◯Wη (◯Wη→W◯ acc ext x) ≡ x
        from-to =
          ◯-elim
            (λ _ → Separated-◯ _ _)
            (λ x →
               W◯→◯Wη (◯Wη→W◯ acc ext (η x))  ≡⟨ cong W◯→◯Wη $
                                                 ◯Wη→W◯-η acc ext ext′ ax ⟩
               W◯→◯Wη (W-map η id x)          ≡⟨ W◯→◯Wη-W-map-η-id ext′ ⟩∎
               η x                            ∎)

        to-from : ∀ x → ◯Wη→W◯ acc ext (W◯→◯Wη x) ≡ x
        to-from (sup x f) =
          ◯-elim
            {P = λ x →
                   ∀ f →
                   (∀ y → ◯Wη→W◯ acc ext (W◯→◯Wη (f y)) ≡ f y) →
                   ◯Wη→W◯ acc ext (W◯→◯Wη (sup x f)) ≡
                   sup x f}
            (λ _ → Modal-Π ext′ λ _ →
                   Modal-Π ext′ λ _ →
                   Separated-W ext′ Separated-◯ _ _)
            (λ x f hyp →
               ◯Wη→W◯ acc ext (W◯→◯Wη (sup (η x) f))                    ≡⟨ cong (◯Wη→W◯ acc ext) $ W◯→◯Wη-sup-η ext′ f ⟩

               ◯Wη→W◯ acc ext (◯-map (sup x) (Π◯→◯Π (W◯→◯Wη ∘ f)))      ≡⟨ ◯-elim
                                                                             {P = λ f′ →
                                                                                    ◯Wη→W◯ acc ext (◯-map (sup x) f′) ≡
                                                                                    sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ f′)}
                                                                             (λ _ → Separated-W ext′ Separated-◯ _ _)
                                                                             (λ f′ →
                 ◯Wη→W◯ acc ext (◯-map (sup x) (η f′))                          ≡⟨ cong (◯Wη→W◯ acc ext)
                                                                                   ◯-map-η ⟩
                 ◯Wη→W◯ acc ext (η (sup x f′))                                  ≡⟨ ◯Wη→W◯-η acc ext ext′ ax ⟩
                 W-map η id (sup x f′)                                          ≡⟨⟩
                 sup (η x) (W-map η id ∘ f′)                                    ≡⟨ (cong (sup _) $ sym $ apply-ext ext′ λ _ →
                                                                                    ◯Wη→W◯-η acc ext ext′ ax) ⟩
                 sup (η x) (◯Wη→W◯ acc ext ∘ η ∘ f′)                            ≡⟨ cong (sup _ ∘ (◯Wη→W◯ acc ext ∘_)) $ sym $
                                                                                   ◯Π→Π◯-η ext′ ⟩∎
                 sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ (η f′))                      ∎)
                                                                             _ ⟩

               sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ (Π◯→◯Π (W◯→◯Wη ∘ f)))  ≡⟨ cong (sup _ ∘ (◯Wη→W◯ acc ext ∘_)) $
                                                                           _≃_.left-inverse-of (Π◯≃◯Π ext′) _ ⟩

               sup (η x) (◯Wη→W◯ acc ext ∘ W◯→◯Wη ∘ f)                  ≡⟨ cong (sup (η x)) $ apply-ext ext′
                                                                           hyp ⟩∎
               sup (η x) f                                              ∎)
            x f (λ y → to-from (f y))

  -- Some results that hold if a given family of types is valid
  -- (pointwise).

  module Valid-domain-Π
    {A : Type a} {P : A → Type a}
    (v : ∀ x → Valid-domain (P x))
    where

    -- If the modality is accessibility-modal for a certain relation and
    -- A is modal, then W A P is k-stable for symmetric kinds k
    -- (assuming function extensionality).

    Stable-[]-W :
      @0 Accessibility-modal-for (_<W_ {A = A} {P = P}) →
      @0 Extensionality a a →
      Extensionality? ⌊ k ⌋-sym a a →
      Modal A →
      Stable-[ ⌊ k ⌋-sym ] (W A P)
    Stable-[]-W acc ext ext′ m =
      ◯ (W A P)                         ↝⟨ (◯-cong-↝-sym ext′ λ ext → W-cong₂ ext λ _ → ≡⇒↝ _ $ cong P $ sym
                                            Modal→Stable-η) ⟩
      ◯ (W A (P ∘ Modal→Stable m ∘ η))  ↝⟨ Valid-domain-Π◯.◯Wη≃W◯ _ (λ _ → v _) acc′ ext ext′ ⟩
      W (◯ A) (P ∘ Modal→Stable m)      ↝⟨ (inverse $ W-cong ext′ (Modal→≃◯ m) λ _ → ≡⇒↝ _ $ cong P $ sym
                                            Modal→Stable-η) ⟩□
      W A P                             □
      where
      @0 acc′ :
        Accessibility-modal-for
          (_<W_ {A = A} {P = P ∘ Modal→Stable m ∘ η})
      acc′ =
        subst
          (λ f → Accessibility-modal-for (_<W_ {A = A} {P = P ∘ f}))
          (apply-ext ext λ _ → sym Modal→Stable-η)
          acc

    -- If the modality is accessibility-modal for a certain relation and
    -- A is modal, then W A P is modal (assuming function
    -- extensionality).

    Modal-W :
      @0 Accessibility-modal-for (_<W_ {A = A} {P = P}) →
      Extensionality a a →
      Modal A →
      Modal (W A P)
    Modal-W acc ext m =
      Is-equivalence-η→Modal $
      _≃_.is-equivalence $
      Eq.with-other-function
        (inverse $ Stable-[]-W acc ext ext m)
        η
        lemma
      where
      P≃ : P x ≃ P (Modal→Stable m (η x))
      P≃ = ≡⇒↝ _ $ cong P $ sym Modal→Stable-η

      P→ : P x → P (Modal→Stable m (η x))
      P→ = _≃_.to P≃

      P← : P (Modal→Stable m (η x)) → P x
      P← = _≃_.from P≃

      open module V₁ {x} = Valid-domain₁ (v x)
      open H.Valid-domain-Π◯ (P ∘ Modal→Stable m) (λ _ → v _)

      lemma : ∀ x → ◯-map (W-map id P→) (W◯→◯Wη (W-map η P← x)) ≡ η x
      lemma (sup x f) =
        ◯-map (W-map id P→) (W◯→◯Wη $ W-map η P← (sup x f))                ≡⟨⟩

        ◯-map (W-map id P→) (W◯→◯Wη $ sup (η x) (W-map η P← ∘ f ∘ P←))     ≡⟨ cong (◯-map _) $
                                                                              W◯→◯Wη-sup-η ext (W-map η P← ∘ f ∘ P←) ⟩
        ◯-map (W-map id P→)
          (◯-map (sup x) (Π◯→◯Π (W◯→◯Wη ∘ W-map η P← ∘ f ∘ P←)))           ≡⟨ sym ◯-map-∘ ⟩

        ◯-map (sup x ∘ (_∘ P→) ∘ (W-map id P→ ∘_))
          (Π◯→◯Π (W◯→◯Wη ∘ W-map η P← ∘ f ∘ P←))                           ≡⟨ ◯-map-∘ ⟩

        ◯-map (sup x ∘ (_∘ P→))
          (◯-map (W-map id P→ ∘_) (Π◯→◯Π (W◯→◯Wη ∘ W-map η P← ∘ f ∘ P←)))  ≡⟨ cong (◯-map _) $ sym $
                                                                              Π◯→◯Π-◯-map ext ⟩
        ◯-map (sup x ∘ (_∘ P→))
          (Π◯→◯Π (◯-map (W-map id P→) ∘ W◯→◯Wη ∘ W-map η P← ∘ f ∘ P←))     ≡⟨ (cong (◯-map (sup x ∘ (_∘ P→))) $ cong Π◯→◯Π $
                                                                               apply-ext ext λ y →
                                                                               lemma (f (P← y))) ⟩

        ◯-map (sup x ∘ (_∘ P→)) (Π◯→◯Π (η ∘ f ∘ P←))                       ≡⟨ cong (◯-map (sup x ∘ (_∘ P→))) $ cong Π◯→◯Π $ sym $
                                                                              ◯Π→Π◯-η ext ⟩

        ◯-map (sup x ∘ (_∘ P→)) (Π◯→◯Π (◯Π→Π◯ (η (f ∘ P←))))               ≡⟨ cong (◯-map (sup x ∘ (_∘ P→))) $
                                                                              _≃_.right-inverse-of (Π◯≃◯Π ext) _ ⟩

        ◯-map (sup x ∘ (_∘ P→)) (η (f ∘ P←))                               ≡⟨ ◯-map-η ⟩

        η (sup x (f ∘ P← ∘ P→))                                            ≡⟨ (cong (η ∘ sup x) $ cong (f ∘_) $ apply-ext ext λ _ →
                                                                               _≃_.left-inverse-of P≃ _) ⟩∎
        η (sup x f)                                                        ∎

  ----------------------------------------------------------------------
  -- Some results that hold if all types are valid

  module Valid-domain (v : {A : Type a} → Valid-domain A) where

    private
      open module V₁ {A P} = Valid-domain-Π◯ {A = A} P (λ _ → v) public
      open module V₂ {A P} = Valid-domain-Π {A = A} {P = P} (λ _ → v)
        public
