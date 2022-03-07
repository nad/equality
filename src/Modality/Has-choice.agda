------------------------------------------------------------------------
-- Some results that hold for modalities that satisfy a choice
-- principle
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Modality.Basics

module Modality.Has-choice
  {c⁺}
  (eq-J : ∀ {a p} → Equality-with-J a p c⁺)
  (open Modality.Basics eq-J)
  {a}
  (M : Modality a)
  (has-choice : Modality.Has-choice M)
  where

open Derived-definitions-and-properties eq-J

private
  open module M = Modality M
    hiding (◯Π◯≃◯Π; ◯Π◯≃◯Π-η; ◯Π◯≃◯Π⁻¹-η;
            Stable-Π; Stable-implicit-Π;
            Modal→Stable-Is-equivalence;
            Stable-H-level′; Stable-H-level;
            Stable-W)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Accessibility eq-J using (_<W_)
open import Bijection eq-J as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq-J as Emb using (Embedding; Is-embedding)
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq-J as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
import Equivalence.Erased.Contractible-preimages eq-J as ECP
import Equivalence.Half-adjoint eq-J as HA
open import Erased.Level-1 eq-J as E using ([]-cong-axiomatisation)
open import Extensionality eq-J
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J
open import H-level.Closure eq-J
open import Injection eq-J using (_↣_; Injective)
open import Preimage eq-J using (_⁻¹_)
open import Surjection eq-J using (_↠_; Split-surjective)

private
  variable
    ℓ               : Level
    A B             : Type ℓ
    f f⁻¹ g h k p x : A
    P Q             : A → Type p

------------------------------------------------------------------------
-- A choice principle

-- A kind of choice principle holds.

Π◯→◯Π : ((x : A) → ◯ (P x)) → ◯ ((x : A) → P x)
Π◯→◯Π = has-choice .proj₁

-- A corresponding equivalence (defined using function
-- extensionality).

Π◯≃◯Π : ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
Π◯≃◯Π =
  generalise-ext?
    (record { to = Π◯→◯Π; from = ◯Π→Π◯ })
    (λ ext → _≃_.left-inverse-of  (eq ext)
           , _≃_.right-inverse-of (eq ext))
  where
  eq :
    Extensionality a a →
    ◯ ((x : A) → P x) ≃ ((x : A) → ◯ (P x))
  eq ext =
    Eq.with-other-inverse
      Eq.⟨ ◯Π→Π◯ , has-choice .proj₂ .proj₂ ext .proj₁ ⟩
      (has-choice .proj₁)
      (ext⁻¹ $ sym $ has-choice .proj₂ .proj₂ ext .proj₂ .proj₁)

-- ◯Π→Π◯ is a left inverse of Π◯→◯Π (pointwise).
--
-- Note that this proof does not rely on function extensionality.

◯Π→Π◯-Π◯→◯Π : ◯Π→Π◯ (Π◯→◯Π f) x ≡ f x
◯Π→Π◯-Π◯→◯Π = has-choice .proj₂ .proj₁ _ _

-- A "computation rule" for Π◯→◯Π.

Π◯→◯Π-η :
  Extensionality a a →
  Π◯→◯Π (η ∘ f) ≡ η f
Π◯→◯Π-η {f = f} ext =
  Π◯→◯Π (η ∘ f)        ≡⟨ cong Π◯→◯Π $ sym $ ◯Π→Π◯-η ext ⟩
  Π◯→◯Π (◯Π→Π◯ (η f))  ≡⟨ _≃_.right-inverse-of (Π◯≃◯Π ext) _ ⟩∎
  η f                  ∎

-- Π◯→◯Π commutes with ◯-map in a certain way (assuming function
-- extensionality).

Π◯→◯Π-◯-map :
  {f : ∀ {x} → P x → Q x} {g : (x : A) → ◯ (P x)} →
  Extensionality a a →
  Π◯→◯Π (◯-map f ∘ g) ≡ ◯-map (f ∘_) (Π◯→◯Π g)
Π◯→◯Π-◯-map {f = f} {g = g} ext =
  _≃_.from-to (Π◯≃◯Π ext)
    (◯Π→Π◯ (◯-map (f ∘_) (Π◯→◯Π g))  ≡⟨ (apply-ext ext λ _ → ◯Π→Π◯-◯-map) ⟩
     ◯-map f ∘ ◯Π→Π◯ (Π◯→◯Π g)       ≡⟨ cong (◯-map f ∘_) $ _≃_.left-inverse-of (Π◯≃◯Π ext) _ ⟩∎
     ◯-map f ∘ g                     ∎)

------------------------------------------------------------------------
-- Another equivalence

-- ◯ ((x : A) → ◯ (P x)) is equivalent to ◯ ((x : A) → P x) (assuming
-- function extensionality).

◯Π◯≃◯Π :
  {A : Type a} {P : A → Type a} →
  ◯ ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
◯Π◯≃◯Π {A = A} {P = P} ext =
  ◯ ((x : A) → ◯ (P x))  ↝⟨ ◯-cong-↝ ext Π◯≃◯Π ⟩
  ◯ (◯ ((x : A) → P x))  ↔⟨ inverse ◯≃◯◯ ⟩□
  ◯ ((x : A) → P x)      □

-- Two "computation rules" for ◯Π◯≃◯Π.

◯Π◯≃◯Π-η : ◯Π◯≃◯Π _ (η f) ≡ Π◯→◯Π f
◯Π◯≃◯Π-η {f = f} =
  ◯Π◯≃◯Π _ (η f)                        ≡⟨⟩
  ◯-rec Modal-◯ id (◯-map Π◯→◯Π (η f))  ≡⟨ cong (◯-rec _ _) ◯-map-η ⟩
  ◯-rec Modal-◯ id (η (Π◯→◯Π f))        ≡⟨ ◯-rec-η ⟩∎
  Π◯→◯Π f                               ∎

◯Π◯≃◯Π⁻¹-η :
  Extensionality a a →
  _⇔_.from (◯Π◯≃◯Π _) (η f) ≡ η (η ∘ f)
◯Π◯≃◯Π⁻¹-η {f = f} ext =
  _⇔_.from (◯Π◯≃◯Π _) (η f)  ≡⟨⟩
  ◯-map ◯Π→Π◯ (η (η f))      ≡⟨ ◯-map-η ⟩
  η (◯Π→Π◯ (η f))            ≡⟨ cong η $ ◯Π→Π◯-η ext ⟩∎
  η (η ∘ f)                  ∎

------------------------------------------------------------------------
-- Some lemmas related to W

-- W (◯ A) P implies ◯ (W A (P ∘ η)).

W◯→◯Wη :
  (P : ◯ A → Type a) →
  W (◯ A) P → ◯ (W A (P ∘ η))
W◯→◯Wη {A = A} P (sup x f) =
  ◯-elim′
    {P = λ x → (P x → ◯ (W A (P ∘ η))) → ◯ (W A (P ∘ η))}
    (λ _ → M.Stable-Π λ _ → Modal→Stable Modal-◯)
    (λ x f →
       ◯-map (sup x)
         (                             $⟨ f ⟩
          (P (η x) → ◯ (W A (P ∘ η)))  →⟨ Π◯→◯Π ⟩□
          ◯ ((P ∘ η) x → W A (P ∘ η))  □))
    x (λ y → W◯→◯Wη P (f y))

-- A "computation rule" for W◯→◯Wη.

W◯→◯Wη-sup-η :
  {P : ◯ A → Type a} →
  Extensionality a a →
  (f : P (η x) → W (◯ A) P) →
  W◯→◯Wη P (sup (η x) f) ≡ ◯-map (sup x) (Π◯→◯Π (W◯→◯Wη P ∘ f))
W◯→◯Wη-sup-η {A = A} {x = x} {P = P} ext f =
  ◯-elim′
    {P = λ x → (P x → ◯ (W A (P ∘ η))) → ◯ (W A (P ∘ η))}
    (λ _ → M.Stable-Π λ _ → Modal→Stable Modal-◯)
    (λ x f → ◯-map (sup x) (Π◯→◯Π f))
    (η x) (W◯→◯Wη P ∘ f)                                   ≡⟨ (cong
                                                                 (λ m →
                                                                    ◯-elim′
                                                                      {P = λ x → (P x → ◯ (W A (P ∘ η))) → ◯ (W A (P ∘ η))}
                                                                      m (λ x f → ◯-map (sup x) (Π◯→◯Π f))
                                                                      (η x) (W◯→◯Wη P ∘ f)) $
                                                               apply-ext ext λ _ →
                                                               Stable-Π-Modal-Π ext) ⟩
  ◯-elim′
    {P = λ x → (P x → ◯ (W A (P ∘ η))) → ◯ (W A (P ∘ η))}
    (λ _ → Modal→Stable $ Modal-Π ext λ _ → Modal-◯)
    (λ x f → ◯-map (sup x) (Π◯→◯Π f))
    (η x) (W◯→◯Wη P ∘ f)                                   ≡⟨ cong (_$ (W◯→◯Wη P ∘ f)) $
                                                              ◯-elim′-Modal→Stable-η ⟩∎
  ◯-map (sup x) (Π◯→◯Π (W◯→◯Wη P ∘ f))                     ∎

-- A lemma relating W◯→◯Wη and W-map η id.

W◯→◯Wη-W-map-η-id :
  Extensionality a a →
  W◯→◯Wη P (W-map η id x) ≡ η x
W◯→◯Wη-W-map-η-id {P = P} {x = sup x f} ext =
  W◯→◯Wη P (W-map η id (sup x f))                          ≡⟨⟩
  W◯→◯Wη P (sup (η x) λ y → W-map η id (f y))              ≡⟨ W◯→◯Wη-sup-η ext (λ y → W-map η id (f y)) ⟩
  ◯-map (sup x) (Π◯→◯Π λ y → W◯→◯Wη P (W-map η id (f y)))  ≡⟨ (cong (◯-map (sup x)) $ cong (Π◯→◯Π) $ apply-ext ext λ y →
                                                               W◯→◯Wη-W-map-η-id {x = f y} ext) ⟩
  ◯-map (sup x) (Π◯→◯Π (η ∘ f))                            ≡⟨ cong (◯-map (sup x)) $
                                                              Π◯→◯Π-η ext ⟩
  ◯-map (sup x) (η f)                                      ≡⟨ ◯-map-η ⟩∎
  η (sup x f)                                              ∎

-- Another lemma relating W◯→◯Wη and W-map η id.

◯-map-W-map-η-id-W◯→◯Wη :
  Extensionality a a →
  ◯-map (W-map η id) (W◯→◯Wη P x) ≡ η x
◯-map-W-map-η-id-W◯→◯Wη {P = P} {x = sup x f} ext =
  ◯-elim
    {P = λ x →
           ∀ f →
           (∀ y → ◯-map (W-map η id) (W◯→◯Wη P (f y)) ≡ η (f y)) →
           ◯-map (W-map η id) (W◯→◯Wη P (sup x f)) ≡
           η (sup x f)}
    (λ _ → Modal-Π ext λ _ →
           Modal-Π ext λ _ →
           Separated-◯ _ _)
    (λ x f hyp →
       ◯-map (W-map η id) (W◯→◯Wη P (sup (η x) f))                 ≡⟨ cong (◯-map (W-map η id)) $ W◯→◯Wη-sup-η ext f ⟩

       ◯-map (W-map η id) (◯-map (sup x) (Π◯→◯Π (W◯→◯Wη P ∘ f)))   ≡⟨ sym ◯-map-∘ ⟩

       ◯-map (W-map η id ∘ sup x) (Π◯→◯Π (W◯→◯Wη P ∘ f))           ≡⟨⟩

       ◯-map (sup (η x) ∘ (W-map η id ∘_)) (Π◯→◯Π (W◯→◯Wη P ∘ f))  ≡⟨ ◯-map-∘ ⟩

       ◯-map (sup (η x))
         (◯-map (W-map η id ∘_) (Π◯→◯Π (W◯→◯Wη P ∘ f)))            ≡⟨ cong (◯-map (sup (η x))) $ sym $
                                                                      Π◯→◯Π-◯-map ext ⟩
       ◯-map (sup (η x))
         (Π◯→◯Π (◯-map (W-map η id) ∘ (W◯→◯Wη P ∘ f)))             ≡⟨ cong (◯-map (sup (η x)) ∘ Π◯→◯Π) $ apply-ext ext
                                                                      hyp ⟩

       ◯-map (sup (η x)) (Π◯→◯Π (η ∘ f))                           ≡⟨ cong (◯-map (sup (η x))) $ Π◯→◯Π-η ext ⟩

       ◯-map (sup (η x)) (η f)                                     ≡⟨ ◯-map-η ⟩∎

       η (sup (η x) f)                                             ∎)
    x f
    (λ y → ◯-map-W-map-η-id-W◯→◯Wη {x = f y} ext)

-- ◯ (W (◯ A) P) is equivalent to ◯ (W A (P ∘ η)) (assuming function
-- extensionality).

◯W◯≃◯Wη :
  {P : ◯ A → Type a} →
  ◯ (W (◯ A) P) ↝[ a ∣ a ] ◯ (W A (P ∘ η))
◯W◯≃◯Wη {A = A} {P = P} =
  generalise-ext?
    (record { to = to; from = from })
    (λ ext → to-from ext , from-to ext)
  where
  to   = ◯-rec Modal-◯ (W◯→◯Wη P)
  from = ◯-map (W-map η id)

  to-from :
    Extensionality a a →
    ∀ x → to (from x) ≡ x
  to-from ext =
    ◯-elim
      (λ _ → Separated-◯ _ _)
      (λ x →
         to (from (η x))                                      ≡⟨⟩
         ◯-rec Modal-◯ (W◯→◯Wη P) (◯-map (W-map η id) (η x))  ≡⟨ ◯-rec-◯-map ⟩
         ◯-rec Modal-◯ (W◯→◯Wη P ∘ W-map η id) (η x)          ≡⟨ ◯-rec-η ⟩
         W◯→◯Wη P (W-map η id x)                              ≡⟨ W◯→◯Wη-W-map-η-id ext ⟩∎
         η x                                                  ∎)

  from-to :
    Extensionality a a →
    ∀ x → from (to x) ≡ x
  from-to ext =
    ◯-elim
      (λ _ → Separated-◯ _ _)
      (λ x →
         from (to (η x))                                      ≡⟨⟩
         ◯-map (W-map η id) (◯-rec Modal-◯ (W◯→◯Wη P) (η x))  ≡⟨ cong (◯-map (W-map η id)) ◯-rec-η ⟩
         ◯-map (W-map η id) (W◯→◯Wη P x)                      ≡⟨ ◯-map-W-map-η-id-W◯→◯Wη ext ⟩∎
         η x                                                  ∎)

-- An unfolding lemma for ◯ (W A (P ∘ η)).

◯Wη≃Σ◯Π◯Wη :
  {P : ◯ A → Type a} →
  ◯ (W A (P ∘ η)) ↝[ a ∣ a ] Σ (◯ A) (λ x → P x → ◯ (W A (P ∘ η)))
◯Wη≃Σ◯Π◯Wη {A = A} {P = P} ext =
  ◯ (W A (P ∘ η))                        ↔⟨ ◯-cong-↔ W-unfolding ⟩
  ◯ (Σ A (λ x → P (η x) → W A (P ∘ η)))  ↝⟨ ◯Ση≃Σ◯◯ ext ⟩
  Σ (◯ A) (λ x → ◯ (P x → W A (P ∘ η)))  ↝⟨ (∃-cong λ _ → inverse-ext? Π◯≃◯Π ext) ⟩□
  Σ (◯ A) (λ x → P x → ◯ (W A (P ∘ η)))  □

-- A "computation rule" for ◯Wη≃Σ◯Π◯Wη.

◯Wη≃Σ◯Π◯Wη-η :
  Extensionality a a →
  ◯Wη≃Σ◯Π◯Wη _ (η (sup x f)) ≡ (η x , η ∘ f)
◯Wη≃Σ◯Π◯Wη-η {x = x} {f = f} ext =
  Σ-map id ◯Π→Π◯
    (◯Ση≃Σ◯◯ _ (◯-map (λ w → headᵂ w , tailᵂ w) (η (sup x f))))  ≡⟨ cong (Σ-map id ◯Π→Π◯ ∘ ◯Ση≃Σ◯◯ _) ◯-map-η ⟩

  Σ-map id ◯Π→Π◯ (◯Ση≃Σ◯◯ _ (η (x , f)))                          ≡⟨ cong (Σ-map id ◯Π→Π◯) ◯-rec-η ⟩

  Σ-map id ◯Π→Π◯ (η x , η f)                                      ≡⟨⟩

  (η x , ◯Π→Π◯ (η f))                                             ≡⟨ cong (_ ,_) $ ◯Π→Π◯-η ext ⟩∎

  (η x , η ∘ f)                                                   ∎

-- A lemma relating ◯Wη≃Σ◯Π◯Wη and ◯Wη→Σ◯Π◯Wη.

◯Wη≃Σ◯Π◯Wη≡◯Wη→Σ◯Π◯Wη :
  Extensionality a a →
  ◯Wη≃Σ◯Π◯Wη _ ≡ ◯Wη→Σ◯Π◯Wη {P = P}
◯Wη≃Σ◯Π◯Wη≡◯Wη→Σ◯Π◯Wη ext =
  apply-ext ext $
  ◯-elim
    (λ _ → Modal→Separated
              (Modal-Σ Modal-◯ λ _ →
               Modal-Π ext λ _ →
               Modal-◯)
              _ _)
    (λ where
       (sup x f) →
         ◯Wη≃Σ◯Π◯Wη _ (η (sup x f))  ≡⟨ ◯Wη≃Σ◯Π◯Wη-η ext ⟩
         (η x , η ∘ f)               ≡⟨ sym $ ◯Wη→Σ◯Π◯Wη-η ext ⟩∎
         ◯Wη→Σ◯Π◯Wη (η (sup x f))    ∎)

-- If the modality is accessibility-modal for a certain relation, then
-- ◯ commutes with W in a certain way (assuming function
-- extensionality).

◯Wη≃W◯ :
  {P : ◯ A → Type a} →
  @0 Accessibility-modal-for (_<W_ {A = A} {P = P ∘ η}) →
  @0 Extensionality a a →
  ◯ (W A (P ∘ η)) ↝[ a ∣ a ] W (◯ A) P
◯Wη≃W◯ {A = A} {P = P} acc ext =
  generalise-ext?
    (record { to = ◯Wη→W◯ acc ext; from = W◯→◯Wη P })
    (λ ext′ → to-from ext′ , from-to ext′)
  where
  module _ (ext′ : Extensionality a a) where
    ax = E.Extensionality→[]-cong-axiomatisation ext′

    from-to : ∀ x → W◯→◯Wη P (◯Wη→W◯ acc ext x) ≡ x
    from-to =
      ◯-elim
        (λ _ → Separated-◯ _ _)
        (λ x →
           W◯→◯Wη P (◯Wη→W◯ acc ext (η x))  ≡⟨ cong (W◯→◯Wη P) $
                                               ◯Wη→W◯-η acc ext ext′ ax ⟩
           W◯→◯Wη P (W-map η id x)          ≡⟨ W◯→◯Wη-W-map-η-id ext′ ⟩∎
           η x                              ∎)

    to-from : ∀ x → ◯Wη→W◯ acc ext (W◯→◯Wη P x) ≡ x
    to-from (sup x f) =
      ◯-elim
        {P = λ x →
               ∀ f →
               (∀ y → ◯Wη→W◯ acc ext (W◯→◯Wη P (f y)) ≡ f y) →
               ◯Wη→W◯ acc ext (W◯→◯Wη P (sup x f)) ≡
               sup x f}
        (λ _ → Modal-Π ext′ λ _ →
               Modal-Π ext′ λ _ →
               Separated-W ext′ Separated-◯ _ _)
        (λ x f hyp →
           ◯Wη→W◯ acc ext (W◯→◯Wη P (sup (η x) f))                    ≡⟨ cong (◯Wη→W◯ acc ext) $ W◯→◯Wη-sup-η ext′ f ⟩

           ◯Wη→W◯ acc ext (◯-map (sup x) (Π◯→◯Π (W◯→◯Wη P ∘ f)))      ≡⟨ ◯-elim
                                                                           {P = λ f′ →
                                                                                  ◯Wη→W◯ acc ext (◯-map (sup x) f′) ≡
                                                                                  sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ f′)}
                                                                           (λ _ → Separated-W ext′ Separated-◯ _ _)
                                                                           (λ f′ →
             ◯Wη→W◯ acc ext (◯-map (sup x) (η f′))                            ≡⟨ cong (◯Wη→W◯ acc ext)
                                                                                 ◯-map-η ⟩
             ◯Wη→W◯ acc ext (η (sup x f′))                                    ≡⟨ ◯Wη→W◯-η acc ext ext′ ax ⟩
             W-map η id (sup x f′)                                            ≡⟨⟩
             sup (η x) (W-map η id ∘ f′)                                      ≡⟨ (cong (sup _) $ sym $ apply-ext ext′ λ _ →
                                                                                  ◯Wη→W◯-η acc ext ext′ ax) ⟩
             sup (η x) (◯Wη→W◯ acc ext ∘ η ∘ f′)                              ≡⟨ cong (sup _ ∘ (◯Wη→W◯ acc ext ∘_)) $ sym $
                                                                                 ◯Π→Π◯-η ext′ ⟩∎
             sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ (η f′))                        ∎)
                                                                           _ ⟩

           sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ (Π◯→◯Π (W◯→◯Wη P ∘ f)))  ≡⟨ cong (sup _ ∘ (◯Wη→W◯ acc ext ∘_)) $
                                                                         _≃_.left-inverse-of (Π◯≃◯Π ext′) _ ⟩

           sup (η x) (◯Wη→W◯ acc ext ∘ W◯→◯Wη P ∘ f)                  ≡⟨ cong (sup (η x)) $ apply-ext ext′
                                                                         hyp ⟩∎
           sup (η x) f                                                ∎)
        x f (λ y → to-from (f y))

-- If the modality is accessibility-modal for a certain relation and A
-- is modal, then W A P is k-stable for symmetric kinds k (assuming
-- function extensionality).

Stable-W :
  @0 Accessibility-modal-for (_<W_ {A = A} {P = P}) →
  @0 Extensionality a a →
  Extensionality? ⌊ k ⌋-sym a a →
  Modal A →
  Stable-[ ⌊ k ⌋-sym ] (W A P)
Stable-W {A = A} {P = P} acc ext ext′ m =
  ◯ (W A P)                         ↝⟨ (◯-cong-↝-sym ext′ λ ext → W-cong₂ ext λ _ → ≡⇒↝ _ $ cong P $ sym
                                        Modal→Stable-η) ⟩
  ◯ (W A (P ∘ Modal→Stable m ∘ η))  ↝⟨ ◯Wη≃W◯ acc′ ext ext′ ⟩
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

-- If the modality is accessibility-modal for a certain relation and A
-- is modal, then W A P is modal (assuming function extensionality).

Modal-W :
  @0 Accessibility-modal-for (_<W_ {A = A} {P = P}) →
  Extensionality a a →
  Modal A →
  Modal (W A P)
Modal-W {A = A} {P = P} acc ext m =
  Is-equivalence-η→Modal $
  _≃_.is-equivalence $
  Eq.with-other-function
    (inverse $ Stable-W acc ext ext m)
    η
    lemma
  where
  P≃ : P x ≃ P (Modal→Stable m (η x))
  P≃ = ≡⇒↝ _ $ cong P $ sym Modal→Stable-η

  P→ : P x → P (Modal→Stable m (η x))
  P→ = _≃_.to P≃

  P← : P (Modal→Stable m (η x)) → P x
  P← = _≃_.from P≃

  lemma :
    ∀ x →
    ◯-map (W-map id P→)
      (W◯→◯Wη (P ∘ Modal→Stable m) (W-map η P← x)) ≡
    η x
  lemma (sup x f) =
    ◯-map (W-map id P→)
      (W◯→◯Wη (P ∘ Modal→Stable m) $ W-map η P← (sup x f))  ≡⟨⟩

    ◯-map (W-map id P→)
      (W◯→◯Wη (P ∘ Modal→Stable m) $
       sup (η x) (W-map η P← ∘ f ∘ P←))                     ≡⟨ cong (◯-map _) $
                                                               W◯→◯Wη-sup-η ext (W-map η P← ∘ f ∘ P←) ⟩
    ◯-map (W-map id P→)
      (◯-map (sup x)
         (Π◯→◯Π
            (W◯→◯Wη (P ∘ Modal→Stable m) ∘
             W-map η P← ∘ f ∘ P←)))                         ≡⟨ sym ◯-map-∘ ⟩

    ◯-map (sup x ∘ (_∘ P→) ∘ (W-map id P→ ∘_))
      (Π◯→◯Π
         (W◯→◯Wη (P ∘ Modal→Stable m) ∘
          W-map η P← ∘ f ∘ P←))                             ≡⟨ ◯-map-∘ ⟩

    ◯-map (sup x ∘ (_∘ P→))
      (◯-map (W-map id P→ ∘_)
         (Π◯→◯Π
            (W◯→◯Wη (P ∘ Modal→Stable m) ∘
             W-map η P← ∘ f ∘ P←)))                         ≡⟨ cong (◯-map _) $ sym $
                                                               Π◯→◯Π-◯-map ext ⟩
    ◯-map (sup x ∘ (_∘ P→))
      (Π◯→◯Π
         (◯-map (W-map id P→) ∘
          W◯→◯Wη (P ∘ Modal→Stable m) ∘
          W-map η P← ∘ f ∘ P←))                             ≡⟨ (cong (◯-map (sup x ∘ (_∘ P→))) $ cong Π◯→◯Π $
                                                                apply-ext ext λ y →
                                                                lemma (f (P← y))) ⟩

    ◯-map (sup x ∘ (_∘ P→)) (Π◯→◯Π (η ∘ f ∘ P←))            ≡⟨ cong (◯-map (sup x ∘ (_∘ P→))) $ cong Π◯→◯Π $ sym $
                                                               ◯Π→Π◯-η ext ⟩

    ◯-map (sup x ∘ (_∘ P→)) (Π◯→◯Π (◯Π→Π◯ (η (f ∘ P←))))    ≡⟨ cong (◯-map (sup x ∘ (_∘ P→))) $
                                                               _≃_.right-inverse-of (Π◯≃◯Π ext) _ ⟩

    ◯-map (sup x ∘ (_∘ P→)) (η (f ∘ P←))                    ≡⟨ ◯-map-η ⟩

    η (sup x (f ∘ P← ∘ P→))                                 ≡⟨ (cong (η ∘ sup x) $ cong (f ∘_) $ apply-ext ext λ _ →
                                                                _≃_.left-inverse-of P≃ _) ⟩∎
    η (sup x f)                                             ∎

-- If the modality is accessibility-modal for certain relations, then
-- it is W-modal (assuming function extensionality).

Accessibility-modal-for→W-modal :
  Extensionality a a →
  @0 ({A : Type a} {P : A → Type a} →
      Accessibility-modal-for (_<W_ {A = A} {P = P})) →
  W-modal M
Accessibility-modal-for→W-modal ext acc = Modal-W acc ext

-- If the modality is accessibility-modal, then it is W-modal
-- (assuming function extensionality).

Accessibility-modal→W-modal :
  Extensionality a a →
  @0 Accessibility-modal →
  W-modal M
Accessibility-modal→W-modal ext acc =
  Accessibility-modal-for→W-modal ext acc

------------------------------------------------------------------------
-- ◯ commutes with several kinds of functions (part 1)

private

  -- ◯ commutes with the non-dependent function space (up to _⇔_).

  ◯→⇔◯→◯ : ◯ (A → B) ⇔ (◯ A → ◯ B)
  ◯→⇔◯→◯ {A = A} {B = B} = record
    { to   = ◯-map-◯
    ; from =
        (◯ A → ◯ B)  →⟨ Π◯◯≃Π◯η _ ⟩
        (A → ◯ B)    →⟨ Π◯→◯Π ⟩□
        ◯ (A → B)    □
    }

  abstract

    -- A lemma related to ◯→⇔◯→◯.

    ◯→⇔◯→◯-◯→⇔◯→◯ :
      (f : ◯ A → ◯ B) →
      _⇔_.to ◯→⇔◯→◯ (_⇔_.from ◯→⇔◯→◯ f) x ≡ f x
    ◯→⇔◯→◯-◯→⇔◯→◯ {x = x} f =
      ◯-elim
        (λ _ → Separated-◯ _ _)
        (λ x →
           _⇔_.to ◯→⇔◯→◯ (_⇔_.from ◯→⇔◯→◯ f) (η x)  ≡⟨⟩
           ◯-map-◯ (Π◯→◯Π (f ∘ η)) (η x)            ≡⟨ ◯-map-◯-ηʳ ⟩
           ◯-map (_$ x) (Π◯→◯Π (f ∘ η))             ≡⟨⟩
           ◯Π→Π◯ (Π◯→◯Π (f ∘ η)) x                  ≡⟨ ◯Π→Π◯-Π◯→◯Π ⟩∎
           f (η x)                                  ∎)
        x

-- ◯ commutes with the non-dependent function space (assuming
-- function extensionality).

◯→≃◯→◯ : ◯ (A → B) ↝[ a ∣ a ] (◯ A → ◯ B)
◯→≃◯→◯ {A = A} {B = B} =
  generalise-ext?
    ◯→⇔◯→◯
    (λ ext →
         (λ f → apply-ext ext λ _ → ◯→⇔◯→◯-◯→⇔◯→◯ f)
       , ◯-elim
           (λ _ → Separated-◯ _ _)
           (λ f →
              Π◯→◯Π (◯-map-◯ (η f) ∘ η)  ≡⟨ (cong Π◯→◯Π $ apply-ext ext λ _ → ◯-map-◯-η) ⟩
              Π◯→◯Π (η ∘ f)              ≡⟨ Π◯→◯Π-η ext ⟩∎
              η f                        ∎))

-- ◯ commutes with _⇔_ (assuming function extensionality).

◯⇔≃◯⇔◯ : ◯ (A ⇔ B) ↝[ a ∣ a ] (◯ A ⇔ ◯ B)
◯⇔≃◯⇔◯ {A = A} {B = B} ext =
  ◯ (A ⇔ B)                  ↔⟨ ◯-cong-↔ ⇔↔→×→ ⟩
  ◯ ((A → B) × (B → A))      ↔⟨ ◯×≃ ⟩
  ◯ (A → B) × ◯ (B → A)      ↝⟨ ◯→≃◯→◯ ext ×-cong ◯→≃◯→◯ ext ⟩
  (◯ A → ◯ B) × (◯ B → ◯ A)  ↔⟨ inverse ⇔↔→×→ ⟩□
  ◯ A ⇔ ◯ B                  □

------------------------------------------------------------------------
-- Σ◯→≃Σ◯→◯ and some related results

-- A lemma that is easy to prove, but that relies on function
-- extensionality.

Σ◯→≃Σ◯→◯ :
  Extensionality a a →
  Σ (◯ (A → B)) (P ∘ ◯-map-◯) ↝[ k ] Σ (◯ A → ◯ B) P
Σ◯→≃Σ◯→◯ ext =
  Σ-cong (◯→≃◯→◯ {k = equivalence} ext) λ _ → F.id

-- A variant of Σ◯→≃Σ◯→◯ for logical equivalence.

Σ◯→⇔Σ◯→◯ :
  ({f g : ◯ A → ◯ B} → (∀ x → f x ≡ g x) → P f → P g) →
  Σ (◯ (A → B)) (P ∘ ◯-map-◯) ⇔ Σ (◯ A → ◯ B) P
Σ◯→⇔Σ◯→◯ {P = P} P-resp = record { to = to; from = from }
  where
  to   = Σ-map (_⇔_.to   ◯→⇔◯→◯) id
  from = Σ-map (_⇔_.from ◯→⇔◯→◯) λ {f} →
    P f                                    →⟨ (P-resp λ _ → sym $ ◯→⇔◯→◯-◯→⇔◯→◯ f) ⟩□
    P (_⇔_.to ◯→⇔◯→◯ (_⇔_.from ◯→⇔◯→◯ f))  □

-- A variant of Σ◯→≃Σ◯→◯ that only relies on conditional function
-- extensionality.

Σ◯→↝Σ◯→◯ :
  (P-resp : {f g : ◯ A → ◯ B} → (∀ x → f x ≡ g x) → P f → P g) →
  (∀ {f x} → Extensionality a a → P-resp (refl ∘ f) x ≡ x) →
  Σ (◯ (A → B)) (P ∘ ◯-map-◯) ↝[ a ∣ a ] Σ (◯ A → ◯ B) P
Σ◯→↝Σ◯→◯ {P = P} P-resp P-resp-refl = generalise-ext?
  (Σ◯→⇔Σ◯→◯ P-resp)
  (λ ext →
       (λ (f , p) → Σ-≡,≡→≡
          (apply-ext ext $ eq′ f)
          (lemma ext f p))
     , (λ (f , p) → Σ-≡,≡→≡
          (_≃_.left-inverse-of (◯→≃◯→◯ ext) f)
          (subst (P ∘ ◯-map-◯)
             (_≃_.left-inverse-of (◯→≃◯→◯ ext) f)
             (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                   ≡⟨ subst-∘ _ _ _ ⟩

           subst P
             (cong ◯-map-◯ $ _≃_.left-inverse-of (◯→≃◯→◯ ext) f)
             (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                   ≡⟨ cong (flip (subst P) _) $
                                                                     _≃_.left-right-lemma (◯→≃◯→◯ ext) _ ⟩
           subst P
             (_≃_.right-inverse-of (◯→≃◯→◯ ext) (◯-map-◯ f))
             (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                   ≡⟨ lemma ext _ _ ⟩∎

           p                                                      ∎)))
  where
  eq′ = λ f x → ◯→⇔◯→◯-◯→⇔◯→◯ {x = x} f

  lemma = λ ext f p →
    let eq = apply-ext ext (eq′ f) in

    subst P eq (P-resp (sym ∘ eq′ f) p)                   ≡⟨ cong (λ eq′ → subst P eq (P-resp (sym ∘ eq′) p)) $ sym $
                                                             _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) _ ⟩

    subst P eq (P-resp (sym ∘ ext⁻¹ eq) p)                ≡⟨ elim₁
                                                               (λ eq → subst P eq (P-resp (sym ∘ ext⁻¹ eq) p) ≡ p)
                                                               (
      subst P (refl _) (P-resp (sym ∘ ext⁻¹ (refl _)) p)        ≡⟨ subst-refl _ _ ⟩

      P-resp (sym ∘ ext⁻¹ (refl f)) p                           ≡⟨ (cong (λ q → P-resp (sym ∘ q) p) $ apply-ext ext λ _ →
                                                                    ext⁻¹-refl _) ⟩

      P-resp (sym ∘ refl ∘ f) p                                 ≡⟨ (cong (λ q → P-resp q p) $ apply-ext ext λ _ →
                                                                    sym-refl) ⟩

      P-resp (refl ∘ f) p                                       ≡⟨ P-resp-refl ext ⟩∎

      p                                                         ∎)
                                                               _ ⟩∎
    p                                                     ∎

-- Some results that hold if the []-cong axioms can be instantiated.

module []-cong (ax : []-cong-axiomatisation a) where

  -- A variant of Σ◯→≃Σ◯→◯.

  Σ◯→≃ᴱΣ◯→◯ :
    {P : @0 (◯ A → ◯ B) → Type a} →
    @0 Extensionality a a →
    Σ (◯ (A → B)) (λ f → P (◯-map-◯ f)) ≃ᴱ Σ (◯ A → ◯ B) (λ f → P f)
  Σ◯→≃ᴱΣ◯→◯ ext =
    EEq.[]-cong₁.Σ-cong-≃ᴱ-Erased ax
      (◯→≃◯→◯ {k = equivalenceᴱ} E.[ ext ]) λ _ → F.id

  -- Two other variants of Σ◯→≃Σ◯→◯.

  Σ◯→↝Σ◯→◯-Is-equivalenceᴱ-CP :
    (∃ λ (f : ◯ (A → B)) → ECP.Is-equivalenceᴱ (◯-map-◯ f)) ↝[ a ∣ a ]
    (∃ λ (f : ◯ A → ◯ B) → ECP.Is-equivalenceᴱ f)
  Σ◯→↝Σ◯→◯-Is-equivalenceᴱ-CP =
    generalise-ext?′
      (Σ◯→⇔Σ◯→◯ λ f≡g →
         ECP.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax _ f≡g)
      Σ◯→≃Σ◯→◯
      Σ◯→≃ᴱΣ◯→◯

  Σ◯→↝Σ◯→◯-Is-equivalenceᴱ :
    (∃ λ (f : ◯ (A → B)) → Is-equivalenceᴱ (◯-map-◯ f)) ↝[ a ∣ a ]
    (∃ λ (f : ◯ A → ◯ B) → Is-equivalenceᴱ f)
  Σ◯→↝Σ◯→◯-Is-equivalenceᴱ =
    generalise-ext?′
      (Σ◯→⇔Σ◯→◯ λ f≡g →
         EEq.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax _ f≡g)
      Σ◯→≃Σ◯→◯
      Σ◯→≃ᴱΣ◯→◯

------------------------------------------------------------------------
-- Stability

-- Stability (k-stability) is closed under Π-types (perhaps assuming
-- function extensionality).

Stable-Π :
  {A : Type a} {P : A → Type a} →
  Extensionality? k a a →
  (∀ x → Stable-[ k ] (P x)) →
  Stable-[ k ] ((x : A) → P x)
Stable-Π {A = A} {P = P} ext hyp =
  ◯ ((x : A) → P x)    ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
  ((x : A) → ◯ (P x))  ↝⟨ ∀-cong ext hyp ⟩□
  ((x : A) → P x)      □

-- Stability (k-stability) is closed under implicit Π-types (perhaps
-- assuming function extensionality).

Stable-implicit-Π :
  {A : Type a} {P : A → Type a} →
  Extensionality? k a a →
  (∀ x → Stable-[ k ] (P x)) →
  Stable-[ k ] ({x : A} → P x)
Stable-implicit-Π {A = A} {P = P} ext hyp =
  ◯ ({x : A} → P x)  ↔⟨ ◯-cong-↔ Bijection.implicit-Π↔Π ⟩
  ◯ ((x : A) → P x)  ↝⟨ Stable-Π ext hyp ⟩
  ((x : A) → P x)    ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□
  ({x : A} → P x)    □

-- A variant of Stable-Σ.

Stable-Σ[◯→◯] :
  Extensionality? k a a →
  (P-resp : {f g : ◯ A → ◯ B} → (∀ x → f x ≡ g x) → P f → P g) →
  (∀ {f x} → Extensionality a a → P-resp (refl ∘ f) x ≡ x) →
  (∀ f → Stable-[ k ] (P f)) →
  Stable-[ k ] (Σ (◯ A → ◯ B) P)
Stable-Σ[◯→◯] {A = A} {B = B} {P = P} ext P-resp P-resp-refl s =
  ◯ (Σ (◯ A → ◯ B) P)              ↝⟨ ◯-cong-↝ ext $ inverse-ext? (Σ◯→↝Σ◯→◯ P-resp P-resp-refl) ⟩
  ◯ (Σ (◯ (A → B)) (P ∘ ◯-map-◯))  ↝⟨ Stable-Σ Modal-◯ (s ∘ ◯-map-◯) ⟩
  Σ (◯ (A → B)) (P ∘ ◯-map-◯)      ↝⟨ Σ◯→↝Σ◯→◯ P-resp P-resp-refl ext ⟩□
  Σ (◯ A → ◯ B) P                  □

-- If f has type A → B, where A is modal and B is separated, then
-- Is-equivalence f is k-stable (perhaps assuming function
-- extensionality).

Modal→Stable-Is-equivalence :
  {f : A → B} →
  Extensionality? k a a →
  Modal A → Separated B →
  Stable-[ k ] (Is-equivalence f)
Modal→Stable-Is-equivalence {k = k} {f = f} ext m s =
                                              $⟨ s′ ⟩
  Stable-[ k ] (∀ y → Contractible (f ⁻¹ y))  →⟨ Stable-respects-↝ ext $ inverse-ext?
                                                 Is-equivalence≃Is-equivalence-CP ⟩□
  Stable-[ k ] (Is-equivalence f)             □
  where
  s′ =
    Stable-Π ext λ y →
    let m′ : Modal (f ⁻¹ y)
        m′ = Modal-Σ m (λ _ → s _ _) in
    Stable-Σ m′ λ _ →
    Stable-Π ext λ _ →
    Modal→Stable (Modal→Separated m′ _ _)

-- If A is "modal n levels up", then H-level′ n A is k-stable (perhaps
-- assuming function extensionality).

Stable-H-level′ :
  Extensionality? k a a →
  ∀ n →
  For-iterated-equality n Modal A →
  Stable-[ k ] (H-level′ n A)
Stable-H-level′ {k = k} {A = A} ext zero =
  Modal A                        →⟨ (λ m →
                                       Stable-Σ m λ _ →
                                       Stable-Π ext λ _ →
                                       Modal→Stable $ Modal→Separated m _ _) ⟩□
  Stable-[ k ] (Contractible A)  □
Stable-H-level′ {k = k} {A = A} ext (suc n) =
  For-iterated-equality (suc n) Modal A          →⟨ (λ m →
                                                       Stable-Π ext λ _ →
                                                       Stable-Π ext λ _ →
                                                       Stable-H-level′ ext n $
                                                       m _ _) ⟩□
  Stable-[ k ] ((x y : A) → H-level′ n (x ≡ y))  □

-- If A is "modal n levels up", then H-level n A is k-stable (perhaps
-- assuming function extensionality).

Stable-H-level :
  Extensionality? k a a →
  ∀ n →
  For-iterated-equality n Modal A →
  Stable-[ k ] (H-level n A)
Stable-H-level {A = A} ext n m =
  ◯ (H-level n A)   ↝⟨ ◯-cong-↝ ext H-level↔H-level′ ⟩
  ◯ (H-level′ n A)  ↝⟨ Stable-H-level′ ext n m ⟩
  H-level′ n A      ↝⟨ inverse-ext? H-level↔H-level′ ext ⟩□
  H-level n A       □

------------------------------------------------------------------------
-- ◯ commutes with several kinds of functions (part 2)

-- Some lemmas that can be used to prove that ◯ (F A B) is equivalent
-- to F (◯ A) (◯ B).

◯↝↝◯↝◯ :
  {F : Type a → Type a → Type a}
  {P : {A B : Type a} → (A → B) → Type a} →
  (∀ {A B} → F A B ↔ (∃ λ (f : A → B) → P f)) →
  ({f : A → B} → ◯ (P f) ↝[ a ∣ a ] P (◯-map f)) →
  (∀ {k} {f g : ◯ A → ◯ B} →
   Extensionality? k a a → (∀ x → f x ≡ g x) → P f ↝[ k ] P g) →
  ({f : ◯ A → ◯ B} → Stable-[ k ] (P f)) →
  ((∃ λ (f : ◯ (A → B)) → P (◯-map-◯ f)) ↝[ k ]
   (∃ λ (f : ◯ A → ◯ B) → P f)) →
  Extensionality? k a a →
  ◯ (F A B) ↝[ k ] F (◯ A) (◯ B)
◯↝↝◯↝◯ {A = A} {B = B} {F = F} {P = P}
  F↔ ◯∘P↝P∘◯-map P-cong P-stable Σ◯→↝Σ◯→◯ ext =
  ◯ (F A B)                                  ↔⟨ ◯-cong-↔ F↔ ⟩
  ◯ (∃ λ (f : A → B) → P f)                  ↔⟨ inverse ◯Σ◯≃◯Σ ⟩
  ◯ (∃ λ (f : A → B) → ◯ (P f))              ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → ◯∘P↝P∘◯-map ext) ⟩
  ◯ (∃ λ (f : A → B) → P (◯-map f))          ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → P-cong ext λ _ → sym ◯-map-◯-ηˡ) ⟩
  ◯ (∃ λ (f : A → B) → P (◯-map-◯ (η f)))    ↝⟨ ◯Ση≃Σ◯◯ ext ⟩
  (∃ λ (f : ◯ (A → B)) → ◯ (P (◯-map-◯ f)))  ↝⟨ (∃-cong λ _ → P-stable) ⟩
  (∃ λ (f : ◯ (A → B)) → P (◯-map-◯ f))      ↝⟨ Σ◯→↝Σ◯→◯ ⟩
  (∃ λ (f : ◯ A → ◯ B) → P f)                ↔⟨ inverse F↔ ⟩□
  F (◯ A) (◯ B)                              □

◯↝↝◯↝◯′ :
  {F : Type a → Type a → Type a}
  {P : {A B : Type a} → (A → B) → Type a} →
  (∀ {A B} → F A B ↔ (∃ λ (f : A → B) → P f)) →
  ({f : A → B} → ◯ (P f) ↝[ a ∣ a ] P (◯-map f)) →
  (P-cong :
     ∀ {k} {f g : ◯ A → ◯ B} →
     Extensionality? k a a → (∀ x → f x ≡ g x) → P f ↝[ k ] P g) →
  (∀ {f x} →
   Extensionality a a →
   P-cong {k = implication} _ (refl ∘ f) x ≡ x) →
  ({f : ◯ A → ◯ B} → Stable-[ k ] (P f)) →
  Extensionality? k a a →
  ◯ (F A B) ↝[ k ] F (◯ A) (◯ B)
◯↝↝◯↝◯′ {A = A} {B = B} {F = F} {P = P}
  F↔ ◯∘P↝P∘◯-map P-cong P-cong-refl P-stable ext =
  ◯↝↝◯↝◯
    F↔
    ◯∘P↝P∘◯-map
    P-cong
    P-stable
    (Σ◯→↝Σ◯→◯ (P-cong _) P-cong-refl ext)
    ext

private

  -- An example of how ◯↝↝◯↝◯′ can be used.

  ◯⇔≃◯⇔◯′ : ◯ (A ⇔ B) ↝[ a ∣ a ] (◯ A ⇔ ◯ B)
  ◯⇔≃◯⇔◯′ ext =
    ◯↝↝◯↝◯′
      ⇔↔→×→
      ◯→≃◯→◯
      (λ _ _ → F.id)
      (λ _ → refl _)
      (Stable-Π ext λ _ → Modal→Stable Modal-◯)
      ext

-- A "computation rule" for ◯↝↝◯↝◯.

◯↝↝◯↝◯-η :
  {F : Type a → Type a → Type a}
  {P : {A B : Type a} → (A → B) → Type a}
  (F↔ : ∀ {A B} → F A B ↔ (∃ λ (f : A → B) → P f))
  (◯∘P↝P∘◯-map : {f : A → B} → ◯ (P f) ↝[ a ∣ a ] P (◯-map f)) →
  (P-cong :
     ∀ {k} {f g : ◯ A → ◯ B} →
     Extensionality? k a a → (∀ x → f x ≡ g x) → P f ↝[ k ] P g)
  (P-stable : {f : ◯ A → ◯ B} → Stable (P f)) →
  (∀ {f} {p : P f} → P-stable (η p) ≡ p) →
  (Σ◯→→Σ◯→◯ :
     (∃ λ (f : ◯ (A → B)) → P (◯-map-◯ f)) →
     (∃ λ (f : ◯ A → ◯ B) → P f)) →
  (∀ f p →
     Σ◯→→Σ◯→◯
       (η f , P-cong _ (λ _ → sym ◯-map-◯-ηˡ) (◯∘P↝P∘◯-map _ (η p))) ≡
     (◯-map f , ◯∘P↝P∘◯-map _ (η p))) →
  {x : F A B} →
  ◯↝↝◯↝◯ F↔ ◯∘P↝P∘◯-map P-cong P-stable Σ◯→→Σ◯→◯ _ (η x) ≡
  _↔_.from F↔ (Σ-map ◯-map (◯∘P↝P∘◯-map _ ∘ η) (_↔_.to F↔ x))
◯↝↝◯↝◯-η
  F↔ ◯∘P↝P∘◯-map P-cong P-stable P-stable-η Σ◯→→Σ◯→◯ hyp {x = x} =
  ◯↝↝◯↝◯ F↔ ◯∘P↝P∘◯-map P-cong P-stable Σ◯→→Σ◯→◯ _ (η x)          ≡⟨⟩

  (_↔_.from F↔ $ Σ◯→→Σ◯→◯ $ Σ-map id P-stable $ ◯Ση≃Σ◯◯ _ $
   ◯-map (Σ-map id (P-cong _ λ _ → sym ◯-map-◯-ηˡ)) $
   ◯-map (Σ-map id (◯∘P↝P∘◯-map _)) $ ◯-map (Σ-map id η) $
   ◯-map (_↔_.to F↔) (η x))                                       ≡⟨ cong (_↔_.from F↔) $ cong Σ◯→→Σ◯→◯ $ cong (Σ-map id P-stable) $
                                                                     trans
                                                                       (cong (◯Ση≃Σ◯◯ _) $
                                                                        trans
                                                                          (cong (◯-map (Σ-map id (P-cong _ λ _ → sym ◯-map-◯-ηˡ))) $
                                                                           trans
                                                                             (cong (◯-map (Σ-map id (◯∘P↝P∘◯-map _))) $
                                                                              trans
                                                                                (cong (◯-map (Σ-map id η))
                                                                                 ◯-map-η) $
                                                                              ◯-map-η)
                                                                           ◯-map-η)
                                                                        ◯-map-η)
                                                                     ◯-rec-η ⟩
  (_↔_.from F↔ $ Σ◯→→Σ◯→◯ $
   Σ-map
     η
     (P-stable ∘ η ∘ P-cong _ (λ _ → sym ◯-map-◯-ηˡ) ∘
      ◯∘P↝P∘◯-map _ ∘ η)
     (_↔_.to F↔ x))                                               ≡⟨ cong (_↔_.from F↔) $ cong Σ◯→→Σ◯→◯ $ cong (_ ,_)
                                                                     P-stable-η ⟩
  (_↔_.from F↔ $ Σ◯→→Σ◯→◯ $
   Σ-map
     η
     (P-cong _ (λ _ → sym ◯-map-◯-ηˡ) ∘ ◯∘P↝P∘◯-map _ ∘ η)
     (_↔_.to F↔ x))                                               ≡⟨ cong (_↔_.from F↔) $
                                                                     hyp _ _ ⟩∎
  _↔_.from F↔ (Σ-map ◯-map (◯∘P↝P∘◯-map _ ∘ η) (_↔_.to F↔ x))     ∎

-- A "computation rule" for ◯↝↝◯↝◯′.

◯↝↝◯↝◯′-η :
  {F : Type a → Type a → Type a}
  {P : {A B : Type a} → (A → B) → Type a}
  (F↔ : ∀ {A B} → F A B ↔ (∃ λ (f : A → B) → P f))
  (◯∘P↝P∘◯-map : {f : A → B} → ◯ (P f) ↝[ a ∣ a ] P (◯-map f))
  (P-cong :
     ∀ {k} {f g : ◯ A → ◯ B} →
     Extensionality? k a a → (∀ x → f x ≡ g x) → P f ↝[ k ] P g)
  (P-cong-refl :
     ∀ {f x} →
     Extensionality a a →
     P-cong {k = implication} _ (refl ∘ f) x ≡ x)
  (P-stable : {f : ◯ A → ◯ B} → Stable (P f)) →
  (∀ {f} {p : P f} → P-stable (η p) ≡ p) →
  Extensionality a a →
  {x : F A B} →
  ◯↝↝◯↝◯′ F↔ ◯∘P↝P∘◯-map P-cong P-cong-refl P-stable _ (η x) ≡
  _↔_.from F↔ (Σ-map ◯-map (◯∘P↝P∘◯-map _ ∘ η) (_↔_.to F↔ x))
◯↝↝◯↝◯′-η {P = P}
  F↔ ◯∘P↝P∘◯-map P-cong P-cong-refl P-stable P-stable-η ext {x = x} =
  ◯↝↝◯↝◯-η F↔ ◯∘P↝P∘◯-map P-cong P-stable P-stable-η
    (Σ◯→↝Σ◯→◯ (P-cong _) P-cong-refl _)
    (λ f p →
       Σ-≡,≡→≡
         (◯-map-◯ (η f)  ≡⟨ (apply-ext ext λ _ → ◯-map-◯-ηˡ) ⟩∎
          ◯-map f        ∎)
         (subst P (apply-ext ext λ _ → ◯-map-◯-ηˡ)
            (P-cong _ (λ _ → sym ◯-map-◯-ηˡ)
               (◯∘P↝P∘◯-map _ (η p)))                                  ≡⟨ cong (subst P _) $
                                                                          cong (λ eq → P-cong _ eq (◯∘P↝P∘◯-map _ (η p))) $
                                                                          trans (sym $ _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) _) $
                                                                          cong ext⁻¹ $
                                                                          ext-sym ext ⟩
          subst P (apply-ext ext λ _ → ◯-map-◯-ηˡ)
            (P-cong _ (ext⁻¹ $ sym $ apply-ext ext λ _ → ◯-map-◯-ηˡ)
               (◯∘P↝P∘◯-map _ (η p)))                                  ≡⟨ elim₁
                                                                            (λ eq →
                                                                               subst P eq
                                                                                 (P-cong _ (ext⁻¹ $ sym eq) (◯∘P↝P∘◯-map _ (η p))) ≡
                                                                               ◯∘P↝P∘◯-map _ (η p))
                                                                            (
            subst P (refl _)
              (P-cong _ (ext⁻¹ $ sym $ refl _) (◯∘P↝P∘◯-map _ (η p)))        ≡⟨ subst-refl _ _ ⟩

            P-cong _ (ext⁻¹ $ sym $ refl _) (◯∘P↝P∘◯-map _ (η p))            ≡⟨ (cong (λ eq → P-cong _ eq (◯∘P↝P∘◯-map _ (η p))) $
                                                                                 trans (cong ext⁻¹ sym-refl) $
                                                                                 apply-ext ext λ _ → ext⁻¹-refl _) ⟩

            P-cong _ (λ _ → refl _) (◯∘P↝P∘◯-map _ (η p))                    ≡⟨ P-cong-refl ext ⟩∎

            ◯∘P↝P∘◯-map _ (η p)                                              ∎)
                                                                            _ ⟩∎

          ◯∘P↝P∘◯-map _ (η p)                                          ∎))

------------------------------------------------------------------------
-- Some results that hold if the modality is left exact (in addition
-- to having choice)

module Left-exact (lex : Left-exact-η-cong) where

  ----------------------------------------------------------------------
  -- H-levels

  -- H-level′ n commutes with ◯ (in a certain sense).

  H-level′-◯≃◯-H-level′ :
    ∀ n → H-level′ n (◯ A) ↝[ a ∣ a ] ◯ (H-level′ n A)
  H-level′-◯≃◯-H-level′ {A = A} zero ext =
    Contractible (◯ A)                       ↔⟨⟩
    (∃ λ (x : ◯ A) → (y : ◯ A) → x ≡ y)      ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → from-equivalence $
                                                 Modal→≃◯ (Separated-◯ _ _)) ⟩
    (∃ λ (x : ◯ A) → (y : ◯ A) → ◯ (x ≡ y))  ↝⟨ (∃-cong λ _ → Π◯◯≃Π◯η ext) ⟩
    (∃ λ (x : ◯ A) → (y : A) → ◯ (x ≡ η y))  ↝⟨ (∃-cong λ _ → Π◯≃◯Π ext) ⟩
    (∃ λ (x : ◯ A) → ◯ ((y : A) → x ≡ η y))  ↝⟨ inverse-ext? ◯Ση≃Σ◯◯ ext ⟩
    ◯ (∃ λ (x : A) → (y : A) → η x ≡ η y)    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → ∀-cong ext λ _ →
                                                 from-equivalence $ inverse $ ◯≡≃η≡η lex) ⟩
    ◯ (∃ λ (x : A) → (y : A) → ◯ (x ≡ y))    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → Π◯≃◯Π ext) ⟩
    ◯ (∃ λ (x : A) → ◯ ((y : A) → x ≡ y))    ↔⟨ ◯Σ◯≃◯Σ ⟩
    ◯ (∃ λ (x : A) → (y : A) → x ≡ y)        ↔⟨⟩
    ◯ (Contractible A)                       □
  H-level′-◯≃◯-H-level′ {A = A} (suc n) ext =
    H-level′ (suc n) (◯ A)                            ↝⟨ inverse-ext?
                                                           (λ ext → Stable-H-level′ ext (suc n)
                                                                      (Modal→Modalⁿ (suc n) Modal-◯))
                                                           ext ⟩
    ◯ (H-level′ (suc n) (◯ A))                        ↔⟨⟩
    ◯ ((x y : ◯ A) → H-level′ n (x ≡ y))              ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    ((x : ◯ A) → ◯ ((y : ◯ A) → H-level′ n (x ≡ y)))  ↝⟨ (∀-cong ext λ _ → inverse-ext? Π◯≃◯Π ext) ⟩
    ((x y : ◯ A) → ◯ (H-level′ n (x ≡ y)))            ↝⟨ (∀-cong ext λ _ → Π◯◯≃Π◯η ext) ⟩
    ((x : ◯ A) (y : A) → ◯ (H-level′ n (x ≡ η y)))    ↝⟨ (∀-cong ext λ _ → Π◯≃◯Π ext) ⟩
    ((x : ◯ A) → ◯ ((y : A) → H-level′ n (x ≡ η y)))  ↝⟨ Π◯◯≃Π◯η ext ⟩
    ((x : A) → ◯ ((y : A) → H-level′ n (η x ≡ η y)))  ↝⟨ (∀-cong ext λ _ → ◯-cong-↝ ext λ ext → ∀-cong ext λ _ →
                                                          H-level′-cong ext n $ inverse $ ◯≡≃η≡η lex) ⟩
    ((x : A) → ◯ ((y : A) → H-level′ n (◯ (x ≡ y))))  ↝⟨ (∀-cong ext λ _ → ◯-cong-↝ ext λ ext → ∀-cong ext λ _ →
                                                          H-level′-◯≃◯-H-level′ n ext) ⟩
    ((x : A) → ◯ ((y : A) → ◯ (H-level′ n (x ≡ y))))  ↝⟨ (∀-cong ext λ _ → ◯Π◯≃◯Π ext) ⟩
    ((x : A) → ◯ ((y : A) → H-level′ n (x ≡ y)))      ↝⟨ Π◯≃◯Π ext ⟩
    ◯ ((x y : A) → H-level′ n (x ≡ y))                ↔⟨⟩
    ◯ (H-level′ (suc n) A)                            □

  -- H-level n commutes with ◯ (in a certain sense).

  H-level-◯≃◯-H-level :
    ∀ n → H-level n (◯ A) ↝[ a ∣ a ] ◯ (H-level n A)
  H-level-◯≃◯-H-level {A = A} n ext =
    H-level n (◯ A)   ↝⟨ H-level↔H-level′ ext ⟩
    H-level′ n (◯ A)  ↝⟨ H-level′-◯≃◯-H-level′ n ext ⟩
    ◯ (H-level′ n A)  ↝⟨ ◯-cong-↝ ext $ inverse-ext? H-level↔H-level′ ⟩□
    ◯ (H-level n A)   □

  ----------------------------------------------------------------------
  -- ◯ commutes with several kinds of functions (part 3)

  -- A function f is ◯-connected if and only if ◯ (Is-equivalence f)
  -- holds.

  Connected-→≃◯-Is-equivalence :
    ◯ -Connected-→ f ↝[ a ∣ a ] ◯ (Is-equivalence f)
  Connected-→≃◯-Is-equivalence {f = f} ext =
    ◯ -Connected-→ f                   ↔⟨⟩
    (∀ y → Contractible (◯ (f ⁻¹ y)))  ↝⟨ (∀-cong ext λ _ → H-level-◯≃◯-H-level 0 ext) ⟩
    (∀ y → ◯ (Contractible (f ⁻¹ y)))  ↝⟨ Π◯≃◯Π ext ⟩
    ◯ (∀ y → Contractible (f ⁻¹ y))    ↝⟨ ◯-cong-↝ ext $ inverse-ext? Is-equivalence≃Is-equivalence-CP ⟩□
    ◯ (Is-equivalence f)               □

  -- ◯ (Is-equivalence f) is equivalent to Is-equivalence (◯-map f)
  -- (assuming function extensionality).

  ◯-Is-equivalence≃Is-equivalence :
    ◯ (Is-equivalence f) ↝[ a ∣ a ] Is-equivalence (◯-map f)
  ◯-Is-equivalence≃Is-equivalence {f = f} ext =
    ◯ (Is-equivalence f)      ↝⟨ inverse-ext? Connected-→≃◯-Is-equivalence ext ⟩
    ◯ -Connected-→ f          ↝⟨ Left-exact→Connected-→≃Is-equivalence-◯-map
                                   (_⇔_.from (Left-exact≃Left-exact-η-cong _) lex) ext ⟩□
    Is-equivalence (◯-map f)  □

  -- ◯ commutes with _≃_ (assuming function extensionality).

  ◯≃≃◯≃◯ : ◯ (A ≃ B) ↝[ a ∣ a ] (◯ A ≃ ◯ B)
  ◯≃≃◯≃◯ ext =
    ◯↝↝◯↝◯′
      Eq.≃-as-Σ
      ◯-Is-equivalence≃Is-equivalence
      Is-equivalence-cong
      (λ ext → Is-equivalence-propositional ext _ _)
      (Modal→Stable-Is-equivalence ext Modal-◯ Separated-◯)
      ext

  -- ◯ (Split-surjective f) is equivalent to Split-surjective (◯-map f)
  -- (assuming function extensionality).

  ◯-Split-surjective≃Split-surjective :
    ◯ (Split-surjective f) ↝[ a ∣ a ] Split-surjective (◯-map f)
  ◯-Split-surjective≃Split-surjective {f = f} {k = k} ext =
    ◯ (∀ y → ∃ λ x → f x ≡ y)              ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    (∀ y → ◯ (∃ λ x → f x ≡ y))            ↝⟨ (∀-cong′ λ _ → inverse ◯Σ◯≃◯Σ) ⟩
    (∀ y → ◯ (∃ λ x → ◯ (f x ≡ y)))        ↝⟨ (∀-cong′ λ _ → ◯-cong-≃ $ ∃-cong λ _ → ◯≡≃η≡η lex) ⟩
    (∀ y → ◯ (∃ λ x → η (f x) ≡ η y))      ↝⟨ inverse-ext? Π◯◯≃Π◯η ext ⟩
    (∀ y → ◯ (∃ λ x → η (f x) ≡ y))        ↝⟨ (∀-cong′ λ _ → ◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym ◯-map-η) ⟩
    (∀ y → ◯ (∃ λ x → ◯-map f (η x) ≡ y))  ↝⟨ (∀-cong ext λ _ → ◯Ση≃Σ◯◯ ext) ⟩
    (∀ y → ∃ λ x → ◯ (◯-map f x ≡ y))      ↝⟨ (∀-cong′ λ _ → ∃-cong λ _ → Modal→Stable (Separated-◯ _ _)) ⟩□
    (∀ y → ∃ λ x → ◯-map f x ≡ y)          □
    where
    ∀-cong′ :
      {A : Type a} {P Q : A → Type a} →
      (∀ x → P x ≃ Q x) → ((x : A) → P x) ↝[ k ] ((x : A) → Q x)
    ∀-cong′ = ∀-cong ext ∘ (from-equivalence ∘_)

  -- ◯ commutes with _↠_ (assuming function extensionality).

  ◯↠≃◯↠◯ : ◯ (A ↠ B) ↝[ a ∣ a ] (◯ A ↠ ◯ B)
  ◯↠≃◯↠◯ ext =
    ◯↝↝◯↝◯′
      ↠↔∃-Split-surjective
      ◯-Split-surjective≃Split-surjective
      Split-surjective-cong
      Split-surjective-cong-refl
      (Stable-Π ext λ _ → Modal→Stable $
       Modal-Σ Modal-◯ λ _ → Separated-◯ _ _)
      ext

  private

    -- Some definitions used in the implementations of
    -- ◯-Has-quasi-inverse≃Has-quasi-inverse and ◯↔≃◯↔◯.

    Has-quasi-inverse-proofs :
      (◯ A → ◯ B) → (◯ B → ◯ A) → Type a
    Has-quasi-inverse-proofs f f⁻¹ =
      (∀ x → f (f⁻¹ x) ≡ x) × (∀ x → f⁻¹ (f x) ≡ x)

    Has-quasi-inverse-proofs-resp :
      (∀ x → g x ≡ h x) →
      Has-quasi-inverse-proofs f g →
      Has-quasi-inverse-proofs f h
    Has-quasi-inverse-proofs-resp {f = f} g≡h =
      Σ-map (trans (cong f $ sym $ g≡h _) ∘_)
            (trans (sym $ g≡h _) ∘_)

    Has-quasi-inverse-proofs-resp-refl :
      Extensionality a a →
      Has-quasi-inverse-proofs-resp (refl ∘ f) p ≡ p
    Has-quasi-inverse-proofs-resp-refl {p = p , q} ext =
      ( trans (cong _ $ sym $ refl _) ∘ p
      , trans (sym $ refl _) ∘ q
      )                                    ≡⟨ cong₂ _,_
                                                (apply-ext ext λ _ →
                                                 trans (cong (flip trans _) $
                                                        trans (cong (cong _) sym-refl) $
                                                        cong-refl _) $
                                                 trans-reflˡ _)
                                                (apply-ext ext λ _ →
                                                 trans (cong (flip trans _)
                                                        sym-refl) $
                                                 trans-reflˡ _) ⟩∎
      (p , q)                              ∎

  -- ◯ (Has-quasi-inverse f) is equivalent to
  -- Has-quasi-inverse (◯-map f) (assuming function extensionality).

  ◯-Has-quasi-inverse≃Has-quasi-inverse :
    ◯ (Has-quasi-inverse f) ↝[ a ∣ a ] Has-quasi-inverse (◯-map f)
  ◯-Has-quasi-inverse≃Has-quasi-inverse {f = f} ext =
    ◯ (∃ λ g → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x))              ↔⟨ inverse ◯Σ◯≃◯Σ ⟩

    ◯ (∃ λ g → ◯ ((∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)))          ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯×≃) ⟩

    ◯ (∃ λ g → ◯ (∀ x → f (g x) ≡ x) × ◯ (∀ x → g (f x) ≡ x))          ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ →
                                                                           inverse-ext? (λ ext → Π◯≃◯Π ext ×-cong Π◯≃◯Π ext) ext) ⟩

    ◯ (∃ λ g → (∀ x → ◯ (f (g x) ≡ x)) × (∀ x → ◯ (g (f x) ≡ x)))      ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ →
                                                                           (∀-cong ext λ _ → from-equivalence $ ◯≡≃η≡η lex)
                                                                             ×-cong
                                                                           (∀-cong ext λ _ → from-equivalence $ ◯≡≃η≡η lex)) ⟩

    ◯ (∃ λ g → (∀ x → η (f (g x)) ≡ η x) × (∀ x → η (g (f x)) ≡ η x))  ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ →
                                                                           (∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                            trans (cong (◯-map f) ◯-map-◯-η) ◯-map-η)
                                                                             ×-cong
                                                                           (∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                            ◯-map-◯-η)) ⟩
    ◯ (∃ λ g → (∀ x → ◯-map f (◯-map-◯ (η g) (η x)) ≡ η x) ×
               (∀ x → ◯-map-◯ (η g) (η (f x)) ≡ η x))                  ↝⟨ ◯Ση≃Σ◯◯ ext ⟩

    (∃ λ g → ◯ ((∀ x → ◯-map f (◯-map-◯ g (η x)) ≡ η x) ×
                (∀ x → ◯-map-◯ g (η (f x)) ≡ η x)))                    ↔⟨ (∃-cong λ _ → ◯×≃) ⟩

    (∃ λ g → ◯ (∀ x → ◯-map f (◯-map-◯ g (η x)) ≡ η x) ×
             ◯ (∀ x → ◯-map-◯ g (η (f x)) ≡ η x))                      ↝⟨ inverse-ext?
                                                                            (λ ext → ∃-cong λ _ → Π◯≃◯Π ext ×-cong Π◯≃◯Π ext)
                                                                            ext ⟩
    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g (η x)) ≡ η x)) ×
             (∀ x → ◯ (◯-map-◯ g (η (f x)) ≡ η x)))                    ↝⟨ (∃-cong λ g → ∃-cong λ _ → ∀-cong ext λ _ → ◯-cong-↝ ext λ _ →
                                                                           ≡⇒↝ _ $ cong ((_≡ _) ∘ ◯-map-◯ g) $ sym ◯-map-η) ⟩
    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g (η x)) ≡ η x)) ×
             (∀ x → ◯ (◯-map-◯ g (◯-map f (η x)) ≡ η x)))              ↝⟨ (∃-cong λ _ →
                                                                           inverse-ext? (λ ext → Π◯◯≃Π◯η ext ×-cong Π◯◯≃Π◯η ext) ext) ⟩
    (∃ λ g → (∀ x → ◯ (◯-map f (◯-map-◯ g x) ≡ x)) ×
             (∀ x → ◯ (◯-map-◯ g (◯-map f x) ≡ x)))                    ↝⟨ (∃-cong λ _ →
                                                                           (∀-cong ext λ _ → Modal→Stable (Separated-◯ _ _))
                                                                             ×-cong
                                                                           (∀-cong ext λ _ → Modal→Stable (Separated-◯ _ _))) ⟩
    (∃ λ g → (∀ x → ◯-map f (◯-map-◯ g x) ≡ x) ×
             (∀ x → ◯-map-◯ g (◯-map f x) ≡ x))                        ↝⟨ Σ◯→↝Σ◯→◯
                                                                            Has-quasi-inverse-proofs-resp
                                                                            Has-quasi-inverse-proofs-resp-refl
                                                                            ext ⟩□
    (∃ λ g → (∀ x → ◯-map f (g x) ≡ x) × (∀ x → g (◯-map f x) ≡ x))    □

  -- ◯ commutes with _↔_ (assuming function extensionality).

  ◯↔≃◯↔◯ : ◯ (A ↔ B) ↝[ a ∣ a ] (◯ A ↔ ◯ B)
  ◯↔≃◯↔◯ ext =
    ◯↝↝◯↝◯′
      Bijection.↔-as-Σ
      ◯-Has-quasi-inverse≃Has-quasi-inverse
      Has-quasi-inverse-cong
      Has-quasi-inverse-cong-refl
      (Stable-Σ[◯→◯] ext
         Has-quasi-inverse-proofs-resp
         Has-quasi-inverse-proofs-resp-refl λ _ →
       Stable-×
         (Stable-Π ext λ _ →
          Modal→Stable (Modal→Separated Modal-◯ _ _))
         (Stable-Π ext λ _ →
          Modal→Stable (Modal→Separated Modal-◯ _ _)))
      ext

  -- ◯ (Injective f) is equivalent to Injective (◯-map f) (assuming
  -- function extensionality).

  ◯-Injective≃Injective :
    ◯ (Injective f) ↝[ a ∣ a ] Injective (◯-map f)
  ◯-Injective≃Injective {f = f} ext =
    ◯ (∀ {x y} → f x ≡ f y → x ≡ y)                      ↔⟨ ◯-cong-≃ $ inverse lemma ⟩
    ◯ (∀ x y → f x ≡ f y → x ≡ y)                        ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    (∀ x → ◯ (∀ y → f x ≡ f y → x ≡ y))                  ↝⟨ (∀-cong ext λ _ → inverse-ext? Π◯≃◯Π ext) ⟩
    (∀ x y → ◯ (f x ≡ f y → x ≡ y))                      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ◯→≃◯→◯ ext) ⟩
    (∀ x y → ◯ (f x ≡ f y) → ◯ (x ≡ y))                  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → →-cong₁ ext $
                                                             ◯≡≃η≡η lex) ⟩
    (∀ x y → η (f x) ≡ η (f y) → ◯ (x ≡ y))              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → from-equivalence $
                                                             ◯≡≃η≡η lex) ⟩
    (∀ x y → η (f x) ≡ η (f y) → η x ≡ η y)              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → →-cong₁ ext $
                                                             ≡⇒↝ equivalence $ sym $ cong₂ _≡_ ◯-map-η ◯-map-η) ⟩
    (∀ x y → ◯-map f (η x) ≡ ◯-map f (η y) → η x ≡ η y)  ↝⟨ (∀-cong ext λ _ → inverse-ext? (Π◯↝Πη s) ext) ⟩
    (∀ x y → ◯-map f (η x) ≡ ◯-map f y → η x ≡ y)        ↝⟨ inverse-ext? (Π◯↝Πη λ ext _ → Stable-Π ext (s ext)) ext ⟩
    (∀ x y → ◯-map f x ≡ ◯-map f y → x ≡ y)              ↔⟨ lemma ⟩□
    (∀ {x y} → ◯-map f x ≡ ◯-map f y → x ≡ y)            □
    where
    lemma :
      {P : A → B → Type p} →
      (∀ x y → P x y) ≃ (∀ {x y} → P x y)
    lemma = Eq.↔→≃ (λ f → f _ _) (λ f _ _ → f) refl refl

    s :
      Extensionality? k a a →
      ∀ y → Stable-[ k ] (◯-map f x ≡ ◯-map f y → x ≡ y)
    s ext _ = Stable-Π ext λ _ → Modal→Stable $ Separated-◯ _ _

  -- ◯ commutes with _↣_ (assuming function extensionality).

  ◯↣≃◯↣◯ : ◯ (A ↣ B) ↝[ a ∣ a ] (◯ A ↣ ◯ B)
  ◯↣≃◯↣◯ ext =
    ◯↝↝◯↝◯′
      ↣↔∃-Injective
      ◯-Injective≃Injective
      Injective-cong
      Injective-cong-refl
      (Stable-implicit-Π ext λ _ →
       Stable-implicit-Π ext λ _ →
       Stable-Π          ext λ _ →
       Modal→Stable $ Separated-◯ _ _)
      ext

  -- ◯ (Is-embedding f) is equivalent to Is-embedding (◯-map f)
  -- (assuming function extensionality).

  ◯-Is-embedding≃Is-embedding :
    ◯ (Is-embedding f) ↝[ a ∣ a ] Is-embedding (◯-map f)
  ◯-Is-embedding≃Is-embedding {f = f} ext =
    ◯ (∀ x y → Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y)))             ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩

    (∀ x → ◯ (∀ y → Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y))))       ↝⟨ (∀-cong ext λ _ → inverse-ext? Π◯≃◯Π ext) ⟩

    (∀ x y → ◯ (Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y))))           ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ◯-Is-equivalence≃Is-equivalence ext) ⟩

    (∀ x y → Is-equivalence (◯-map (cong f ⦂ (x ≡ y → f x ≡ f y))))       ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Is-equivalence-cong ext $
                                                                              ◯-map-cong≡ lex) ⟩
    (∀ x y →
       Is-equivalence
         (η-cong⁻¹ lex ∘
          _≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → ◯ (f x ≡ f y))))         ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse-ext?
                                                                                (Is-equivalence≃Is-equivalence-∘ˡ
                                                                                   (_≃_.is-equivalence $ inverse $ ◯≡≃η≡η lex))
                                                                                ext) ⟩
    (∀ x y →
       Is-equivalence
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → η (f x) ≡ η (f y))))     ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse-ext?
                                                                                (Is-equivalence≃Is-equivalence-∘ʳ lex)
                                                                                ext) ⟩
    (∀ x y →
       Is-equivalence
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
          cong (◯-map f) ⦂ (η x ≡ η y → η (f x) ≡ η (f y))))              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse-ext?
                                                                                (Is-equivalence≃Is-equivalence-∘ˡ
                                                                                   (_≃_.is-equivalence $ ≡⇒↝ _ _))
                                                                                ext) ⟩
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (η x ≡ η y → ◯-map f (η x) ≡ ◯-map f (η y))))  ↝⟨ inverse-ext?
                                                                               (Π◯↝Πη λ ext _ →
                                                                                Stable-Π ext λ _ →
                                                                                Modal→Stable-Is-equivalence ext
                                                                                  (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _)))
                                                                               ext ⟩
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (x ≡ η y → ◯-map f x ≡ ◯-map f (η y))))        ↝⟨ (∀-cong ext λ _ →
                                                                              inverse-ext?
                                                                                (Π◯↝Πη λ ext _ →
                                                                                 Modal→Stable-Is-equivalence ext
                                                                                   (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _)))
                                                                                ext) ⟩□
    (∀ x y →
       Is-equivalence
         (cong (◯-map f) ⦂ (x ≡ y → ◯-map f x ≡ ◯-map f y)))              □

  -- ◯ commutes with Embedding (assuming function extensionality).

  ◯-Embedding≃Embedding-◯-◯ :
    ◯ (Embedding A B) ↝[ a ∣ a ] Embedding (◯ A) (◯ B)
  ◯-Embedding≃Embedding-◯-◯ ext =
    ◯↝↝◯↝◯′
      Emb.Embedding-as-Σ
      ◯-Is-embedding≃Is-embedding
      Is-embedding-cong
      (λ ext → Emb.Is-embedding-propositional ext _ _)
      (Stable-Π ext λ _ → Stable-Π ext λ _ →
       Modal→Stable-Is-equivalence ext
         (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _)))
      ext

  -- ◯ (HA.Proofs f f⁻¹) is equivalent to
  -- HA.Proofs (◯-map f) (◯-map f⁻¹) (assuming function
  -- extensionality).

  ◯-Half-adjoint-proofs≃Half-adjoint-proofs-◯-map-◯-map :
    {f : A → B} →
    Extensionality a a →
    ◯ (HA.Proofs f f⁻¹) ≃ HA.Proofs (◯-map f) (◯-map f⁻¹)
  ◯-Half-adjoint-proofs≃Half-adjoint-proofs-◯-map-◯-map
    {A = A} {B = B} {f⁻¹ = f⁻¹} {f = f} ext =
    ◯ (HA.Proofs f f⁻¹)                                                   ↔⟨⟩

    ◯ (∃ λ (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
       ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
       (x : A) → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))                          ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ∃-cong λ _ → inverse (Π◯≃◯Π ext)) F.∘
                                                                             ◯Σ◯≃◯Σ F.∘
                                                                             (◯-cong-≃ $ ∃-cong λ _ → inverse ◯Σ◯≃◯Σ) F.∘
                                                                             inverse ◯Σ◯≃◯Σ ⟩
    ◯ (∃ λ (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
       ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
       (x : A) → ◯ (cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x)))                      ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ◯≡≃η≡η lex) ⟩
    ◯ (∃ λ (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
       ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
       (x : A) → η (cong f (f⁻¹-f x)) ≡ η (f-f⁻¹ (f x)))                  ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ sym $ cong₂ _≡_ ◯-map-η ◯-map-η) ⟩
    ◯ (∃ λ (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
       ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
       (x : A) →
       ◯-map (cong f ∘ (_$ x)) (η f⁻¹-f) ≡ ◯-map (_$ f x) (η f-f⁻¹))      ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse (Π◯≃◯Π ext)) F.∘
                                                                             (∃-cong λ _ → ◯Ση≃Σ◯◯ ext) F.∘
                                                                             ◯Ση≃Σ◯◯ ext ⟩
    (∃ λ (f-f⁻¹ : ◯ (∀ x → f (f⁻¹ x) ≡ x)) →
     ∃ λ (f⁻¹-f : ◯ (∀ x → f⁻¹ (f x) ≡ x)) →
     (x : A) → ◯ (◯-map (cong f ∘ (_$ x)) f⁻¹-f ≡ ◯-map (_$ f x) f-f⁻¹))  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse $
                                                                              Modal→≃◯ $ Separated-◯ _ _) ⟩
    (∃ λ (f-f⁻¹ : ◯ (∀ x → f (f⁻¹ x) ≡ x)) →
     ∃ λ (f⁻¹-f : ◯ (∀ x → f⁻¹ (f x) ≡ x)) →
     (x : A) → ◯-map (cong f ∘ (_$ x)) f⁻¹-f ≡ ◯-map (_$ f x) f-f⁻¹)      ↝⟨ (Σ-cong (lemma₂ _ _) λ _ →
                                                                              Σ-cong (lemma₂ _ _) λ _ →
                                                                              ∀-cong ext λ _ → lemma₃ _ _ _) ⟩
    (∃ λ (f-f⁻¹ : ∀ x → ◯-map f (◯-map f⁻¹ x) ≡ x) →
     ∃ λ (f⁻¹-f : ∀ x → ◯-map f⁻¹ (◯-map f x) ≡ x) →
     (x : A) → cong (◯-map f) (f⁻¹-f (η x)) ≡ f-f⁻¹ (◯-map f (η x)))      ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse $
                                                                              Π◯≃Πη ext λ _ →
                                                                              Modal→Stable $ Modal→Separated (Separated-◯ _ _) _ _) ⟩
    (∃ λ (f-f⁻¹ : ∀ x → ◯-map f (◯-map f⁻¹ x) ≡ x) →
     ∃ λ (f⁻¹-f : ∀ x → ◯-map f⁻¹ (◯-map f x) ≡ x) →
     (x : ◯ A) → cong (◯-map f) (f⁻¹-f x) ≡ f-f⁻¹ (◯-map f x))            ↔⟨⟩

    HA.Proofs (◯-map f) (◯-map f⁻¹)                                       □
    where
    lemma₁ :
      ∀ {A B : Type a} (g : A → B) (h : B → A) {x} →
      ◯-map g (◯-map h (η x)) ≡ η (g (h x))
    lemma₁ g h {x = x} =
      ◯-map g (◯-map h (η x))  ≡⟨ cong (◯-map g) ◯-map-η ⟩
      ◯-map g (η (h x))        ≡⟨ ◯-map-η ⟩∎
      η (g (h x))              ∎

    s : ∀ x → Stable-[ equivalence ] (◯-map g (◯-map h x) ≡ x)
    s _ = Modal→Stable $ Separated-◯ _ _

    abstract

      lemma₂ :
        {A B : Type a} (g : A → B) (h : B → A) →
        ◯ ((x : B) → g (h x) ≡ x) ≃
        ((x : ◯ B) → ◯-map g (◯-map h x) ≡ x)
      lemma₂ {B = B} g h =
        ◯ ((x : B) → g (h x) ≡ x)                  ↝⟨ inverse (Π◯≃◯Π ext) ⟩
        ((x : B) → ◯ (g (h x) ≡ x))                ↝⟨ (∀-cong ext λ _ → ◯≡≃η≡η lex) ⟩
        ((x : B) → η (g (h x)) ≡ η x)              ↔⟨ (∀-cong ext λ _ → trans-isomorphism (lemma₁ g h)) ⟩
        ((x : B) → ◯-map g (◯-map h (η x)) ≡ η x)  ↝⟨ inverse $ Π◯≃Πη ext s ⟩□
        ((x : ◯ B) → ◯-map g (◯-map h x) ≡ x)      □

      lemma₂-η :
        ∀ {A B : Type a} {g : A → B} {h p x} →
        _≃_.to (lemma₂ g h) (η p) (η x) ≡
        trans (lemma₁ g h) (cong η (p x))
      lemma₂-η {g = g} {h = h} {p = p} {x = x} =
        _≃_.to (lemma₂ g h) (η p) (η x)                ≡⟨⟩

        _≃_.from (Π◯≃Πη ext s)
          (trans (lemma₁ g h) ∘ η-cong ∘ ◯Π→Π◯ (η p))
          (η x)                                        ≡⟨ Π◯≃Πη⁻¹-η ext s ⟩

        trans (lemma₁ g h) (η-cong (◯Π→Π◯ (η p) x))    ≡⟨ cong (trans (lemma₁ g h) ∘ η-cong) $ cong (_$ x) $
                                                          ◯Π→Π◯-η ext ⟩

        trans (lemma₁ g h) (η-cong (η (p x)))          ≡⟨ cong (trans (lemma₁ g h))
                                                          η-cong-η ⟩∎
        trans (lemma₁ g h) (cong η (p x))              ∎

    lemma₂-ηˡ :
      ∀ {A B : Type a} {g : A → B} {h p x} →
      _≃_.to (lemma₂ g h) (η p) x ≡
      ◯-elim (λ _ → Separated-◯ _ _) (trans (lemma₁ g h) ∘ cong η ∘ p) x
    lemma₂-ηˡ {g = g} {h = h} {p = p} {x = x} =
      ◯-elim
        {P = λ x →
               _≃_.to (lemma₂ g h) (η p) x ≡
               ◯-elim (λ _ → Separated-◯ _ _)
                 (trans (lemma₁ g h) ∘ cong η ∘ p) x}
        (λ _ → Modal→Separated (Separated-◯ _ _) _ _)
        (λ x →
           _≃_.to (lemma₂ g h) (η p) (η x)                     ≡⟨ lemma₂-η ⟩

           trans (lemma₁ g h) (cong η (p x))                   ≡⟨ sym ◯-elim-η ⟩∎

           ◯-elim (λ x → Separated-◯ (◯-map g (◯-map h x)) x)
             (trans (lemma₁ g h) ∘ cong η ∘ p) (η x)           ∎)
        x

    lemma₃ :
      ∀ x f-f⁻¹ f⁻¹-f →
      (◯-map (cong f ∘ (_$ x)) f⁻¹-f ≡ ◯-map (_$ f x) f-f⁻¹) ≃
      (cong (◯-map f) (_≃_.to (lemma₂ f⁻¹ f) f⁻¹-f (η x)) ≡
       _≃_.to (lemma₂ f f⁻¹) f-f⁻¹ (◯-map f (η x)))
    lemma₃ x =
      ◯-elim (λ _ → Modal-Π ext λ _ → m) λ f-f⁻¹ →
      ◯-elim (λ _ → m) λ f⁻¹-f →

        ◯-map (cong f ∘ (_$ x)) (η f⁻¹-f) ≡ ◯-map (_$ f x) (η f-f⁻¹)  ↝⟨ ≡⇒↝ _ $ cong₂ _≡_ ◯-map-η ◯-map-η ⟩

        η (cong f (f⁻¹-f x)) ≡ η (f-f⁻¹ (f x))                        ↝⟨ inverse $ Eq.≃-≡ $ ◯≡≃η≡η lex ⟩

        η-cong (η (cong f (f⁻¹-f x))) ≡ η-cong (η (f-f⁻¹ (f x)))      ↝⟨ ≡⇒↝ _ $ cong₂ _≡_ η-cong-η η-cong-η ⟩

        cong η (cong f (f⁻¹-f x)) ≡ cong η (f-f⁻¹ (f x))              ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ $ flip-trans-isomorphism _ ⟩

        trans (cong η (cong f (f⁻¹-f x))) (sym ◯-map-η) ≡
        trans (cong η (f-f⁻¹ (f x))) (sym ◯-map-η)                    ↝⟨ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ $ trans-isomorphism _ ⟩

        trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
          (trans (cong η (cong f (f⁻¹-f x))) (sym ◯-map-η)) ≡
        trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
          (trans (cong η (f-f⁻¹ (f x))) (sym ◯-map-η))                ↝⟨ ≡⇒↝ _ $ sym $ cong₂ _≡_ (lemma₄ _) (lemma₅ _) ⟩□

        cong (◯-map f) (_≃_.to (lemma₂ f⁻¹ f) (η f⁻¹-f) (η x)) ≡
        _≃_.to (lemma₂ f f⁻¹) (η f-f⁻¹) (◯-map f (η x))               □
      where
      m :
        ∀ {f-f⁻¹ f⁻¹-f} →
        Modal
          ((◯-map (cong f ∘ (_$ x)) f⁻¹-f ≡ ◯-map (_$ f x) f-f⁻¹) ≃
           (cong (◯-map f) (_≃_.to (lemma₂ f⁻¹ f) f⁻¹-f (η x)) ≡
            _≃_.to (lemma₂ f f⁻¹) f-f⁻¹ (◯-map f (η x))))
      m =
        Modal-≃ ext (Separated-◯ _ _) $
        Modal→Separated (Separated-◯ _ _) _ _

      lemma₄ :
        (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
        cong (◯-map f) (_≃_.to (lemma₂ f⁻¹ f) (η f⁻¹-f) (η x)) ≡
        trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
          (trans (cong η (cong f (f⁻¹-f x))) (sym ◯-map-η))
      lemma₄ f⁻¹-f =
        cong (◯-map f) (_≃_.to (lemma₂ f⁻¹ f) (η f⁻¹-f) (η x))     ≡⟨ cong (cong (◯-map f)) lemma₂-η ⟩

        cong (◯-map f) (trans (lemma₁ f⁻¹ f) (cong η (f⁻¹-f x)))   ≡⟨ elim¹
                                                                        (λ p →
                                                                           cong (◯-map f) (trans (lemma₁ f⁻¹ f) (cong η p)) ≡
                                                                           trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
                                                                             (trans (cong η (cong f p)) (sym ◯-map-η)))
                                                                        (
          cong (◯-map f) (trans (lemma₁ f⁻¹ f) (cong η (refl _)))        ≡⟨ cong (cong (◯-map f)) $
                                                                            trans (cong (trans _) $ cong-refl _) $
                                                                            trans-reflʳ _ ⟩

          cong (◯-map f) (lemma₁ f⁻¹ f)                                  ≡⟨ sym $
                                                                            trans-[trans]-sym _ _ ⟩
          trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
            (sym ◯-map-η)                                                ≡⟨ cong (trans _) $ sym $
                                                                            trans (cong (flip trans _) $
                                                                                   trans (cong (cong η) $ cong-refl _) $
                                                                                   cong-refl _) $
                                                                            trans-reflˡ _ ⟩∎
          trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
            (trans (cong η (cong f (refl _))) (sym ◯-map-η))             ∎)
                                                                        _ ⟩∎
        trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
          (trans (cong η (cong f (f⁻¹-f x))) (sym ◯-map-η))        ∎

      lemma₅ :
        (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
        _≃_.to (lemma₂ f f⁻¹) (η f-f⁻¹) (◯-map f (η x)) ≡
        trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
          (trans (cong η (f-f⁻¹ (f x))) (sym ◯-map-η))
      lemma₅ f-f⁻¹ =
        _≃_.to (lemma₂ f f⁻¹) (η f-f⁻¹) (◯-map f (η x))             ≡⟨ lemma₂-ηˡ ⟩

        ◯-elim
          {P = λ x → ◯-map f (◯-map f⁻¹ x) ≡ x}
          (λ _ → Separated-◯ _ _)
          (trans (lemma₁ f f⁻¹) ∘ cong η ∘ f-f⁻¹)
          (◯-map f (η x))                                           ≡⟨ ◯-elim-◯-map ⟩

        ◯-elim
          {P = λ x → ◯-map f (◯-map f⁻¹ (◯-map f x)) ≡ ◯-map f x}
          (λ _ → Separated-◯ _ _)
          (subst (λ x → ◯-map f (◯-map f⁻¹ x) ≡ x) (sym ◯-map-η) ∘
           trans (lemma₁ f f⁻¹) ∘ cong η ∘ f-f⁻¹ ∘ f)
          (η x)                                                     ≡⟨ ◯-elim-η ⟩

        subst (λ x → ◯-map f (◯-map f⁻¹ x) ≡ x) (sym ◯-map-η)
          (trans (lemma₁ f f⁻¹) (cong η (f-f⁻¹ (f x))))             ≡⟨ subst-in-terms-of-trans-and-cong ⟩

        trans (sym (cong (◯-map f ∘ ◯-map f⁻¹) (sym ◯-map-η)))
          (trans (trans (lemma₁ f f⁻¹) (cong η (f-f⁻¹ (f x))))
             (cong id (sym ◯-map-η)))                               ≡⟨ cong (trans _) $
                                                                       trans (cong (trans _) $ sym $ cong-id _) $
                                                                       trans-assoc _ _ _ ⟩
        trans (sym (cong (◯-map f ∘ ◯-map f⁻¹) (sym ◯-map-η)))
          (trans (lemma₁ f f⁻¹)
             (trans (cong η (f-f⁻¹ (f x))) (sym ◯-map-η)))          ≡⟨ elim¹
                                                                         (λ eq →
                                                                            trans (sym (cong (◯-map f ∘ ◯-map f⁻¹) (sym ◯-map-η)))
                                                                              (trans (lemma₁ f f⁻¹) eq) ≡
                                                                            trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η) eq)
                                                                         (trans (cong (trans _) $ trans-reflʳ _) $
                                                                          trans lemma₆ $
                                                                          sym $ trans-reflʳ _)
                                                                         _ ⟩∎
        trans (trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η)
          (trans (cong η (f-f⁻¹ (f x))) (sym ◯-map-η))              ∎
        where
        lemma₆ =
          trans (sym (cong (◯-map f ∘ ◯-map f⁻¹)
                        (sym $ ◯-map-η {x = x})))
            (lemma₁ f f⁻¹)                                        ≡⟨⟩

          trans (sym (cong (◯-map f ∘ ◯-map f⁻¹) (sym ◯-map-η)))
            (trans (cong (◯-map f) ◯-map-η) ◯-map-η)              ≡⟨ cong (flip trans _) $
                                                                     trans (sym $ cong-sym _ _) $
                                                                     cong (cong _) $ sym-sym _ ⟩
          trans (cong (◯-map f ∘ ◯-map f⁻¹) ◯-map-η)
            (trans (cong (◯-map f) ◯-map-η) ◯-map-η)              ≡⟨ cong (flip trans _) $ sym $
                                                                     cong-∘ _ _ _ ⟩
          trans (cong (◯-map f) (cong (◯-map f⁻¹) ◯-map-η))
            (trans (cong (◯-map f) ◯-map-η) ◯-map-η)              ≡⟨ trans (sym $ trans-assoc _ _ _) $
                                                                     cong (flip trans _) $ sym $
                                                                     cong-trans _ _ _ ⟩
          trans (cong (◯-map f)
                   (trans (cong (◯-map f⁻¹) ◯-map-η) ◯-map-η))
            ◯-map-η                                               ≡⟨⟩

          trans (cong (◯-map f) (lemma₁ f⁻¹ f)) ◯-map-η           ∎
