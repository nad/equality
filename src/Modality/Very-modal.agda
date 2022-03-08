------------------------------------------------------------------------
-- Some results that hold for every very modal modality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Modality.Basics

module Modality.Very-modal
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (open Modality.Basics eq)
  {a}
  (M : Modality a)
  (very-modal : Very-modal M)
  where

open Derived-definitions-and-properties eq

private
  open module M = Modality M
    hiding (◯Ση≃Σ◯◯; ◯Π◯≃◯Π; ◯Π◯≃◯Π-η; ◯Π◯≃◯Π⁻¹-η; ◯≡≃η≡η;
            Stable-Π; Stable-Erased; Stable-Contractibleᴱ; Stable-⁻¹ᴱ)

open import Logical-equivalence using (_⇔_)
import Modality.Box-cong
import Modality.Has-choice
open import Prelude

open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (Contractibleᴱ; _⁻¹ᴱ_)
import Equivalence.Half-adjoint eq as HA
open import Equivalence.Path-split eq using (_-Null_)
open import Erased.Level-1 eq as E
  using (Erased; []-cong-axiomatisation)
import Erased.Level-2 eq as E₂
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq

private
  variable
    ℓ p       : Level
    A B C     : Type ℓ
    f k m x y : A
    P         : A → Type p

------------------------------------------------------------------------
-- Should "Very-modal" be stated differently?

abstract

  -- ◯ (∀ x → Modal (P x)) is inhabited.
  --
  -- One might wonder if something like ◯ ({A : Type a} → Modal A)
  -- would be more general than Very-modal M. However, the former
  -- statement is not type-correct. The statement
  --
  --   {A : Type a} {P : A → Type a} → ◯ (∀ x → Modal (P x))
  --
  -- is type-correct, but follows from Very-modal M.

  ◯-Π-Modal :
    {A : Type a} {P : A → Type a} → ◯ (∀ x → Modal (P x))
  ◯-Π-Modal {A = A} {P = P} =
                                     $⟨ (λ {_} → very-modal) ⟩
    Very-modal M                     →⟨ (λ m → m , m) ⟩
    ◯ (Modal A) × ◯ (Modal (Σ A P))  →⟨ _≃_.from ◯×≃ ⟩
    ◯ (Modal A × Modal (Σ A P))      →⟨ ◯-map (λ (mA , mΣAP) → Modal-Σ≃Π-Modal mA _ mΣAP) ⟩□
    ◯ (∀ x → Modal (P x))            □

------------------------------------------------------------------------
-- The modality has choice

-- ◯ ((x : A) → ◯ (P x)) is equivalent to ◯ ((x : A) → P x) (assuming
-- function extensionality).

◯Π◯≃◯Π :
  {A : Type a} {P : A → Type a} →
  ◯ ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
◯Π◯≃◯Π = M.◯Π◯≃◯Π ◯-Π-Modal

-- Two "computation rules" for ◯Π◯≃◯Π.

◯Π◯≃◯Π-η :
  ◯Π◯≃◯Π _ (η f) ≡
  ◯-map (λ m x → Modal→Stable (m x) (f x)) ◯-Π-Modal
◯Π◯≃◯Π-η {f = f} =
  ◯-elim
    {P = λ m →
           M.◯Π◯≃◯Π m _ (η f) ≡
           ◯-map (λ m x → Modal→Stable (m x) (f x)) m}
    (λ _ → Separated-◯ _ _)
    (λ m →
       M.◯Π◯≃◯Π (η m) _ (η f)                          ≡⟨ M.◯Π◯≃◯Π-η ⟩
       η (λ x → Modal→Stable (m x) (f x))              ≡⟨ sym ◯-map-η ⟩∎
       ◯-map (λ m x → Modal→Stable (m x) (f x)) (η m)  ∎)
    ◯-Π-Modal

◯Π◯≃◯Π⁻¹-η : _⇔_.from (◯Π◯≃◯Π _) (η f) ≡ η (η ∘ f)
◯Π◯≃◯Π⁻¹-η = M.◯Π◯≃◯Π⁻¹-η ◯-Π-Modal

-- The modality satisfies a kind of choice principle.

has-choice : Has-choice
has-choice {A = A} {P = P} =
  Π◯→◯Π , ◯Π→Π◯-Π◯→◯Π , (λ ext → equiv ext , refl _ , ◯Π→Π◯-Π◯→◯Π≡ ext)
  where
  Π◯→◯Π =
    ((x : A) → ◯ (P x))    →⟨ η ⟩
    ◯ ((x : A) → ◯ (P x))  →⟨ ◯Π◯≃◯Π _ ⟩□
    ◯ ((x : A) → P x)      □

  ◯Π→Π◯-Π◯→◯Π : ∀ f x → ◯Π→Π◯ (Π◯→◯Π f) x ≡ f x
  ◯Π→Π◯-Π◯→◯Π f x =
    ◯Π→Π◯ (◯Π◯≃◯Π _ (η f)) x                                      ≡⟨ cong (flip ◯Π→Π◯ _) ◯Π◯≃◯Π-η ⟩
    ◯Π→Π◯ (◯-map (λ m x → Modal→Stable (m x) (f x)) ◯-Π-Modal) x  ≡⟨ ◯-elim
                                                                       {P = λ m →
                                                                              ◯Π→Π◯ (◯-map (λ m x → Modal→Stable (m x) (f x)) m) x ≡
                                                                              f x}
                                                                       (λ _ → Separated-◯ _ _)
                                                                       (λ m →
      ◯Π→Π◯ (◯-map (λ m x → Modal→Stable (m x) (f x)) (η m)) x            ≡⟨ cong (flip ◯Π→Π◯ _) ◯-map-η ⟩
      ◯Π→Π◯ (η (λ x → Modal→Stable (m x) (f x))) x                        ≡⟨ ◯-map-η ⟩
      η (Modal→Stable (m x) (f x))                                        ≡⟨⟩
      η (η⁻¹ (m x) (f x))                                                 ≡⟨ η-η⁻¹ ⟩∎
      f x                                                                 ∎)
                                                                       ◯-Π-Modal ⟩∎
    f x                                                           ∎

  equiv :
    Extensionality a a →
    Is-equivalence (◯Π→Π◯ {P = P})
  equiv ext =
    _≃_.is-equivalence $
    Eq.↔→≃
      _
      Π◯→◯Π
      (apply-ext ext ∘ ◯Π→Π◯-Π◯→◯Π)
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ f →
            ◯Π◯≃◯Π _ (η (◯Π→Π◯ (η f)))            ≡⟨ cong (◯Π◯≃◯Π _ ∘ η) $ ◯Π→Π◯-η ext ⟩
            ◯Π◯≃◯Π _ (η (η ∘ f))                  ≡⟨ cong (◯Π◯≃◯Π _) $ sym ◯Π◯≃◯Π⁻¹-η ⟩
            ◯Π◯≃◯Π _ (_⇔_.from (◯Π◯≃◯Π _) (η f))  ≡⟨ _≃_.right-inverse-of (◯Π◯≃◯Π ext) _ ⟩∎
            η f                                   ∎))

  ◯Π→Π◯-Π◯→◯Π≡ :
    (ext : Extensionality a a) →
    ∀ f x →
    ◯Π→Π◯-Π◯→◯Π f x ≡
    trans (cong (λ g → ◯Π→Π◯ (g f) x) (refl Π◯→◯Π))
      (ext⁻¹ (_≃_.right-inverse-of Eq.⟨ ◯Π→Π◯ , equiv ext ⟩ f) x)
  ◯Π→Π◯-Π◯→◯Π≡ ext f x =
    ◯Π→Π◯-Π◯→◯Π f x                                                ≡⟨ cong (_$ x) $ sym $
                                                                      _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) _ ⟩

    ext⁻¹ (apply-ext ext (◯Π→Π◯-Π◯→◯Π f)) x                        ≡⟨⟩

    ext⁻¹ (_≃_.right-inverse-of Eq.⟨ ◯Π→Π◯ , equiv ext ⟩ f) x      ≡⟨ trans (sym $ trans-reflˡ _) $
                                                                      cong (flip trans _) $ sym $
                                                                      cong-refl _ ⟩∎
    trans (cong (λ g → ◯Π→Π◯ (g f) x) (refl Π◯→◯Π))
      (ext⁻¹ (_≃_.right-inverse-of Eq.⟨ ◯Π→Π◯ , equiv ext ⟩ f) x)  ∎

private
  module C = Modality.Has-choice eq M has-choice
open C public
  hiding (◯Π◯≃◯Π; ◯Π◯≃◯Π-η; ◯Π◯≃◯Π⁻¹-η;
          module Left-exact; module []-cong)

------------------------------------------------------------------------
-- The modality is left exact

-- Very modal modalities are left exact.

left-exact-η-cong : Left-exact-η-cong
left-exact-η-cong =
  ◯-Modal→Is-equivalence-η-cong very-modal _ _

open C.Left-exact left-exact-η-cong public

-- Very modal modalities are left exact.

left-exact : Left-exact ◯
left-exact {A = A} {x = x} {y = y} =
  Contractible (◯ A)        →⟨ H-level′-◯≃◯-H-level′ 0 _ ⟩
  ◯ (Contractible A)        →⟨ ◯-map $ H-level.⇒≡ 0 ⟩
  ◯ (Contractible (x ≡ y))  →⟨ inverse-ext? (H-level′-◯≃◯-H-level′ 0) _ ⟩□
  Contractible (◯ (x ≡ y))  □

-- There is an equivalence between ◯ (x ≡ y) and η x ≡ η y.

◯≡≃η≡η : ◯ (x ≡ y) ≃ (η x ≡ η y)
◯≡≃η≡η = M.◯≡≃η≡η left-exact-η-cong

------------------------------------------------------------------------
-- Modal A is equivalent to Modal -Null A

-- Modal A is equivalent to Modal -Null A (assuming function
-- extensionality).

Modal≃Modal-Null :
  Extensionality a a →
  Modal A ↝[ lsuc a ∣ a ] Modal -Null A
Modal≃Modal-Null {A = A} ext =
  generalise-ext?-prop
    (record { to = to; from = from })
    (λ _ → Modal-propositional ext)
    (λ ext′ →
       Π-closure ext′ 1 λ _ →
       Is-equivalence-propositional ext)
  where
  to : Modal A → Modal -Null A
  to m _ =
    _≃_.is-equivalence $
    Eq.↔→≃
      const
      (λ f → η⁻¹ m (◯-map f very-modal))
      (λ f → apply-ext ext λ m′ →
         ◯-elim
           {P = λ m″ → η⁻¹ m (◯-map f m″) ≡ f m′}
           (λ _ → Modal→Separated m _ _)
           (λ m″ →
              η⁻¹ m (◯-map f (η m″))  ≡⟨ cong (η⁻¹ m) ◯-map-η ⟩
              η⁻¹ m (η (f m″))        ≡⟨ η⁻¹-η ⟩
              f m″                    ≡⟨ cong f $ Modal-propositional ext _ _ ⟩∎
              f m′                    ∎)
           very-modal)
      (λ x →
         ◯-elim
           {P = λ m′ → η⁻¹ m (◯-map (const x) m′) ≡ x}
           (λ _ → Modal→Separated m _ _)
           (λ m′ →
              η⁻¹ m (◯-map (const x) (η m′))  ≡⟨ cong (η⁻¹ m) ◯-map-η ⟩
              η⁻¹ m (η x)                     ≡⟨ η⁻¹-η ⟩∎
              x                               ∎)
           very-modal)

  from : Modal -Null A → Modal A
  from null =
    Is-equivalence-η→Modal $
    _≃_.is-equivalence $
    Eq.↔→≃
      η
      (◯ A            →⟨ flip η⁻¹ ⟩
       (Modal A → A)  ↔⟨ inverse A≃ ⟩□
       A              □)
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ x → cong η (lemma x)))
      lemma
    where
    A≃ : A ≃ (Modal A → A)
    A≃ = Eq.⟨ const , null A ⟩

    lemma : ∀ x → _≃_.from A≃ (λ m → η⁻¹ m (η x)) ≡ x
    lemma x =
      _≃_.from A≃ (λ m → η⁻¹ m (η x))  ≡⟨ (cong (_≃_.from A≃) $
                                           apply-ext ext λ _ →
                                           η⁻¹-η) ⟩
      _≃_.from A≃ (const x)            ≡⟨⟩
      _≃_.from A≃ (_≃_.to A≃ x)        ≡⟨ _≃_.left-inverse-of A≃ _ ⟩∎
      x                                ∎

------------------------------------------------------------------------
-- Some equivalences

-- ◯ (Modal A) is equivalent to the unit type (assuming function
-- extensionality).

◯-Modal≃⊤ : ◯ (Modal A) ↝[ a ∣ a ] ⊤
◯-Modal≃⊤ {A = A} =
  generalise-ext?
    (record { from = λ _ → very-modal })
    (λ ext →
         refl
       , (λ m →
            very-modal  ≡⟨ Left-exact-η-cong→H-level→H-level-◯
                             left-exact-η-cong 1
                             (Modal-propositional ext)
                             _ _ ⟩∎
            m           ∎))

-- ◯ B is equivalent to ◯ (Modal A × B) (assuming function
-- extensionality).

◯≃◯-Modal-× : ◯ B ↝[ a ∣ a ] ◯ (Modal A × B)
◯≃◯-Modal-× {B = B} {A = A} ext =
  ◯ B                ↝⟨ inverse-ext? (drop-⊤-left-× ∘ const ∘ ◯-Modal≃⊤) ext ⟩
  ◯ (Modal A) × ◯ B  ↔⟨ inverse ◯×≃ ⟩□
  ◯ (Modal A × B)    □

-- Two "computation rules" for ◯≃◯-Modal-×.

◯≃◯-Modal-×-η : ◯≃◯-Modal-× {A = A} _ (η x) ≡ ◯-map (_, x) very-modal
◯≃◯-Modal-×-η {x = x} =
  _≃_.from ◯×≃ (very-modal , η x)  ≡⟨ ◯×≃⁻¹-ηʳ ⟩∎
  ◯-map (_, x) very-modal          ∎

◯≃◯-Modal-×⁻¹-η : _⇔_.from (◯≃◯-Modal-× _) (η (m , x)) ≡ η x
◯≃◯-Modal-×⁻¹-η {m = m} {x = x} =
  _≃_.to ◯×≃ (η (m , x)) .proj₂  ≡⟨ cong proj₂ ◯×≃-η ⟩∎
  η x                            ∎

-- A variant of ◯≃◯-Modal-×.

◯≃◯Σ-Modal :
  (P : A → Type a) →
  ◯ (P x) ↝[ a ∣ a ] ◯ (∃ λ (m : Modal A) → P (◯-rec m id (η x)))
◯≃◯Σ-Modal {A = A} {x = x} P ext =
  ◯ (P x)                                       ↝⟨ ◯≃◯-Modal-× ext ⟩
  ◯ (Modal A × P x)                             ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $ cong P $ sym ◯-rec-η) ⟩□
  ◯ (∃ λ (m : Modal A) → P (◯-rec m id (η x)))  □

-- A variant of M.◯Ση≃Σ◯◯ proved using the assumption that the
-- modality is very modal, instead of function extensionality.

◯Ση≃Σ◯◯ : ◯ (Σ A (P ∘ η)) ≃ Σ (◯ A) (◯ ∘ P)
◯Ση≃Σ◯◯ {A = A} {P = P} = Eq.↔→≃
  (M.◯Ση≃Σ◯◯ _)
  (Σ (◯ A) (◯ ∘ P)          →⟨ (λ (x , y) → ◯-map (x ,_) y) ⟩
   ◯ (Σ (◯ A) P)            →⟨ ◯≃◯-Modal-× _ ⟩
   ◯ (Modal A × Σ (◯ A) P)  →⟨ ◯-map (proj₂ ∘ ∃-cong λ m → _≃_.from $ Σ-cong (Modal→≃◯ m) λ _ → Eq.id) ⟩□
   ◯ (Σ A (P ∘ η))          □)
  (λ (x , y) →
     ◯-elim
       {P = λ m →
              ◯-rec m₁ (Σ-map η η)
                (◯-map (proj₂ ∘
                        ∃-cong λ m → _≃_.from $
                        Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                   (_≃_.from ◯×≃ (m , ◯-map (x ,_) y))) ≡
              (x , y)}
       (λ _ → Modal→Separated m₁ _ _)
       (λ m →
          ◯-elim
            {P = λ y →
                   ◯-rec m₁ (Σ-map η η)
                     (◯-map (proj₂ ∘
                             ∃-cong λ m → _≃_.from $
                             Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                        (_≃_.from ◯×≃ (η m , ◯-map (x ,_) y))) ≡
                   (x , y)}
            (λ _ → Modal→Separated m₁ _ _)
            (λ y →
               ◯-rec m₁ (Σ-map η η)
                 (◯-map (proj₂ ∘
                         ∃-cong λ m → _≃_.from $
                         Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                    (_≃_.from ◯×≃ (η m , ◯-map (x ,_) (η y))))     ≡⟨ cong (◯-rec _ _) $ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_)
                                                                      ◯-map-η ⟩
               ◯-rec m₁ (Σ-map η η)
                 (◯-map (proj₂ ∘
                         ∃-cong λ m → _≃_.from $
                         Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                    (_≃_.from ◯×≃ (η m , η (x , y))))              ≡⟨ cong (◯-rec _ _) $ cong (◯-map _)
                                                                      ◯×≃⁻¹-η ⟩
               ◯-rec m₁ (Σ-map η η)
                 (◯-map (proj₂ ∘
                         ∃-cong λ m → _≃_.from $
                         Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                    (η (m , x , y)))                               ≡⟨ cong (◯-rec _ _)
                                                                      ◯-map-η ⟩
               ◯-rec m₁ (Σ-map η η)
                 (η (_≃_.from
                       (Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                       (x , y)))                                   ≡⟨ ◯-rec-η ⟩

               Σ-map η η
                 (_≃_.from (Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                    (x , y))                                       ≡⟨⟩

               ( η (_≃_.from (Modal→≃◯ m) x)
               , η (subst P
                      (sym (_≃_.right-inverse-of (Modal→≃◯ m) x))
                      y)
               )                                                   ≡⟨ elim₁
                                                                        (λ {x′} eq → (x′ , η (subst P (sym eq) y)) ≡ (x , η y))
                                                                        (
                 (x , η (subst P (sym $ refl x) y))                      ≡⟨ cong (x ,_) $ cong η $
                                                                            trans (cong (flip (subst P) _) $ sym-refl) $
                                                                            subst-refl _ _ ⟩∎
                 (x , η y)                                               ∎)
                                                                        _ ⟩∎
               (x , η y)                                           ∎)
            y)
       very-modal)
  (◯-elim
     (λ _ → Separated-◯ _ _)
     (λ (x , y) →
        let f = (λ (x , y) → ◯-map (x ,_) y) in
        ◯-elim
          {P = λ m →
                 ◯-map (proj₂ ∘
                        ∃-cong λ m → _≃_.from $
                        Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                   (_≃_.from ◯×≃
                      (m , f (◯-rec m₁ (Σ-map η η) (η (x , y))))) ≡
                 η (x , y)}
          (λ _ → Separated-◯ _ _)
          (λ m →
             ◯-map (proj₂ ∘
                    ∃-cong λ m → _≃_.from $
                    Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
               (_≃_.from ◯×≃
                  (η m , f (◯-rec m₁ (Σ-map η η) (η (x , y)))))     ≡⟨ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_) $ cong f
                                                                       ◯-rec-η ⟩
             ◯-map (proj₂ ∘
                    ∃-cong λ m → _≃_.from $
                    Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
               (_≃_.from ◯×≃ (η m , ◯-map (η x ,_) (η y)))          ≡⟨ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_)
                                                                       ◯-map-η ⟩
             ◯-map (proj₂ ∘
                    ∃-cong λ m → _≃_.from $
                    Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
               (_≃_.from ◯×≃ (η m , η (η x , y)))                   ≡⟨ cong (◯-map _)
                                                                       ◯×≃⁻¹-η ⟩
             ◯-map (proj₂ ∘
                    ∃-cong λ m → _≃_.from $
                    Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
               (η (m , η x , y))                                    ≡⟨ ◯-map-η ⟩

             η (_≃_.from (Σ-cong (Modal→≃◯ m) λ _ → Eq.id)
                  (η x , y))                                        ≡⟨⟩

             η ( _≃_.from (Modal→≃◯ m) (η x)
               , subst P
                   (sym (_≃_.right-inverse-of (Modal→≃◯ m) (η x)))
                   y
               )                                                    ≡⟨ cong η $ cong (_ ,_) $ cong (flip (subst P) _) $ cong sym $ sym $
                                                                       _≃_.left-right-lemma (Modal→≃◯ m) _ ⟩
             η ( _≃_.from (Modal→≃◯ m) (η x)
               , subst P
                   (sym $ cong η $
                    _≃_.left-inverse-of (Modal→≃◯ m) x)
                   y
               )                                                    ≡⟨ cong η $
                                                                       elim₁
                                                                         (λ {x′} eq → (x′ , subst P (sym $ cong η eq) y) ≡ (x , y))
                                                                         (
               (x , subst P (sym $ cong η $ refl x) y)                    ≡⟨ cong (x ,_) $
                                                                             trans (cong (flip (subst P) _) $
                                                                                    trans (cong sym $ cong-refl _) $
                                                                                    sym-refl) $
                                                                             subst-refl _ _ ⟩∎
               (x , y)                                                    ∎)
                                                                         _ ⟩∎
             η (x , y)                                              ∎)
          very-modal))
  where
  m₁ = _

-- ◯ commutes with Σ in a certain way.

◯Σ≃Σ◯◯ :
  {P : A → Type a} →
  ◯ (Σ A P) ↝[ a ∣ a ] Σ (◯ A) (λ x → ◯ (∃ λ m → P (◯-rec m id x)))
◯Σ≃Σ◯◯ {A = A} {P = P} ext =
  ◯ (Σ A P)                                     ↝⟨ ◯≃◯-Modal-× ext ⟩
  ◯ (Modal A × Σ A P)                           ↔⟨ ◯-cong-↔ ∃-comm ⟩
  ◯ (Σ A (λ x → Modal A × P x))                 ↔⟨ ◯-cong-≃ $ (∃-cong λ _ → ∃-cong λ _ → ≡⇒↝ _ $ cong P $ sym ◯-rec-η) ⟩
  ◯ (Σ A (λ x → ∃ λ m → P (◯-rec m id (η x))))  ↔⟨ ◯Ση≃Σ◯◯ ⟩□
  Σ (◯ A) (λ x → ◯ (∃ λ m → P (◯-rec m id x)))  □

------------------------------------------------------------------------
-- Preservation lemmas

-- One can prove that ◯ A ↝[ k ] ◯ B holds by proving A ↝[ d ∣ e ] B
-- under the assumption that any type C is modal (perhaps assuming
-- function extensionality).

◯-cong-↝-Modal→ :
  ∀ d e →
  Extensionality? k (a ⊔ d) (a ⊔ e) →
  (Modal C → A ↝[ a ⊔ d ∣ a ⊔ e ] B) →
  ◯ A ↝[ k ] ◯ B
◯-cong-↝-Modal→ {C = C} {A = A} {B = B} d e ext hyp =
  generalise-ext?′
    (◯ A              ↝⟨ ◯≃◯-Modal-× _ ⟩
     ◯ (Modal C × A)  ↝⟨ ◯-cong-⇔ (∃-cong λ m → hyp m _) ⟩
     ◯ (Modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Modal-× _ ⟩□
     ◯ B              □)
    (λ ext →
       ◯ A              ↝⟨ ◯≃◯-Modal-× (lower-extensionality d e ext) ⟩
       ◯ (Modal C × A)  ↝⟨ ◯-cong-↔ (∃-cong λ m → hyp m ext) ⟩
       ◯ (Modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Modal-× (lower-extensionality d e ext) ⟩□
       ◯ B              □)
    (λ ext →
       ◯ A              ↝⟨ ◯≃◯-Modal-× (lower-extensionality? equivalenceᴱ d e E.[ ext ]) ⟩
       ◯ (Modal C × A)  ↝⟨ ◯-cong-≃ᴱ (∃-cong λ m → hyp m E.[ ext ]) ⟩
       ◯ (Modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Modal-× (lower-extensionality? equivalenceᴱ d e E.[ ext ]) ⟩□
       ◯ B              □)
    ext

-- A variant of ◯-cong-↝-Modal→.

Modal→↝→↝ :
  ∀ d e →
  Extensionality? k (a ⊔ d) (a ⊔ e) →
  A ↝[ k ] ◯ A →
  ◯ B ↝[ k ] B →
  (Modal C → A ↝[ a ⊔ d ∣ a ⊔ e ] B) →
  A ↝[ k ] B
Modal→↝→↝ {A = A} {B = B} d e ext A↝◯A ◯B↝B A↝B =
  A    ↝⟨ A↝◯A ⟩
  ◯ A  ↝⟨ ◯-cong-↝-Modal→ d e ext A↝B ⟩
  ◯ B  ↝⟨ ◯B↝B ⟩□
  B    □

------------------------------------------------------------------------
-- Some results related to Erased

-- ◯ (Erased A) is logically equivalent to Erased (◯ A).
--
-- See also []-cong.◯-Erased≃Erased-◯ below.

◯-Erased⇔Erased-◯ : ◯ (Erased A) ⇔ Erased (◯ A)
◯-Erased⇔Erased-◯ {A = A} = record
  { to   = λ x → ◯-Erased→Erased-◯ x
  ; from =
      Erased (◯ A)                →⟨ η ⟩
      ◯ (Erased (◯ A))            →⟨ ◯≃◯-Modal-× _ ⟩
      ◯ (Modal A × Erased (◯ A))  →⟨ ◯-map (uncurry λ m → E.map (Modal→Stable m)) ⟩□
      ◯ (Erased A)                □
  }

-- Some results that hold if the []-cong axioms can be instantiated.

module []-cong (ax : []-cong-axiomatisation a) where

  open C.[]-cong ax public

  private
    open module MBC = Modality.Box-cong eq ax M
      hiding (Modal→Stable-Is-equivalenceᴱ; ◯-cong-◯)

  private
    module BC       = E.[]-cong₁ ax
    module EC       = E₂.[]-cong₂-⊔ ax ax ax
    module BC-ECP   = ECP.[]-cong₂ ax ax
    module BC-ECP-⊔ = ECP.[]-cong₂-⊔ ax ax ax

  ----------------------------------------------------------------------
  -- Some equivalences

  -- ◯ (Erased A) is equivalent to Erased (◯ A).

  ◯-Erased≃Erased-◯ : ◯ (Erased A) ≃ Erased (◯ A)
  ◯-Erased≃Erased-◯ {A = A} =
    Eq.↔→≃
      (_⇔_.to   ◯-Erased⇔Erased-◯)
      (_⇔_.from ◯-Erased⇔Erased-◯)
      (λ (E.[ x ]) →
         ◯-Erased→Erased-◯
           (◯-map (uncurry λ m → E.map (Modal→Stable m))
              (◯≃◯-Modal-× _ (η E.[ x ])))                    ≡⟨ cong (λ x → ◯-Erased→Erased-◯ (◯-map _ x))
                                                                 ◯≃◯-Modal-×-η ⟩
         ◯-Erased→Erased-◯
           (◯-map (uncurry λ m → E.map (Modal→Stable m))
              (◯-map (_, E.[ x ]) very-modal))                ≡⟨ cong (λ x → ◯-Erased→Erased-◯ x) $ sym
                                                                 ◯-map-∘ ⟩
         ◯-Erased→Erased-◯
           (◯-map (λ m → E.[ Modal→Stable m x ]) very-modal)  ≡⟨ ◯-elim
                                                                   {P = λ m →
                                                                          ◯-Erased→Erased-◯ (◯-map (λ m → E.[ Modal→Stable m x ]) m) ≡
                                                                          E.[ x ]}
                                                                   (λ _ → Modal→Separated (Modal-Erased Modal-◯) _ _)
                                                                   (λ m →
           ◯-Erased→Erased-◯
             (◯-map (λ m → E.[ Modal→Stable m x ]) (η m))             ≡⟨ cong (λ x → ◯-Erased→Erased-◯ x) ◯-map-η ⟩

           ◯-Erased→Erased-◯ (η E.[ Modal→Stable m x ])               ≡⟨⟩

           E.[ ◯-map E.erased (η E.[ Modal→Stable m x ]) ]            ≡⟨ BC.[]-cong E.[ ◯-map-η ] ⟩

           E.[ η (Modal→Stable m x) ]                                 ≡⟨⟩

           E.[ η (η⁻¹ m x) ]                                          ≡⟨ BC.[]-cong E.[ η-η⁻¹ ] ⟩∎

           E.[ x ]                                                    ∎)
                                                                   very-modal ⟩∎
         E.[ x ]                                              ∎)
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ (E.[ x ]) →
            ◯-map (uncurry λ m → E.map (Modal→Stable m))
              (◯≃◯-Modal-× _ (η (◯-Erased→Erased-◯ (η E.[ x ]))))   ≡⟨⟩

            ◯-map (uncurry λ m → E.map (Modal→Stable m))
              (◯≃◯-Modal-× _ (η E.[ ◯-map E.erased (η E.[ x ]) ]))  ≡⟨ cong (◯-map _) $ cong (◯≃◯-Modal-× _ ∘ η) $
                                                                       BC.[]-cong E.[ ◯-map-η ] ⟩
            ◯-map (uncurry λ m → E.map (Modal→Stable m))
              (◯≃◯-Modal-× _ (η E.[ η x ]))                         ≡⟨ cong (◯-map _) ◯≃◯-Modal-×-η ⟩

            ◯-map (uncurry λ m → E.map (Modal→Stable m))
              (◯-map (_, E.[ η x ]) very-modal)                     ≡⟨ sym ◯-map-∘ ⟩

            ◯-map (λ m → E.[ Modal→Stable m (η x) ]) very-modal     ≡⟨ ◯-elim
                                                                         {P = λ m →
                                                                                ◯-map (λ m → E.[ Modal→Stable m (η x) ]) m ≡
                                                                                η E.[ x ]}
                                                                         (λ _ → Separated-◯ _ _)
                                                                         (λ m →
              ◯-map (λ m → E.[ Modal→Stable m (η x) ]) (η m)                ≡⟨ ◯-map-η ⟩
              η E.[ Modal→Stable m (η x) ]                                  ≡⟨ cong η $ BC.[]-cong E.[ Modal→Stable-η ] ⟩∎
              η E.[ x ]                                                     ∎)
                                                                         very-modal ⟩∎
            η E.[ x ]                                               ∎))

  -- ◯ commutes with Contractibleᴱ (assuming function extensionality).

  ◯-Contractibleᴱ≃Contractibleᴱ-◯ :
    ◯ (Contractibleᴱ A) ↝[ a ∣ a ]ᴱ Contractibleᴱ (◯ A)
  ◯-Contractibleᴱ≃Contractibleᴱ-◯ {A = A} ext =
    ◯ (Contractibleᴱ A)                           ↔⟨⟩
    ◯ (∃ λ (x : A) → Erased (∀ y → x ≡ y))        ↔⟨ inverse ◯Σ◯≃◯Σ ⟩
    ◯ (∃ λ (x : A) → ◯ (Erased (∀ y → x ≡ y)))    ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯-Erased≃Erased-◯) ⟩
    ◯ (∃ λ (x : A) → Erased (◯ (∀ y → x ≡ y)))    ↝⟨ (◯-cong-↝ᴱ ext λ ext → ∃-cong λ _ → EC.Erased-cong (inverse-ext? Π◯≃◯Π ext)) ⟩
    ◯ (∃ λ (x : A) → Erased (∀ y → ◯ (x ≡ y)))    ↝⟨ (◯-cong-↝ᴱ ext λ ext → ∃-cong λ _ → EC.Erased-cong (∀-cong ext λ _ → from-equivalence
                                                      ◯≡≃η≡η)) ⟩
    ◯ (∃ λ (x : A) → Erased (∀ y → η x ≡ η y))    ↔⟨ ◯Ση≃Σ◯◯ ⟩
    (∃ λ (x : ◯ A) → ◯ (Erased (∀ y → x ≡ η y)))  ↔⟨ (∃-cong λ _ → ◯-Erased≃Erased-◯) ⟩
    (∃ λ (x : ◯ A) → Erased (◯ (∀ y → x ≡ η y)))  ↝⟨ (∃-cong λ _ → EC.Erased-cong (◯-cong-↝-Modal→ lzero lzero ext λ m ext →
                                                      Π-cong ext (Modal→≃◯ m) λ _ → F.id)) ⟩
    (∃ λ (x : ◯ A) → Erased (◯ (∀ y → x ≡ y)))    ↝⟨ (∃-cong λ _ → EC.Erased-cong (inverse-ext? Π◯≃◯Π ext)) ⟩
    (∃ λ (x : ◯ A) → Erased (∀ y → ◯ (x ≡ y)))    ↝⟨ (∃-cong λ _ → EC.Erased-cong (∀-cong ext λ _ → from-equivalence $ inverse $
                                                      Modal→≃◯ (Separated-◯ _ _))) ⟩
    (∃ λ (x : ◯ A) → Erased (∀ y → x ≡ y))        ↔⟨⟩
    Contractibleᴱ (◯ A)                           □

  ----------------------------------------------------------------------
  -- Some results related to stability

  -- If A is k-stable, then Erased A is k-stable.

  Stable-Erased : @0 Stable-[ k ] A → Stable-[ k ] (Erased A)
  Stable-Erased {A = A} s =
    ◯ (Erased A)  ↔⟨ ◯-Erased≃Erased-◯ ⟩
    Erased (◯ A)  ↝⟨ EC.Erased-cong s ⟩□
    Erased A      □

  -- If A is modal, then Contractibleᴱ A is k-stable (perhaps assuming
  -- function extensionality).

  Stable-Contractibleᴱ :
    @0 Extensionality? k a a →
    Modal A →
    Stable-[ k ] (Contractibleᴱ A)
  Stable-Contractibleᴱ ext m =
    Stable-Σ m λ _ →
    Stable-Erased (
    Stable-Π ext λ _ →
    Modal→Stable (Modal→Separated m _ _))

  -- If f has type A → B, A is modal, and equality is k-stable for B,
  -- then f ⁻¹ᴱ y is k-stable.

  Stable-⁻¹ᴱ :
    {A B : Type a} {f : A → B} {y : B} →
    Modal A →
    @0 For-iterated-equality 1 Stable-[ k ] B →
    Stable-[ k ] (f ⁻¹ᴱ y)
  Stable-⁻¹ᴱ m s =
    Stable-Σ m λ _ →
    Stable-Erased (s _ _)

  -- If f has type A → B, where A is modal and B is separated, then
  -- ECP.Is-equivalenceᴱ f is k-stable (perhaps assuming function
  -- extensionality).

  Modal→Stable-Is-equivalenceᴱ-CP :
    {@0 f : A → B} →
    Extensionality? k a a →
    Modal A → @0 Separated B →
    Stable-[ k ] (ECP.Is-equivalenceᴱ f)
  Modal→Stable-Is-equivalenceᴱ-CP {f = f} ext m s =
    Stable-Π ext λ y →
    let m′ : Modal (f ⁻¹ᴱ y)
        m′ = Modal-⁻¹ᴱ m s in
    Stable-Σ m′ λ _ →
    Stable-Erased (
    Stable-Π ext λ _ →
    Modal→Stable (Modal→Separated m′ _ _))

  -- If f has type A → B, where A is modal and B is separated, then
  -- Is-equivalenceᴱ f is k-stable (perhaps assuming function
  -- extensionality).

  Modal→Stable-Is-equivalenceᴱ :
    {@0 f : A → B} →
    Extensionality? k a a →
    Modal A → @0 Separated B →
    Stable-[ k ] (Is-equivalenceᴱ f)
  Modal→Stable-Is-equivalenceᴱ {k = k} {f = f} ext m s =
    generalise-ext?′
      (Stable→Stable-⇔ $ MBC.Modal→Stable-Is-equivalenceᴱ m s)
      (λ ext → Modal→Stable $ Modal-Is-equivalenceᴱ ext m s)
      Modal→Stable-≃ᴱ-Is-equivalenceᴱ
      ext
    where
    Modal→Stable-≃ᴱ-Is-equivalenceᴱ :
      @0 Extensionality a a →
      Stable-[ equivalenceᴱ ] (Is-equivalenceᴱ f)
    Modal→Stable-≃ᴱ-Is-equivalenceᴱ ext =
                                                               $⟨ s′ ⟩
      Stable-[ equivalenceᴱ ] (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  →⟨ Stable-respects-↝-sym $ inverse $
                                                                  EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext ⟩□
      Stable-[ equivalenceᴱ ] (Is-equivalenceᴱ f)              □
      where
      ext′ = E.[ ext ]

      s′ =
        Stable-Π ext′ λ y →
        let m′ : Modal (f ⁻¹ᴱ y)
            m′ = Modal-⁻¹ᴱ m s in
        Stable-Σ m′ λ _ →
        Stable-Erased (
        Stable-Π ext′ λ _ →
        Modal→Stable (Modal→Separated m′ _ _))

  ----------------------------------------------------------------------
  -- More equivalences

  -- A lemma relating ◯, ◯-map and _⁻¹ᴱ_.

  ◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ :
    {A : Type a} {@0 B : Type a} {@0 f : A → B} {y : ◯ B} →
    ◯ (η ∘ f ⁻¹ᴱ y) ≃ ◯-map f ⁻¹ᴱ y
  ◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ {f = f} {y = y} =
    ◯ (∃ λ x → Erased (η (f x) ≡ y))        ↝⟨ ◯-cong-≃ (∃-cong λ _ → EC.Erased-cong (≡⇒↝ _ $ cong (_≡ _) $ sym ◯-map-η)) ⟩
    ◯ (∃ λ x → Erased (◯-map f (η x) ≡ y))  ↝⟨ ◯Ση≃Σ◯◯ ⟩
    (∃ λ x → ◯ (Erased (◯-map f x ≡ y)))    ↝⟨ (∃-cong λ _ → Modal→Stable (Modal-Erased (Separated-◯ _ _))) ⟩
    (∃ λ x → Erased (◯-map f x ≡ y))        □

  -- ◯ (ECP.Is-equivalenceᴱ f) is equivalent to
  -- ECP.Is-equivalenceᴱ (◯-map f) (assuming function extensionality).

  ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP :
    ◯ (ECP.Is-equivalenceᴱ f) ↝[ a ∣ a ] ECP.Is-equivalenceᴱ (◯-map f)
  ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP {f = f} ext =
    ◯ (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))                ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    (∀ y → ◯ (Contractibleᴱ (f ⁻¹ᴱ y)))              ↝⟨ Modal→↝→↝ lzero lzero ext
                                                          (
      (∀ x → ◯ (Contractibleᴱ (f ⁻¹ᴱ x)))                  ↝⟨ inverse-ext?
                                                                (λ ext →
                                                                   Stable-Π ext λ _ →
                                                                   Modal→Stable Modal-◯)
                                                                ext ⟩
      ◯ (∀ x → ◯ (Contractibleᴱ (f ⁻¹ᴱ x)))                □)
                                                          (
      ◯ (∀ x → Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ x)))            ↝⟨ (Stable-Π ext λ _ →
                                                               Stable-Contractibleᴱ ext Modal-◯) ⟩□
      (∀ x → Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ x)))              □)
                                                          (λ m ext →
                                                             Π-cong-contra ext (inverse $ Modal→≃◯ m) λ x →
      ◯ (Contractibleᴱ (f ⁻¹ᴱ Modal→Stable m x))               ↝⟨ ◯-Contractibleᴱ≃Contractibleᴱ-◯ ext ⟩
      Contractibleᴱ (◯ (f ⁻¹ᴱ Modal→Stable m x))               ↝⟨ BC-ECP.Contractibleᴱ-cong ext $ ◯-cong-≃ $ inverse $
                                                                  BC-ECP-⊔.to-∘-⁻¹ᴱ-≃-⁻¹ᴱ-from (Modal→≃◯ m) ⟩□
      Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ x))                          □) ⟩

    (∀ y → Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ y)))          ↝⟨ (∀-cong ext λ _ → BC-ECP.Contractibleᴱ-cong ext ◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ) ⟩□
    (∀ y → Contractibleᴱ (◯-map f ⁻¹ᴱ y))            □

  private

    -- ◯ (Is-equivalenceᴱ f) is logically equivalent to
    -- Is-equivalenceᴱ (◯-map f).

    ◯-Is-equivalenceᴱ⇔Is-equivalenceᴱ :
      ◯ (Is-equivalenceᴱ f) ⇔ Is-equivalenceᴱ (◯-map f)
    ◯-Is-equivalenceᴱ⇔Is-equivalenceᴱ {f = f} =
      ◯ (Is-equivalenceᴱ f)                  ↝⟨ ◯-cong-⇔ EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP ⟩
      ◯ (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))      ↝⟨ ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP _ ⟩
      (∀ y → Contractibleᴱ (◯-map f ⁻¹ᴱ y))  ↝⟨ inverse $ EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP ⟩□
      Is-equivalenceᴱ (◯-map f)              □

    -- ◯ (Is-equivalenceᴱ f) is equivalent (with erased proofs) to
    -- Is-equivalenceᴱ (◯-map f) (assuming function extensionality).

    ◯-Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ :
      @0 Extensionality a a →
      ◯ (Is-equivalenceᴱ f) ≃ᴱ Is-equivalenceᴱ (◯-map f)
    ◯-Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ {f = f} ext =
      ◯ (Is-equivalenceᴱ f)                  ↝⟨ ◯-cong-≃ᴱ (EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext) ⟩
      ◯ (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))      ↝⟨ ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP E.[ ext ] ⟩
      (∀ y → Contractibleᴱ (◯-map f ⁻¹ᴱ y))  ↝⟨ inverse $ EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext ⟩□
      Is-equivalenceᴱ (◯-map f)              □

    -- ◯ (Is-equivalenceᴱ f) is equivalent to
    -- Is-equivalenceᴱ (◯-map f) (assuming function extensionality).

    ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ′ :
      {f : A → B} →
      Extensionality a a →
      ◯ (Is-equivalenceᴱ f) ≃ Is-equivalenceᴱ (◯-map f)
    ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ′ {A = A} {B = B} {f = f} ext =
      ◯ (Is-equivalenceᴱ f)                                                 ↔⟨⟩

      ◯ (∃ λ (f⁻¹ : B → A) → Erased (HA.Proofs f f⁻¹))                      ↝⟨ inverse ◯Σ◯≃◯Σ ⟩

      ◯ (∃ λ (f⁻¹ : B → A) → ◯ (Erased (HA.Proofs f f⁻¹)))                  ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯-Erased≃Erased-◯) ⟩

      ◯ (∃ λ (f⁻¹ : B → A) → Erased (◯ (HA.Proofs f f⁻¹)))                  ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → EC.Erased-cong (
                                                                                ◯-Half-adjoint-proofs≃Half-adjoint-proofs-◯-map-◯-map ext)) ⟩

      ◯ (∃ λ (f⁻¹ : B → A) → Erased (HA.Proofs (◯-map f) (◯-map f⁻¹)))      ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $
                                                                                cong (λ g → Erased (HA.Proofs (◯-map f) g)) $ sym $
                                                                                apply-ext ext λ _ → ◯-map-◯-ηˡ) ⟩
      ◯ (∃ λ (f⁻¹ : B → A) →
           Erased (HA.Proofs (◯-map f) (◯-map-◯ (η f⁻¹))))                  ↝⟨ ◯Ση≃Σ◯◯ ⟩

      (∃ λ (f⁻¹ : ◯ (B → A)) →
         ◯ (Erased (HA.Proofs (◯-map f) (◯-map-◯ f⁻¹))))                    ↝⟨ (∃-cong λ _ →
                                                                                Modal→Stable $
                                                                                Modal-Erased (
                                                                                Modal-Σ (Modal-Π ext λ _ → Separated-◯ _ _) λ _ →
                                                                                Modal-Σ (Modal-Π ext λ _ → Separated-◯ _ _) λ _ →
                                                                                Modal-Π ext λ _ →
                                                                                Modal→Separated (Separated-◯ _ _) _ _)) ⟩

      (∃ λ (f⁻¹ : ◯ (B → A)) → Erased (HA.Proofs (◯-map f) (◯-map-◯ f⁻¹)))  ↝⟨ Σ◯→≃Σ◯→◯ ext ⟩

      (∃ λ (f⁻¹ : ◯ B → ◯ A) → Erased (HA.Proofs (◯-map f) f⁻¹))            ↔⟨⟩

      Is-equivalenceᴱ (◯-map f)                                             □

  -- ◯ (Is-equivalenceᴱ f) is equivalent to Is-equivalenceᴱ (◯-map f)
  -- (assuming function extensionality).

  ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ :
    ◯ (Is-equivalenceᴱ f) ↝[ a ∣ a ] Is-equivalenceᴱ (◯-map f)
  ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ =
    generalise-ext?′
      ◯-Is-equivalenceᴱ⇔Is-equivalenceᴱ
      (from-equivalence ∘ ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ′)
      ◯-Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ

  -- ◯ commutes with ECP._≃ᴱ_ (assuming function extensionality).

  ◯≃ᴱ-CP-≃◯≃ᴱ-CP-◯ : ◯ (A ECP.≃ᴱ B) ↝[ a ∣ a ] (◯ A ECP.≃ᴱ ◯ B)
  ◯≃ᴱ-CP-≃◯≃ᴱ-CP-◯ ext =
    ◯↝↝◯↝◯
      {P = λ f → ECP.Is-equivalenceᴱ f}
      F.id
      ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP
      (λ ext f≡g → ECP.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax ext f≡g)
      (Modal→Stable-Is-equivalenceᴱ-CP ext Modal-◯ Separated-◯)
      (Σ◯→↝Σ◯→◯-Is-equivalenceᴱ-CP ext)
      ext

  -- ◯ commutes with _≃ᴱ_ (assuming function extensionality).

  ◯≃ᴱ≃◯≃ᴱ◯ : ◯ (A ≃ᴱ B) ↝[ a ∣ a ] (◯ A ≃ᴱ ◯ B)
  ◯≃ᴱ≃◯≃ᴱ◯ ext =
    ◯↝↝◯↝◯
      (from-equivalence EEq.≃ᴱ-as-Σ)
      ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ
      (λ ext f≡g → EEq.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax ext f≡g)
      (Modal→Stable-Is-equivalenceᴱ ext Modal-◯ Separated-◯)
      (Σ◯→↝Σ◯→◯-Is-equivalenceᴱ ext)
      ext

  -- ◯ commutes with _↝[ k ]_ (assuming function extensionality).

  ◯↝≃◯↝◯ : ◯ (A ↝[ k ] B) ↝[ a ∣ a ] (◯ A ↝[ k ] ◯ B)
  ◯↝≃◯↝◯ {k = implication}         = ◯→≃◯→◯
  ◯↝≃◯↝◯ {k = logical-equivalence} = ◯⇔≃◯⇔◯
  ◯↝≃◯↝◯ {k = injection}           = ◯↣≃◯↣◯
  ◯↝≃◯↝◯ {k = embedding}           = ◯-Embedding≃Embedding-◯-◯
  ◯↝≃◯↝◯ {k = surjection}          = ◯↠≃◯↠◯
  ◯↝≃◯↝◯ {k = bijection}           = ◯↔≃◯↔◯
  ◯↝≃◯↝◯ {k = equivalence}         = ◯≃≃◯≃◯
  ◯↝≃◯↝◯ {k = equivalenceᴱ}        = ◯≃ᴱ≃◯≃ᴱ◯

  -- A variant of MBC.◯-cong-◯.

  ◯-cong-◯ : ◯ (A ↝[ k ] B) → ◯ A ↝[ k ] ◯ B
  ◯-cong-◯ = ◯↝≃◯↝◯ _
