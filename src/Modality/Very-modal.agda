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
    hiding (◯Ση≃Σ◯◯;
            Stable-Π; Stable-implicit-Π;
            Stable-Erased; Stable-Contractibleᴱ; Stable-⁻¹ᴱ;
            Is-modal→Stable-Is-equivalence;
            ◯Π◯≃◯Π; ◯≡≃η≡η)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq as Emb using (Embedding; Is-embedding)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (Contractibleᴱ; _⁻¹ᴱ_)
open import Equivalence.Path-split eq as PS
  using (Is-∞-extendable-along-[_]; _-Null_)
open import Erased.Level-1 eq as E
  using (Erased; []-cong-axiomatisation)
import Erased.Level-2 eq as E₂
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_; Injective)
import Modality.Box-cong
open import Preimage eq using (_⁻¹_)
open import Surjection eq using (_↠_; Split-surjective)

private
  variable
    ℓ             : Level
    A B C         : Type ℓ
    f g h k p x y : A
    P             : A → Type p

------------------------------------------------------------------------
-- Should "Very-modal" be stated differently?

-- ◯ (∀ x → Is-modal (P x)) is inhabited.
--
-- One might wonder if something like ◯ ({A : Type a} → Is-modal A)
-- would be more general than Very-modal M. However, the former
-- statement is not type-correct. The statement
--
--   {A : Type a} {P : A → Type a} → ◯ (∀ x → Is-modal (P x))
--
-- is type-correct, but follows from Very-modal M.

◯-Π-Is-modal :
  {A : Type a} {P : A → Type a} → ◯ (∀ x → Is-modal (P x))
◯-Π-Is-modal {A = A} {P = P} =
                                         $⟨ (λ {_} → very-modal) ⟩
  Very-modal M                           →⟨ (λ m → m , m) ⟩
  ◯ (Is-modal A) × ◯ (Is-modal (Σ A P))  →⟨ _≃_.from ◯×≃ ⟩
  ◯ (Is-modal A × Is-modal (Σ A P))      →⟨ ◯-map (λ (mA , mΣAP) → Is-modal-Σ≃Π-Is-modal mA _ mΣAP) ⟩□
  ◯ (∀ x → Is-modal (P x))               □

------------------------------------------------------------------------
-- The modality is left exact and, assuming function extensionality,
-- topological

-- Very modal modalities are left exact.
--
-- See also left-exact below.

left-exact-η-cong : Left-exact-η-cong
left-exact-η-cong =
  ◯-Is-modal→Is-equivalence-η-cong very-modal _ _

-- There is an equivalence between ◯ (x ≡ y) and η x ≡ η y.

◯≡≃η≡η : ◯ (x ≡ y) ≃ (η x ≡ η y)
◯≡≃η≡η = M.◯≡≃η≡η left-exact-η-cong

-- ◯ ((x : A) → ◯ (P x)) is equivalent to ◯ (((x : A) → P x))
-- (assuming function extensionality).

◯Π◯≃◯Π :
  {A : Type a} {P : A → Type a} →
  ◯ ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ (((x : A) → P x))
◯Π◯≃◯Π = M.◯Π◯≃◯Π ◯-Π-Is-modal

-- Is-modal A is equivalent to Is-modal -Null A (assuming function
-- extensionality).

Is-modal≃Is-modal-Null :
  Extensionality a a →
  Is-modal A ↝[ lsuc a ∣ a ] Is-modal -Null A
Is-modal≃Is-modal-Null {A = A} ext =
  generalise-ext?-prop
    (record { to = to; from = from })
    (λ _ → Is-modal-propositional ext)
    (λ ext′ →
       Π-closure ext′ 1 λ _ →
       Eq.propositional ext _)
  where
  to : Is-modal A → Is-modal -Null A
  to m _ =
    _≃_.is-equivalence $
    Eq.↔→≃
      const
      (λ f → η⁻¹ m (◯-map f very-modal))
      (λ f → apply-ext ext λ m′ →
         ◯-elim
           {P = λ m″ → η⁻¹ m (◯-map f m″) ≡ f m′}
           (λ _ → Is-modal→Separated m _ _)
           (λ m″ →
              η⁻¹ m (◯-map f (η m″))  ≡⟨ cong (η⁻¹ m) ◯-map-η ⟩
              η⁻¹ m (η (f m″))        ≡⟨ η⁻¹-η ⟩
              f m″                    ≡⟨ cong f $ Is-modal-propositional ext _ _ ⟩∎
              f m′                    ∎)
           very-modal)
      (λ x →
         ◯-elim
           {P = λ m′ → η⁻¹ m (◯-map (const x) m′) ≡ x}
           (λ _ → Is-modal→Separated m _ _)
           (λ m′ →
              η⁻¹ m (◯-map (const x) (η m′))  ≡⟨ cong (η⁻¹ m) ◯-map-η ⟩
              η⁻¹ m (η x)                     ≡⟨ η⁻¹-η ⟩∎
              x                               ∎)
           very-modal)

  from : Is-modal -Null A → Is-modal A
  from null =
    Is-equivalence-η→Is-modal $
    _≃_.is-equivalence $
    Eq.↔→≃
      η
      (◯ A               →⟨ flip η⁻¹ ⟩
       (Is-modal A → A)  ↔⟨ inverse A≃ ⟩□
       A                 □)
      (◯-elim
         (λ _ → Separated-◯ _ _)
         (λ x → cong η (lemma x)))
      lemma
    where
    A≃ : A ≃ (Is-modal A → A)
    A≃ = Eq.⟨ const , null A ⟩

    lemma : ∀ x → _≃_.from A≃ (λ m → η⁻¹ m (η x)) ≡ x
    lemma x =
      _≃_.from A≃ (λ m → η⁻¹ m (η x))  ≡⟨ (cong (_≃_.from A≃) $
                                           apply-ext ext λ _ →
                                           η⁻¹-η) ⟩
      _≃_.from A≃ (const x)            ≡⟨⟩
      _≃_.from A≃ (_≃_.to A≃ x)        ≡⟨ _≃_.left-inverse-of A≃ _ ⟩∎
      x                                ∎

-- The modality is topological for certain universe levels (assuming
-- function extensionality).
--
-- TODO: Are there any topological modalities which are not very
-- modal?

topological :
  Extensionality (lsuc a ⊔ ℓ) (lsuc a ⊔ ℓ) →
  Topological (lsuc a ⊔ ℓ) M
topological {ℓ = ℓ} ext =
    ( ↑ ℓ (Type a)
    , ↑ _ ∘ Is-modal ∘ lower
    , (λ A →
         Is-modal A                                     ↝⟨ Is-modal≃Is-modal-Null ext′ _ ⟩
         Is-modal -Null A                               ↝⟨ (inverse $
                                                            Π-cong _ Bijection.↑↔ λ B →
                                                            Is-equivalence≃Is-equivalence-∘ˡ
                                                              (_≃_.is-equivalence $
                                                               Eq.↔→≃ (_∘ lift) (_∘ lower) refl refl)
                                                              _) ⟩
         (↑ _ ∘ Is-modal ∘ lower) -Null A               ↔⟨ inverse $ PS.Π-Is-∞-extendable-along≃Null ext ⟩□
         (∀ _ → Is-∞-extendable-along-[ _ ] (λ _ → A))  □)
    )
  , (λ _ → ↑-closure 1 $ Is-modal-propositional ext′)
  where
  ext′ = lower-extensionality _ _ ext

------------------------------------------------------------------------
-- Some equivalences

-- ◯ (Is-modal A) is equivalent to the unit type (assuming function
-- extensionality).

◯-Is-modal≃⊤ : ◯ (Is-modal A) ↝[ a ∣ a ] ⊤
◯-Is-modal≃⊤ {A = A} =
  generalise-ext?
    (record { from = λ _ → very-modal })
    (λ ext →
         refl
       , (λ m →
            very-modal  ≡⟨ Left-exact-η-cong→H-level→H-level-◯
                             ext left-exact-η-cong 1
                             (Is-modal-propositional ext)
                             _ _ ⟩∎
            m           ∎))

-- ◯ B is equivalent to ◯ (Is-modal A × B) (assuming function
-- extensionality).

◯≃◯-Is-modal-× : ◯ B ↝[ a ∣ a ] ◯ (Is-modal A × B)
◯≃◯-Is-modal-× {B = B} {A = A} ext =
  ◯ B                   ↝⟨ inverse-ext? (drop-⊤-left-× ∘ const ∘ ◯-Is-modal≃⊤) ext ⟩
  ◯ (Is-modal A) × ◯ B  ↔⟨ inverse ◯×≃ ⟩□
  ◯ (Is-modal A × B)    □

-- A variant of ◯≃◯-Is-modal-×.

◯≃◯Σ-Is-modal :
  (P : A → Type a) →
  ◯ (P x) ↝[ a ∣ a ] ◯ (∃ λ (m : Is-modal A) → P (◯-rec m id (η x)))
◯≃◯Σ-Is-modal {A = A} {x = x} P ext =
  ◯ (P x)                                          ↝⟨ ◯≃◯-Is-modal-× ext ⟩
  ◯ (Is-modal A × P x)                             ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $ cong P $ sym ◯-rec-η) ⟩□
  ◯ (∃ λ (m : Is-modal A) → P (◯-rec m id (η x)))  □

-- A kind of choice principle holds.

Π◯≃◯Π :
  {A : Type a} {P : A → Type a} →
  ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
Π◯≃◯Π {A = A} {P = P} ext =
  ((x : A) → ◯ (P x))    ↝⟨ lemma ext ⟩
  ◯ ((x : A) → ◯ (P x))  ↝⟨ ◯Π◯≃◯Π ext ⟩□
  ◯ ((x : A) → P x)      □
  where
  from =
    ◯ ((x : A) → ◯ (P x))    →⟨ ◯Π→Π◯ ⟩
    ((x : A) → ◯ (◯ (P x)))  →⟨ _≃_.from ◯≃◯◯ ∘_ ⟩□
    ((x : A) → ◯ (P x))      □

  lemma =
    generalise-ext?
      (record { to = η; from = from })
      (λ ext →
         let from-η : ∀ f → from (η f) ≡ f
             from-η = λ f → apply-ext ext λ x →
               from (η f) x                              ≡⟨⟩
               ◯-rec Is-modal-◯ id (◯-map (_$ x) (η f))  ≡⟨ cong (◯-rec _ _) ◯-map-η ⟩
               ◯-rec Is-modal-◯ id (η (f x))             ≡⟨ ◯-rec-η ⟩∎
               f x                                       ∎
         in
           (◯-elim
              (λ _ → Separated-◯ _ _)
              (λ f →
                 η (from (η f))  ≡⟨ cong η $ from-η f ⟩∎
                 η f             ∎))
         , from-η)

-- A variant of Modality-lemma.◯Ση≃Σ◯◯ proved using the assumption
-- that the modality is very modal, instead of function
-- extensionality.

◯Ση≃Σ◯◯ : ◯ (Σ A (P ∘ η)) ≃ Σ (◯ A) (◯ ∘ P)
◯Ση≃Σ◯◯ {A = A} {P = P} = Eq.↔→≃
  ◯Ση→Σ◯◯
  (Σ (◯ A) (◯ ∘ P)             →⟨ (λ (x , y) → ◯-map (x ,_) y) ⟩
   ◯ (Σ (◯ A) P)               →⟨ ◯≃◯-Is-modal-× _ ⟩
   ◯ (Is-modal A × Σ (◯ A) P)  →⟨ ◯-map (proj₂ ∘ ∃-cong λ m → _≃_.from $ Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id) ⟩□
   ◯ (Σ A (P ∘ η))             □)
  (λ (x , y) →
     ◯-elim
       {P = λ m →
              ◯-rec m₁ (Σ-map η η)
                (◯-map (proj₂ ∘
                        ∃-cong λ m → _≃_.from $
                        Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                   (_≃_.from ◯×≃ (m , ◯-map (x ,_) y))) ≡
              (x , y)}
       (λ _ → Is-modal→Separated m₁ _ _)
       (λ m →
          ◯-elim
            {P = λ y →
                   ◯-rec m₁ (Σ-map η η)
                     (◯-map (proj₂ ∘
                             ∃-cong λ m → _≃_.from $
                             Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                        (_≃_.from ◯×≃ (η m , ◯-map (x ,_) y))) ≡
                   (x , y)}
            (λ _ → Is-modal→Separated m₁ _ _)
            (λ y →
               ◯-rec m₁ (Σ-map η η)
                 (◯-map (proj₂ ∘
                         ∃-cong λ m → _≃_.from $
                         Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                    (_≃_.from ◯×≃ (η m , ◯-map (x ,_) (η y))))        ≡⟨ cong (◯-rec _ _) $ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_)
                                                                         ◯-map-η ⟩
               ◯-rec m₁ (Σ-map η η)
                 (◯-map (proj₂ ∘
                         ∃-cong λ m → _≃_.from $
                         Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                    (_≃_.from ◯×≃ (η m , η (x , y))))                 ≡⟨ cong (◯-rec _ _) $ cong (◯-map _)
                                                                         ◯×≃⁻¹-η ⟩
               ◯-rec m₁ (Σ-map η η)
                 (◯-map (proj₂ ∘
                         ∃-cong λ m → _≃_.from $
                         Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                    (η (m , x , y)))                                  ≡⟨ cong (◯-rec _ _)
                                                                         ◯-map-η ⟩
               ◯-rec m₁ (Σ-map η η)
                 (η (_≃_.from
                       (Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                       (x , y)))                                      ≡⟨ ◯-rec-η ⟩

               Σ-map η η
                 (_≃_.from (Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                    (x , y))                                          ≡⟨⟩

               ( η (_≃_.from (Is-modal→≃◯ m) x)
               , η (subst P
                      (sym (_≃_.right-inverse-of (Is-modal→≃◯ m) x))
                      y)
               )                                                      ≡⟨ elim₁
                                                                           (λ {x′} eq → (x′ , η (subst P (sym eq) y)) ≡ (x , η y))
                                                                           (
                 (x , η (subst P (sym $ refl x) y))                         ≡⟨ cong (x ,_) $ cong η $
                                                                               trans (cong (flip (subst P) _) $ sym-refl) $
                                                                               subst-refl _ _ ⟩∎
                 (x , η y)                                                  ∎)
                                                                           _ ⟩∎
               (x , η y)                                              ∎)
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
                        Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                   (_≃_.from ◯×≃
                      (m , f (◯-rec m₁ (Σ-map η η) (η (x , y))))) ≡
                 η (x , y)}
          (λ _ → Separated-◯ _ _)
          (λ m →
             ◯-map (proj₂ ∘
                    ∃-cong λ m → _≃_.from $
                    Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
               (_≃_.from ◯×≃
                  (η m , f (◯-rec m₁ (Σ-map η η) (η (x , y)))))        ≡⟨ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_) $ cong f
                                                                          ◯-rec-η ⟩
             ◯-map (proj₂ ∘
                    ∃-cong λ m → _≃_.from $
                    Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
               (_≃_.from ◯×≃ (η m , ◯-map (η x ,_) (η y)))             ≡⟨ cong (◯-map _) $ cong (_≃_.from ◯×≃) $ cong (η m ,_)
                                                                          ◯-map-η ⟩
             ◯-map (proj₂ ∘
                    ∃-cong λ m → _≃_.from $
                    Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
               (_≃_.from ◯×≃ (η m , η (η x , y)))                      ≡⟨ cong (◯-map _)
                                                                          ◯×≃⁻¹-η ⟩
             ◯-map (proj₂ ∘
                    ∃-cong λ m → _≃_.from $
                    Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
               (η (m , η x , y))                                       ≡⟨ ◯-map-η ⟩

             η (_≃_.from (Σ-cong (Is-modal→≃◯ m) λ _ → Eq.id)
                  (η x , y))                                           ≡⟨⟩

             η ( _≃_.from (Is-modal→≃◯ m) (η x)
               , subst P
                   (sym (_≃_.right-inverse-of (Is-modal→≃◯ m) (η x)))
                   y
               )                                                       ≡⟨ cong η $ cong (_ ,_) $ cong (flip (subst P) _) $ cong sym $ sym $
                                                                          _≃_.left-right-lemma (Is-modal→≃◯ m) _ ⟩
             η ( _≃_.from (Is-modal→≃◯ m) (η x)
               , subst P
                   (sym $ cong η $
                    _≃_.left-inverse-of (Is-modal→≃◯ m) x)
                   y
               )                                                       ≡⟨ cong η $
                                                                          elim₁
                                                                            (λ {x′} eq → (x′ , subst P (sym $ cong η eq) y) ≡ (x , y))
                                                                            (
               (x , subst P (sym $ cong η $ refl x) y)                       ≡⟨ cong (x ,_) $
                                                                                trans (cong (flip (subst P) _) $
                                                                                       trans (cong sym $ cong-refl _) $
                                                                                       sym-refl) $
                                                                                subst-refl _ _ ⟩∎
               (x , y)                                                       ∎)
                                                                            _ ⟩∎
             η (x , y)                                                 ∎)
          very-modal))
  where
  m₁ = Is-modal-Σ Is-modal-◯ λ _ → Is-modal-◯

-- ◯ commutes with Σ in a certain way.

◯Σ≃Σ◯◯ :
  {P : A → Type a} →
  ◯ (Σ A P) ↝[ a ∣ a ] Σ (◯ A) (λ x → ◯ (∃ λ m → P (◯-rec m id x)))
◯Σ≃Σ◯◯ {A = A} {P = P} ext =
  ◯ (Σ A P)                                     ↝⟨ ◯≃◯-Is-modal-× ext ⟩
  ◯ (Is-modal A × Σ A P)                        ↔⟨ ◯-cong-↔ ∃-comm ⟩
  ◯ (Σ A (λ x → Is-modal A × P x))              ↔⟨ ◯-cong-≃ $ (∃-cong λ _ → ∃-cong λ _ → ≡⇒↝ _ $ cong P $ sym ◯-rec-η) ⟩
  ◯ (Σ A (λ x → ∃ λ m → P (◯-rec m id (η x))))  ↔⟨ ◯Ση≃Σ◯◯ ⟩□
  Σ (◯ A) (λ x → ◯ (∃ λ m → P (◯-rec m id x)))  □

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

-- If f has type A → B, where A and B are modal, then
-- Is-equivalence f is k-stable (perhaps assuming function
-- extensionality).

Is-modal→Stable-Is-equivalence :
  {f : A → B} →
  Extensionality? k a a →
  Is-modal A → Is-modal B →
  Stable-[ k ] (Is-equivalence f)
Is-modal→Stable-Is-equivalence {k = k} {f = f} ext mA mB =
                                              $⟨ s ⟩
  Stable-[ k ] (∀ y → Contractible (f ⁻¹ y))  →⟨ Stable-respects-↝ ext $ inverse-ext?
                                                 Is-equivalence≃Is-equivalence-CP ⟩□
  Stable-[ k ] (Is-equivalence f)             □
  where
  s =
    Stable-Π ext λ y →
    let m : Is-modal (f ⁻¹ y)
        m = Is-modal-Σ mA (λ _ → Is-modal→Separated mB _ _) in
    Stable-Σ m λ _ →
    Stable-Π ext λ _ →
    Is-modal→Stable (Is-modal→Separated m _ _)

-- If A is modal, then H-level′ n A is k-stable (perhaps assuming
-- function extensionality).

Stable-H-level′ :
  Extensionality? k a a →
  ∀ n →
  Is-modal A →
  Stable-[ k ] (H-level′ n A)
Stable-H-level′ {k = k} {A = A} ext zero =
  Is-modal A                     →⟨ (λ m →
                                       Stable-Σ m λ _ →
                                       Stable-Π ext λ _ →
                                       Is-modal→Stable $ Is-modal→Separated m _ _) ⟩□
  Stable-[ k ] (Contractible A)  □
Stable-H-level′ {k = k} {A = A} ext (suc n) =
  Is-modal A                                     →⟨ (λ m →
                                                       Stable-Π ext λ _ →
                                                       Stable-Π ext λ _ →
                                                       Stable-H-level′ ext n $
                                                       Is-modal→Separated m _ _) ⟩□
  Stable-[ k ] ((x y : A) → H-level′ n (x ≡ y))  □

-- If A is modal, then H-level n A is k-stable (perhaps assuming
-- function extensionality).

Stable-H-level :
  Extensionality? k a a →
  ∀ n →
  Is-modal A →
  Stable-[ k ] (H-level n A)
Stable-H-level {A = A} ext n m =
  ◯ (H-level n A)   ↝⟨ ◯-cong-↝ ext H-level↔H-level′ ⟩
  ◯ (H-level′ n A)  ↝⟨ Stable-H-level′ ext n m ⟩
  H-level′ n A      ↝⟨ inverse-ext? H-level↔H-level′ ext ⟩□
  H-level n A       □

------------------------------------------------------------------------
-- Preservation lemmas

-- One can prove that ◯ A ↝[ k ] ◯ B holds by proving A ↝[ d ∣ e ] B
-- under the assumption that any type C is modal (perhaps assuming
-- function extensionality).

◯-cong-↝-Is-modal→ :
  ∀ d e →
  Extensionality? k (a ⊔ d) (a ⊔ e) →
  (Is-modal C → A ↝[ a ⊔ d ∣ a ⊔ e ] B) →
  ◯ A ↝[ k ] ◯ B
◯-cong-↝-Is-modal→ {C = C} {A = A} {B = B} d e ext hyp =
  generalise-ext?′
    (◯ A                 ↝⟨ ◯≃◯-Is-modal-× _ ⟩
     ◯ (Is-modal C × A)  ↝⟨ ◯-cong-⇔ (∃-cong λ m → hyp m _) ⟩
     ◯ (Is-modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Is-modal-× _ ⟩□
     ◯ B                 □)
    (λ ext →
       ◯ A                 ↝⟨ ◯≃◯-Is-modal-× (lower-extensionality d e ext) ⟩
       ◯ (Is-modal C × A)  ↝⟨ ◯-cong-↔ (∃-cong λ m → hyp m ext) ⟩
       ◯ (Is-modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Is-modal-× (lower-extensionality d e ext) ⟩□
       ◯ B                 □)
    (λ ext →
       ◯ A                 ↝⟨ ◯≃◯-Is-modal-× (lower-extensionality? equivalenceᴱ d e E.[ ext ]) ⟩
       ◯ (Is-modal C × A)  ↝⟨ ◯-cong-≃ᴱ (∃-cong λ m → hyp m E.[ ext ]) ⟩
       ◯ (Is-modal C × B)  ↝⟨ inverse-ext? ◯≃◯-Is-modal-× (lower-extensionality? equivalenceᴱ d e E.[ ext ]) ⟩□
       ◯ B                 □)
    ext

-- A variant of ◯-cong-↝-Is-modal→.

Is-modal→↝→↝ :
  ∀ d e →
  Extensionality? k (a ⊔ d) (a ⊔ e) →
  A ↝[ k ] ◯ A →
  ◯ B ↝[ k ] B →
  (Is-modal C → A ↝[ a ⊔ d ∣ a ⊔ e ] B) →
  A ↝[ k ] B
Is-modal→↝→↝ {A = A} {B = B} d e ext A↝◯A ◯B↝B A↝B =
  A    ↝⟨ A↝◯A ⟩
  ◯ A  ↝⟨ ◯-cong-↝-Is-modal→ d e ext A↝B ⟩
  ◯ B  ↝⟨ ◯B↝B ⟩□
  B    □

------------------------------------------------------------------------
-- H-levels

-- H-level′ n commutes with ◯ (in a certain sense).

H-level′-◯≃◯-H-level′ :
  ∀ n → H-level′ n (◯ A) ↝[ a ∣ a ] ◯ (H-level′ n A)
H-level′-◯≃◯-H-level′ {A = A} zero ext =
  Contractible (◯ A)                   ↔⟨⟩
  (∃ λ (x : ◯ A) → ∀ y → x ≡ y)        ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → from-equivalence $
                                           Is-modal→≃◯ (Separated-◯ _ _)) ⟩
  (∃ λ (x : ◯ A) → ∀ y → ◯ (x ≡ y))    ↝⟨ (∃-cong λ _ → Π◯≃◯Π ext) ⟩
  (∃ λ (x : ◯ A) → ◯ (∀ y → x ≡ y))    ↝⟨ (∃-cong λ _ → ◯-cong-↝-Is-modal→ lzero lzero ext λ m →
                                           inverse-ext? λ ext → Π-cong ext (Is-modal→≃◯ m) λ _ → F.id) ⟩
  (∃ λ (x : ◯ A) → ◯ (∀ y → x ≡ η y))  ↔⟨ inverse ◯Ση≃Σ◯◯ ⟩
  ◯ (∃ λ (x : A) → ∀ y → η x ≡ η y)    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → ∀-cong ext λ _ → from-equivalence $ inverse
                                           ◯≡≃η≡η) ⟩
  ◯ (∃ λ (x : A) → ∀ y → ◯ (x ≡ y))    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → Π◯≃◯Π ext) ⟩
  ◯ (∃ λ (x : A) → ◯ (∀ y → x ≡ y))    ↔⟨ ◯Σ◯≃◯Σ ⟩
  ◯ (∃ λ (x : A) → ∀ y → x ≡ y)        ↔⟨⟩
  ◯ (Contractible A)                   □
H-level′-◯≃◯-H-level′ {A = A} (suc n) ext =
  H-level′ (suc n) (◯ A)                              ↔⟨⟩
  ((x y : ◯ A) → H-level′ n (x ≡ y))                  ↝⟨ Is-modal→↝→↝ lzero lzero ext
                                                           (
    ((x y : ◯ A) → H-level′ n (x ≡ y))                      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                inverse-ext?
                                                                  (λ ext →
                                                                     Stable-H-level′ ext n $
                                                                     Separated-◯ _ _)
                                                                  ext) ⟩
    ((x y : ◯ A) → ◯ (H-level′ n (x ≡ y)))                  ↝⟨ (∀-cong ext λ _ → Π◯≃◯Π ext) ⟩
    ((x : ◯ A) → ◯ ((y : ◯ A) → H-level′ n (x ≡ y)))        ↝⟨ Π◯≃◯Π ext ⟩□
    ◯ ((x y : ◯ A) → H-level′ n (x ≡ y))                    □)
                                                           (
    ◯ ((x y : A) → ◯ (H-level′ n (x ≡ y)))                  ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    ((x : A) → ◯ ((y : A) → ◯ (H-level′ n (x ≡ y))))        ↝⟨ (∀-cong ext λ _ → inverse-ext? Π◯≃◯Π ext) ⟩
    ((x y : A) → ◯ (◯ (H-level′ n (x ≡ y))))                ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → from-equivalence $ inverse ◯≃◯◯) ⟩□
    ((x y : A) → ◯ (H-level′ n (x ≡ y)))                    □)
                                                           (λ (m : Is-modal A) ext →
    ((x y : ◯ A) → H-level′ n (x ≡ y))                        ↝⟨ (Π-cong-contra ext (Is-modal→≃◯ m) λ _ →
                                                                  Π-cong-contra ext (Is-modal→≃◯ m) λ _ →
                                                                  F.id) ⟩
    ((x y : A) → H-level′ n (η x ≡ η y))                      ↝⟨ ((∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                  H-level′-cong ext n $ inverse
                                                                  ◯≡≃η≡η)) ⟩
    ((x y : A) → H-level′ n (◯ (x ≡ y)))                      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                  H-level′-◯≃◯-H-level′ n ext) ⟩□
    ((x y : A) → ◯ (H-level′ n (x ≡ y)))                      □) ⟩

  ((x y : A) → ◯ (H-level′ n (x ≡ y)))                ↝⟨ (∀-cong ext λ _ → Π◯≃◯Π ext) ⟩
  ((x : A) → ◯ ((y : A) → H-level′ n (x ≡ y)))        ↝⟨ Π◯≃◯Π ext ⟩
  ◯ ((x y : A) → H-level′ n (x ≡ y))                  ↔⟨⟩
  ◯ (H-level′ (suc n) A)                              □

-- H-level n commutes with ◯ (in a certain sense).

H-level-◯≃◯-H-level :
  ∀ n → H-level n (◯ A) ↝[ a ∣ a ] ◯ (H-level n A)
H-level-◯≃◯-H-level {A = A} n ext =
  H-level n (◯ A)   ↝⟨ H-level↔H-level′ ext ⟩
  H-level′ n (◯ A)  ↝⟨ H-level′-◯≃◯-H-level′ n ext ⟩
  ◯ (H-level′ n A)  ↝⟨ ◯-cong-↝ ext $ inverse-ext? H-level↔H-level′ ⟩□
  ◯ (H-level n A)   □

-- A variant of Left-exact-η-cong→H-level→H-level-◯ proved using the
-- assumption that the modality is very modal, instead of function
-- extensionality and left exactness.

H-level→H-level-◯ :
  ∀ n → H-level n A → H-level n (◯ A)
H-level→H-level-◯ {A = A} n =
  H-level n A      →⟨ η ⟩
  ◯ (H-level n A)  →⟨ _⇔_.from (H-level-◯≃◯-H-level n _) ⟩□
  H-level n (◯ A)  □

------------------------------------------------------------------------
-- The modality is left exact

-- Very modal modalities are left exact.
--
-- See also left-exact-η-cong above.

left-exact : Left-exact ◯
left-exact {A = A} {x = x} {y = y} =
  Contractible (◯ A)        →⟨ H-level′-◯≃◯-H-level′ 0 _ ⟩
  ◯ (Contractible A)        →⟨ ◯-map $ H-level.⇒≡ 0 ⟩
  ◯ (Contractible (x ≡ y))  →⟨ inverse-ext? (H-level′-◯≃◯-H-level′ 0) _ ⟩□
  Contractible (◯ (x ≡ y))  □

------------------------------------------------------------------------
-- More equivalences

private

  -- A lemma used to implement ◯→⇔◯→◯.

  ◯→⇔◯→◯-lemma : (◯ A → ◯ B) → (A → Is-modal B) → A → B
  ◯→⇔◯→◯-lemma f m x = Is-modal→Stable (m x) (f (η x))

  -- ◯ commutes with the non-dependent function space (up to _⇔_).

  ◯→⇔◯→◯ : ◯ (A → B) ⇔ (◯ A → ◯ B)
  ◯→⇔◯→◯ {A = A} {B = B} = record
    { to   = ◯-map-◯
    ; from = λ f → ◯-map (◯→⇔◯→◯-lemma f) ◯-Π-Is-modal
    }

  abstract

    -- A lemma related to ◯→⇔◯→◯.

    ◯→⇔◯→◯-◯→⇔◯→◯ :
      (f : ◯ A → ◯ B) →
      _⇔_.to ◯→⇔◯→◯ (_⇔_.from ◯→⇔◯→◯ f) x ≡ f x
    ◯→⇔◯→◯-◯→⇔◯→◯ {x = x} f =
      ◯-elim
        {P = λ m → ◯-map-◯ (◯-map (◯→⇔◯→◯-lemma f) m) x ≡ f x}
        (λ _ → Separated-◯ _ _)
        (λ m →
           ◯-elim
             (λ _ → Separated-◯ _ _)
             (λ x →
                ◯-map-◯ (◯-map (◯→⇔◯→◯-lemma f) (η m)) (η x)  ≡⟨ cong (flip ◯-map-◯ _) ◯-map-η ⟩

                ◯-map-◯ (η (◯→⇔◯→◯-lemma f m)) (η x)          ≡⟨ ◯-map-◯-η ⟩

                η (◯→⇔◯→◯-lemma f m x)                        ≡⟨⟩

                η (Is-modal→Stable (m x) (f (η x)))           ≡⟨ _≃_.right-inverse-of (Is-modal→≃◯ (m x)) _ ⟩∎

                f (η x)                                       ∎)
             x)
        ◯-Π-Is-modal

-- ◯ commutes with the non-dependent function space (assuming
-- function extensionality).

◯→≃◯→◯ : ◯ (A → B) ↝[ a ∣ a ] (◯ A → ◯ B)
◯→≃◯→◯ {A = A} {B = B} =
  generalise-ext?
    ◯→⇔◯→◯
    (λ ext →
         (λ f → apply-ext ext λ _ → ◯→⇔◯→◯-◯→⇔◯→◯ f)
       , (◯-elim (λ _ → Separated-◯ _ _) λ f →
            ◯-elim
              {P = λ m → ◯-map (◯→⇔◯→◯-lemma (◯-map-◯ (η f))) m ≡ η f}
              (λ _ → Separated-◯ _ _)
              (λ m →
                 ◯-map (◯→⇔◯→◯-lemma (◯-map-◯ (η f))) (η m)             ≡⟨ ◯-map-η ⟩
                 η (◯→⇔◯→◯-lemma (◯-map-◯ (η f)) m)                     ≡⟨⟩
                 η (λ x → Is-modal→Stable (m x) (◯-map-◯ (η f) (η x)))  ≡⟨ (cong η $ apply-ext ext λ x → cong (Is-modal→Stable (m x))
                                                                            ◯-map-◯-η) ⟩
                 η (λ x → Is-modal→Stable (m x) (η (f x)))              ≡⟨ (cong η $ apply-ext ext λ x →
                                                                            _≃_.left-inverse-of (Is-modal→≃◯ (m x)) _) ⟩∎
                 η f                                                    ∎)
              ◯-Π-Is-modal))

-- ◯ commutes with _⇔_ (assuming function extensionality).

◯⇔≃◯⇔◯ : ◯ (A ⇔ B) ↝[ a ∣ a ] (◯ A ⇔ ◯ B)
◯⇔≃◯⇔◯ {A = A} {B = B} ext =
  ◯ (A ⇔ B)                  ↔⟨ ◯-cong-↔ ⇔↔→×→ ⟩
  ◯ ((A → B) × (B → A))      ↔⟨ ◯×≃ ⟩
  ◯ (A → B) × ◯ (B → A)      ↝⟨ ◯→≃◯→◯ ext ×-cong ◯→≃◯→◯ ext ⟩
  (◯ A → ◯ B) × (◯ B → ◯ A)  ↔⟨ inverse ⇔↔→×→ ⟩□
  ◯ A ⇔ ◯ B                  □

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
     let ext′ = Eq.good-ext ext in
       (λ (f , p) → Σ-≡,≡→≡
          (apply-ext ext′ $ eq′ f)
          (lemma ext f p))
     , (λ (f , p) → Σ-≡,≡→≡
          (_≃_.left-inverse-of (◯→≃◯→◯ ext′) f)
          (subst (P ∘ ◯-map-◯)
             (_≃_.left-inverse-of (◯→≃◯→◯ ext′) f)
             (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                    ≡⟨ subst-∘ _ _ _ ⟩

           subst P
             (cong ◯-map-◯ $ _≃_.left-inverse-of (◯→≃◯→◯ ext′) f)
             (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                    ≡⟨ cong (flip (subst P) _) $
                                                                      _≃_.left-right-lemma (◯→≃◯→◯ ext′) _ ⟩
           subst P
             (_≃_.right-inverse-of (◯→≃◯→◯ ext′) (◯-map-◯ f))
             (P-resp (sym ∘ eq′ (◯-map-◯ f)) p)                    ≡⟨ lemma ext _ _ ⟩∎

           p                                                       ∎)))
  where
  eq′ = λ f x → ◯→⇔◯→◯-◯→⇔◯→◯ {x = x} f

  lemma = λ ext f p →
    let eq = apply-ext (Eq.good-ext ext) (eq′ f) in

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

-- A variant of Stable-Σ.

Stable-Σ[◯→◯] :
  Extensionality? k a a →
  (P-resp : {f g : ◯ A → ◯ B} → (∀ x → f x ≡ g x) → P f → P g) →
  (∀ {f x} → Extensionality a a → P-resp (refl ∘ f) x ≡ x) →
  (∀ f → Stable-[ k ] (P f)) →
  Stable-[ k ] (Σ (◯ A → ◯ B) P)
Stable-Σ[◯→◯] {A = A} {B = B} {P = P} ext P-resp P-resp-refl s =
  ◯ (Σ (◯ A → ◯ B) P)              ↝⟨ ◯-cong-↝ ext $ inverse-ext? (Σ◯→↝Σ◯→◯ P-resp P-resp-refl) ⟩
  ◯ (Σ (◯ (A → B)) (P ∘ ◯-map-◯))  ↝⟨ Stable-Σ Is-modal-◯ (s ∘ ◯-map-◯) ⟩
  Σ (◯ (A → B)) (P ∘ ◯-map-◯)      ↝⟨ Σ◯→↝Σ◯→◯ P-resp P-resp-refl ext ⟩□
  Σ (◯ A → ◯ B) P                  □

-- Some lemmas that can be used to prove that ◯ (F A B) is equivalent
-- to F (◯ A) (◯ B).

◯↝↝◯↝◯′ :
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
◯↝↝◯↝◯′ {A = A} {B = B} {F = F} {P = P}
  F↔ ◯∘P↝P∘◯-map P-cong P-stable Σ◯→↝Σ◯→◯ ext =
  ◯ (F A B)                                  ↔⟨ ◯-cong-↔ F↔ ⟩
  ◯ (∃ λ (f : A → B) → P f)                  ↔⟨ inverse ◯Σ◯≃◯Σ ⟩
  ◯ (∃ λ (f : A → B) → ◯ (P f))              ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → ◯∘P↝P∘◯-map ext) ⟩
  ◯ (∃ λ (f : A → B) → P (◯-map f))          ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → P-cong ext λ _ → sym ◯-map-◯-ηˡ) ⟩
  ◯ (∃ λ (f : A → B) → P (◯-map-◯ (η f)))    ↔⟨ ◯Ση≃Σ◯◯ ⟩
  (∃ λ (f : ◯ (A → B)) → ◯ (P (◯-map-◯ f)))  ↝⟨ (∃-cong λ _ → P-stable) ⟩
  (∃ λ (f : ◯ (A → B)) → P (◯-map-◯ f))      ↝⟨ Σ◯→↝Σ◯→◯ ⟩
  (∃ λ (f : ◯ A → ◯ B) → P f)                ↔⟨ inverse F↔ ⟩□
  F (◯ A) (◯ B)                              □

◯↝↝◯↝◯″ :
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
◯↝↝◯↝◯″ {A = A} {B = B} {F = F} {P = P}
  F↔ ◯∘P↝P∘◯-map P-cong P-cong-refl P-stable ext =
  ◯↝↝◯↝◯′
    F↔
    ◯∘P↝P∘◯-map
    P-cong
    P-stable
    (Σ◯→↝Σ◯→◯ (P-cong _) P-cong-refl ext)
    ext

private

  -- An example of how ◯↝↝◯↝◯″ can be used.

  ◯⇔≃◯⇔◯′ : ◯ (A ⇔ B) ↝[ a ∣ a ] (◯ A ⇔ ◯ B)
  ◯⇔≃◯⇔◯′ ext =
    ◯↝↝◯↝◯″
      ⇔↔→×→
      ◯→≃◯→◯
      (λ _ _ → F.id)
      (λ _ → refl _)
      (Stable-Π ext λ _ → Is-modal→Stable Is-modal-◯)
      ext

-- ◯ (Split-surjective f) is equivalent to
-- Split-surjective (◯-map f) (assuming function extensionality).

◯-Split-surjective≃Split-surjective :
  ◯ (Split-surjective f) ↝[ a ∣ a ] Split-surjective (◯-map f)
◯-Split-surjective≃Split-surjective {f = f} {k = k} ext =
  ◯ (∀ y → ∃ λ x → f x ≡ y)              ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
  (∀ y → ◯ (∃ λ x → f x ≡ y))            ↝⟨ (∀-cong′ λ _ → inverse ◯Σ◯≃◯Σ) ⟩
  (∀ y → ◯ (∃ λ x → ◯ (f x ≡ y)))        ↝⟨ (∀-cong′ λ _ → ◯-cong-≃ $ ∃-cong λ _ → ◯≡≃η≡η) ⟩
  (∀ y → ◯ (∃ λ x → η (f x) ≡ η y))      ↝⟨ inverse-ext? Π◯◯≃Π◯η ext ⟩
  (∀ y → ◯ (∃ λ x → η (f x) ≡ y))        ↝⟨ (∀-cong′ λ _ → ◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym ◯-map-η) ⟩
  (∀ y → ◯ (∃ λ x → ◯-map f (η x) ≡ y))  ↝⟨ (∀-cong′ λ _ → ◯Ση≃Σ◯◯) ⟩
  (∀ y → ∃ λ x → ◯ (◯-map f x ≡ y))      ↝⟨ (∀-cong′ λ _ → ∃-cong λ _ → Is-modal→Stable (Separated-◯ _ _)) ⟩□
  (∀ y → ∃ λ x → ◯-map f x ≡ y)          □
  where
  ∀-cong′ :
    {A : Type a} {P Q : A → Type a} →
    (∀ x → P x ≃ Q x) → ((x : A) → P x) ↝[ k ] ((x : A) → Q x)
  ∀-cong′ = ∀-cong ext ∘ (from-equivalence ∘_)

-- ◯ commutes with _↠_ (assuming function extensionality).

◯↠≃◯↠◯ : ◯ (A ↠ B) ↝[ a ∣ a ] (◯ A ↠ ◯ B)
◯↠≃◯↠◯ ext =
  ◯↝↝◯↝◯″
    ↠↔∃-Split-surjective
    ◯-Split-surjective≃Split-surjective
    Split-surjective-cong
    Split-surjective-cong-refl
    (Stable-Π ext λ _ → Is-modal→Stable $
     Is-modal-Σ Is-modal-◯ λ _ → Separated-◯ _ _)
    ext

-- ◯ (Is-equivalence f) is equivalent to Is-equivalence (◯-map f)
-- (assuming function extensionality).

◯-Is-equivalence≃Is-equivalence :
  ◯ (Is-equivalence f) ↝[ a ∣ a ] Is-equivalence (◯-map f)
◯-Is-equivalence≃Is-equivalence {f = f} ext =
  ◯ (Is-equivalence f)                           ↝⟨ ◯-cong-↝ ext Is-equivalence≃Is-equivalence-CP ⟩
  ◯ (∀ y → Contractible (f ⁻¹ y))                ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
  (∀ y → ◯ (Contractible (f ⁻¹ y)))              ↝⟨ Is-modal→↝→↝ lzero lzero ext
                                                      (
    (∀ x → ◯ (Contractible (f ⁻¹ x)))                  ↝⟨ inverse-ext?
                                                            (λ ext →
                                                               Stable-Π ext λ _ →
                                                               Is-modal→Stable Is-modal-◯)
                                                            ext ⟩
    ◯ (∀ x → ◯ (Contractible (f ⁻¹ x)))                □)
                                                      (
    ◯ (∀ x → Contractible (◯ (η ∘ f ⁻¹ x)))            ↝⟨ (Stable-Π ext λ _ →
                                                           Stable-H-level′ ext 0 Is-modal-◯) ⟩□
    (∀ x → Contractible (◯ (η ∘ f ⁻¹ x)))              □)
                                                      (λ m ext →
                                                         Π-cong-contra ext (inverse $ Is-modal→≃◯ m) λ x →
    ◯ (Contractible (f ⁻¹ Is-modal→Stable m x))            ↝⟨ inverse-ext? (H-level′-◯≃◯-H-level′ 0) ext ⟩
    Contractible (◯ (f ⁻¹ Is-modal→Stable m x))            ↝⟨ H-level-cong ext 0 $ ◯-cong-≃ $ inverse $
                                                              to-∘-⁻¹-≃-⁻¹-from (Is-modal→≃◯ m) ⟩□
    Contractible (◯ (η ∘ f ⁻¹ x))                          □) ⟩

  (∀ y → Contractible (◯ (η ∘ f ⁻¹ y)))          ↔⟨⟩
  ◯ -Connected-→ (η ∘ f)                         ↝⟨ Connected-→-η-∘-≃Is-equivalence-◯-map ext ⟩□
  Is-equivalence (◯-map f)                       □

-- A function f is ◯-connected if and only if ◯ (Is-equivalence f)
-- holds.

Connected-→≃◯-Is-equivalence :
  ◯ -Connected-→ f ↝[ a ∣ a ] ◯ (Is-equivalence f)
Connected-→≃◯-Is-equivalence {f = f} ext =
  ◯ -Connected-→ f          ↝⟨ Left-exact→Connected-→≃Is-equivalence-◯-map left-exact ext ⟩
  Is-equivalence (◯-map f)  ↝⟨ inverse-ext? ◯-Is-equivalence≃Is-equivalence ext ⟩□
  ◯ (Is-equivalence f)      □

-- ◯ commutes with _≃_ (assuming function extensionality).

◯≃≃◯≃◯ : ◯ (A ≃ B) ↝[ a ∣ a ] (◯ A ≃ ◯ B)
◯≃≃◯≃◯ ext =
  ◯↝↝◯↝◯″
    Eq.≃-as-Σ
    ◯-Is-equivalence≃Is-equivalence
    Is-equivalence-cong
    (λ ext → Eq.propositional ext _ _ _)
    (Is-modal→Stable-Is-equivalence ext Is-modal-◯ Is-modal-◯)
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
                                                                         (∀-cong ext λ _ → from-equivalence ◯≡≃η≡η)
                                                                           ×-cong
                                                                         (∀-cong ext λ _ → from-equivalence ◯≡≃η≡η)) ⟩

  ◯ (∃ λ g → (∀ x → η (f (g x)) ≡ η x) × (∀ x → η (g (f x)) ≡ η x))  ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ →
                                                                         (∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                          trans (cong (◯-map f) ◯-map-◯-η) ◯-map-η)
                                                                           ×-cong
                                                                         (∀-cong ext λ _ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                          ◯-map-◯-η)) ⟩
  ◯ (∃ λ g → (∀ x → ◯-map f (◯-map-◯ (η g) (η x)) ≡ η x) ×
             (∀ x → ◯-map-◯ (η g) (η (f x)) ≡ η x))                  ↔⟨ ◯Ση≃Σ◯◯ ⟩

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
                                                                         (∀-cong ext λ _ → Is-modal→Stable (Separated-◯ _ _))
                                                                           ×-cong
                                                                         (∀-cong ext λ _ → Is-modal→Stable (Separated-◯ _ _))) ⟩
  (∃ λ g → (∀ x → ◯-map f (◯-map-◯ g x) ≡ x) ×
           (∀ x → ◯-map-◯ g (◯-map f x) ≡ x))                        ↝⟨ Σ◯→↝Σ◯→◯
                                                                          Has-quasi-inverse-proofs-resp
                                                                          Has-quasi-inverse-proofs-resp-refl
                                                                          ext ⟩□
  (∃ λ g → (∀ x → ◯-map f (g x) ≡ x) × (∀ x → g (◯-map f x) ≡ x))    □

-- ◯ commutes with _↔_ (assuming function extensionality).

◯↔≃◯↔◯ : ◯ (A ↔ B) ↝[ a ∣ a ] (◯ A ↔ ◯ B)
◯↔≃◯↔◯ ext =
  ◯↝↝◯↝◯″
    Bijection.↔-as-Σ
    ◯-Has-quasi-inverse≃Has-quasi-inverse
    Has-quasi-inverse-cong
    Has-quasi-inverse-cong-refl
    (Stable-Σ[◯→◯] ext
       Has-quasi-inverse-proofs-resp
       Has-quasi-inverse-proofs-resp-refl λ _ →
     Stable-×
       (Stable-Π ext λ _ →
        Is-modal→Stable (Is-modal→Separated Is-modal-◯ _ _))
       (Stable-Π ext λ _ →
        Is-modal→Stable (Is-modal→Separated Is-modal-◯ _ _)))
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
  (∀ x y → ◯ (f x ≡ f y) → ◯ (x ≡ y))                  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → →-cong₁ ext
                                                           ◯≡≃η≡η) ⟩
  (∀ x y → η (f x) ≡ η (f y) → ◯ (x ≡ y))              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → from-equivalence
                                                           ◯≡≃η≡η) ⟩
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
  s ext _ = Stable-Π ext λ _ → Is-modal→Stable $ Separated-◯ _ _

-- ◯ commutes with _↣_ (assuming function extensionality).

◯↣≃◯↣◯ : ◯ (A ↣ B) ↝[ a ∣ a ] (◯ A ↣ ◯ B)
◯↣≃◯↣◯ ext =
  ◯↝↝◯↝◯″
    ↣↔∃-Injective
    ◯-Injective≃Injective
    Injective-cong
    Injective-cong-refl
    (Stable-implicit-Π ext λ _ →
     Stable-implicit-Π ext λ _ →
     Stable-Π          ext λ _ →
     Is-modal→Stable $ Separated-◯ _ _)
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
                                                                            ◯-map-cong≡ left-exact-η-cong) ⟩
  (∀ x y →
     Is-equivalence
       (η-cong⁻¹ left-exact-η-cong ∘
        _≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
        cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → ◯ (f x ≡ f y))))         ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                            inverse-ext?
                                                                              (Is-equivalence≃Is-equivalence-∘ˡ
                                                                                 (_≃_.is-equivalence $ inverse ◯≡≃η≡η))
                                                                              ext) ⟩
  (∀ x y →
     Is-equivalence
       (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
        cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → η (f x) ≡ η (f y))))     ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                            inverse-ext?
                                                                              (Is-equivalence≃Is-equivalence-∘ʳ left-exact-η-cong)
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
                                                                              Is-modal→Stable-Is-equivalence ext
                                                                                (Separated-◯ _ _) (Separated-◯ _ _))
                                                                             ext ⟩
  (∀ x y →
     Is-equivalence
       (cong (◯-map f) ⦂ (x ≡ η y → ◯-map f x ≡ ◯-map f (η y))))        ↝⟨ (∀-cong ext λ _ →
                                                                            inverse-ext?
                                                                              (Π◯↝Πη λ ext _ →
                                                                               Is-modal→Stable-Is-equivalence ext
                                                                                 (Separated-◯ _ _) (Separated-◯ _ _))
                                                                              ext) ⟩□
  (∀ x y →
     Is-equivalence
       (cong (◯-map f) ⦂ (x ≡ y → ◯-map f x ≡ ◯-map f y)))              □

-- ◯ commutes with Embedding (assuming function extensionality).

◯-Embedding≃Embedding-◯-◯ :
  ◯ (Embedding A B) ↝[ a ∣ a ] Embedding (◯ A) (◯ B)
◯-Embedding≃Embedding-◯-◯ ext =
  ◯↝↝◯↝◯″
    Emb.Embedding-as-Σ
    ◯-Is-embedding≃Is-embedding
    Is-embedding-cong
    (λ ext → Emb.Is-embedding-propositional ext _ _)
    (Stable-Π ext λ _ → Stable-Π ext λ _ →
     Is-modal→Stable-Is-equivalence ext
       (Separated-◯ _ _) (Separated-◯ _ _))
    ext

------------------------------------------------------------------------
-- Some results related to Erased

-- ◯ (Erased (◯ A)) is logically equivalent to ◯ (Erased A).
--
-- See also []-cong.◯-Erased-◯≃◯-Erased below.

◯-Erased-◯⇔◯-Erased :
  ◯ (Erased (◯ A)) ⇔ ◯ (Erased A)
◯-Erased-◯⇔◯-Erased {A = A} =
  ◯ (Erased (◯ A))               ↝⟨ ◯≃◯-Is-modal-× _ ⟩
  ◯ (Is-modal A × Erased (◯ A))  ↝⟨ (◯-cong-⇔ $ ∃-cong λ m → E.Erased-cong-⇔ (Is-modal→Stable m)) ⟩
  ◯ (Is-modal A × Erased A)      ↝⟨ inverse $ ◯≃◯-Is-modal-× _ ⟩□
  ◯ (Erased A)                   □

-- ◯ (Erased A) is logically equivalent to Erased (◯ A).
--
-- See also []-cong.◯-Erased≃Erased-◯ below.

◯-Erased⇔Erased-◯ :
  ◯ (Erased A) ⇔ Erased (◯ A)
◯-Erased⇔Erased-◯ {A = A} =
  ◯ (Erased A)      ↝⟨ inverse ◯-Erased-◯⇔◯-Erased ⟩
  ◯ (Erased (◯ A))  ↝⟨ lemma ⟩□
  Erased (◯ A)      □
  where
  lemma = record
    { to   = M.Stable-Erased (Is-modal→Stable Is-modal-◯)
    ; from = η
    }

-- Some results that hold if the []-cong axioms can be instantiated.

module []-cong (ax : []-cong-axiomatisation a) where

  open Modality.Box-cong eq ax M

  private
    module BC       = E.[]-cong₁ ax
    module EC       = E₂.[]-cong₂-⊔ ax ax ax
    module BC-ECP   = ECP.[]-cong₂ ax ax
    module BC-ECP-⊔ = ECP.[]-cong₂-⊔ ax ax ax

  -- ◯ (Erased (◯ A)) is equivalent to ◯ (Erased A) (assuming function
  -- extensionality).

  ◯-Erased-◯≃◯-Erased :
    ◯ (Erased (◯ A)) ↝[ a ∣ a ] ◯ (Erased A)
  ◯-Erased-◯≃◯-Erased {A = A} ext =
    ◯-cong-↝-Is-modal→ lzero lzero ext λ m _ →
      Erased (◯ A)  ↔⟨ EC.Erased-cong (inverse $ Is-modal→≃◯ m) ⟩□
      Erased A      □

  -- ◯ (Erased A) is equivalent to Erased (◯ A) (assuming function
  -- extensionality).

  ◯-Erased≃Erased-◯ :
    ◯ (Erased A) ↝[ a ∣ a ] Erased (◯ A)
  ◯-Erased≃Erased-◯ {A = A} ext =
    ◯ (Erased A)      ↝⟨ inverse-ext? ◯-Erased-◯≃◯-Erased ext ⟩
    ◯ (Erased (◯ A))  ↔⟨ lemma ⟩□
    Erased (◯ A)      □
    where
    lemma′ = λ (E.[ x ]) →
      E.[ ◯-rec Is-modal-◯ id (◯-map E.erased (η E.[ x ])) ]  ≡⟨ BC.[]-cong E.[ cong (_≃_.from ◯≃◯◯) ◯-map-η ] ⟩
      E.[ ◯-rec Is-modal-◯ id (η x) ]                         ≡⟨ BC.[]-cong E.[ ◯-rec-η ] ⟩∎
      E.[ x ]                                                 ∎

    lemma = Eq.↔→≃
      (M.Stable-Erased (Is-modal→Stable Is-modal-◯))
      η
      lemma′
      (◯-elim (λ _ → Separated-◯ _ _) (cong η ∘ lemma′))

  -- ◯ commutes with Contractibleᴱ (assuming function extensionality).

  ◯-Contractibleᴱ≃Contractibleᴱ-◯ :
    ◯ (Contractibleᴱ A) ↝[ a ∣ a ] Contractibleᴱ (◯ A)
  ◯-Contractibleᴱ≃Contractibleᴱ-◯ {A = A} ext =
    ◯ (Contractibleᴱ A)                           ↔⟨⟩
    ◯ (∃ λ (x : A) → Erased (∀ y → x ≡ y))        ↔⟨ inverse ◯Σ◯≃◯Σ ⟩
    ◯ (∃ λ (x : A) → ◯ (Erased (∀ y → x ≡ y)))    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → ◯-Erased≃Erased-◯ ext) ⟩
    ◯ (∃ λ (x : A) → Erased (◯ (∀ y → x ≡ y)))    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → EC.Erased-cong (inverse-ext? Π◯≃◯Π ext)) ⟩
    ◯ (∃ λ (x : A) → Erased (∀ y → ◯ (x ≡ y)))    ↝⟨ (◯-cong-↝ ext λ ext → ∃-cong λ _ → EC.Erased-cong (∀-cong ext λ _ → from-equivalence
                                                      ◯≡≃η≡η)) ⟩
    ◯ (∃ λ (x : A) → Erased (∀ y → η x ≡ η y))    ↔⟨ ◯Ση≃Σ◯◯ ⟩
    (∃ λ (x : ◯ A) → ◯ (Erased (∀ y → x ≡ η y)))  ↝⟨ (∃-cong λ _ → ◯-Erased≃Erased-◯ ext) ⟩
    (∃ λ (x : ◯ A) → Erased (◯ (∀ y → x ≡ η y)))  ↝⟨ (∃-cong λ _ → EC.Erased-cong (◯-cong-↝-Is-modal→ lzero lzero ext λ m ext →
                                                      Π-cong ext (Is-modal→≃◯ m) λ _ → F.id)) ⟩
    (∃ λ (x : ◯ A) → Erased (◯ (∀ y → x ≡ y)))    ↝⟨ (∃-cong λ _ → EC.Erased-cong (inverse-ext? Π◯≃◯Π ext)) ⟩
    (∃ λ (x : ◯ A) → Erased (∀ y → ◯ (x ≡ y)))    ↝⟨ (∃-cong λ _ → EC.Erased-cong (∀-cong ext λ _ → from-equivalence $ inverse $
                                                      Is-modal→≃◯ (Separated-◯ _ _))) ⟩
    (∃ λ (x : ◯ A) → Erased (∀ y → x ≡ y))        ↔⟨⟩
    Contractibleᴱ (◯ A)                           □

  -- If A is k-stable, then Erased A is k-stable (perhaps assuming
  -- function extensionality).

  Stable-Erased :
    Extensionality? k a a →
    @0 Stable-[ k ] A → Stable-[ k ] (Erased A)
  Stable-Erased {A = A} ext s =
    ◯ (Erased A)  ↝⟨ ◯-Erased≃Erased-◯ ext ⟩
    Erased (◯ A)  ↝⟨ EC.Erased-cong s ⟩□
    Erased A      □

  -- If A is modal, then Contractibleᴱ A is k-stable (perhaps assuming
  -- function extensionality).

  Stable-Contractibleᴱ :
    Extensionality? k a a →
    Is-modal A →
    Stable-[ k ] (Contractibleᴱ A)
  Stable-Contractibleᴱ ext m =
    Stable-Σ m λ _ →
    Stable-Erased ext (
    Stable-Π ext λ _ →
    Is-modal→Stable (Is-modal→Separated m _ _))

  -- If f has type A → B, A is modal, and equality is k-stable for B,
  -- then f ⁻¹ᴱ y is k-stable (perhaps assuming function
  -- extensionality).

  Stable-⁻¹ᴱ :
    {A B : Type a} {f : A → B} {y : B} →
    Extensionality? k a a →
    Is-modal A →
    @0 For-iterated-equality 1 Stable-[ k ] B →
    Stable-[ k ] (f ⁻¹ᴱ y)
  Stable-⁻¹ᴱ ext m s =
    Stable-Σ m λ _ →
    Stable-Erased ext (s _ _)

  -- If f has type A → B, where A and B are modal, then
  -- ECP.Is-equivalenceᴱ f is k-stable (perhaps assuming function
  -- extensionality).

  Is-modal→Stable-Is-equivalenceᴱ-CP :
    {@0 f : A → B} →
    Extensionality? k a a →
    Is-modal A → @0 Is-modal B →
    Stable-[ k ] (ECP.Is-equivalenceᴱ f)
  Is-modal→Stable-Is-equivalenceᴱ-CP {f = f} ext mA mB =
    Stable-Π ext λ y →
    let m : Is-modal (f ⁻¹ᴱ y)
        m = Is-modal-Σ mA λ _ →
            Is-modal-Erased (Is-modal→Separated mB _ _) in
    Stable-Σ m λ _ →
    Stable-Erased ext (
    Stable-Π ext λ _ →
    Is-modal→Stable (Is-modal→Separated m _ _))

  -- If f has type A → B, where A and B are modal, then
  -- Is-equivalenceᴱ f is equivalenceᴱ-stable (assuming function
  -- extensionality).

  Is-modal→Stable-≃ᴱ-Is-equivalenceᴱ :
    {@0 f : A → B} →
    @0 Extensionality a a →
    Is-modal A → @0 Is-modal B →
    Stable-[ equivalenceᴱ ] (Is-equivalenceᴱ f)
  Is-modal→Stable-≃ᴱ-Is-equivalenceᴱ {f = f} ext mA mB =
                                                             $⟨ s ⟩
    Stable-[ equivalenceᴱ ] (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  →⟨ Stable-respects-↝-sym $ inverse $
                                                                EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext ⟩□
    Stable-[ equivalenceᴱ ] (Is-equivalenceᴱ f)              □
    where
    ext′ = E.[ ext ]

    s =
      Stable-Π ext′ λ y →
      let m : Is-modal (f ⁻¹ᴱ y)
          m = Is-modal-Σ mA λ _ →
              Is-modal-Erased (Is-modal→Separated mB _ _) in
      Stable-Σ m λ _ →
      Stable-Erased ext′ (
      Stable-Π ext′ λ _ →
      Is-modal→Stable (Is-modal→Separated m _ _))

  -- A lemma relating ◯, ◯-map and _⁻¹ᴱ_.

  ◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ :
    {A : Type a} {@0 B : Type a} {@0 f : A → B} {y : ◯ B} →
    ◯ (η ∘ f ⁻¹ᴱ y) ≃ ◯-map f ⁻¹ᴱ y
  ◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ {f = f} {y = y} =
    ◯ (∃ λ x → Erased (η (f x) ≡ y))        ↝⟨ ◯-cong-≃ (∃-cong λ _ → EC.Erased-cong (≡⇒↝ _ $ cong (_≡ _) $ sym ◯-map-η)) ⟩
    ◯ (∃ λ x → Erased (◯-map f (η x) ≡ y))  ↝⟨ ◯Ση≃Σ◯◯ ⟩
    (∃ λ x → ◯ (Erased (◯-map f x ≡ y)))    ↝⟨ (∃-cong λ _ → Is-modal→Stable (Is-modal-Erased (Separated-◯ _ _))) ⟩
    (∃ λ x → Erased (◯-map f x ≡ y))        □

  -- ◯ (ECP.Is-equivalenceᴱ f) is equivalent to
  -- Is-equivalenceᴱ (◯-map f) (assuming function extensionality).

  ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP :
    ◯ (ECP.Is-equivalenceᴱ f) ↝[ a ∣ a ] ECP.Is-equivalenceᴱ (◯-map f)
  ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP {f = f} ext =
    ◯ (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))                ↝⟨ inverse-ext? Π◯≃◯Π ext ⟩
    (∀ y → ◯ (Contractibleᴱ (f ⁻¹ᴱ y)))              ↝⟨ Is-modal→↝→↝ lzero lzero ext
                                                          (
      (∀ x → ◯ (Contractibleᴱ (f ⁻¹ᴱ x)))                  ↝⟨ inverse-ext?
                                                                (λ ext →
                                                                   Stable-Π ext λ _ →
                                                                   Is-modal→Stable Is-modal-◯)
                                                                ext ⟩
      ◯ (∀ x → ◯ (Contractibleᴱ (f ⁻¹ᴱ x)))                □)
                                                          (
      ◯ (∀ x → Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ x)))            ↝⟨ (Stable-Π ext λ _ →
                                                               Stable-Contractibleᴱ ext Is-modal-◯) ⟩□
      (∀ x → Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ x)))              □)
                                                          (λ m ext →
                                                             Π-cong-contra ext (inverse $ Is-modal→≃◯ m) λ x →
      ◯ (Contractibleᴱ (f ⁻¹ᴱ Is-modal→Stable m x))            ↝⟨ ◯-Contractibleᴱ≃Contractibleᴱ-◯ ext ⟩
      Contractibleᴱ (◯ (f ⁻¹ᴱ Is-modal→Stable m x))            ↝⟨ BC-ECP.Contractibleᴱ-cong ext $ ◯-cong-≃ $ inverse $
                                                                  BC-ECP-⊔.to-∘-⁻¹ᴱ-≃-⁻¹ᴱ-from (Is-modal→≃◯ m) ⟩□
      Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ x))                          □) ⟩

    (∀ y → Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ y)))          ↝⟨ (∀-cong ext λ _ → BC-ECP.Contractibleᴱ-cong ext ◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ) ⟩□
    (∀ y → Contractibleᴱ (◯-map f ⁻¹ᴱ y))            □

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

  -- ◯ commutes with ECP._≃ᴱ_ (assuming function extensionality).

  ◯≃ᴱ-CP-≃◯≃ᴱ-CP-◯ : ◯ (A ECP.≃ᴱ B) ↝[ a ∣ a ] (◯ A ECP.≃ᴱ ◯ B)
  ◯≃ᴱ-CP-≃◯≃ᴱ-CP-◯ ext =
    ◯↝↝◯↝◯′
      {P = λ f → ECP.Is-equivalenceᴱ f}
      F.id
      ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP
      (λ ext f≡g → ECP.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax ext f≡g)
      (Is-modal→Stable-Is-equivalenceᴱ-CP ext Is-modal-◯ Is-modal-◯)
      (Σ◯→↝Σ◯→◯-Is-equivalenceᴱ-CP ext)
      ext

  -- ◯ commutes with _≃ᴱ_ up to _≃ᴱ_ (assuming function
  -- extensionality).

  ◯≃ᴱ≃ᴱ◯≃ᴱ◯ :
    @0 Extensionality a a →
    ◯ (A ≃ᴱ B) ≃ᴱ (◯ A ≃ᴱ ◯ B)
  ◯≃ᴱ≃ᴱ◯≃ᴱ◯ {A = A} {B = B} ext =
    ◯ (A ≃ᴱ B)        ↝⟨ ◯-cong-≃ᴱ $ EEq.≃ᴱ≃ᴱ≃ᴱ-CP ext ⟩
    ◯ (A ECP.≃ᴱ B)    ↝⟨ ◯≃ᴱ-CP-≃◯≃ᴱ-CP-◯ E.[ ext ] ⟩
    (◯ A ECP.≃ᴱ ◯ B)  ↝⟨ inverse $ EEq.≃ᴱ≃ᴱ≃ᴱ-CP ext ⟩□
    (◯ A ≃ᴱ ◯ B)      □

  -- ◯ (A ↝[ k ] B) is related to ◯ A ↝[ k ] ◯ B (perhaps assuming
  -- function extensionality).

  ◯↝↝◯↝◯ :
    Extensionality? k a a →
    ◯ (A ↝[ k ] B) ↝[ k ] (◯ A ↝[ k ] ◯ B)
  ◯↝↝◯↝◯ {k = implication}         = ◯→≃◯→◯
  ◯↝↝◯↝◯ {k = logical-equivalence} = ◯⇔≃◯⇔◯
  ◯↝↝◯↝◯ {k = injection}           = ◯↣≃◯↣◯
  ◯↝↝◯↝◯ {k = embedding}           = ◯-Embedding≃Embedding-◯-◯
  ◯↝↝◯↝◯ {k = surjection}          = ◯↠≃◯↠◯
  ◯↝↝◯↝◯ {k = bijection}           = ◯↔≃◯↔◯
  ◯↝↝◯↝◯ {k = equivalence}         = ◯≃≃◯≃◯
  ◯↝↝◯↝◯ {k = equivalenceᴱ}        = λ ext → ◯≃ᴱ≃ᴱ◯≃ᴱ◯ (E.erased ext)

  ◯↝≃ᴱ◯↝◯ :
    @0 Extensionality a a →
    ◯ (A ↝[ k ] B) ≃ᴱ (◯ A ↝[ k ] ◯ B)
  ◯↝≃ᴱ◯↝◯ {k = implication}         ext = ◯→≃◯→◯ E.[ ext ]
  ◯↝≃ᴱ◯↝◯ {k = logical-equivalence} ext = ◯⇔≃◯⇔◯ E.[ ext ]
  ◯↝≃ᴱ◯↝◯ {k = injection}           ext = ◯↣≃◯↣◯ E.[ ext ]
  ◯↝≃ᴱ◯↝◯ {k = embedding}           ext = ◯-Embedding≃Embedding-◯-◯
                                                 E.[ ext ]
  ◯↝≃ᴱ◯↝◯ {k = surjection}          ext = ◯↠≃◯↠◯ E.[ ext ]
  ◯↝≃ᴱ◯↝◯ {k = bijection}           ext = ◯↔≃◯↔◯ E.[ ext ]
  ◯↝≃ᴱ◯↝◯ {k = equivalence}         ext = ◯≃≃◯≃◯ E.[ ext ]
  ◯↝≃ᴱ◯↝◯ {k = equivalenceᴱ}        ext = ◯≃ᴱ≃ᴱ◯≃ᴱ◯ ext
