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
            Is-modal→Stable-Is-equivalence; Stable-W;
            ◯Π◯≃◯Π; ◯Π◯≃◯Π-η; ◯Π◯≃◯Π⁻¹-η; ◯≡≃η≡η)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq as Emb using (Embedding; Is-embedding)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq as ECP
  using (Contractibleᴱ; _⁻¹ᴱ_)
import Equivalence.Half-adjoint eq as HA
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
    ℓ                 : Level
    A B C             : Type ℓ
    f f⁻¹ g h k p x y : A
    P Q               : A → Type p

------------------------------------------------------------------------
-- Should "Very-modal" be stated differently?

abstract

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
  ◯ ((x : A) → ◯ (P x)) ↝[ a ∣ a ] ◯ ((x : A) → P x)
◯Π◯≃◯Π = M.◯Π◯≃◯Π ◯-Π-Is-modal

-- Two "computation rules" for ◯Π◯≃◯Π.

◯Π◯≃◯Π-η :
  ◯Π◯≃◯Π _ (η f) ≡
  ◯-map (λ m x → Is-modal→Stable (m x) (f x)) ◯-Π-Is-modal
◯Π◯≃◯Π-η {f = f} =
  ◯-elim
    {P = λ m →
           M.◯Π◯≃◯Π m _ (η f) ≡
           ◯-map (λ m x → Is-modal→Stable (m x) (f x)) m}
    (λ _ → Separated-◯ _ _)
    (λ m →
       M.◯Π◯≃◯Π (η m) _ (η f)                             ≡⟨ M.◯Π◯≃◯Π-η ⟩
       η (λ x → Is-modal→Stable (m x) (f x))              ≡⟨ sym ◯-map-η ⟩∎
       ◯-map (λ m x → Is-modal→Stable (m x) (f x)) (η m)  ∎)
    ◯-Π-Is-modal

◯Π◯≃◯Π⁻¹-η : _⇔_.from (◯Π◯≃◯Π _) (η f) ≡ η (η ∘ f)
◯Π◯≃◯Π⁻¹-η = M.◯Π◯≃◯Π⁻¹-η {m = ◯-Π-Is-modal}

-- A variant of ◯Π◯≃◯Π-η.

◯Π◯≃◯Π-η′ :
  (f : ◯ ((x : A) → P x) → B)
  (g : ((x : A) → ◯ (P x)) → B) →
  Is-modal B →
  (∀ m → f (η λ x → Is-modal→Stable (m x) (h x)) ≡ g h) →
  f (◯Π◯≃◯Π _ (η h)) ≡ g h
◯Π◯≃◯Π-η′ {h = h} f g m hyp =
  f (◯Π◯≃◯Π _ (η h))                                            ≡⟨ cong f ◯Π◯≃◯Π-η ⟩
  f (◯-map (λ m x → Is-modal→Stable (m x) (h x)) ◯-Π-Is-modal)  ≡⟨ ◯-elim
                                                                     {P = λ m →
                                                                            f (◯-map (λ m x → Is-modal→Stable (m x) (h x)) m) ≡
                                                                            g h}
                                                                     (λ _ → Is-modal→Separated m _ _)
                                                                     (λ m →
    f (◯-map (λ m x → Is-modal→Stable (m x) (h x)) (η m))               ≡⟨ cong f ◯-map-η ⟩
    f (η λ x → Is-modal→Stable (m x) (h x))                             ≡⟨ hyp m ⟩∎
    g h                                                                 ∎)
                                                                     ◯-Π-Is-modal ⟩∎
  g h                                                           ∎

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
  ∀ ℓ →
  Extensionality (lsuc a ⊔ ℓ) (lsuc a ⊔ ℓ) →
  Topological (lsuc a ⊔ ℓ) M
topological ℓ ext =
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
Π◯≃◯Π {A = A} {P = P} =
  generalise-ext?
    (record { to = to; from = ◯Π→Π◯ })
    (λ ext →
         ◯-elim
           (λ _ → Separated-◯ _ _)
           (λ f →
              ◯Π◯≃◯Π _ (η (◯Π→Π◯ (η f)))            ≡⟨ cong (◯Π◯≃◯Π _ ∘ η) $ ◯Π→Π◯-η ext ⟩
              ◯Π◯≃◯Π _ (η (η ∘ f))                  ≡⟨ cong (◯Π◯≃◯Π _) $ sym ◯Π◯≃◯Π⁻¹-η ⟩
              ◯Π◯≃◯Π _ (_⇔_.from (◯Π◯≃◯Π _) (η f))  ≡⟨ _≃_.right-inverse-of (◯Π◯≃◯Π ext) _ ⟩∎
              η f                                   ∎)
       , (λ f →
            ◯Π→Π◯ (◯Π◯≃◯Π _ (η f))                           ≡⟨ ◯Π◯≃◯Π-η′ ◯Π→Π◯ id
                                                                  (Is-modal-Π ext λ _ → Is-modal-◯)
                                                                  (λ m →
              ◯Π→Π◯ (η (λ x → Is-modal→Stable (m x) (f x)))          ≡⟨ ◯Π→Π◯-η ext ⟩
              (λ x → η (Is-modal→Stable (m x) (f x)))                ≡⟨⟩
              (λ x → η (η⁻¹ (m x) (f x)))                            ≡⟨ (apply-ext ext λ _ → η-η⁻¹) ⟩∎
              f                                                      ∎) ⟩∎

            f                                                ∎))
  where
  to =
    ((x : A) → ◯ (P x))    →⟨ η ⟩
    ◯ ((x : A) → ◯ (P x))  →⟨ ◯Π◯≃◯Π _ ⟩□
    ◯ ((x : A) → P x)      □

-- A "computation rule" for Π◯≃◯Π.

Π◯≃◯Π-η :
  Extensionality a a →
  Π◯≃◯Π _ (η ∘ f) ≡ η f
Π◯≃◯Π-η {f = f} ext =
  Π◯≃◯Π _ (η ∘ f)        ≡⟨ cong (Π◯≃◯Π _) $ sym $ ◯Π→Π◯-η ext ⟩
  Π◯≃◯Π _ (◯Π→Π◯ (η f))  ≡⟨ _≃_.right-inverse-of (Π◯≃◯Π ext) _ ⟩∎
  η f                    ∎

-- Π◯≃◯Π commutes with ◯-map in a certain way (assuming function
-- extensionality).

Π◯≃◯Π-◯-map :
  {f : ∀ {x} → P x → Q x} {g : (x : A) → ◯ (P x)} →
  Extensionality a a →
  Π◯≃◯Π _ (◯-map f ∘ g) ≡ ◯-map (f ∘_) (Π◯≃◯Π _ g)
Π◯≃◯Π-◯-map {f = f} {g = g} ext =
  Π◯≃◯Π _ (◯-map f ∘ g)                                  ≡⟨⟩
  ◯Π◯≃◯Π _ (η (◯-map f ∘ g))                             ≡⟨ sym $
                                                            ◯Π◯≃◯Π-η′
                                                              (◯-map (f ∘_))
                                                              (λ g → ◯Π◯≃◯Π _ (η (◯-map f ∘ g)))
                                                              Is-modal-◯
                                                              (λ m₁ →
                                                                 sym $
                                                                 ◯-elim
                                                                   {P = λ m₂ →
                                                                          M.◯Π◯≃◯Π m₂ _ (η (◯-map f ∘ g)) ≡
                                                                          ◯-map (f ∘_) (η λ x → Is-modal→Stable (m₁ x) (g x))}
                                                                   (λ _ → Separated-◯ _ _)
                                                                   (λ m₂ →
    M.◯Π◯≃◯Π (η m₂) _ (η (◯-map f ∘ g))                               ≡⟨ M.◯Π◯≃◯Π-η ⟩
    η (λ x → Is-modal→Stable (m₂ x) (◯-map f (g x)))                  ≡⟨ (cong η $
                                                                          apply-ext ext λ x →
                                                                          ◯-elim
                                                                            {P = λ y →
                                                                                   Is-modal→Stable (m₂ x) (◯-map f y) ≡
                                                                                   f (Is-modal→Stable (m₁ x) y)}
                                                                            (λ _ → Is-modal→Separated (m₂ x) _ _)
                                                                            (λ y →
      Is-modal→Stable (m₂ x) (◯-map f (η y))                                   ≡⟨ cong (Is-modal→Stable (m₂ x)) ◯-map-η ⟩
      Is-modal→Stable (m₂ x) (η (f y))                                         ≡⟨ Is-modal→Stable-η ⟩
      f y                                                                      ≡⟨ cong f $ sym Is-modal→Stable-η ⟩∎
      f (Is-modal→Stable (m₁ x) (η y))                                         ∎)
                                                                            (g x)) ⟩
    η (λ x → f (Is-modal→Stable (m₁ x) (g x)))                        ≡⟨ sym ◯-map-η ⟩∎
    ◯-map (f ∘_) (η λ x → Is-modal→Stable (m₁ x) (g x))               ∎)
                                                                   ◯-Π-Is-modal) ⟩

  ◯-map (f ∘_) (◯Π◯≃◯Π _ (η g))                          ≡⟨⟩
  ◯-map (f ∘_) (Π◯≃◯Π _ g)                               ∎

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
  m₁ = _

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

-- If f has type A → B, where A is modal and B is separated, then
-- Is-equivalence f is k-stable (perhaps assuming function
-- extensionality).

Is-modal→Stable-Is-equivalence :
  {f : A → B} →
  Extensionality? k a a →
  Is-modal A → Separated B →
  Stable-[ k ] (Is-equivalence f)
Is-modal→Stable-Is-equivalence {k = k} {f = f} ext m s =
                                              $⟨ s′ ⟩
  Stable-[ k ] (∀ y → Contractible (f ⁻¹ y))  →⟨ Stable-respects-↝ ext $ inverse-ext?
                                                 Is-equivalence≃Is-equivalence-CP ⟩□
  Stable-[ k ] (Is-equivalence f)             □
  where
  s′ =
    Stable-Π ext λ y →
    let m′ : Is-modal (f ⁻¹ y)
        m′ = Is-modal-Σ m (λ _ → s _ _) in
    Stable-Σ m′ λ _ →
    Stable-Π ext λ _ →
    Is-modal→Stable (Is-modal→Separated m′ _ _)

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
-- Some lemmas related to W

-- W (◯ A) P implies ◯ (W A (P ∘ η)).

W◯→◯Wη :
  (P : ◯ A → Type a) →
  W (◯ A) P → ◯ (W A (P ∘ η))
W◯→◯Wη {A = A} P (sup x f) =
  ◯-elim′
    {P = λ x → (P x → ◯ (W A (P ∘ η))) → ◯ (W A (P ∘ η))}
    (λ _ → M.Stable-Π λ _ → Is-modal→Stable Is-modal-◯)
    (λ x f →
       ◯-map (sup x)
         (                             $⟨ f ⟩
          (P (η x) → ◯ (W A (P ∘ η)))  →⟨ Π◯≃◯Π _ ⟩□
          ◯ ((P ∘ η) x → W A (P ∘ η))  □))
    x (λ y → W◯→◯Wη P (f y))

-- A "computation rule" for W◯→◯Wη.

W◯→◯Wη-sup-η :
  {P : ◯ A → Type a} →
  Extensionality a a →
  (f : P (η x) → W (◯ A) P) →
  W◯→◯Wη P (sup (η x) f) ≡ ◯-map (sup x) (Π◯≃◯Π _ (W◯→◯Wη P ∘ f))
W◯→◯Wη-sup-η {A = A} {x = x} {P = P} ext f =
  ◯-elim′
    {P = λ x → (P x → ◯ (W A (P ∘ η))) → ◯ (W A (P ∘ η))}
    (λ _ → M.Stable-Π λ _ → Is-modal→Stable Is-modal-◯)
    (λ x f → ◯-map (sup x) (Π◯≃◯Π _ f))
    (η x) (W◯→◯Wη P ∘ f)                                       ≡⟨ (cong
                                                                     (λ m →
                                                                        ◯-elim′
                                                                          {P = λ x → (P x → ◯ (W A (P ∘ η))) → ◯ (W A (P ∘ η))}
                                                                          m (λ x f → ◯-map (sup x) (Π◯≃◯Π _ f))
                                                                          (η x) (W◯→◯Wη P ∘ f)) $
                                                                   apply-ext ext λ _ →
                                                                   Stable-Π-Is-modal-Π ext) ⟩
  ◯-elim′
    {P = λ x → (P x → ◯ (W A (P ∘ η))) → ◯ (W A (P ∘ η))}
    (λ _ → Is-modal→Stable $ Is-modal-Π ext λ _ → Is-modal-◯)
    (λ x f → ◯-map (sup x) (Π◯≃◯Π _ f))
    (η x) (W◯→◯Wη P ∘ f)                                       ≡⟨ cong (_$ (W◯→◯Wη P ∘ f)) $
                                                                  ◯-elim′-Is-modal→Stable-η ⟩∎
  ◯-map (sup x) (Π◯≃◯Π _ (W◯→◯Wη P ∘ f))                       ∎

-- A lemma relating W◯→◯Wη and W-map η id.

W◯→◯Wη-W-map-η-id :
  Extensionality a a →
  W◯→◯Wη P (W-map η id x) ≡ η x
W◯→◯Wη-W-map-η-id {P = P} {x = sup x f} ext =
  W◯→◯Wη P (W-map η id (sup x f))                            ≡⟨⟩
  W◯→◯Wη P (sup (η x) λ y → W-map η id (f y))                ≡⟨ W◯→◯Wη-sup-η ext (λ y → W-map η id (f y)) ⟩
  ◯-map (sup x) (Π◯≃◯Π _ λ y → W◯→◯Wη P (W-map η id (f y)))  ≡⟨ (cong (◯-map (sup x)) $ cong (Π◯≃◯Π _) $ apply-ext ext λ y →
                                                                 W◯→◯Wη-W-map-η-id {x = f y} ext) ⟩
  ◯-map (sup x) (Π◯≃◯Π _ (η ∘ f))                            ≡⟨ cong (◯-map (sup x)) $
                                                                Π◯≃◯Π-η ext ⟩
  ◯-map (sup x) (η f)                                        ≡⟨ ◯-map-η ⟩∎
  η (sup x f)                                                ∎

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
    (λ _ → Is-modal-Π ext λ _ →
           Is-modal-Π ext λ _ →
           Separated-◯ _ _)
    (λ x f hyp →
       ◯-map (W-map η id) (W◯→◯Wη P (sup (η x) f))                   ≡⟨ cong (◯-map (W-map η id)) $ W◯→◯Wη-sup-η ext f ⟩

       ◯-map (W-map η id) (◯-map (sup x) (Π◯≃◯Π _ (W◯→◯Wη P ∘ f)))   ≡⟨ sym ◯-map-∘ ⟩

       ◯-map (W-map η id ∘ sup x) (Π◯≃◯Π _ (W◯→◯Wη P ∘ f))           ≡⟨⟩

       ◯-map (sup (η x) ∘ (W-map η id ∘_)) (Π◯≃◯Π _ (W◯→◯Wη P ∘ f))  ≡⟨ ◯-map-∘ ⟩

       ◯-map (sup (η x))
         (◯-map (W-map η id ∘_) (Π◯≃◯Π _ (W◯→◯Wη P ∘ f)))            ≡⟨ cong (◯-map (sup (η x))) $ sym $
                                                                        Π◯≃◯Π-◯-map ext ⟩
       ◯-map (sup (η x))
         (Π◯≃◯Π _ (◯-map (W-map η id) ∘ (W◯→◯Wη P ∘ f)))             ≡⟨ cong (◯-map (sup (η x)) ∘ Π◯≃◯Π _) $ apply-ext ext
                                                                        hyp ⟩

       ◯-map (sup (η x)) (Π◯≃◯Π _ (η ∘ f))                           ≡⟨ cong (◯-map (sup (η x))) $ Π◯≃◯Π-η ext ⟩

       ◯-map (sup (η x)) (η f)                                       ≡⟨ ◯-map-η ⟩∎

       η (sup (η x) f)                                               ∎)
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
  to   = ◯-rec Is-modal-◯ (W◯→◯Wη P)
  from = ◯-map (W-map η id)

  to-from :
    Extensionality a a →
    ∀ x → to (from x) ≡ x
  to-from ext =
    ◯-elim
      (λ _ → Separated-◯ _ _)
      (λ x →
         to (from (η x))                                         ≡⟨⟩
         ◯-rec Is-modal-◯ (W◯→◯Wη P) (◯-map (W-map η id) (η x))  ≡⟨ ◯-rec-◯-map ⟩
         ◯-rec Is-modal-◯ (W◯→◯Wη P ∘ W-map η id) (η x)          ≡⟨ ◯-rec-η ⟩
         W◯→◯Wη P (W-map η id x)                                 ≡⟨ W◯→◯Wη-W-map-η-id ext ⟩∎
         η x                                                     ∎)

  from-to :
    Extensionality a a →
    ∀ x → from (to x) ≡ x
  from-to ext =
    ◯-elim
      (λ _ → Separated-◯ _ _)
      (λ x →
         from (to (η x))                                         ≡⟨⟩
         ◯-map (W-map η id) (◯-rec Is-modal-◯ (W◯→◯Wη P) (η x))  ≡⟨ cong (◯-map (W-map η id)) ◯-rec-η ⟩
         ◯-map (W-map η id) (W◯→◯Wη P x)                         ≡⟨ ◯-map-W-map-η-id-W◯→◯Wη ext ⟩∎
         η x                                                     ∎)

-- An unfolding lemma for ◯ (W A (P ∘ η)).

◯Wη≃Σ◯Π◯Wη :
  {P : ◯ A → Type a} →
  ◯ (W A (P ∘ η)) ↝[ a ∣ a ] Σ (◯ A) (λ x → P x → ◯ (W A (P ∘ η)))
◯Wη≃Σ◯Π◯Wη {A = A} {P = P} ext =
  ◯ (W A (P ∘ η))                        ↔⟨ ◯-cong-↔ W-unfolding ⟩
  ◯ (Σ A (λ x → P (η x) → W A (P ∘ η)))  ↔⟨ ◯Ση≃Σ◯◯ ⟩
  Σ (◯ A) (λ x → ◯ (P x → W A (P ∘ η)))  ↝⟨ (∃-cong λ _ → inverse-ext? Π◯≃◯Π ext) ⟩□
  Σ (◯ A) (λ x → P x → ◯ (W A (P ∘ η)))  □

-- A "computation rule" for ◯Wη≃Σ◯Π◯Wη.

◯Wη≃Σ◯Π◯Wη-η :
  Extensionality a a →
  ◯Wη≃Σ◯Π◯Wη _ (η (sup x f)) ≡ (η x , η ∘ f)
◯Wη≃Σ◯Π◯Wη-η {x = x} {f = f} ext =
  Σ-map id ◯Π→Π◯
    (◯Ση→Σ◯◯ (◯-map (λ w → headᵂ w , tailᵂ w) (η (sup x f))))  ≡⟨ cong (Σ-map id ◯Π→Π◯ ∘ ◯Ση→Σ◯◯) ◯-map-η ⟩

  Σ-map id ◯Π→Π◯ (◯Ση→Σ◯◯ (η (x , f)))                         ≡⟨ cong (Σ-map id ◯Π→Π◯) ◯-rec-η ⟩

  Σ-map id ◯Π→Π◯ (η x , η f)                                   ≡⟨⟩

  (η x , ◯Π→Π◯ (η f))                                          ≡⟨ cong (_ ,_) $ ◯Π→Π◯-η ext ⟩∎

  (η x , η ∘ f)                                                ∎

-- A lemma relating ◯Wη≃Σ◯Π◯Wη and ◯Wη→Σ◯Π◯Wη.

◯Wη≃Σ◯Π◯Wη≡◯Wη→Σ◯Π◯Wη :
  Extensionality a a →
  ◯Wη≃Σ◯Π◯Wη _ ≡ ◯Wη→Σ◯Π◯Wη {P = P}
◯Wη≃Σ◯Π◯Wη≡◯Wη→Σ◯Π◯Wη ext =
  apply-ext ext $
  ◯-elim
    (λ _ → Is-modal→Separated
              (Is-modal-Σ Is-modal-◯ λ _ →
               Is-modal-Π ext λ _ →
               Is-modal-◯)
              _ _)
    (λ where
       (sup x f) →
         ◯Wη≃Σ◯Π◯Wη _ (η (sup x f))  ≡⟨ ◯Wη≃Σ◯Π◯Wη-η ext ⟩
         (η x , η ∘ f)               ≡⟨ sym $ ◯Wη→Σ◯Π◯Wη-η ext ⟩∎
         ◯Wη→Σ◯Π◯Wη (η (sup x f))    ∎)

-- If the modality is accessibility-modal, then ◯ commutes with W in a
-- certain way (assuming function extensionality).

◯Wη≃W◯ :
  {P : ◯ A → Type a} →
  Accessibility-modal →
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
        (λ _ → Is-modal-Π ext′ λ _ →
               Is-modal-Π ext′ λ _ →
               Separated-W ext′ Separated-◯ _ _)
        (λ x f hyp →
           ◯Wη→W◯ acc ext (W◯→◯Wη P (sup (η x) f))                      ≡⟨ cong (◯Wη→W◯ acc ext) $ W◯→◯Wη-sup-η ext′ f ⟩

           ◯Wη→W◯ acc ext (◯-map (sup x) (Π◯≃◯Π _ (W◯→◯Wη P ∘ f)))      ≡⟨ ◯-elim
                                                                             {P = λ f′ →
                                                                                    ◯Wη→W◯ acc ext (◯-map (sup x) f′) ≡
                                                                                    sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ f′)}
                                                                             (λ _ → Separated-W ext′ Separated-◯ _ _)
                                                                             (λ f′ →
             ◯Wη→W◯ acc ext (◯-map (sup x) (η f′))                              ≡⟨ cong (◯Wη→W◯ acc ext)
                                                                                   ◯-map-η ⟩
             ◯Wη→W◯ acc ext (η (sup x f′))                                      ≡⟨ ◯Wη→W◯-η acc ext ext′ ax ⟩
             W-map η id (sup x f′)                                              ≡⟨⟩
             sup (η x) (W-map η id ∘ f′)                                        ≡⟨ (cong (sup _) $ sym $ apply-ext ext′ λ _ →
                                                                                    ◯Wη→W◯-η acc ext ext′ ax) ⟩
             sup (η x) (◯Wη→W◯ acc ext ∘ η ∘ f′)                                ≡⟨ cong (sup _ ∘ (◯Wη→W◯ acc ext ∘_)) $ sym $
                                                                                   ◯Π→Π◯-η ext′ ⟩∎
             sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ (η f′))                          ∎)
                                                                             _ ⟩

           sup (η x) (◯Wη→W◯ acc ext ∘ ◯Π→Π◯ (Π◯≃◯Π _ (W◯→◯Wη P ∘ f)))  ≡⟨ cong (sup _ ∘ (◯Wη→W◯ acc ext ∘_)) $
                                                                           _≃_.left-inverse-of (Π◯≃◯Π ext′) _ ⟩

           sup (η x) (◯Wη→W◯ acc ext ∘ W◯→◯Wη P ∘ f)                    ≡⟨ cong (sup (η x)) $ apply-ext ext′
                                                                           hyp ⟩∎
           sup (η x) f                                                  ∎)
        x f (λ y → to-from (f y))

-- If the modality is accessibility-modal and A is modal, then W A P
-- is k-stable for symmetric kinds k (assuming function
-- extensionality).

Stable-W :
  Accessibility-modal →
  @0 Extensionality a a →
  Extensionality? ⌊ k ⌋-sym a a →
  Is-modal A →
  Stable-[ ⌊ k ⌋-sym ] (W A P)
Stable-W {A = A} {P = P} acc ext ext′ m =
  ◯ (W A P)                            ↝⟨ (◯-cong-↝-sym ext′ λ ext → W-cong₂ ext λ _ → ≡⇒↝ _ $ cong P $ sym
                                           Is-modal→Stable-η) ⟩
  ◯ (W A (P ∘ Is-modal→Stable m ∘ η))  ↝⟨ ◯Wη≃W◯ acc ext ext′ ⟩
  W (◯ A) (P ∘ Is-modal→Stable m)      ↝⟨ (inverse $ W-cong ext′ (Is-modal→≃◯ m) λ _ → ≡⇒↝ _ $ cong P $ sym
                                           Is-modal→Stable-η) ⟩□
  W A P                                □

-- If the modality is accessibility-modal and A is modal, then W A P
-- is modal (assuming function extensionality).

Is-modal-W :
  Accessibility-modal →
  Extensionality a a →
  Is-modal A →
  Is-modal (W A P)
Is-modal-W {A = A} {P = P} acc ext m =
  Is-equivalence-η→Is-modal $
  _≃_.is-equivalence $
  Eq.with-other-function
    (inverse $ Stable-W acc ext ext m)
    η
    lemma
  where
  P≃ : P x ≃ P (Is-modal→Stable m (η x))
  P≃ = ≡⇒↝ _ $ cong P $ sym Is-modal→Stable-η

  P→ : P x → P (Is-modal→Stable m (η x))
  P→ = _≃_.to P≃

  P← : P (Is-modal→Stable m (η x)) → P x
  P← = _≃_.from P≃

  lemma :
    ∀ x →
    ◯-map (W-map id P→)
      (W◯→◯Wη (P ∘ Is-modal→Stable m) (W-map η P← x)) ≡
    η x
  lemma (sup x f) =
    ◯-map (W-map id P→)
      (W◯→◯Wη (P ∘ Is-modal→Stable m) $ W-map η P← (sup x f))  ≡⟨⟩

    ◯-map (W-map id P→)
      (W◯→◯Wη (P ∘ Is-modal→Stable m) $
       sup (η x) (W-map η P← ∘ f ∘ P←))                        ≡⟨ cong (◯-map _) $
                                                                  W◯→◯Wη-sup-η ext (W-map η P← ∘ f ∘ P←) ⟩
    ◯-map (W-map id P→)
      (◯-map (sup x)
         (Π◯≃◯Π _
            (W◯→◯Wη (P ∘ Is-modal→Stable m) ∘
             W-map η P← ∘ f ∘ P←)))                            ≡⟨ sym ◯-map-∘ ⟩

    ◯-map (sup x ∘ (_∘ P→) ∘ (W-map id P→ ∘_))
      (Π◯≃◯Π _
         (W◯→◯Wη (P ∘ Is-modal→Stable m) ∘
          W-map η P← ∘ f ∘ P←))                                ≡⟨ ◯-map-∘ ⟩

    ◯-map (sup x ∘ (_∘ P→))
      (◯-map (W-map id P→ ∘_)
         (Π◯≃◯Π _
            (W◯→◯Wη (P ∘ Is-modal→Stable m) ∘
             W-map η P← ∘ f ∘ P←)))                            ≡⟨ cong (◯-map _) $ sym $
                                                                  Π◯≃◯Π-◯-map ext ⟩
    ◯-map (sup x ∘ (_∘ P→))
      (Π◯≃◯Π _
         (◯-map (W-map id P→) ∘
          W◯→◯Wη (P ∘ Is-modal→Stable m) ∘
          W-map η P← ∘ f ∘ P←))                                ≡⟨ (cong (◯-map (sup x ∘ (_∘ P→))) $ cong (Π◯≃◯Π _) $
                                                                   apply-ext ext λ y →
                                                                   lemma (f (P← y))) ⟩

    ◯-map (sup x ∘ (_∘ P→)) (Π◯≃◯Π _ (η ∘ f ∘ P←))             ≡⟨ cong (◯-map (sup x ∘ (_∘ P→))) $ cong (Π◯≃◯Π _) $ sym $
                                                                  ◯Π→Π◯-η ext ⟩

    ◯-map (sup x ∘ (_∘ P→)) (Π◯≃◯Π _ (◯Π→Π◯ (η (f ∘ P←))))     ≡⟨ cong (◯-map (sup x ∘ (_∘ P→))) $
                                                                  _≃_.right-inverse-of (Π◯≃◯Π ext) _ ⟩

    ◯-map (sup x ∘ (_∘ P→)) (η (f ∘ P←))                       ≡⟨ ◯-map-η ⟩

    η (sup x (f ∘ P← ∘ P→))                                    ≡⟨ (cong (η ∘ sup x) $ cong (f ∘_) $ apply-ext ext λ _ →
                                                                   _≃_.left-inverse-of P≃ _) ⟩∎
    η (sup x f)                                                ∎

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
  ◯ (∃ λ (f : A → B) → P (◯-map-◯ (η f)))    ↔⟨ ◯Ση≃Σ◯◯ ⟩
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
      (Stable-Π ext λ _ → Is-modal→Stable Is-modal-◯)
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
  ◯↝↝◯↝◯ F↔ ◯∘P↝P∘◯-map P-cong P-stable Σ◯→→Σ◯→◯ _ (η x)             ≡⟨⟩

  (_↔_.from F↔ $ Σ◯→→Σ◯→◯ $ Σ-map id P-stable $ ◯Ση→Σ◯◯ $
   ◯-map (Σ-map id (P-cong _ λ _ → sym ◯-map-◯-ηˡ)) $
   ◯-map (Σ-map id (◯∘P↝P∘◯-map _)) $ ◯-map (Σ-map id η) $
   ◯-map (_↔_.to F↔) (η x))                                    ≡⟨ cong (_↔_.from F↔) $ cong Σ◯→→Σ◯→◯ $ cong (Σ-map id P-stable) $
                                                                  trans
                                                                    (cong ◯Ση→Σ◯◯ $
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
     (_↔_.to F↔ x))                                            ≡⟨ cong (_↔_.from F↔) $ cong Σ◯→→Σ◯→◯ $ cong (_ ,_)
                                                                  P-stable-η ⟩
  (_↔_.from F↔ $ Σ◯→→Σ◯→◯ $
   Σ-map
     η
     (P-cong _ (λ _ → sym ◯-map-◯-ηˡ) ∘ ◯∘P↝P∘◯-map _ ∘ η)
     (_↔_.to F↔ x))                                            ≡⟨ cong (_↔_.from F↔) $
                                                                  hyp _ _ ⟩∎
  _↔_.from F↔ (Σ-map ◯-map (◯∘P↝P∘◯-map _ ∘ η) (_↔_.to F↔ x))  ∎

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
         (◯-map-◯ (η f)  ≡⟨ (apply-ext ext′ λ _ → ◯-map-◯-ηˡ) ⟩∎
          ◯-map f        ∎)
         (subst P (apply-ext ext′ λ _ → ◯-map-◯-ηˡ)
            (P-cong _ (λ _ → sym ◯-map-◯-ηˡ)
               (◯∘P↝P∘◯-map _ (η p)))                                  ≡⟨ cong (subst P _) $
                                                                          cong (λ eq → P-cong _ eq (◯∘P↝P∘◯-map _ (η p))) $
                                                                          trans (sym $ _≃_.left-inverse-of (Eq.extensionality-isomorphism ext) _) $
                                                                          cong ext⁻¹ $
                                                                          Eq.good-ext-sym ext _ ⟩
          subst P (apply-ext ext′ λ _ → ◯-map-◯-ηˡ)
            (P-cong _ (ext⁻¹ $ sym $ apply-ext ext′ λ _ → ◯-map-◯-ηˡ)
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
  where
  ext′ = Eq.good-ext ext

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
  ◯↝↝◯↝◯′
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
  ◯↝↝◯↝◯′
    Eq.≃-as-Σ
    ◯-Is-equivalence≃Is-equivalence
    Is-equivalence-cong
    (λ ext → Eq.propositional ext _ _ _)
    (Is-modal→Stable-Is-equivalence ext Is-modal-◯ Separated-◯)
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
  ◯↝↝◯↝◯′
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
                                                                                (Separated-◯ _ _) (Is-modal→Separated (Separated-◯ _ _)))
                                                                             ext ⟩
  (∀ x y →
     Is-equivalence
       (cong (◯-map f) ⦂ (x ≡ η y → ◯-map f x ≡ ◯-map f (η y))))        ↝⟨ (∀-cong ext λ _ →
                                                                            inverse-ext?
                                                                              (Π◯↝Πη λ ext _ →
                                                                               Is-modal→Stable-Is-equivalence ext
                                                                                 (Separated-◯ _ _) (Is-modal→Separated (Separated-◯ _ _)))
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
     Is-modal→Stable-Is-equivalence ext
       (Separated-◯ _ _) (Is-modal→Separated (Separated-◯ _ _)))
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

  private
    open module MBC = Modality.Box-cong eq ax M
      hiding (Is-modal→Stable-Is-equivalenceᴱ; ◯-cong-◯)

  private
    module BC       = E.[]-cong₁ ax
    module EC       = E₂.[]-cong₂-⊔ ax ax ax
    module BC-ECP   = ECP.[]-cong₂ ax ax
    module BC-ECP-⊔ = ECP.[]-cong₂-⊔ ax ax ax

  ----------------------------------------------------------------------
  -- Some equivalences

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

  ----------------------------------------------------------------------
  -- Some results related to stability

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

  -- If f has type A → B, where A is modal and B is separated, then
  -- ECP.Is-equivalenceᴱ f is k-stable (perhaps assuming function
  -- extensionality).

  Is-modal→Stable-Is-equivalenceᴱ-CP :
    {@0 f : A → B} →
    Extensionality? k a a →
    Is-modal A → @0 Separated B →
    Stable-[ k ] (ECP.Is-equivalenceᴱ f)
  Is-modal→Stable-Is-equivalenceᴱ-CP {f = f} ext m s =
    Stable-Π ext λ y →
    let m′ : Is-modal (f ⁻¹ᴱ y)
        m′ = Is-modal-Σ m λ _ → Is-modal-Erased (s _ _) in
    Stable-Σ m′ λ _ →
    Stable-Erased ext (
    Stable-Π ext λ _ →
    Is-modal→Stable (Is-modal→Separated m′ _ _))

  -- If f has type A → B, where A is modal and B is separated, then
  -- Is-equivalenceᴱ f is k-stable (perhaps assuming function
  -- extensionality).

  Is-modal→Stable-Is-equivalenceᴱ :
    {@0 f : A → B} →
    Extensionality? k a a →
    Is-modal A → @0 Separated B →
    Stable-[ k ] (Is-equivalenceᴱ f)
  Is-modal→Stable-Is-equivalenceᴱ {k = k} {f = f} ext m s =
    generalise-ext?′
      (Stable→Stable-⇔ $ MBC.Is-modal→Stable-Is-equivalenceᴱ m s)
      (λ ext → Is-modal→Stable $ Is-modal-Is-equivalenceᴱ ext m s)
      Is-modal→Stable-≃ᴱ-Is-equivalenceᴱ
      ext
    where
    Is-modal→Stable-≃ᴱ-Is-equivalenceᴱ :
      @0 Extensionality a a →
      Stable-[ equivalenceᴱ ] (Is-equivalenceᴱ f)
    Is-modal→Stable-≃ᴱ-Is-equivalenceᴱ ext =
                                                               $⟨ s′ ⟩
      Stable-[ equivalenceᴱ ] (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  →⟨ Stable-respects-↝-sym $ inverse $
                                                                  EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext ⟩□
      Stable-[ equivalenceᴱ ] (Is-equivalenceᴱ f)              □
      where
      ext′ = E.[ ext ]

      s′ =
        Stable-Π ext′ λ y →
        let m′ : Is-modal (f ⁻¹ᴱ y)
            m′ = Is-modal-Σ m λ _ → Is-modal-Erased (s _ _) in
        Stable-Σ m′ λ _ →
        Stable-Erased ext′ (
        Stable-Π ext′ λ _ →
        Is-modal→Stable (Is-modal→Separated m′ _ _))

  ----------------------------------------------------------------------
  -- More equivalences

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
                                                                              ◯≡≃η≡η) ⟩
    ◯ (∃ λ (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
       ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
       (x : A) → η (cong f (f⁻¹-f x)) ≡ η (f-f⁻¹ (f x)))                  ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ sym $ cong₂ _≡_ ◯-map-η ◯-map-η) ⟩
    ◯ (∃ λ (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
       ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
       (x : A) →
       ◯-map (cong f ∘ (_$ x)) (η f⁻¹-f) ≡ ◯-map (_$ f x) (η f-f⁻¹))      ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse (Π◯≃◯Π ext)) F.∘
                                                                             (∃-cong λ _ → ◯Ση≃Σ◯◯) F.∘
                                                                             ◯Ση≃Σ◯◯ ⟩
    (∃ λ (f-f⁻¹ : ◯ (∀ x → f (f⁻¹ x) ≡ x)) →
     ∃ λ (f⁻¹-f : ◯ (∀ x → f⁻¹ (f x) ≡ x)) →
     (x : A) → ◯ (◯-map (cong f ∘ (_$ x)) f⁻¹-f ≡ ◯-map (_$ f x) f-f⁻¹))  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ → inverse $
                                                                              Is-modal→≃◯ $ Separated-◯ _ _) ⟩
    (∃ λ (f-f⁻¹ : ◯ (∀ x → f (f⁻¹ x) ≡ x)) →
     ∃ λ (f⁻¹-f : ◯ (∀ x → f⁻¹ (f x) ≡ x)) →
     (x : A) → ◯-map (cong f ∘ (_$ x)) f⁻¹-f ≡ ◯-map (_$ f x) f-f⁻¹)      ↝⟨ (Σ-cong (lemma₂ _ _) λ _ →
                                                                              Σ-cong (lemma₂ _ _) λ _ →
                                                                              ∀-cong ext λ _ → lemma₃ _ _ _) ⟩
    (∃ λ (f-f⁻¹ : ∀ x → ◯-map f (◯-map f⁻¹ x) ≡ x) →
     ∃ λ (f⁻¹-f : ∀ x → ◯-map f⁻¹ (◯-map f x) ≡ x) →
     (x : A) → cong (◯-map f) (f⁻¹-f (η x)) ≡ f-f⁻¹ (◯-map f (η x)))      ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse $
                                                                              Π◯≃Πη ext λ _ →
                                                                              Is-modal→Stable $ Is-modal→Separated (Separated-◯ _ _) _ _) ⟩
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
    s _ = Is-modal→Stable $ Separated-◯ _ _

    abstract

      lemma₂ :
        {A B : Type a} (g : A → B) (h : B → A) →
        ◯ ((x : B) → g (h x) ≡ x) ≃
        ((x : ◯ B) → ◯-map g (◯-map h x) ≡ x)
      lemma₂ {B = B} g h =
        ◯ ((x : B) → g (h x) ≡ x)                  ↝⟨ inverse (Π◯≃◯Π ext) ⟩
        ((x : B) → ◯ (g (h x) ≡ x))                ↝⟨ (∀-cong ext λ _ → ◯≡≃η≡η) ⟩
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
        (λ _ → Is-modal→Separated (Separated-◯ _ _) _ _)
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
      ◯-elim (λ _ → Is-modal-Π ext λ _ → m) λ f-f⁻¹ →
      ◯-elim (λ _ → m) λ f⁻¹-f →

        ◯-map (cong f ∘ (_$ x)) (η f⁻¹-f) ≡ ◯-map (_$ f x) (η f-f⁻¹)  ↝⟨ ≡⇒↝ _ $ cong₂ _≡_ ◯-map-η ◯-map-η ⟩

        η (cong f (f⁻¹-f x)) ≡ η (f-f⁻¹ (f x))                        ↝⟨ inverse $ Eq.≃-≡ ◯≡≃η≡η ⟩

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
        Is-modal
          ((◯-map (cong f ∘ (_$ x)) f⁻¹-f ≡ ◯-map (_$ f x) f-f⁻¹) ≃
           (cong (◯-map f) (_≃_.to (lemma₂ f⁻¹ f) f⁻¹-f (η x)) ≡
            _≃_.to (lemma₂ f f⁻¹) f-f⁻¹ (◯-map f (η x))))
      m =
        Is-modal-≃ ext (Separated-◯ _ _) $
        Is-modal→Separated (Separated-◯ _ _) _ _

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

      ◯ (∃ λ (f⁻¹ : B → A) → Erased (HA.Proofs f f⁻¹))                      ↔⟨ inverse ◯Σ◯≃◯Σ ⟩

      ◯ (∃ λ (f⁻¹ : B → A) → ◯ (Erased (HA.Proofs f f⁻¹)))                  ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯-Erased≃Erased-◯ ext) ⟩

      ◯ (∃ λ (f⁻¹ : B → A) → Erased (◯ (HA.Proofs f f⁻¹)))                  ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → EC.Erased-cong (
                                                                                ◯-Half-adjoint-proofs≃Half-adjoint-proofs-◯-map-◯-map ext)) ⟩

      ◯ (∃ λ (f⁻¹ : B → A) → Erased (HA.Proofs (◯-map f) (◯-map f⁻¹)))      ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $
                                                                                cong (λ g → Erased (HA.Proofs (◯-map f) g)) $ sym $
                                                                                apply-ext ext λ _ → ◯-map-◯-ηˡ) ⟩
      ◯ (∃ λ (f⁻¹ : B → A) →
           Erased (HA.Proofs (◯-map f) (◯-map-◯ (η f⁻¹))))                  ↝⟨ ◯Ση≃Σ◯◯ ⟩

      (∃ λ (f⁻¹ : ◯ (B → A)) →
         ◯ (Erased (HA.Proofs (◯-map f) (◯-map-◯ f⁻¹))))                    ↝⟨ (∃-cong λ _ →
                                                                                Is-modal→Stable $
                                                                                Is-modal-Erased (
                                                                                Is-modal-Σ (Is-modal-Π ext λ _ → Separated-◯ _ _) λ _ →
                                                                                Is-modal-Σ (Is-modal-Π ext λ _ → Separated-◯ _ _) λ _ →
                                                                                Is-modal-Π ext λ _ →
                                                                                Is-modal→Separated (Separated-◯ _ _) _ _)) ⟩

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
    ◯↝↝◯↝◯
      {P = λ f → ECP.Is-equivalenceᴱ f}
      F.id
      ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP
      (λ ext f≡g → ECP.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax ext f≡g)
      (Is-modal→Stable-Is-equivalenceᴱ-CP ext Is-modal-◯ Separated-◯)
      (Σ◯→↝Σ◯→◯-Is-equivalenceᴱ-CP ext)
      ext

  -- ◯ commutes with _≃ᴱ_ (assuming function extensionality).

  ◯≃ᴱ≃◯≃ᴱ◯ : ◯ (A ≃ᴱ B) ↝[ a ∣ a ] (◯ A ≃ᴱ ◯ B)
  ◯≃ᴱ≃◯≃ᴱ◯ ext =
    ◯↝↝◯↝◯
      (from-equivalence EEq.≃ᴱ-as-Σ)
      ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ
      (λ ext f≡g → EEq.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax ext f≡g)
      (Is-modal→Stable-Is-equivalenceᴱ ext Is-modal-◯ Separated-◯)
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
