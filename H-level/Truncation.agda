------------------------------------------------------------------------
-- Truncation
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly following the HoTT book.

open import Equality

module H-level.Truncation
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude
open import Logical-equivalence using (_⇔_)

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Equality.Decidable-UIP eq
open import Equivalence eq as Eq hiding (_∘_; inverse)
open import Function-universe eq as F hiding (_∘_)
open import H-level eq
open import H-level.Closure eq

-- Truncation.

∥_∥ : ∀ {a} → Set a → ℕ → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
∥ A ∥ n ℓ = (P : Set ℓ) → H-level n P → (A → P) → P

-- If A is inhabited, then ∥ A ∥ n ℓ is also inhabited.

∣_∣ : ∀ {n ℓ a} {A : Set a} → A → ∥ A ∥ n ℓ
∣ x ∣ = λ _ _ f → f x

-- The truncation produces types of the right h-level (assuming
-- extensionality).

truncation-has-correct-h-level :
  ∀ n {ℓ a} {A : Set a} →
  Extensionality (a ⊔ lsuc ℓ) (a ⊔ ℓ) →
  H-level n (∥ A ∥ n ℓ)
truncation-has-correct-h-level n {ℓ} {a} ext =
  Π-closure (lower-extensionality a            lzero ext) n λ _ →
  Π-closure (lower-extensionality (a ⊔ lsuc ℓ) lzero ext) n λ h →
  Π-closure (lower-extensionality (lsuc ℓ)     a     ext) n λ _ →
  h

-- Primitive "recursion" for truncated types.

rec :
  ∀ {n a b} {A : Set a} {B : Set b} →
  H-level n B →
  (A → B) → ∥ A ∥ n b → B
rec h f x = x _ h f

private

  -- The function rec computes in the right way.

  rec-∣∣ :
    ∀ {n a b} {A : Set a} {B : Set b}
    (h : H-level n B) (f : A → B) (x : A) →
    rec h f ∣ x ∣ ≡ f x
  rec-∣∣ _ _ _ = refl _

-- The universe level can be decreased (unless it is zero).

with-lower-level :
  ∀ ℓ₁ {ℓ₂ a n} {A : Set a} →
  ∥ A ∥ n (ℓ₁ ⊔ ℓ₂) → ∥ A ∥ n ℓ₂
with-lower-level ℓ₁ x =
  λ P h f → lower (x (↑ ℓ₁ P) (↑-closure _ h) (lift ∘ f))

-- The function rec can be used to define a kind of dependently typed
-- eliminator for the propositional truncation (assuming
-- extensionality).

prop-elim :
  ∀ {ℓ a p} {A : Set a} →
  Extensionality (lsuc ℓ ⊔ a) (ℓ ⊔ a ⊔ p) →
  (P : ∥ A ∥ 1 ℓ → Set p) →
  (∀ x → Is-proposition (P x)) →
  ((x : A) → P ∣ x ∣) →
  ∥ A ∥ 1 (lsuc ℓ ⊔ a ⊔ p) → (x : ∥ A ∥ 1 ℓ) → P x
prop-elim {ℓ} {a} {p} {A} ext P P-prop f =
  rec {A = A}
      {B = ∀ x → P x}
      (Π-closure (lower-extensionality lzero (ℓ ⊔ a) ext) 1 P-prop)
      (λ x _ → subst P
                     (_⇔_.to propositional⇔irrelevant
                        (truncation-has-correct-h-level 1
                           (lower-extensionality lzero p ext)) _ _)
                     (f x))

abstract

  -- The eliminator gives the right result, up to propositional
  -- equality, when applied to ∣ x ∣ and ∣ x ∣.

  prop-elim-∣∣ :
    ∀ {ℓ a p} {A : Set a}
    (ext : Extensionality (lsuc ℓ ⊔ a) (ℓ ⊔ a ⊔ p))
    (P : ∥ A ∥ 1 ℓ → Set p)
    (P-prop : ∀ x → Is-proposition (P x))
    (f : (x : A) → P ∣ x ∣) (x : A) →
    prop-elim ext P P-prop f ∣ x ∣ ∣ x ∣ ≡ f x
  prop-elim-∣∣ _ _ P-prop _ _ =
    _⇔_.to propositional⇔irrelevant (P-prop _) _ _

-- The following two results come from "Generalizations of Hedberg's
-- Theorem" by Kraus, Escardó, Coquand and Altenkirch.

-- Types with constant endofunctions are "h-stable" (meaning that
-- "mere inhabitance" implies inhabitance).

constant-endofunction⇒h-stable :
  ∀ {a} {A : Set a} {f : A → A} →
  Constant f → ∥ A ∥ 1 a → A
constant-endofunction⇒h-stable {a} {A} {f} c =
  ∥ A ∥ 1 a                ↝⟨ rec (fixpoint-lemma f c) (λ x → f x , c (f x) x) ⟩
  (∃ λ (x : A) → f x ≡ x)  ↝⟨ proj₁ ⟩□
  A                        □

-- Having a constant endofunction is logically equivalent to being
-- h-stable (assuming extensionality).

constant-endofunction⇔h-stable :
  ∀ {a} {A : Set a} →
  Extensionality (lsuc a) a →
  (∃ λ (f : A → A) → Constant f) ⇔ (∥ A ∥ 1 a → A)
constant-endofunction⇔h-stable ext = record
  { to = λ { (_ , c) → constant-endofunction⇒h-stable c }
  ; from = λ f → f ∘ ∣_∣ , λ x y →

      f ∣ x ∣  ≡⟨ cong f $ _⇔_.to propositional⇔irrelevant
                             (truncation-has-correct-h-level 1 ext) _ _ ⟩∎
      f ∣ y ∣  ∎
  }

-- A simple isomorphism involving propositional truncation.

∥∥×↔ :
  ∀ {ℓ a} {A : Set a} →
  Extensionality (lsuc ℓ ⊔ a) (ℓ ⊔ a) →
  ∥ A ∥ 1 ℓ × A ↔ A
∥∥×↔ {ℓ} {A = A} ext =
  ∥ A ∥ 1 ℓ × A  ↝⟨ ×-comm ⟩
  A × ∥ A ∥ 1 ℓ  ↝⟨ (∃-cong λ a →
                       inverse $ _⇔_.to contractible⇔⊤↔ $
                         propositional⇒inhabited⇒contractible
                           (truncation-has-correct-h-level 1 ext)
                           ∣ a ∣) ⟩
  A × ⊤          ↝⟨ ×-right-identity ⟩□
  A              □

-- Having a constant function into a set is equivalent to having a
-- function from a propositionally truncated type into the set
-- (assuming extensionality). This result is Example 2.2 in "The
-- General Universal Property of the Propositional Truncation" by
-- Kraus.

constant-function≃∥inhabited∥⇒inhabited :
  ∀ {a b} ℓ {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ) →
  Is-set B →
  (∃ λ (f : A → B) → Constant f) ≃ (∥ A ∥ 1 (a ⊔ b ⊔ ℓ) → B)
constant-function≃∥inhabited∥⇒inhabited {a} {b} ℓ {A} {B} ext B-set =
  (∃ λ (f : A → B) → Constant f)                          ↝⟨ Σ-cong (→-cong (lower-extensionality lzero (a ⊔ ℓ) ext)
                                                                            (inverse $ ∥∥×↔ ext)
                                                                            F.id) (λ _ →
                                                               Π-preserves (lower-extensionality lzero ℓ ext)
                                                                           (inverse $ ↔⇒≃ $ ∥∥×↔ ext)
                                                                           (λ _ → F.id)) ⟩
  (∃ λ (f : ∥ A ∥ 1 ℓ′ × A → B) →
     (p : ∥ A ∥ 1 ℓ′ × A) → ∀ y → f p ≡ f (proj₁ p , y))  ↔⟨ Σ-cong currying (λ _ → currying) ⟩

  (∃ λ (f : ∥ A ∥ 1 ℓ′ → A → B) →
     (∥a∥ : ∥ A ∥ 1 ℓ′) → Constant (λ x → f ∥a∥ x))       ↔⟨ inverse ΠΣ-comm ⟩

  (∥ A ∥ 1 ℓ′ → ∃ λ (f : A → B) → Constant f)             ↝⟨ ∀-preserves (lower-extensionality lzero ℓ ext) (inverse ∘ lemma₂) ⟩□

  (∥ A ∥ 1 ℓ′ → B)                                        □

  where
  ℓ′ = a ⊔ b ⊔ ℓ

  lemma₁ : A → B ≃ ∃ λ (f : A → B) → Constant f
  lemma₁ a₀ = ↔⇒≃ (
    B                                                            ↝⟨ inverse ×-right-identity ⟩

    B × ⊤                                                        ↝⟨ (∃-cong λ _ →
                                                                       _⇔_.to contractible⇔⊤↔ $
                                                                         Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 0 λ _ →
                                                                         singleton-contractible _) ⟩
    (∃ λ (f₁ : B) → (a : A) → ∃ λ (b : B) → b ≡ f₁)              ↝⟨ (∃-cong λ _ → ΠΣ-comm) ⟩

    (∃ λ (f₁ : B) → ∃ λ (f : A → B) → (a : A) → f a ≡ f₁)        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse ×-right-identity) ⟩

    (∃ λ (f₁ : B) → ∃ λ (f : A → B) → ((a : A) → f a ≡ f₁) × ⊤)  ↝⟨ (∃-cong λ f₁ → ∃-cong λ f → ∃-cong λ eq →
                                                                       _⇔_.to contractible⇔⊤↔ $
                                                                         propositional⇒inhabited⇒contractible
                                                                           (Π-closure (lower-extensionality _ ℓ       ext) 1 λ _ →
                                                                            Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 1 λ _ →
                                                                            B-set _ _)
                                                                           (λ x y → f x  ≡⟨ eq x ⟩
                                                                                    f₁   ≡⟨ sym (eq y) ⟩∎
                                                                                    f y  ∎)) ⟩
    (∃ λ (f₁ : B) → ∃ λ (f : A → B) →
       ((a : A) → f a ≡ f₁) × Constant f)                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → inverse ×-right-identity) ⟩

    (∃ λ (f₁ : B) → ∃ λ (f : A → B) →
       ((a : A) → f a ≡ f₁) × Constant f × ⊤)                    ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ eq → ∃-cong λ _ →
                                                                       _⇔_.to contractible⇔⊤↔ $
                                                                         propositional⇒inhabited⇒contractible
                                                                           (B-set _ _)
                                                                           (eq a₀)) ⟩
    (∃ λ (f₁ : B) → ∃ λ (f : A → B) →
       ((a : A) → f a ≡ f₁) × Constant f × f a₀ ≡ f₁)            ↝⟨ ∃-comm ⟩

    (∃ λ (f : A → B) → ∃ λ (f₁ : B) →
       ((a : A) → f a ≡ f₁) × Constant f × f a₀ ≡ f₁)            ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩

    (∃ λ (f : A → B) → ∃ λ (f₁ : B) →
       (Constant f × f a₀ ≡ f₁) × ((a : A) → f a ≡ f₁))          ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse ×-assoc) ⟩

    (∃ λ (f : A → B) → ∃ λ (f₁ : B) →
       Constant f × f a₀ ≡ f₁ × ((a : A) → f a ≡ f₁))            ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (f : A → B) → Constant f × ∃ λ (f₁ : B) →
       f a₀ ≡ f₁ × ((a : A) → f a ≡ f₁))                         ↝⟨ (∃-cong λ f → ∃-cong λ const → ∃-cong λ f₁ → ∃-cong λ eq →
                                                                       inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                         propositional⇒inhabited⇒contractible
                                                                           (Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 1 λ _ →
                                                                            B-set _ _)
                                                                           (λ a → f a   ≡⟨ const a a₀ ⟩
                                                                                  f a₀  ≡⟨ eq ⟩∎
                                                                                  f₁    ∎)) ⟩
    (∃ λ (f : A → B) → Constant f × ∃ λ (f₁ : B) →
       f a₀ ≡ f₁ × ⊤)                                            ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ×-right-identity) ⟩

    (∃ λ (f : A → B) → Constant f × ∃ λ (f₁ : B) → f a₀ ≡ f₁)    ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                       inverse $ _⇔_.to contractible⇔⊤↔ $
                                                                         other-singleton-contractible _) ⟩
    (∃ λ (f : A → B) → Constant f × ⊤)                           ↝⟨ (∃-cong λ _ → ×-right-identity) ⟩□

    (∃ λ (f : A → B) → Constant f)                               □)

  -- The forward component of the equivalence above does not depend on
  -- the value a₀ of type A, so we get the following result:

  lemma₂ : ∥ A ∥ 1 ℓ′ → B ≃ ∃ λ (f : A → B) → Constant f
  lemma₂ ∥a∥ =
    ⟨ (λ b → (λ _ → b) , λ _ _ → trans (refl b) (sym (refl b)))
    , rec (Eq.propositional (lower-extensionality _ ℓ ext) _)
          (λ a → _≃_.is-equivalence (lemma₁ a))
          (with-lower-level ℓ ∥a∥)
    ⟩

-- Some properties of an imagined "real" /propositional/ truncation.

module Real-propositional-truncation
  (∥_∥ʳ : ∀ {a} → Set a → Set a)
  (∣_∣ʳ : ∀ {a} {A : Set a} → A → ∥ A ∥ʳ)
  (truncation-is-proposition :
     ∀ {a} {A : Set a} → Is-proposition ∥ A ∥ʳ)
  (recʳ :
    ∀ {a b} {A : Set a} {B : Set b} →
    Is-proposition B →
    (A → B) → ∥ A ∥ʳ → B)
  where

  -- The function recʳ can be used to define a dependently typed
  -- eliminator (assuming extensionality).

  elimʳ :
    ∀ {a p} {A : Set a} →
    Extensionality a p →
    (P : ∥ A ∥ʳ → Set p) →
    (∀ x → Is-proposition (P x)) →
    ((x : A) → P ∣ x ∣ʳ) →
    (x : ∥ A ∥ʳ) → P x
  elimʳ {A = A} ext P P-prop f x =
    recʳ {A = A}
         {B = ∀ x → P x}
         (Π-closure ext 1 P-prop)
         (λ x _ → subst P
                        (_⇔_.to propositional⇔irrelevant
                           truncation-is-proposition _ _)
                        (f x))
         x
         x

  -- The eliminator gives the right result, up to propositional
  -- equality, when applied to ∣ x ∣ʳ.

  elimʳ-∣∣ʳ :
    ∀ {a p} {A : Set a}
    (ext : Extensionality a p)
    (P : ∥ A ∥ʳ → Set p)
    (P-prop : ∀ x → Is-proposition (P x))
    (f : (x : A) → P ∣ x ∣ʳ)
    (x : A) →
    elimʳ ext P P-prop f ∣ x ∣ʳ ≡ f x
  elimʳ-∣∣ʳ ext P P-prop f x =
    _⇔_.to propositional⇔irrelevant (P-prop _) _ _

  -- The "real" propositional truncation is isomorphic to the one
  -- defined above (assuming extensionality).

  isomorphic :
    ∀ {ℓ a} {A : Set a} →
    Extensionality (lsuc (a ⊔ ℓ)) (a ⊔ ℓ) →
    ∥ A ∥ʳ ↔ ∥ A ∥ 1 (a ⊔ ℓ)
  isomorphic {ℓ} ext = record
    { surjection = record
      { logical-equivalence = record
        { to   = recʳ (truncation-has-correct-h-level 1 ext) ∣_∣
        ; from = lower {ℓ = ℓ} ∘
                 rec (↑-closure 1 truncation-is-proposition)
                     (lift ∘ ∣_∣ʳ)
        }
      ; right-inverse-of = λ _ →
          _⇔_.to propositional⇔irrelevant
            (truncation-has-correct-h-level 1 ext) _ _
      }
    ; left-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant
          truncation-is-proposition _ _
    }
