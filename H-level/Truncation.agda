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

open import Bijection eq hiding (_∘_)
open Derived-definitions-and-properties eq
open import Equality.Decidable-UIP eq
open import Function-universe eq hiding (_∘_)
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
