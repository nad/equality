------------------------------------------------------------------------
-- Propositional truncation
------------------------------------------------------------------------

-- Note that this module is experimental: it uses rewrite rules and
-- postulates to encode a higher inductive type.

{-# OPTIONS --without-K --rewriting #-}

-- Partly following the HoTT book.

module H-level.Truncation.Propositional where

open import Equality.Propositional hiding (elim)
open import Prelude
open import Logical-equivalence using (_⇔_)

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equivalence equality-with-J as Eq hiding (id; _∘_; inverse)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
import H-level.Truncation equality-with-J as Trunc
open import Preimage equality-with-J as Preimage using (_⁻¹_)
open import Surjection equality-with-J using (_↠_)

postulate

  -- Propositional truncation.

  ∥_∥ : ∀ {a} → Set a → Set a

  -- If A is inhabited, then ∥ A ∥ is also inhabited.

  ∣_∣ : ∀ {a} {A : Set a} → A → ∥ A ∥

  -- The truncation produces propositions.

  truncation-is-proposition :
    ∀ {a} {A : Set a} → Is-proposition ∥ A ∥

  -- Primitive "recursion" for truncated types.

  rec : ∀ {a b} {A : Set a} {B : Set b} →
        Is-proposition B →
        (A → B) → ∥ A ∥ → B

  -- Computation rule for rec.
  --
  -- NOTE: There is no computation rule corresponding to
  -- truncation-is-proposition.

  rec-∣∣ :
    ∀ {a b} {A : Set a} {B : Set b}
    (B-prop : Is-proposition B) (f : A → B) (x : A) →
    rec B-prop f ∣ x ∣ ≡ f x

  {-# REWRITE rec-∣∣ #-}

-- The propositional truncation defined here is isomorphic to the one
-- defined in H-level.Truncation (assuming extensionality).

∥∥↔∥∥ :
  ∀ ℓ {a} {A : Set a} →
  Extensionality (lsuc (a ⊔ ℓ)) (a ⊔ ℓ) →
  ∥ A ∥ ↔ Trunc.∥ A ∥ 1 (a ⊔ ℓ)
∥∥↔∥∥ ℓ ext = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec (Trunc.truncation-has-correct-h-level 1 ext)
                   Trunc.∣_∣
      ; from = lower {ℓ = ℓ} ∘
               Trunc.rec (↑-closure 1 truncation-is-proposition)
                         (lift ∘ ∣_∣)
      }
    ; right-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant
          (Trunc.truncation-has-correct-h-level 1 ext) _ _
    }
  ; left-inverse-of = λ _ →
      _⇔_.to propositional⇔irrelevant
        truncation-is-proposition _ _
  }

-- Map function.

∥∥-map : ∀ {a b} {A : Set a} {B : Set b} →
         (A → B) → ∥ A ∥ → ∥ B ∥
∥∥-map f = rec truncation-is-proposition (∣_∣ ∘ f)

-- The function rec can be used to define a dependently typed
-- eliminator (assuming extensionality).

elim :
  ∀ {a p} {A : Set a} →
  Extensionality a p →
  (P : ∥ A ∥ → Set p) →
  (∀ x → Is-proposition (P x)) →
  ((x : A) → P ∣ x ∣) →
  (x : ∥ A ∥) → P x
elim ext P P-prop f x =
  rec (Π-closure ext 1 P-prop)
      (λ x _ → subst P
                     (_⇔_.to propositional⇔irrelevant
                        truncation-is-proposition _ _)
                     (f x))
      x
      x

-- The eliminator gives the right result, up to propositional
-- equality, when applied to ∣ x ∣.

elim-∣∣ :
  ∀ {a p} {A : Set a}
  (ext : Extensionality a p)
  (P : ∥ A ∥ → Set p)
  (P-prop : ∀ x → Is-proposition (P x))
  (f : (x : A) → P ∣ x ∣)
  (x : A) →
  elim ext P P-prop f ∣ x ∣ ≡ f x
elim-∣∣ ext P P-prop f x =
  _⇔_.to propositional⇔irrelevant (P-prop _) _ _

-- The truncation operator preserves bijections (assuming
-- extensionality).

∥∥-cong : ∀ {a b} {A : Set a} {B : Set b} →
          Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
          A ↔ B → ∥ A ∥ ↔ ∥ B ∥
∥∥-cong {a} {b} {A} {B} ext A↔B =
  ∥ A ∥                  ↝⟨ ∥∥↔∥∥ b ext ⟩
  Trunc.∥ A ∥ 1 (a ⊔ b)  ↝⟨ Trunc.∥∥-cong ext A↔B ⟩
  Trunc.∥ B ∥ 1 (a ⊔ b)  ↝⟨ inverse (∥∥↔∥∥ a ext) ⟩□
  ∥ B ∥                  □

-- Nested truncations can be flattened.

flatten↠ : ∀ {a} {A : Set a} → ∥ ∥ A ∥ ∥ ↠ ∥ A ∥
flatten↠ = record
  { logical-equivalence = record
    { to   = rec truncation-is-proposition id
    ; from = ∣_∣
    }
  ; right-inverse-of = λ _ → refl
  }

flatten↔ : ∀ {a} {A : Set a} →
           Extensionality a a →
           ∥ ∥ A ∥ ∥ ↔ ∥ A ∥
flatten↔ ext = record
  { surjection      = flatten↠
  ; left-inverse-of = λ x → elim
      ext
      (λ x → ∣ rec truncation-is-proposition id x ∣ ≡ x)
      (λ _ → mono₁ 0 (truncation-is-proposition _ _))
      (λ _ → refl)
      x
  }

-- Surjectivity.

Surjective : ∀ {a b} {A : Set a} {B : Set b} →
             (A → B) → Set (a ⊔ b)
Surjective f = ∀ b → ∥ f ⁻¹ b ∥

-- If the underlying type is a proposition, then truncations of the
-- type are isomorphic to the type itself.

∥∥↔ : ∀ {a} {A : Set a} →
      Is-proposition A → ∥ A ∥ ↔ A
∥∥↔ A-prop = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec A-prop id
      ; from = ∣_∣
      }
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ _ →
      _⇔_.to propositional⇔irrelevant truncation-is-proposition _ _
  }

-- A simple isomorphism involving propositional truncation.

∥∥×↔ : ∀ {a} {A : Set a} → ∥ A ∥ × A ↔ A
∥∥×↔ {A = A} =
  ∥ A ∥ × A  ↝⟨ ×-comm ⟩
  A × ∥ A ∥  ↝⟨ (drop-⊤-right λ a → inverse $
                 _⇔_.to contractible⇔⊤↔ $
                   propositional⇒inhabited⇒contractible
                     truncation-is-proposition
                     ∣ a ∣) ⟩□
  A          □

-- A variant of ∥∥×↔, introduced to ensure that the right-inverse-of
-- proof is, by definition, simple (see right-inverse-of-∥∥×≃ below).

∥∥×≃ :
  ∀ {a} {A : Set a} → (∥ A ∥ × A) ≃ A
∥∥×≃ =
  ⟨ proj₂
  , (λ a → propositional⇒inhabited⇒contractible
             (mono₁ 0 $
                Preimage.bijection⁻¹-contractible ∥∥×↔ a)
             ((∣ a ∣ , a) , refl))
  ⟩

private

  right-inverse-of-∥∥×≃ :
    ∀ {a} {A : Set a} (x : A) →
    _≃_.right-inverse-of ∥∥×≃ x ≡ refl
  right-inverse-of-∥∥×≃ _ = refl

-- ∥_∥ commutes with _×_.

∥∥×∥∥↔∥×∥ :
  ∀ {a b} {A : Set a} {B : Set b} →
  (∥ A ∥ × ∥ B ∥) ↔ ∥ A × B ∥
∥∥×∥∥↔∥×∥ = record
  { surjection = record
    { logical-equivalence = record
      { from = λ p → ∥∥-map proj₁ p , ∥∥-map proj₂ p
      ; to   = λ { (x , y) →
                   rec truncation-is-proposition
                       (λ x → rec truncation-is-proposition
                                  (λ y → ∣ x , y ∣)
                                  y)
                       x }
      }
    ; right-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ →
      _⇔_.to propositional⇔irrelevant
        (×-closure 1 truncation-is-proposition
                     truncation-is-proposition)
        _ _
  }

-- If A is merely inhabited, then the truncation of A is isomorphic to
-- the unit type.

inhabited⇒∥∥↔⊤ :
  ∀ {a} {A : Set a} →
  ∥ A ∥ → ∥ A ∥ ↔ ⊤
inhabited⇒∥∥↔⊤ ∥a∥ =
  inverse $ _⇔_.to contractible⇔⊤↔ $
    propositional⇒inhabited⇒contractible
      truncation-is-proposition
      ∥a∥

-- If A is not inhabited, then the propositional truncation of A is
-- isomorphic to the empty type.

not-inhabited⇒∥∥↔⊥ :
  ∀ {ℓ a} {A : Set a} →
  ¬ A → ∥ A ∥ ↔ ⊥ {ℓ = ℓ}
not-inhabited⇒∥∥↔⊥ {A = A} =
  ¬ A        ↝⟨ (λ ¬a ∥a∥ → rec ⊥-propositional ¬a ∥a∥) ⟩
  ¬ ∥ A ∥    ↝⟨ inverse ∘ ⊥↔uninhabited ⟩□
  ∥ A ∥ ↔ ⊥  □

-- The following two results come from "Generalizations of Hedberg's
-- Theorem" by Kraus, Escardó, Coquand and Altenkirch.

-- Types with constant endofunctions are "h-stable" (meaning that
-- "mere inhabitance" implies inhabitance).

constant-endofunction⇒h-stable :
  ∀ {a} {A : Set a} {f : A → A} →
  Constant f → ∥ A ∥ → A
constant-endofunction⇒h-stable {a} {A} {f} c =
  ∥ A ∥                    ↝⟨ rec (fixpoint-lemma f c) (λ x → f x , c (f x) x) ⟩
  (∃ λ (x : A) → f x ≡ x)  ↝⟨ proj₁ ⟩□
  A                        □

-- Having a constant endofunction is logically equivalent to being
-- h-stable.

constant-endofunction⇔h-stable :
  ∀ {a} {A : Set a} →
  (∃ λ (f : A → A) → Constant f) ⇔ (∥ A ∥ → A)
constant-endofunction⇔h-stable = record
  { to = λ { (_ , c) → constant-endofunction⇒h-stable c }
  ; from = λ f → f ∘ ∣_∣ , λ x y →

      f ∣ x ∣  ≡⟨ cong f $ _⇔_.to propositional⇔irrelevant
                             truncation-is-proposition _ _ ⟩∎
      f ∣ y ∣  ∎
  }

-- The following three lemmas were communicated to me by Nicolai
-- Kraus. (In slightly different form.) They are closely related to
-- Lemma 2.1 in his paper "The General Universal Property of the
-- Propositional Truncation".

-- A variant of ∥∥×≃.

drop-∥∥ :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  Extensionality a b →

  (∥ A ∥ → ∀ x → B x)
    ↔
  (∀ x → B x)
drop-∥∥ {A = A} {B} ext =
  (∥ A ∥ → ∀ x → B x)              ↝⟨ inverse currying ⟩
  ((p : ∥ A ∥ × A) → B (proj₂ p))  ↔⟨ Π-preserves ext ∥∥×≃ (λ _ → F.id) ⟩□
  (∀ x → B x)                      □

-- Another variant of ∥∥×≃.

push-∥∥ :
  ∀ {a b c} {A : Set a} {B : A → Set b} {C : (∀ x → B x) → Set c} →
  Extensionality a (b ⊔ c) →

  (∥ A ∥ → ∃ λ (f : ∀ x → B x) → C f)
    ↔
  (∃ λ (f : ∀ x → B x) → ∥ A ∥ → C f)

push-∥∥ {b = b} {c} {A} {B} {C} ext =

  (∥ A ∥ → ∃ λ (f : ∀ x → B x) → C f)                ↝⟨ ΠΣ-comm ⟩

  (∃ λ (f : ∥ A ∥ → ∀ x → B x) → ∀ ∥x∥ → C (f ∥x∥))  ↔⟨ Σ-cong (drop-∥∥ (lower-extensionality lzero c ext)) (λ f →
                                                        Eq.∀-preserves (lower-extensionality lzero b ext) λ ∥x∥ →
                                                        ≡⇒↝ _ $ cong C $ lower-extensionality lzero c ext λ x →
      f ∥x∥ x                                             ≡⟨ cong (λ ∥x∥ → f ∥x∥ x) $
                                                             _⇔_.to propositional⇔irrelevant truncation-is-proposition _ _ ⟩∎
      f ∣ x ∣ x                                           ∎) ⟩□

  (∃ λ (f : ∀ x → B x) → ∥ A ∥ → C (λ x → f x))      □

-- This is an instance of a variant of Lemma 2.1 from "The General
-- Universal Property of the Propositional Truncation" by Kraus.

drop-∥∥₃ :
  ∀ {a b c d}
    {A : Set a} {B : A → Set b} {C : A → (∀ x → B x) → Set c}
    {D : A → (f : ∀ x → B x) → (∀ x → C x f) → Set d} →
  Extensionality a (a ⊔ b ⊔ c ⊔ d) →

  (∥ A ∥ →
   ∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)
    ↔
  (∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)

drop-∥∥₃ {a} {b} {c} {A = A} {B} {C} {D} ext =
  (∥ A ∥ →
   ∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)  ↝⟨ push-∥∥ ext ⟩

  (∃ λ (f : ∀ x → B x) →
   ∥ A ∥ → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)                ↝⟨ (∃-cong λ _ →
                                                                     push-∥∥ (lower-extensionality lzero b ext)) ⟩
  (∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) →
   ∥ A ∥ → ∀ x → D x f g)                                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                     drop-∥∥ (lower-extensionality lzero (a ⊔ b ⊔ c) ext)) ⟩□
  (∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)  □

-- Having a coherently constant function into a groupoid is equivalent
-- to having a function from a propositionally truncated type into the
-- groupoid (assuming extensionality). This result is Proposition 2.3
-- in "The General Universal Property of the Propositional Truncation"
-- by Kraus.

Coherently-constant :
  ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Coherently-constant f =
  ∃ λ (c : Constant f) →
  ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃

coherently-constant-function≃∥inhabited∥⇒inhabited :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
  H-level 3 B →
  (∃ λ (f : A → B) → Coherently-constant f) ≃ (∥ A ∥ → B)
coherently-constant-function≃∥inhabited∥⇒inhabited {a} {b} {A} {B}
                                                   ext B-groupoid =
  (∃ λ (f : A → B) → Coherently-constant f)  ↝⟨ Trunc.coherently-constant-function≃∥inhabited∥⇒inhabited lzero ext B-groupoid ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)                ↔⟨ →-cong (lower-extensionality lzero a ext)
                                                       (inverse $ ∥∥↔∥∥ (a ⊔ b) ext) F.id ⟩□
  (∥ A ∥ → B)                                □

-- Having a constant function into a set is equivalent to having a
-- function from a propositionally truncated type into the set
-- (assuming extensionality). The statement of this result is that of
-- Proposition 2.2 in "The General Universal Property of the
-- Propositional Truncation" by Kraus, but it uses a different proof:
-- as observed by Kraus this result follows from Proposition 2.3.

constant-function≃∥inhabited∥⇒inhabited :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
  Is-set B →
  (∃ λ (f : A → B) → Constant f) ≃ (∥ A ∥ → B)
constant-function≃∥inhabited∥⇒inhabited {a} {b} {A} {B} ext B-set =
  (∃ λ (f : A → B) → Constant f)  ↝⟨ Trunc.constant-function≃∥inhabited∥⇒inhabited lzero ext B-set ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)     ↔⟨ →-cong (lower-extensionality lzero a ext)
                                            (inverse $ ∥∥↔∥∥ (a ⊔ b) ext) F.id ⟩□
  (∥ A ∥ → B)                     □

-- The propositional truncation's universal property (defined using
-- extensionality).
--
-- As observed by Kraus this result follows from Proposition 2.2 in
-- his "The General Universal Property of the Propositional
-- Truncation".

universal-property :
  ∀ {a b} {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b)) (a ⊔ b) →
  Is-proposition B →
  (∥ A ∥ → B) ≃ (A → B)
universal-property {a} {b} {A} {B} ext B-prop =
  (∥ A ∥ → B)                  ↔⟨ →-cong (lower-extensionality lzero a ext)
                                         (∥∥↔∥∥ (a ⊔ b) ext) F.id ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)  ↝⟨ Trunc.universal-property lzero ext B-prop ⟩□
  (A → B)                      □

private

  -- The universal property computes in the right way.

  to-universal-property :
    ∀ {a b} {A : Set a} {B : Set b}
    (ext : Extensionality (lsuc (a ⊔ b)) (a ⊔ b))
    (B-prop : Is-proposition B)
    (f : ∥ A ∥ → B) →
    _≃_.to (universal-property ext B-prop) f ≡ f ∘ ∣_∣
  to-universal-property _ _ _ = refl

  from-universal-property :
    ∀ {a b} {A : Set a} {B : Set b}
    (ext : Extensionality (lsuc (a ⊔ b)) (a ⊔ b))
    (B-prop : Is-proposition B)
    (f : A → B) (x : A) →
    _≃_.from (universal-property ext B-prop) f ∣ x ∣ ≡ f x
  from-universal-property _ _ _ _ = refl

-- The axiom of choice, in one of the alternative forms given in the
-- HoTT book (§3.8).

Axiom-of-choice : (a b : Level) → Set (lsuc (a ⊔ b))
Axiom-of-choice a b =
  {A : Set a} {B : A → Set b} →
  Is-set A → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥
