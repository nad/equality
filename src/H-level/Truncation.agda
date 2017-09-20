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

open import Bijection eq as Bijection using (_↔_)
open Derived-definitions-and-properties eq
open import Embedding eq hiding (_∘_)
open import Equality.Decidable-UIP eq
import Equality.Groupoid eq as EG
open import Equivalence eq as Eq hiding (_∘_; inverse)
open import Function-universe eq as F hiding (_∘_)
open import Groupoid eq
open import H-level eq as H-level
open import H-level.Closure eq
open import Nat eq
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq using (_↠_)

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

-- Map function.

∥∥-map : ∀ {n a b ℓ} {A : Set a} {B : Set b} →
         (A → B) →
         ∥ A ∥ n ℓ → ∥ B ∥ n ℓ
∥∥-map f x = λ P h g → x P h (g ∘ f)

-- The truncation operator preserves logical equivalences.

∥∥-cong-⇔ : ∀ {n a b ℓ} {A : Set a} {B : Set b} →
            A ⇔ B → ∥ A ∥ n ℓ ⇔ ∥ B ∥ n ℓ
∥∥-cong-⇔ A⇔B = record
  { to   = ∥∥-map (_⇔_.to   A⇔B)
  ; from = ∥∥-map (_⇔_.from A⇔B)
  }

-- The truncation operator preserves bijections (assuming
-- extensionality).

∥∥-cong : ∀ {k n a b ℓ} {A : Set a} {B : Set b} →
          Extensionality (a ⊔ b ⊔ lsuc ℓ) (a ⊔ b ⊔ ℓ) →
          A ↔[ k ] B → ∥ A ∥ n ℓ ↔[ k ] ∥ B ∥ n ℓ
∥∥-cong {k} {n} {a} {b} {ℓ} ext A↝B = from-bijection (record
  { surjection = record
    { logical-equivalence = record
      { to   = ∥∥-map (_↔_.to   A↔B)
      ; from = ∥∥-map (_↔_.from A↔B)
      }
    ; right-inverse-of = lemma (lower-extensionality a a ext) A↔B
    }
  ; left-inverse-of = lemma (lower-extensionality b b ext) (inverse A↔B)
  })
  where
  A↔B = from-isomorphism A↝B

  lemma :
    ∀ {c d} {C : Set c} {D : Set d} →
    Extensionality (d ⊔ lsuc ℓ) (d ⊔ ℓ) →
    (C↔D : C ↔ D) (∥d∥ : ∥ D ∥ n ℓ) →
    ∥∥-map (_↔_.to C↔D) (∥∥-map (_↔_.from C↔D) ∥d∥) ≡ ∥d∥
  lemma {d = d} ext C↔D ∥d∥ =
    apply-ext (lower-extensionality d        lzero ext) λ P →
    apply-ext (lower-extensionality _        lzero ext) λ h →
    apply-ext (lower-extensionality (lsuc ℓ) d     ext) λ g →

      ∥d∥ P h (g ∘ _↔_.to C↔D ∘ _↔_.from C↔D)  ≡⟨ cong (λ f → ∥d∥ P h (g ∘ f)) $
                                                    apply-ext (lower-extensionality (lsuc ℓ) ℓ ext)
                                                      (_↔_.right-inverse-of C↔D) ⟩∎
      ∥d∥ P h g                                ∎

-- The universe level can be decreased (unless it is zero).

with-lower-level :
  ∀ ℓ₁ {ℓ₂ a n} {A : Set a} →
  ∥ A ∥ n (ℓ₁ ⊔ ℓ₂) → ∥ A ∥ n ℓ₂
with-lower-level ℓ₁ x =
  λ P h f → lower (x (↑ ℓ₁ P) (↑-closure _ h) (lift ∘ f))

private

  -- The function with-lower-level computes in the right way.

  with-lower-level-∣∣ :
    ∀ {ℓ₁ ℓ₂ a n} {A : Set a} (x : A) →
    with-lower-level ℓ₁ {ℓ₂ = ℓ₂} {n = n} ∣ x ∣ ≡ ∣ x ∣
  with-lower-level-∣∣ _ = refl _

-- ∥_∥ is downwards closed in the h-level.

downwards-closed :
  ∀ {m n a ℓ} {A : Set a} →
  n ≤ m →
  ∥ A ∥ m ℓ → ∥ A ∥ n ℓ
downwards-closed n≤m x = λ P h f → x P (H-level.mono n≤m h) f

private

  -- The function downwards-closed computes in the right way.

  downwards-closed-∣∣ :
    ∀ {m n a ℓ} {A : Set a} (n≤m : n ≤ m) (x : A) →
    downwards-closed {ℓ = ℓ} n≤m ∣ x ∣ ≡ ∣ x ∣
  downwards-closed-∣∣ _ _ = refl _

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

-- Nested truncations can sometimes be flattened.

flatten↠ :
  ∀ {m n a ℓ} {A : Set a} →
  Extensionality (a ⊔ lsuc ℓ) (a ⊔ ℓ) →
  m ≤ n →
  ∥ ∥ A ∥ m ℓ ∥ n (a ⊔ lsuc ℓ) ↠ ∥ A ∥ m ℓ
flatten↠ ext m≤n = record
  { logical-equivalence = record
    { to   = rec (H-level.mono m≤n
                    (truncation-has-correct-h-level _ ext))
                 F.id
    ; from = ∣_∣
    }
  ; right-inverse-of = refl
  }

flatten↔ :
  ∀ {a ℓ} {A : Set a} →
  Extensionality (lsuc (a ⊔ lsuc ℓ)) (lsuc (a ⊔ lsuc ℓ)) →
  (∥ ∥ A ∥ 1 ℓ ∥ 1       (a ⊔ lsuc ℓ) →
   ∥ ∥ A ∥ 1 ℓ ∥ 1 (lsuc (a ⊔ lsuc ℓ))) →
  ∥ ∥ A ∥ 1 ℓ ∥ 1 (a ⊔ lsuc ℓ) ↔ ∥ A ∥ 1 ℓ
flatten↔ ext resize = record
  { surjection      = flatten↠ ext′ ≤-refl
  ; left-inverse-of = λ x →
      prop-elim
        ext
        (λ x → ∣ rec (H-level.mono ≤-refl
                        (truncation-has-correct-h-level _ ext′))
                     F.id x ∣ ≡ x)
        (λ _ → mono₁ 0 (truncation-has-correct-h-level
                          1 (lower-extensionality lzero _ ext)
                          _ _))
        (λ x → refl ∣ x ∣)
        (resize x)
        x
  }
  where
  ext′ = lower-extensionality _ _ ext

-- Surjectivity.
--
-- I'm not quite sure what the universe level of the truncation should
-- be, so I've included it as a parameter.

Surjective : ∀ {a b} ℓ {A : Set a} {B : Set b} →
             (A → B) → Set (a ⊔ b ⊔ lsuc ℓ)
Surjective ℓ f = ∀ b → ∥ f ⁻¹ b ∥ 1 ℓ

-- The property Surjective ℓ f is a proposition (assuming
-- extensionality).

Surjective-propositional :
  ∀ {ℓ a b} {A : Set a} {B : Set b} {f : A → B} →
  Extensionality (a ⊔ b ⊔ lsuc ℓ) (a ⊔ b ⊔ lsuc ℓ) →
  Is-proposition (Surjective ℓ f)
Surjective-propositional {ℓ} {a} ext =
  Π-closure (lower-extensionality (a ⊔ lsuc ℓ) lzero ext) 1 λ _ →
  truncation-has-correct-h-level 1
    (lower-extensionality lzero (lsuc ℓ) ext)

-- Being both surjective and an embedding is equivalent to being an
-- equivalence.
--
-- This is Corollary 4.6.4 from the first edition of the HoTT book
-- (the proof is perhaps not quite identical).

surjective×embedding≃equivalence :
  ∀ {a b} ℓ {A : Set a} {B : Set b} {f : A → B} →
  Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (lsuc (a ⊔ b ⊔ ℓ)) →
  (Surjective (a ⊔ b ⊔ ℓ) f × Is-embedding f) ≃ Is-equivalence f
surjective×embedding≃equivalence {a} {b} ℓ {f = f} ext =
  _↔_.to (⇔↔≃ ext (×-closure 1 (Surjective-propositional ext)
                               (Is-embedding-propositional
                                  (lower-extensionality _ _ ext)))
                  (Eq.propositional (lower-extensionality _ _ ext) _))
    (record
       { from = λ is-eq →

                    (λ y →                        $⟨ is-eq y ⟩
                       Contractible (f ⁻¹ y)      ↝⟨ proj₁ ⟩
                       f ⁻¹ y                     ↝⟨ ∣_∣ ⟩□
                       ∥ f ⁻¹ y ∥ 1 (a ⊔ b ⊔ ℓ)   □)

                  ,                  ($⟨ is-eq ⟩
                    Is-equivalence f  ↝⟨ Embedding.is-embedding ∘ from-equivalence ∘ ⟨ _ ,_⟩ ⟩□
                    Is-embedding f    □)

       ; to = λ { (is-surj , is-emb) y →
                                             $⟨ is-surj y ⟩
                  ∥ f ⁻¹ y ∥ 1 (a ⊔ b ⊔ ℓ)   ↝⟨ with-lower-level ℓ ⟩
                  ∥ f ⁻¹ y ∥ 1 (a ⊔ b)       ↝⟨ rec (Contractible-propositional
                                                       (lower-extensionality _ _ ext))
                      (f ⁻¹ y                       ↝⟨ propositional⇒inhabited⇒contractible
                                                         (embedding→⁻¹-propositional is-emb y) ⟩□
                       Contractible (f ⁻¹ y)        □) ⟩□

                  Contractible (f ⁻¹ y)      □ }
       })

-- If the underlying type has a certain h-level, then there is a split
-- surjection from corresponding truncations (if they are "big"
-- enough) to the type itself.

∥∥↠ : ∀ ℓ {a} {A : Set a} n →
      H-level n A → ∥ A ∥ n (a ⊔ ℓ) ↠ A
∥∥↠ ℓ _ h = record
  { logical-equivalence = record
    { to   = rec h F.id ∘ with-lower-level ℓ
    ; from = ∣_∣
    }
  ; right-inverse-of = refl
  }

-- If the underlying type is a proposition, then propositional
-- truncations of the type are isomorphic to the type itself (if they
-- are "big" enough, and assuming extensionality).

∥∥↔ : ∀ ℓ {a} {A : Set a} →
      Extensionality (lsuc (a ⊔ ℓ)) (a ⊔ ℓ) →
      Is-proposition A → ∥ A ∥ 1 (a ⊔ ℓ) ↔ A
∥∥↔ ℓ ext A-prop = record
  { surjection      = ∥∥↠ ℓ 1 A-prop
  ; left-inverse-of = λ _ →
      _⇔_.to propositional⇔irrelevant
        (truncation-has-correct-h-level 1 ext) _ _
  }

-- A simple isomorphism involving propositional truncation.

∥∥×↔ :
  ∀ {ℓ a} {A : Set a} →
  Extensionality (lsuc ℓ ⊔ a) (ℓ ⊔ a) →
  ∥ A ∥ 1 ℓ × A ↔ A
∥∥×↔ {ℓ} {A = A} ext =
  ∥ A ∥ 1 ℓ × A  ↝⟨ ×-comm ⟩
  A × ∥ A ∥ 1 ℓ  ↝⟨ (drop-⊤-right λ a →
                     _⇔_.to contractible⇔↔⊤ $
                       propositional⇒inhabited⇒contractible
                         (truncation-has-correct-h-level 1 ext)
                         ∣ a ∣) ⟩□
  A              □

-- A variant of ∥∥×↔, introduced to ensure that the right-inverse-of
-- proof is, by definition, simple (see right-inverse-of-∥∥×≃ below).

∥∥×≃ :
  ∀ {ℓ a} {A : Set a} →
  Extensionality (lsuc ℓ ⊔ a) (ℓ ⊔ a) →
  (∥ A ∥ 1 ℓ × A) ≃ A
∥∥×≃ ext =
  ⟨ proj₂
  , (λ a → propositional⇒inhabited⇒contractible
             (mono₁ 0 $
                Preimage.bijection⁻¹-contractible (∥∥×↔ ext) a)
             ((∣ a ∣ , a) , refl a))
  ⟩

private

  right-inverse-of-∥∥×≃ :
    ∀ {ℓ a} {A : Set a}
    (ext : Extensionality (lsuc ℓ ⊔ a) (ℓ ⊔ a)) (x : A) →
    _≃_.right-inverse-of (∥∥×≃ {ℓ = ℓ} ext) x ≡ refl x
  right-inverse-of-∥∥×≃ _ x = refl (refl x)

-- ∥_∥ commutes with _×_ (assuming extensionality and a resizing
-- function for the propositional truncation).

∥∥×∥∥↔∥×∥ :
  ∀ {a b} ℓ {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ) →
  (∀ {x} {X : Set x} →
     ∥ X ∥ 1       (a ⊔ b ⊔ ℓ) →
     ∥ X ∥ 1 (lsuc (a ⊔ b ⊔ ℓ))) →
  let ℓ′ = a ⊔ b ⊔ ℓ in
  (∥ A ∥ 1 ℓ′ × ∥ B ∥ 1 ℓ′) ↔ ∥ A × B ∥ 1 ℓ′
∥∥×∥∥↔∥×∥ _ ext resize = record
  { surjection = record
    { logical-equivalence = record
      { from = λ p → ∥∥-map proj₁ p , ∥∥-map proj₂ p
      ; to   = λ { (x , y) →
                   rec (truncation-has-correct-h-level 1 ext)
                       (λ x → rec (truncation-has-correct-h-level 1 ext)
                                  (λ y → ∣ x , y ∣)
                                  (resize y))
                       (resize x) }
      }
    ; right-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant
          (truncation-has-correct-h-level 1 ext)
          _ _
    }
  ; left-inverse-of = λ _ →
      _⇔_.to propositional⇔irrelevant
        (×-closure 1
           (truncation-has-correct-h-level 1 ext)
           (truncation-has-correct-h-level 1 ext))
        _ _
  }

-- If A is merely inhabited (at a certain level), then the
-- propositional truncation of A (at the same level) is isomorphic to
-- the unit type (assuming extensionality).

inhabited⇒∥∥↔⊤ :
  ∀ {ℓ a} {A : Set a} →
  Extensionality (lsuc ℓ ⊔ a) (ℓ ⊔ a) →
  ∥ A ∥ 1 ℓ → ∥ A ∥ 1 ℓ ↔ ⊤
inhabited⇒∥∥↔⊤ ext ∥a∥ =
  _⇔_.to contractible⇔↔⊤ $
    propositional⇒inhabited⇒contractible
      (truncation-has-correct-h-level 1 ext)
      ∥a∥

-- If A is not inhabited, then the propositional truncation of A is
-- isomorphic to the empty type.

not-inhabited⇒∥∥↔⊥ :
  ∀ {ℓ₁ ℓ₂ a} {A : Set a} →
  ¬ A → ∥ A ∥ 1 ℓ₁ ↔ ⊥ {ℓ = ℓ₂}
not-inhabited⇒∥∥↔⊥ {A = A} =
  ¬ A            ↝⟨ (λ ¬a ∥a∥ → rec ⊥-propositional ¬a (with-lower-level _ ∥a∥)) ⟩
  ¬ ∥ A ∥ 1 _    ↝⟨ inverse ∘ Bijection.⊥↔uninhabited ⟩□
  ∥ A ∥ 1 _ ↔ ⊥  □

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

-- The following three lemmas were communicated to me by Nicolai
-- Kraus. (In slightly different form.) They are closely related to
-- Lemma 2.1 in his paper "The General Universal Property of the
-- Propositional Truncation".

-- A variant of ∥∥×≃.

drop-∥∥ :
  ∀ ℓ {a b} {A : Set a} {B : A → Set b} →
  Extensionality (lsuc (a ⊔ ℓ)) (a ⊔ b ⊔ ℓ) →

  (∥ A ∥ 1 (a ⊔ ℓ) → ∀ x → B x)
    ↔
  (∀ x → B x)
drop-∥∥ ℓ {a} {b} {A} {B} ext =

  (∥ A ∥ 1 _ → ∀ x → B x)              ↝⟨ inverse currying ⟩

  ((p : ∥ A ∥ 1 _ × A) → B (proj₂ p))  ↝⟨ Π-cong (lower-extensionality lzero (a ⊔ ℓ) ext)
                                                 (∥∥×≃ (lower-extensionality lzero b ext))
                                                 (λ _ → F.id) ⟩□
  (∀ x → B x)                          □

-- Another variant of ∥∥×≃.

push-∥∥ :
  ∀ ℓ {a b c} {A : Set a} {B : A → Set b} {C : (∀ x → B x) → Set c} →
  Extensionality (lsuc (a ⊔ ℓ)) (a ⊔ b ⊔ c ⊔ ℓ) →

  (∥ A ∥ 1 (a ⊔ ℓ) → ∃ λ (f : ∀ x → B x) → C f)
    ↔
  (∃ λ (f : ∀ x → B x) → ∥ A ∥ 1 (a ⊔ ℓ) → C f)

push-∥∥ ℓ {a} {b} {c} {A} {B} {C} ext =

  (∥ A ∥ 1 _ → ∃ λ (f : ∀ x → B x) → C f)                ↝⟨ ΠΣ-comm ⟩

  (∃ λ (f : ∥ A ∥ 1 _ → ∀ x → B x) → ∀ ∥x∥ → C (f ∥x∥))  ↝⟨ Σ-cong (drop-∥∥ ℓ (lower-extensionality lzero c ext)) (λ f →
                                                            ∀-cong (lower-extensionality lzero (a ⊔ b ⊔ ℓ) ext) λ ∥x∥ →
                                                            ≡⇒↝ _ $ cong C $ apply-ext (lower-extensionality _ (a ⊔ c ⊔ ℓ) ext) λ x →
      f ∥x∥ x                                                 ≡⟨ cong (λ ∥x∥ → f ∥x∥ x) $
                                                                 _⇔_.to propositional⇔irrelevant
                                                                   (truncation-has-correct-h-level 1
                                                                      (lower-extensionality lzero (b ⊔ c) ext))
                                                                   _ _ ⟩
      f ∣ x ∣ x                                               ≡⟨ sym $ subst-refl _ _ ⟩∎
      subst B (refl x) (f ∣ x ∣ x)                            ∎) ⟩□

  (∃ λ (f : ∀ x → B x) → ∥ A ∥ 1 _ → C (λ x → f x))      □

-- This is an instance of a variant of Lemma 2.1 from "The General
-- Universal Property of the Propositional Truncation" by Kraus.

drop-∥∥₃ :
  ∀ ℓ {a b c d}
    {A : Set a} {B : A → Set b} {C : A → (∀ x → B x) → Set c}
    {D : A → (f : ∀ x → B x) → (∀ x → C x f) → Set d} →
  Extensionality (lsuc (a ⊔ ℓ)) (a ⊔ b ⊔ c ⊔ d ⊔ ℓ) →

  (∥ A ∥ 1 (a ⊔ ℓ) →
   ∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)
    ↔
  (∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)

drop-∥∥₃ ℓ {b = b} {c} {A = A} {B} {C} {D} ext =
  (∥ A ∥ 1 _ →
   ∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)  ↝⟨ push-∥∥ ℓ ext ⟩

  (∃ λ (f : ∀ x → B x) →
   ∥ A ∥ 1 _ → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)            ↝⟨ (∃-cong λ _ →
                                                                     push-∥∥ ℓ (lower-extensionality lzero b ext)) ⟩
  (∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) →
   ∥ A ∥ 1 _ → ∀ x → D x f g)                                    ↝⟨ (∃-cong λ _ → ∃-cong λ _ →
                                                                     drop-∥∥ ℓ (lower-extensionality lzero (b ⊔ c) ext)) ⟩□
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
  ∀ {a b} ℓ {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ) →
  H-level 3 B →
  (∃ λ (f : A → B) → Coherently-constant f) ≃ (∥ A ∥ 1 (a ⊔ b ⊔ ℓ) → B)
coherently-constant-function≃∥inhabited∥⇒inhabited {a} {b} ℓ {A} {B}
                                                   ext B-groupoid =
  (∃ λ (f : A → B) → Coherently-constant f)               ↔⟨ inverse $ drop-∥∥₃ (b ⊔ ℓ) ext ⟩
  (∥ A ∥ 1 ℓ′ → ∃ λ (f : A → B) → Coherently-constant f)  ↝⟨ ∀-cong (lower-extensionality lzero ℓ ext) (inverse ∘ equivalence₂) ⟩□
  (∥ A ∥ 1 ℓ′ → B)                                        □
  where
  ℓ′ = a ⊔ b ⊔ ℓ

  rearrangement-lemma = λ a₀ →
    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (c : Constant f) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) → ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ ∃-comm ⟩

    (∃ λ (f : A → B) →
     ∃ λ (f₁ : B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (c : Constant f) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) → ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (f : A → B) →
     ∃ λ (f₁ : B) →
     ∃ λ (c : Constant f) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) → ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (f₁ : B) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) → ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ∃-cong λ _ → ∃-comm) ⟩
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (f₁ : B) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ∃-comm) ⟩
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (f₁ : B) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (f₁ : B) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (f₁ : B) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ∃-comm) ⟩
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-comm) ⟩

    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (d₂ : (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂) →
     trans (c a₀ a₀) (c₁ a₀) ≡ c₂)                                     ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ∃-cong λ _ → ∃-comm) ⟩□
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₂ : (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     trans (c a₀ a₀) (c₁ a₀) ≡ c₂)                                     □

  equivalence₁ : A → (B ≃ ∃ λ (f : A → B) → Coherently-constant f)
  equivalence₁ a₀ = ↔⇒≃ (
    B                                                                    ↝⟨ (inverse $ drop-⊤-right λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 0 λ _ →
                                                                               singleton-contractible _) ⟩
    (∃ λ (f₁ : B) →
     (a : A) → ∃ λ (b : B) → b ≡ f₁)                                     ↝⟨ (∃-cong λ _ → ΠΣ-comm) ⟩

    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → (a : A) → f a ≡ f₁)                               ↝⟨ (∃-cong λ _ → ∃-cong λ _ → inverse $ drop-⊤-right λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               Π-closure (lower-extensionality _ ℓ       ext) 0 λ _ →
                                                                               Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 0 λ _ →
                                                                               singleton-contractible _) ⟩
    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∀ a₁ a₂ → ∃ λ (c : f a₁ ≡ f a₂) → c ≡ trans (c₁ a₁) (sym (c₁ a₂)))  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                             ∀-cong (lower-extensionality _ ℓ       ext) λ _ →
                                                                             ∀-cong (lower-extensionality _ (a ⊔ ℓ) ext) λ _ →
                                                                             ∃-cong λ _ → ≡⇒↝ _ $ sym $ [trans≡]≡[≡trans-symʳ] _ _ _) ⟩
    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∀ a₁ a₂ → ∃ λ (c : f a₁ ≡ f a₂) → trans c (c₁ a₂) ≡ c₁ a₁)          ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                             ∀-cong (lower-extensionality _ ℓ ext) λ _ →
                                                                             ΠΣ-comm) ⟩
    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∀ a₁ → ∃ λ (c : ∀ a₂ → f a₁ ≡ f a₂) →
            ∀ a₂ → trans (c a₂) (c₁ a₂) ≡ c₁ a₁)                         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ΠΣ-comm) ⟩

    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (c : Constant f) → ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁)   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                             inverse $ drop-⊤-right λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               other-singleton-contractible _) ⟩
    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (c : Constant f) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) → trans (c a₀ a₀) (c₁ a₀) ≡ c₂)                ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ c₁ → ∃-cong λ c → ∃-cong λ d₁ →
                                                                             ∃-cong λ _ → inverse $ drop-⊤-right λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               propositional⇒inhabited⇒contractible
                                                                                 (Π-closure (lower-extensionality _ ℓ       ext) 1 λ _ →
                                                                                  Π-closure (lower-extensionality _ ℓ       ext) 1 λ _ →
                                                                                  Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 1 λ _ →
                                                                                  B-groupoid _ _ _ _)
                                                                                 (λ a₁ a₂ a₃ →
         trans (c a₁ a₂) (c a₂ a₃)                                                  ≡⟨ cong₂ trans (≡⇒↝ implication
                                                                                                        ([trans≡]≡[≡trans-symʳ] _ _ _) (d₁ _ _))
                                                                                                   (≡⇒↝ implication
                                                                                                        ([trans≡]≡[≡trans-symʳ] _ _ _) (d₁ _ _)) ⟩
         trans (trans (c₁ a₁) (sym (c₁ a₂)))
               (trans (c₁ a₂) (sym (c₁ a₃)))                                        ≡⟨ sym $ trans-assoc _ _ _ ⟩

         trans (trans (trans (c₁ a₁) (sym (c₁ a₂))) (c₁ a₂))
               (sym (c₁ a₃))                                                        ≡⟨ cong (flip trans _) $ trans-[trans-sym]- _ _ ⟩

         trans (c₁ a₁) (sym (c₁ a₃))                                                ≡⟨ sym $ ≡⇒↝ implication
                                                                                                 ([trans≡]≡[≡trans-symʳ] _ _ _) (d₁ _ _) ⟩∎
         c a₁ a₃                                                                    ∎)) ⟩

    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (c : Constant f) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) → ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃)                   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ c₁ → ∃-cong λ c → ∃-cong λ d₁ →
                                                                             ∃-cong λ c₂ → ∃-cong λ d₃ → inverse $ drop-⊤-right λ d →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               propositional⇒inhabited⇒contractible
                                                                                 (Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 1 λ _ →
                                                                                  B-groupoid _ _ _ _)
                                                                                 (λ a →
         trans (c a₀ a) (c₁ a)                                                      ≡⟨ cong (λ x → trans x _) $ sym $ d _ _ _ ⟩
         trans (trans (c a₀ a₀) (c a₀ a)) (c₁ a)                                    ≡⟨ trans-assoc _ _ _ ⟩
         trans (c a₀ a₀) (trans (c a₀ a) (c₁ a))                                    ≡⟨ cong (trans _) $ d₁ _ _ ⟩
         trans (c a₀ a₀) (c₁ a₀)                                                    ≡⟨ d₃ ⟩∎
         c₂                                                                         ∎)) ⟩

    (∃ λ (f₁ : B) →
     ∃ λ (f : A → B) → ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (c : Constant f) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     ∃ λ (c₂ : f a₀ ≡ f₁) → ∃ λ (d₃ : trans (c a₀ a₀) (c₁ a₀) ≡ c₂) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                               ↝⟨ rearrangement-lemma a₀ ⟩

    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₂ : (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂) →
     ∃ λ (d₁ : ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁) →
     trans (c a₀ a₀) (c₁ a₀) ≡ c₂)                                       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                             ∃-cong λ _ → ∃-cong λ d₂ → drop-⊤-right λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               propositional⇒inhabited⇒contractible
                                                                                 (B-groupoid _ _ _ _)
                                                                                 (d₂ _)) ⟩
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     ∃ λ (d₂ : (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂) →
     ∀ a₁ a₂ → trans (c a₁ a₂) (c₁ a₂) ≡ c₁ a₁)                          ↝⟨ (∃-cong λ _ → ∃-cong λ c → ∃-cong λ d → ∃-cong λ _ → ∃-cong λ c₂ →
                                                                             ∃-cong λ c₁ → drop-⊤-right λ d₂ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               propositional⇒inhabited⇒contractible
                                                                                 (Π-closure (lower-extensionality _ ℓ       ext) 1 λ _ →
                                                                                  Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 1 λ _ →
                                                                                  B-groupoid _ _ _ _)
                                                                                 (λ a₁ a₂ →
         trans (c a₁ a₂) (c₁ a₂)                                                    ≡⟨ cong₂ trans (sym $ d _ _ _)
                                                                                                   (≡⇒↝ implication
                                                                                                        ([trans≡]≡[≡trans-symˡ] _ _ _) (d₂ _)) ⟩
         trans (trans (c a₁ a₀) (c a₀ a₂)) (trans (sym (c a₀ a₂)) c₂)               ≡⟨ sym $ trans-assoc _ _ _ ⟩
         trans (trans (trans (c a₁ a₀) (c a₀ a₂)) (sym (c a₀ a₂))) c₂               ≡⟨ cong (flip trans _) $ trans-[trans]-sym _ _ ⟩
         trans (c a₁ a₀) c₂                                                         ≡⟨ cong (trans _) $ sym $ d₂ _ ⟩
         trans (c a₁ a₀) (trans (c a₀ a₁) (c₁ a₁))                                  ≡⟨ sym $ trans-assoc _ _ _ ⟩
         trans (trans (c a₁ a₀) (c a₀ a₁)) (c₁ a₁)                                  ≡⟨ cong (flip trans _) $ d _ _ _ ⟩
         trans (c a₁ a₁) (c₁ a₁)                                                    ≡⟨ cong (flip trans _) $
                                                                                         Groupoid.idempotent⇒≡id (EG.groupoid _) (d _ _ _) ⟩
         trans (refl _) (c₁ a₁)                                                     ≡⟨ trans-reflˡ _ ⟩∎
         c₁ a₁                                                                      ∎)) ⟩

    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → ∃ λ (c₂ : f a₀ ≡ f₁) →
     ∃ λ (c₁ : (a : A) → f a ≡ f₁) →
     (a : A) → trans (c a₀ a) (c₁ a) ≡ c₂)                               ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                             inverse ΠΣ-comm) ⟩
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → ∃ λ (c₂ : f a₀ ≡ f₁) →
     (a : A) → ∃ λ (c₁ : f a ≡ f₁) → trans (c a₀ a) c₁ ≡ c₂)             ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                             ∀-cong (lower-extensionality _ (a ⊔ ℓ) ext) λ _ → ∃-cong λ _ →
                                                                             ≡⇒↝ _ $ [trans≡]≡[≡trans-symˡ] _ _ _) ⟩
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → ∃ λ (c₂ : f a₀ ≡ f₁) →
     (a : A) → ∃ λ (c₁ : f a ≡ f₁) → c₁ ≡ trans (sym (c a₀ a)) c₂)       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                             drop-⊤-right λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 0 λ _ →
                                                                               singleton-contractible _) ⟩
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∃ λ (d : ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃) →
     ∃ λ (f₁ : B) → f a₀ ≡ f₁)                                           ↝⟨ (∃-cong λ _ → ∃-cong λ _ → drop-⊤-right λ _ →
                                                                             _⇔_.to contractible⇔↔⊤ $
                                                                               other-singleton-contractible _) ⟩□
    (∃ λ (f : A → B) → ∃ λ (c : Constant f) →
     ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃)                   □)

  -- An alternative implementation of the forward component of the
  -- equivalence above (with shorter proofs).

  to : B → ∃ λ (f : A → B) → Coherently-constant f
  to b =
      (λ _ → b)
    , (λ _ _ → refl b)
    , (λ _ _ _ → trans-refl-refl)

  to-is-an-equivalence : A → Is-equivalence to
  to-is-an-equivalence a₀ =
    respects-extensional-equality
      (λ b →
         Σ-≡,≡→≡ (refl _) $
         Σ-≡,≡→≡
           (proj₁ (subst Coherently-constant
                         (refl _)
                         (proj₂ (_≃_.to (equivalence₁ a₀) b)))  ≡⟨ cong proj₁ $ subst-refl Coherently-constant _ ⟩

            (λ _ _ → trans (refl b) (sym (refl b)))             ≡⟨ (apply-ext (lower-extensionality _ ℓ       ext) λ _ →
                                                                    apply-ext (lower-extensionality _ (a ⊔ ℓ) ext) λ _ →
                                                                    trans-symʳ _) ⟩∎
            (λ _ _ → refl b)                                    ∎)
           (_⇔_.to propositional⇔irrelevant
              (Π-closure (lower-extensionality _ ℓ       ext) 1 λ _ →
               Π-closure (lower-extensionality _ ℓ       ext) 1 λ _ →
               Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 1 λ _ →
               B-groupoid _ _ _ _)
              _ _))
      (_≃_.is-equivalence (equivalence₁ a₀))

  -- The forward component of the equivalence above does not depend on
  -- the value a₀ of type A, so it suffices to assume that A is merely
  -- inhabited.

  equivalence₂ :
    ∥ A ∥ 1 ℓ′ → (B ≃ ∃ λ (f : A → B) → Coherently-constant f)
  equivalence₂ ∥a∥ =
    ⟨ to
    , rec (Eq.propositional (lower-extensionality _ ℓ ext) _)
          to-is-an-equivalence
          (with-lower-level ℓ ∥a∥)
    ⟩

-- Having a constant function into a set is equivalent to having a
-- function from a propositionally truncated type into the set
-- (assuming extensionality). The statement of this result is that of
-- Proposition 2.2 in "The General Universal Property of the
-- Propositional Truncation" by Kraus, but it uses a different proof:
-- as observed by Kraus this result follows from Proposition 2.3.

constant-function≃∥inhabited∥⇒inhabited :
  ∀ {a b} ℓ {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ) →
  Is-set B →
  (∃ λ (f : A → B) → Constant f) ≃ (∥ A ∥ 1 (a ⊔ b ⊔ ℓ) → B)
constant-function≃∥inhabited∥⇒inhabited {a} {b} ℓ {A} {B} ext B-set =
  (∃ λ (f : A → B) → Constant f)             ↔⟨ (∃-cong λ f → inverse $ drop-⊤-right λ c →
                                                 _⇔_.to contractible⇔↔⊤ $
                                                   Π-closure (lower-extensionality _ ℓ       ext) 0 λ _ →
                                                   Π-closure (lower-extensionality _ ℓ       ext) 0 λ _ →
                                                   Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 0 λ _ →
                                                   B-set _ _ _ _) ⟩
  (∃ λ (f : A → B) → Coherently-constant f)  ↝⟨ coherently-constant-function≃∥inhabited∥⇒inhabited ℓ ext (mono₁ 2 B-set) ⟩□
  (∥ A ∥ 1 (a ⊔ b ⊔ ℓ) → B)                  □

private

  -- One direction of the proposition above computes in the right way.

  to-constant-function≃∥inhabited∥⇒inhabited :
    ∀ {a b} ℓ {A : Set a} {B : Set b}
    (ext : Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ))
    (B-set : Is-set B)
    (f : ∃ λ (f : A → B) → Constant f) (x : A) →
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited ℓ ext B-set)
      f ∣ x ∣ ≡ proj₁ f x
  to-constant-function≃∥inhabited∥⇒inhabited _ _ _ _ _ = refl _

-- The propositional truncation's universal property (defined using
-- extensionality).
--
-- As observed by Kraus this result follows from Proposition 2.2 in
-- his "The General Universal Property of the Propositional
-- Truncation".

universal-property :
  ∀ {a b} ℓ {A : Set a} {B : Set b} →
  Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ) →
  Is-proposition B →
  (∥ A ∥ 1 (a ⊔ b ⊔ ℓ) → B) ≃ (A → B)
universal-property {a = a} {b} ℓ {A} {B} ext B-prop =
  with-other-function
    ((∥ A ∥ 1 (a ⊔ b ⊔ ℓ) → B)       ↝⟨ inverse $ constant-function≃∥inhabited∥⇒inhabited ℓ ext (mono₁ 1 B-prop) ⟩
     (∃ λ (f : A → B) → Constant f)  ↔⟨ (drop-⊤-right λ _ →
                                         _⇔_.to contractible⇔↔⊤ $
                                         Π-closure (lower-extensionality _ ℓ       ext) 0 λ _ →
                                         Π-closure (lower-extensionality _ (a ⊔ ℓ) ext) 0 λ _ →
                                         B-prop _ _) ⟩□
     (A → B)                         □)

    (_∘ ∣_∣)

    (λ f → apply-ext (lower-extensionality _ (a ⊔ ℓ) ext) λ x →
       subst (const B) (refl x) (f ∣ x ∣)  ≡⟨ subst-refl _ _ ⟩∎
       f ∣ x ∣                             ∎)

private

  -- The universal property computes in the right way.

  to-universal-property :
    ∀ {a b} ℓ {A : Set a} {B : Set b}
    (ext : Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ))
    (B-prop : Is-proposition B)
    (f : ∥ A ∥ 1 (a ⊔ b ⊔ ℓ) → B) →
    _≃_.to (universal-property ℓ ext B-prop) f ≡ f ∘ ∣_∣
  to-universal-property _ _ _ _ = refl _

  from-universal-property :
    ∀ {a b} ℓ {A : Set a} {B : Set b}
    (ext : Extensionality (lsuc (a ⊔ b ⊔ ℓ)) (a ⊔ b ⊔ ℓ))
    (B-prop : Is-proposition B)
    (f : A → B) (x : A) →
    _≃_.from (universal-property ℓ ext B-prop) f ∣ x ∣ ≡ f x
  from-universal-property _ _ _ _ _ = refl _

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

-- The axiom of choice, in one of the alternative forms given in the
-- HoTT book (§3.8).
--
-- The HoTT book uses a "real" propositional truncation, rather than
-- the defined one used here. Note that I don't know if the universe
-- levels used below (b ⊔ ℓ and a ⊔ b ⊔ ℓ) make sense. However, in the
-- presence of a "real" propositional truncation (and extensionality)
-- they can be dropped (see Real-propositional-truncation.isomorphic).

Axiom-of-choice : (a b ℓ : Level) → Set (lsuc (a ⊔ b ⊔ ℓ))
Axiom-of-choice a b ℓ =
  {A : Set a} {B : A → Set b} →
  Is-set A → (∀ x → ∥ B x ∥ 1 (b ⊔ ℓ)) → ∥ (∀ x → B x) ∥ 1 (a ⊔ b ⊔ ℓ)
