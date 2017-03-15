------------------------------------------------------------------------
-- Propositional truncation
------------------------------------------------------------------------

-- Note that this module is experimental: it uses rewrite rules and
-- postulates to encode a higher inductive type.

{-# OPTIONS --without-K --rewriting #-}

-- Partly following the HoTT book.

module H-level.Truncation.Propositional where

open import Equality.Propositional as EP hiding (elim)
open import Interval using (ext)
open import Prelude
open import Logical-equivalence using (_⇔_)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Embedding equality-with-J hiding (id; _∘_)
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
-- defined in H-level.Truncation.

∥∥↔∥∥ :
  ∀ ℓ {a} {A : Set a} →
  ∥ A ∥ ↔ Trunc.∥ A ∥ 1 (a ⊔ ℓ)
∥∥↔∥∥ ℓ = record
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
-- eliminator.

elim :
  ∀ {a p} {A : Set a} →
  (P : ∥ A ∥ → Set p) →
  (∀ x → Is-proposition (P x)) →
  ((x : A) → P ∣ x ∣) →
  (x : ∥ A ∥) → P x
elim P P-prop f x =
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
  (P : ∥ A ∥ → Set p)
  (P-prop : ∀ x → Is-proposition (P x))
  (f : (x : A) → P ∣ x ∣)
  (x : A) →
  elim P P-prop f ∣ x ∣ ≡ f x
elim-∣∣ P P-prop f x =
  _⇔_.to propositional⇔irrelevant (P-prop _) _ _

-- The truncation operator preserves logical equivalences.

∥∥-cong-⇔ : ∀ {a b} {A : Set a} {B : Set b} →
            A ⇔ B → ∥ A ∥ ⇔ ∥ B ∥
∥∥-cong-⇔ A⇔B = record
  { to   = ∥∥-map (_⇔_.to   A⇔B)
  ; from = ∥∥-map (_⇔_.from A⇔B)
  }

-- The truncation operator preserves bijections.

∥∥-cong : ∀ {k a b} {A : Set a} {B : Set b} →
          A ↔[ k ] B → ∥ A ∥ ↔[ k ] ∥ B ∥
∥∥-cong {a = a} {b} {A} {B} A↔B =
  ∥ A ∥                  ↔⟨ ∥∥↔∥∥ b ⟩
  Trunc.∥ A ∥ 1 (a ⊔ b)  ↝⟨ Trunc.∥∥-cong ext A↔B ⟩
  Trunc.∥ B ∥ 1 (a ⊔ b)  ↔⟨ inverse (∥∥↔∥∥ a) ⟩□
  ∥ B ∥                  □

-- A generalised flattening lemma.

flatten′ :
  ∀ {ℓ f}
  (F : (Set ℓ → Set ℓ) → Set f) →
  (∀ {G H} → (∀ {A} → G A → H A) → F G → F H) →
  (F ∥_∥ → ∥ F id ∥) →
  ∥ F ∥_∥ ∥ ↔ ∥ F id ∥
flatten′ _ map f = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec truncation-is-proposition f
      ; from = ∥∥-map (map ∣_∣)
      }
    ; right-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ →
      _⇔_.to propositional⇔irrelevant truncation-is-proposition _ _
  }

-- Nested truncations can be flattened.

flatten : ∀ {a} {A : Set a} →
          ∥ ∥ A ∥ ∥ ↔ ∥ A ∥
flatten {A = A} = flatten′ (λ F → F A) (λ f → f) id

private

  -- Another flattening lemma, given as an example of how flatten′ can
  -- be used.

  ∥∃∥∥∥↔∥∃∥ : ∀ {a b} {A : Set a} {B : A → Set b} →
              ∥ ∃ (∥_∥ ∘ B) ∥ ↔ ∥ ∃ B ∥
  ∥∃∥∥∥↔∥∃∥ {B = B} =
    flatten′ (λ F → ∃ (F ∘ B))
             (λ f → Σ-map id f)
             (uncurry λ x → ∥∥-map (x ,_))

-- Surjectivity.

Surjective : ∀ {a b} {A : Set a} {B : Set b} →
             (A → B) → Set (a ⊔ b)
Surjective f = ∀ b → ∥ f ⁻¹ b ∥

-- The property Surjective f is a proposition.

Surjective-propositional :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} →
  Is-proposition (Surjective f)
Surjective-propositional =
  Π-closure ext 1 λ _ →
  truncation-is-proposition

-- Being both surjective and an embedding is equivalent to being an
-- equivalence.
--
-- This is Corollary 4.6.4 from the first edition of the HoTT book
-- (the proof is perhaps not quite identical).

surjective×embedding≃equivalence :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} →
  (Surjective f × Is-embedding f) ≃ Is-equivalence f
surjective×embedding≃equivalence {f = f} =
  (Surjective f × Is-embedding f)          ↔⟨ ∀-cong ext (λ _ → ∥∥↔∥∥ lzero) ×-cong F.id ⟩
  (Trunc.Surjective _ f × Is-embedding f)  ↝⟨ Trunc.surjective×embedding≃equivalence lzero ext ⟩□
  Is-equivalence f                         □

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
  ¬ ∥ A ∥    ↝⟨ inverse ∘ Bijection.⊥↔uninhabited ⟩□
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

  (∥ A ∥ → ∀ x → B x)
    ↔
  (∀ x → B x)
drop-∥∥ {A = A} {B} =
  (∥ A ∥ → ∀ x → B x)              ↝⟨ inverse currying ⟩
  ((p : ∥ A ∥ × A) → B (proj₂ p))  ↔⟨ Π-preserves ext ∥∥×≃ (λ _ → F.id) ⟩□
  (∀ x → B x)                      □

-- Another variant of ∥∥×≃.

push-∥∥ :
  ∀ {a b c} {A : Set a} {B : A → Set b} {C : (∀ x → B x) → Set c} →

  (∥ A ∥ → ∃ λ (f : ∀ x → B x) → C f)
    ↔
  (∃ λ (f : ∀ x → B x) → ∥ A ∥ → C f)

push-∥∥ {b = b} {c} {A} {B} {C} =

  (∥ A ∥ → ∃ λ (f : ∀ x → B x) → C f)                ↝⟨ ΠΣ-comm ⟩

  (∃ λ (f : ∥ A ∥ → ∀ x → B x) → ∀ ∥x∥ → C (f ∥x∥))  ↝⟨ Σ-cong drop-∥∥ (λ f →
                                                        ∀-cong ext λ ∥x∥ →
                                                        ≡⇒↝ _ $ cong C $ ext λ x →
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

  (∥ A ∥ →
   ∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)
    ↔
  (∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)

drop-∥∥₃ {a} {b} {c} {A = A} {B} {C} {D} =
  (∥ A ∥ →
   ∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)  ↝⟨ push-∥∥ ⟩

  (∃ λ (f : ∀ x → B x) →
   ∥ A ∥ → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)                ↝⟨ (∃-cong λ _ → push-∥∥) ⟩

  (∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) →
   ∥ A ∥ → ∀ x → D x f g)                                        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → drop-∥∥) ⟩□

  (∃ λ (f : ∀ x → B x) → ∃ λ (g : ∀ x → C x f) → ∀ x → D x f g)  □

-- Having a coherently constant function into a groupoid is equivalent
-- to having a function from a propositionally truncated type into the
-- groupoid. This result is Proposition 2.3 in "The General Universal
-- Property of the Propositional Truncation" by Kraus.

Coherently-constant :
  ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Coherently-constant f =
  ∃ λ (c : Constant f) →
  ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃

coherently-constant-function≃∥inhabited∥⇒inhabited :
  ∀ {a b} {A : Set a} {B : Set b} →
  H-level 3 B →
  (∃ λ (f : A → B) → Coherently-constant f) ≃ (∥ A ∥ → B)
coherently-constant-function≃∥inhabited∥⇒inhabited {a} {b} {A} {B}
                                                   B-groupoid =
  (∃ λ (f : A → B) → Coherently-constant f)  ↝⟨ Trunc.coherently-constant-function≃∥inhabited∥⇒inhabited lzero ext B-groupoid ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)                ↔⟨ →-cong ext (inverse $ ∥∥↔∥∥ (a ⊔ b)) F.id ⟩□
  (∥ A ∥ → B)                                □

-- Having a constant function into a set is equivalent to having a
-- function from a propositionally truncated type into the set. The
-- statement of this result is that of Proposition 2.2 in "The General
-- Universal Property of the Propositional Truncation" by Kraus, but
-- it uses a different proof: as observed by Kraus this result follows
-- from Proposition 2.3.

constant-function≃∥inhabited∥⇒inhabited :
  ∀ {a b} {A : Set a} {B : Set b} →
  Is-set B →
  (∃ λ (f : A → B) → Constant f) ≃ (∥ A ∥ → B)
constant-function≃∥inhabited∥⇒inhabited {a} {b} {A} {B} B-set =
  (∃ λ (f : A → B) → Constant f)  ↝⟨ Trunc.constant-function≃∥inhabited∥⇒inhabited lzero ext B-set ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)     ↔⟨ →-cong ext (inverse $ ∥∥↔∥∥ (a ⊔ b)) F.id ⟩□
  (∥ A ∥ → B)                     □

private

  -- One direction of the proposition above computes in the right way.

  to-constant-function≃∥inhabited∥⇒inhabited :
    ∀ {a b} {A : Set a} {B : Set b}
    (B-set : Is-set B)
    (f : ∃ λ (f : A → B) → Constant f) (x : A) →
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited B-set) f ∣ x ∣ ≡
    proj₁ f x
  to-constant-function≃∥inhabited∥⇒inhabited _ _ _ = refl

-- The propositional truncation's universal property.
--
-- As observed by Kraus this result follows from Proposition 2.2 in
-- his "The General Universal Property of the Propositional
-- Truncation".

universal-property :
  ∀ {a b} {A : Set a} {B : Set b} →
  Is-proposition B →
  (∥ A ∥ → B) ≃ (A → B)
universal-property {a} {b} {A} {B} B-prop =
  (∥ A ∥ → B)                  ↔⟨ →-cong ext (∥∥↔∥∥ (a ⊔ b)) F.id ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)  ↝⟨ Trunc.universal-property lzero ext B-prop ⟩□
  (A → B)                      □

private

  -- The universal property computes in the right way.

  to-universal-property :
    ∀ {a b} {A : Set a} {B : Set b}
    (B-prop : Is-proposition B)
    (f : ∥ A ∥ → B) →
    _≃_.to (universal-property B-prop) f ≡ f ∘ ∣_∣
  to-universal-property _ _ = refl

  from-universal-property :
    ∀ {a b} {A : Set a} {B : Set b}
    (B-prop : Is-proposition B)
    (f : A → B) (x : A) →
    _≃_.from (universal-property B-prop) f ∣ x ∣ ≡ f x
  from-universal-property _ _ _ = refl

-- The axiom of choice, in one of the alternative forms given in the
-- HoTT book (§3.8).

Axiom-of-choice : (a b : Level) → Set (lsuc (a ⊔ b))
Axiom-of-choice a b =
  {A : Set a} {B : A → Set b} →
  Is-set A → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

-- The axiom of choice can be turned into a bijection.

choice-bijection :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  Axiom-of-choice a b → Is-set A →
  (∀ x → ∥ B x ∥) ↔ ∥ (∀ x → B x) ∥
choice-bijection choice A-set = record
  { surjection = record
    { logical-equivalence = record
      { to   = choice A-set
      ; from = λ f x → ∥∥-map (_$ x) f
      }
    ; right-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant
          truncation-is-proposition
          _ _
    }
  ; left-inverse-of = λ _ →
      _⇔_.to propositional⇔irrelevant
          (Π-closure ext 1 λ _ →
           truncation-is-proposition)
          _ _
  }

-- The axiom of countable choice, stated in a corresponding way.

Axiom-of-countable-choice : (b : Level) → Set (lsuc b)
Axiom-of-countable-choice b =
  {B : ℕ → Set b} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

-- The axiom of countable choice can be turned into a bijection.

countable-choice-bijection :
  ∀ {b} {B : ℕ → Set b} →
  Axiom-of-countable-choice b →
  (∀ x → ∥ B x ∥) ↔ ∥ (∀ x → B x) ∥
countable-choice-bijection cc = record
  { surjection = record
    { logical-equivalence = record
      { to   = cc
      ; from = λ f x → ∥∥-map (_$ x) f
      }
    ; right-inverse-of = λ _ →
        _⇔_.to propositional⇔irrelevant
          truncation-is-proposition
          _ _
    }
  ; left-inverse-of = λ _ →
      _⇔_.to propositional⇔irrelevant
          (Π-closure ext 1 λ _ →
           truncation-is-proposition)
          _ _
  }
