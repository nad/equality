------------------------------------------------------------------------
-- A variant of the propositional truncation operator with an erased
-- truncation constructor
------------------------------------------------------------------------

-- Partly following the HoTT book, but adapted for erasure.

{-# OPTIONS --cubical --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the propositional truncation
-- operator uses path equality, but the supplied notion of equality is
-- used for many other things.

import Equality.Path as P

module H-level.Truncation.Propositional.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude as P
open import Logical-equivalence using (_⇔_)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Embedding equality-with-J as Emb using (Is-embedding)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased equality-with-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ; Contractibleᴱ; _⁻¹ᴱ_)
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as Er using (Erased; [_])
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as PT
  using (∥_∥; Surjective)
open import Monad equality-with-J
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J using (_↠_; Split-surjective)

private
  variable
    a b ℓ p r         : Level
    A A₁ A₂ B B₁ B₂ C : Set a
    P Q               : A → Set p
    R                 : A → A → Set r
    f g k x y         : A

------------------------------------------------------------------------
-- The type former

-- A propositional truncation operator with an erased higher
-- constructor.

data ∥_∥ᴱ (A : Set a) : Set a where
  ∣_∣                           : A → ∥ A ∥ᴱ
  @0 truncation-is-propositionᴾ : P.Is-proposition ∥ A ∥ᴱ

-- The truncation produces propositions (in erased contexts).

@0 truncation-is-proposition : Is-proposition ∥ A ∥ᴱ
truncation-is-proposition =
  _↔_.from (H-level↔H-level 1) truncation-is-propositionᴾ

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ′ {A : Set a} (P : ∥ A ∥ᴱ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    @0 truncation-is-propositionʳ :
      (p : P x) (q : P y) →
      P.[ (λ i → P (truncation-is-propositionᴾ x y i)) ] p ≡ q

open Elimᴾ′ public

elimᴾ′ : Elimᴾ′ P → (x : ∥ A ∥ᴱ) → P x
elimᴾ′ {A = A} {P = P} e = helper
  where
  module E = Elimᴾ′ e

  helper : (x : ∥ A ∥ᴱ) → P x
  helper ∣ x ∣                              = E.∣∣ʳ x
  helper (truncation-is-propositionᴾ x y i) =
    E.truncation-is-propositionʳ (helper x) (helper y) i

-- A possibly more useful dependent eliminator, expressed using paths.

record Elimᴾ {A : Set a} (P : ∥ A ∥ᴱ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    @0 truncation-is-propositionʳ :
      (x : ∥ A ∥ᴱ) → P.Is-proposition (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : ∥ A ∥ᴱ) → P x
elimᴾ e = elimᴾ′ λ where
    .∣∣ʳ                            → E.∣∣ʳ
    .truncation-is-propositionʳ _ _ →
      P.heterogeneous-irrelevance E.truncation-is-propositionʳ
  where
  module E = Elimᴾ e

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ                           : A → B
    @0 truncation-is-propositionʳ : P.Is-proposition B

open Recᴾ public

recᴾ : Recᴾ A B → ∥ A ∥ᴱ → B
recᴾ r = elimᴾ λ where
    .∣∣ʳ                          → R.∣∣ʳ
    .truncation-is-propositionʳ _ → R.truncation-is-propositionʳ
  where
  module R = Recᴾ r

-- A dependently typed eliminator.

record Elim {A : Set a} (P : ∥ A ∥ᴱ → Set p) : Set (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    @0 truncation-is-propositionʳ :
      (x : ∥ A ∥ᴱ) → Is-proposition (P x)

open Elim public

elim : Elim P → (x : ∥ A ∥ᴱ) → P x
elim e = elimᴾ λ where
    .∣∣ʳ                        → E.∣∣ʳ
    .truncation-is-propositionʳ →
      _↔_.to (H-level↔H-level 1) ∘ E.truncation-is-propositionʳ
  where
  module E = Elim e

-- Primitive "recursion".

record Rec (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  field
    ∣∣ʳ                           : A → B
    @0 truncation-is-propositionʳ : Is-proposition B

open Rec public

rec : Rec A B → ∥ A ∥ᴱ → B
rec r = recᴾ λ where
    .∣∣ʳ                        → R.∣∣ʳ
    .truncation-is-propositionʳ →
      _↔_.to (H-level↔H-level 1) R.truncation-is-propositionʳ
  where
  module R = Rec r

------------------------------------------------------------------------
-- Conversion functions

-- If A is merely inhabited (with erased proofs), then A is merely
-- inhabited.

∥∥ᴱ→∥∥ : ∥ A ∥ᴱ → ∥ A ∥
∥∥ᴱ→∥∥ = rec λ where
  .∣∣ʳ                        → PT.∣_∣
  .truncation-is-propositionʳ → PT.truncation-is-proposition

-- In an erased context the propositional truncation operator defined
-- here is equivalent to the one defined in
-- H-level.Truncation.Propositional.

@0 ∥∥ᴱ≃∥∥ : ∥ A ∥ᴱ ≃ ∥ A ∥
∥∥ᴱ≃∥∥ = Eq.⇔→≃
  truncation-is-proposition
  PT.truncation-is-proposition
  ∥∥ᴱ→∥∥
  (PT.rec truncation-is-proposition ∣_∣)

------------------------------------------------------------------------
-- Some preservation lemmas and related results

-- A map function.

∥∥ᴱ-map : (A → B) → ∥ A ∥ᴱ → ∥ B ∥ᴱ
∥∥ᴱ-map f = rec λ where
  .∣∣ʳ                        → ∣_∣ ∘ f
  .truncation-is-propositionʳ → truncation-is-proposition

mutual

  -- If A and B are logically equivalent, then there is an equivalence
  -- with erased proofs between ∥ A ∥ᴱ and ∥ B ∥ᴱ.

  ∥∥ᴱ-cong-⇔ : A ⇔ B → ∥ A ∥ᴱ ≃ᴱ ∥ B ∥ᴱ
  ∥∥ᴱ-cong-⇔ A⇔B = ∥∥ᴱ-cong-⇔′ (∣_∣ ∘ _⇔_.to A⇔B) (∣_∣ ∘ _⇔_.from A⇔B)

  -- A variant of the previous result.

  ∥∥ᴱ-cong-⇔′ : (A → ∥ B ∥ᴱ) → (B → ∥ A ∥ᴱ) → ∥ A ∥ᴱ ≃ᴱ ∥ B ∥ᴱ
  ∥∥ᴱ-cong-⇔′ A→∥B∥ B→∥A∥ = EEq.⇔→≃ᴱ
    truncation-is-proposition
    truncation-is-proposition
    (rec λ where
       .∣∣ʳ                        → A→∥B∥
       .truncation-is-propositionʳ → truncation-is-proposition)
    (rec λ where
       .∣∣ʳ                        → B→∥A∥
       .truncation-is-propositionʳ → truncation-is-proposition)

-- The following lemma implies, among other things, that the
-- truncation operator preserves equivalences with erased proofs.

∥∥ᴱ-cong : A ↝[ ⌊ k ⌋-sym ] B → ∥ A ∥ᴱ ≃ᴱ ∥ B ∥ᴱ
∥∥ᴱ-cong {k = logical-equivalence} = ∥∥ᴱ-cong-⇔
∥∥ᴱ-cong {k = bijection}           = ∥∥ᴱ-cong-⇔ ∘ from-isomorphism
∥∥ᴱ-cong {k = equivalence}         = ∥∥ᴱ-cong-⇔ ∘ from-isomorphism
∥∥ᴱ-cong {k = equivalenceᴱ}        =
  ∥∥ᴱ-cong-⇔ ∘ _≃ᴱ_.logical-equivalence

_ : A ≃ᴱ B → ∥ A ∥ᴱ ≃ᴱ ∥ B ∥ᴱ
_ = ∥∥ᴱ-cong

------------------------------------------------------------------------
-- Some bijections/erased equivalences

-- If the underlying type is a proposition, then truncations of the
-- type are isomorphic to the type itself.

∥∥ᴱ↔ : @0 Is-proposition A → ∥ A ∥ᴱ ↔ A
∥∥ᴱ↔ A-prop = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec λ where
          .∣∣ʳ                        → id
          .truncation-is-propositionʳ → A-prop
      ; from = ∣_∣
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = elim λ where
      .∣∣ʳ _                        → refl _
      .truncation-is-propositionʳ _ → mono₁ 1 truncation-is-proposition
  }

-- If A is merely inhabited, then the truncation of A is equivalent
-- (with erased proofs) to the unit type.

inhabited⇒∥∥ᴱ≃ᴱ⊤ : ∥ A ∥ᴱ → ∥ A ∥ᴱ ≃ᴱ ⊤
inhabited⇒∥∥ᴱ≃ᴱ⊤ ∥a∥ =
  EEq.inhabited→Is-proposition→≃ᴱ⊤ ∥a∥ truncation-is-proposition

-- If A is not inhabited, then the propositional truncation of A is
-- isomorphic to the empty type.

not-inhabited⇒∥∥ᴱ↔⊥ : ¬ A → ∥ A ∥ᴱ ↔ ⊥ {ℓ = ℓ}
not-inhabited⇒∥∥ᴱ↔⊥ {A = A} =
  ¬ A         ↝⟨ (λ ¬a → rec λ where
                           .∣∣ʳ                        → ¬a
                           .truncation-is-propositionʳ → ⊥-propositional) ⟩
  ¬ ∥ A ∥ᴱ    ↝⟨ inverse ∘ Bijection.⊥↔uninhabited ⟩□
  ∥ A ∥ᴱ ↔ ⊥  □

-- The negation of the truncation of A is isomorphic to the negation
-- of A.

¬∥∥ᴱ↔¬ : ¬ ∥ A ∥ᴱ ↔ ¬ A
¬∥∥ᴱ↔¬ {A = A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → f ∘ ∣_∣
      ; from = λ ¬A → rec λ where
                        .∣∣ʳ                        → ¬A
                        .truncation-is-propositionʳ → ⊥-propositional
      }
    ; right-inverse-of = λ _ → ¬-propositional ext _ _
    }
  ; left-inverse-of = λ _ → ¬-propositional ext _ _
  }

-- A form of idempotence for binary sums.

idempotent : ∥ A ⊎ A ∥ᴱ ≃ᴱ ∥ A ∥ᴱ
idempotent = ∥∥ᴱ-cong-⇔ (record { to = P.[ id , id ]; from = inj₁ })

------------------------------------------------------------------------
-- The universal property

mutual

  -- The propositional truncation operator's universal property.
  --
  -- See also Quotient.Erased.Σ→Erased-Constant≃∥∥ᴱ→.

  universal-property :
    @0 Is-proposition B →
    (∥ A ∥ᴱ → B) ≃ (A → B)
  universal-property B-prop = universal-property-Π (λ _ → B-prop)

  -- A generalisation of the universal property.

  universal-property-Π :
    @0 (∀ x → Is-proposition (P x)) →
    ((x : ∥ A ∥ᴱ) → P x) ≃ ((x : A) → P ∣ x ∣)
  universal-property-Π {A = A} {P = P} P-prop =
    ((x : ∥ A ∥ᴱ) → P x)      ↝⟨ Eq.↔⇒≃ (record
                                   { surjection = record
                                     { logical-equivalence = record
                                       { to   = λ f → ∣ f ∘ ∣_∣ ∣
                                       ; from = rec λ where
                                           .∣∣ʳ f → elim λ where
                                             .∣∣ʳ                        → f
                                             .truncation-is-propositionʳ → P-prop
                                           .truncation-is-propositionʳ →
                                             Π-closure ext 1 λ _ → P-prop _
                                       }
                                     ; right-inverse-of = elim λ where
                                         .∣∣ʳ _                        → refl _
                                         .truncation-is-propositionʳ _ →
                                           mono₁ 1 truncation-is-proposition
                                     }
                                   ; left-inverse-of = λ f → ⟨ext⟩ $ elim λ where
                                       .∣∣ʳ _                        → refl _
                                       .truncation-is-propositionʳ _ →
                                         mono₁ 1 (P-prop _)
                                   }) ⟩
    ∥ ((x : A) → P ∣ x ∣) ∥ᴱ  ↔⟨ ∥∥ᴱ↔ (Π-closure ext 1 λ _ → P-prop _) ⟩□
    ((x : A) → P ∣ x ∣)       □

-- The universal property computes in the "right" way.

_ :
  (@0 B-prop : Is-proposition B)
  (f : ∥ A ∥ᴱ → B) →
  _≃_.to (universal-property B-prop) f ≡ f ∘ ∣_∣
_ = λ _ _ → refl _

_ :
  (@0 B-prop : Is-proposition B)
  (f : A → B) (x : A) →
  _≃_.from (universal-property B-prop) f ∣ x ∣ ≡ f x
_ = λ _ _ _ → refl _

------------------------------------------------------------------------
-- Some results based on "Generalizations of Hedberg's Theorem" by
-- Kraus, Escardó, Coquand and Altenkirch

-- Types with constant endofunctions are "h-stable" (meaning that
-- "mere inhabitance" implies inhabitance).

constant-endofunction⇒h-stable :
  {f : A → A} → @0 Constant f → ∥ A ∥ᴱ → A
constant-endofunction⇒h-stable {A = A} {f = f} c =
  ∥ A ∥ᴱ                            ↝⟨ (rec λ where
                                          .∣∣ʳ x → f x , [ c (f x) x ]
                                          .truncation-is-propositionʳ → prop) ⟩
  (∃ λ (x : A) → Erased (f x ≡ x))  ↝⟨ proj₁ ⟩□
  A                                 □
  where
  @0 prop : _
  prop =                                       $⟨ fixpoint-lemma f c ⟩
    Is-proposition (∃ λ x → f x ≡ x)           ↝⟨ H-level-cong _ 1 (∃-cong λ _ → inverse $ Er.erased Er.Erased↔) ⦂ (_ → _) ⟩□
    Is-proposition (∃ λ x → Erased (f x ≡ x))  □

-- Having a constant endofunction is logically equivalent to being
-- h-stable.

constant-endofunction⇔h-stable :
  (∃ λ (f : A → A) → Erased (Constant f)) ⇔ (∥ A ∥ᴱ → A)
constant-endofunction⇔h-stable = record
  { to   = λ (_ , [ c ]) → constant-endofunction⇒h-stable c
  ; from = λ f → f ∘ ∣_∣
         , [ (λ x y →
                f ∣ x ∣  ≡⟨ cong f $ truncation-is-proposition _ _ ⟩∎
                f ∣ y ∣  ∎)
           ]
  }

------------------------------------------------------------------------
-- Some results related to _×_

-- The cartesian product of the truncation of A and A is equivalent
-- (with erased "proofs") to A.

∥∥ᴱ×≃ : (∥ A ∥ᴱ × A) ≃ᴱ A
∥∥ᴱ×≃ =
  EEq.⟨ proj₂
      , (λ a → EEq.inhabited→Is-proposition→Contractibleᴱ
                 ((∣ a ∣ , a) , [ refl _ ])
                 (                                     $⟨ EEq.bijection⁻¹ᴱ-contractible
                                                            proj₂
                                                            (λ a → ∣ a ∣ , a)
                                                            refl
                                                            (λ p → cong (_, _) $
                                                                     truncation-is-proposition _ _)
                                                            a ⟩
                  EEq.Contractibleᴱ (proj₂ EEq.⁻¹ᴱ a)  ↔⟨ inverse EEq.Contractible≃Contractibleᴱ ⟩
                  Contractible (proj₂ EEq.⁻¹ᴱ a)       ↝⟨ mono₁ 0 ⟩□
                  Is-proposition (proj₂ EEq.⁻¹ᴱ a)     □))
      ⟩

-- The application _≃ᴱ_.right-inverse-of ∥∥ᴱ×≃ x computes in a certain
-- way.

_ : _≃ᴱ_.right-inverse-of ∥∥ᴱ×≃ x ≡ refl _
_ = refl _

-- This is, at the time of writing, not the case for the following
-- proof.

_ : (∥ A ∥ᴱ × A) ≃ᴱ A
_ = EEq.[≃]→≃ᴱ (EEq.[proofs] (PT.∥∥×≃ Eq.∘ (∥∥ᴱ≃∥∥ ×-cong Eq.id)))

-- ∥_∥ᴱ commutes with _×_.

∥∥ᴱ×∥∥ᴱ↔∥×∥ᴱ : (∥ A ∥ᴱ × ∥ B ∥ᴱ) ↔ ∥ A × B ∥ᴱ
∥∥ᴱ×∥∥ᴱ↔∥×∥ᴱ = record
  { surjection = record
    { logical-equivalence = record
      { from = λ p → ∥∥ᴱ-map proj₁ p , ∥∥ᴱ-map proj₂ p
      ; to   = uncurry $ rec λ where
                 .∣∣ʳ x → rec λ where
                   .∣∣ʳ y                      → ∣ x , y ∣
                   .truncation-is-propositionʳ →
                     truncation-is-proposition
                 .truncation-is-propositionʳ →
                   Π-closure ext 1 λ _ →
                   truncation-is-proposition
      }
    ; right-inverse-of = elim λ where
        .∣∣ʳ _                        → refl _
        .truncation-is-propositionʳ _ →
          mono₁ 1 truncation-is-proposition
    }
  ; left-inverse-of = uncurry $ elim λ where
      .∣∣ʳ _ → elim λ where
        .∣∣ʳ _ → refl _
        .truncation-is-propositionʳ _ →
          mono₁ 1 $
          ×-closure 1 truncation-is-proposition
                      truncation-is-proposition
      .truncation-is-propositionʳ _ →
        Π-closure ext 1 λ _ →
        mono₁ 1 $
        ×-closure 1 truncation-is-proposition
                    truncation-is-proposition
  }

------------------------------------------------------------------------
-- Some results related to h-levels

-- Variants of proj₁-closure.

H-level-×₁ :
  (A → ∥ B ∥ᴱ) →
  ∀ n → H-level n (A × B) → H-level n A
H-level-×₁ inhabited = PT.H-level-×₁ (∥∥ᴱ→∥∥ ∘ inhabited)

H-level-×₂ :
  (B → ∥ A ∥ᴱ) →
  ∀ n → H-level n (A × B) → H-level n B
H-level-×₂ inhabited = PT.H-level-×₂ (∥∥ᴱ→∥∥ ∘ inhabited)

------------------------------------------------------------------------
-- Flattening

-- A generalised flattening lemma.

flatten′ :
  (F : (Set ℓ → Set ℓ) → Set f)
  (map : ∀ {G H} → (∀ {A} → G A → H A) → F G → F H)
  (f : F ∥_∥ᴱ → ∥ F id ∥ᴱ) →
  (∀ x → f (map ∣_∣ x) ≡ ∣ x ∣) →
  (∀ x → ∥∥ᴱ-map (map ∣_∣) (f x) ≡ ∣ x ∣) →
  ∥ F ∥_∥ᴱ ∥ᴱ ↔ ∥ F id ∥ᴱ
flatten′ _ map f f-map map-f = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec λ where
                 .∣∣ʳ                        → f
                 .truncation-is-propositionʳ → truncation-is-proposition
      ; from = ∥∥ᴱ-map (map ∣_∣)
      }
    ; right-inverse-of = elim λ where
        .∣∣ʳ                          → f-map
        .truncation-is-propositionʳ _ →
          mono₁ 1 truncation-is-proposition
    }
  ; left-inverse-of = elim λ where
      .∣∣ʳ                          → map-f
      .truncation-is-propositionʳ _ →
        mono₁ 1 truncation-is-proposition
  }

-- Nested truncations can be flattened.

flatten : ∥ ∥ A ∥ᴱ ∥ᴱ ↔ ∥ A ∥ᴱ
flatten {A = A} = flatten′
  (λ F → F A)
  (λ f → f)
  id
  (λ _ → refl _)
  (elim λ where
     .∣∣ʳ _                        → refl _
     .truncation-is-propositionʳ _ → mono₁ 1 truncation-is-proposition)

private

  -- Another flattening lemma, given as an example of how flatten′ can
  -- be used.

  ∥∃∥∥ᴱ∥ᴱ↔∥∃∥ᴱ : ∥ ∃ (∥_∥ᴱ ∘ P) ∥ᴱ ↔ ∥ ∃ P ∥ᴱ
  ∥∃∥∥ᴱ∥ᴱ↔∥∃∥ᴱ {P = P} = flatten′
    (λ F → ∃ (F ∘ P))
    (λ f → Σ-map id f)
    (uncurry λ x → ∥∥ᴱ-map (x ,_))
    (λ _ → refl _)
    (uncurry λ _ → elim λ where
       .∣∣ʳ _ → refl _
       .truncation-is-propositionʳ _ →
         mono₁ 1 truncation-is-proposition)

------------------------------------------------------------------------
-- The propositional truncation operator is a monad

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∥ A ∥ᴱ → (A → ∥ B ∥ᴱ) → ∥ B ∥ᴱ
x >>=′ f = _↔_.to flatten (∥∥ᴱ-map f x)

-- The universe-polymorphic variant of bind is associative.

>>=′-associative :
  (x : ∥ A ∥ᴱ) →
  x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
>>=′-associative = elim λ where
  .∣∣ʳ _                        → refl _
  .truncation-is-propositionʳ _ → ⇒≡ 1 truncation-is-proposition

instance

  -- The propositional truncation operator is a monad.

  raw-monad : Raw-monad (∥_∥ᴱ {a = a})
  Raw-monad.return raw-monad = ∣_∣
  Raw-monad._>>=_  raw-monad = _>>=′_

  monad : Monad (∥_∥ᴱ {a = a})
  Monad.raw-monad monad           = raw-monad
  Monad.left-identity monad _ _   = refl _
  Monad.associativity monad x _ _ = >>=′-associative x
  Monad.right-identity monad      = elim λ where
    .∣∣ʳ                        _ → refl _
    .truncation-is-propositionʳ _ → ⇒≡ 1 truncation-is-proposition

------------------------------------------------------------------------
-- Surjectivity

-- A variant of surjectivity with "erased proofs".

Surjectiveᴱ :
  {A : Set a} {B : Set b} →
  (A → B) → Set (a ⊔ b)
Surjectiveᴱ f = ∀ y → ∥ f ⁻¹ᴱ y ∥ᴱ

-- The property Surjectiveᴱ f is a proposition (in erased contexts).

@0 Surjectiveᴱ-propositional : Is-proposition (Surjectiveᴱ f)
Surjectiveᴱ-propositional =
  Π-closure ext 1 λ _ →
  truncation-is-proposition

-- The function ∣_∣ is surjective (with erased proofs).

∣∣-surjective : Surjectiveᴱ (∣_∣ {A = A})
∣∣-surjective = elim λ where
  .∣∣ʳ x                        → ∣ x , [ refl _ ] ∣
  .truncation-is-propositionʳ _ → truncation-is-proposition

-- Split surjective functions are surjective (with erased proofs).

Split-surjective→Surjectiveᴱ :
  Split-surjective f → Surjectiveᴱ f
Split-surjective→Surjectiveᴱ s = λ y → ∣ EEq.⁻¹→⁻¹ᴱ (s y) ∣

-- In an erased context surjectivity with erased proofs is equivalent
-- to surjectivity.
--
-- It appears to me as if neither direction of this equivalence can be
-- established if the erasure annotation is removed.

@0 Surjectiveᴱ≃Surjective : Surjectiveᴱ f ≃ Surjective f
Surjectiveᴱ≃Surjective {f = f} =
  (∀ y → ∥ f ⁻¹ᴱ y ∥ᴱ)  ↝⟨ (∀-cong ext λ _ → ∥∥ᴱ≃∥∥) ⟩
  (∀ y → ∥ f ⁻¹ᴱ y ∥)   ↝⟨ (∀-cong ext λ _ → PT.∥∥-cong (inverse EEq.⁻¹≃⁻¹ᴱ)) ⟩□
  (∀ y → ∥ f ⁻¹  y ∥)   □

-- Being both surjective (with erased proofs) and an embedding
-- (completely erased) is equivalent to being an equivalence (with
-- erased proofs).
--
-- This result, without erasure, is Corollary 4.6.4 from the first
-- edition of the HoTT book.

Surjectiveᴱ×Erased-Is-embedding≃ᴱIs-equivalenceᴱ :
  (Surjectiveᴱ f × Erased (Is-embedding f)) ≃ᴱ Is-equivalenceᴱ f
Surjectiveᴱ×Erased-Is-embedding≃ᴱIs-equivalenceᴱ {f = f} = EEq.⇔→≃ᴱ
  (×-closure 1
     Surjectiveᴱ-propositional
     (Er.H-level-Erased 1
        (Emb.Is-embedding-propositional ext)))
  (EEq.Is-equivalenceᴱ-propositional ext f)
  (λ (is-surj , is-emb) y →
                              $⟨ is-surj y ⟩
     ∥ f ⁻¹ᴱ y ∥ᴱ             ↝⟨ (rec λ where
                                    .∣∣ʳ p → EEq.inhabited→Is-proposition→Contractibleᴱ p
                                               (H-level-cong _ 1
                                                  EEq.⁻¹≃⁻¹ᴱ
                                                  (Emb.embedding→⁻¹-propositional (Er.erased is-emb) _))
                                    .truncation-is-propositionʳ →
                                      EEq.Contractibleᴱ-propositional ext) ⟩□
     Contractibleᴱ (f ⁻¹ᴱ y)  □)
  (λ is-eq →
       (λ y →                      $⟨ is-eq y ⟩
          Contractibleᴱ (f ⁻¹ᴱ y)  ↝⟨ proj₁ ⟩
          f ⁻¹ᴱ y                  ↝⟨ ∣_∣ ⟩
          ∥ f ⁻¹ᴱ y ∥ᴱ             □)

     ,                            ($⟨ is-eq ⟩
       Is-equivalenceᴱ f           ↝⟨ Er.[_]→ ⟩
       Erased (Is-equivalenceᴱ f)  ↝⟨ Er.map EEq.Is-equivalenceᴱ→Is-equivalence ⟩
       Erased (Is-equivalence f)   ↝⟨ Er.map Emb.Is-equivalence→Is-embedding ⟩□
       Erased (Is-embedding f)     □))

------------------------------------------------------------------------
-- Another lemma

-- The function λ R x y → ∥ R x y ∥ᴱ preserves Is-equivalence-relation.

∥∥ᴱ-preserves-Is-equivalence-relation :
  Is-equivalence-relation R →
  Is-equivalence-relation (λ x y → ∥ R x y ∥ᴱ)
∥∥ᴱ-preserves-Is-equivalence-relation R-equiv = record
  { reflexive  = ∣ reflexive ∣
  ; symmetric  = symmetric ⟨$⟩_
  ; transitive = λ p q → transitive ⟨$⟩ p ⊛ q
  }
  where
  open Is-equivalence-relation R-equiv

------------------------------------------------------------------------
-- Definitions related to truncated binary sums

-- Truncated binary sums.

infixr 1 _∥⊎∥ᴱ_

_∥⊎∥ᴱ_ : Set a → Set b → Set (a ⊔ b)
A ∥⊎∥ᴱ B = ∥ A ⊎ B ∥ᴱ

-- Introduction rules.

∣inj₁∣ : A → A ∥⊎∥ᴱ B
∣inj₁∣ = ∣_∣ ∘ inj₁

∣inj₂∣ : B → A ∥⊎∥ᴱ B
∣inj₂∣ = ∣_∣ ∘ inj₂

-- In erased contexts _∥⊎∥ᴱ_ is pointwise propositional.

@0 ∥⊎∥ᴱ-propositional : Is-proposition (A ∥⊎∥ᴱ B)
∥⊎∥ᴱ-propositional = truncation-is-proposition

-- The following lemma implies, among other things, that _∥⊎∥ᴱ_
-- preserves equivalences with erased proofs.

infixr 1 _∥⊎∥ᴱ-cong_

_∥⊎∥ᴱ-cong_ :
  A₁ ↝[ ⌊ k ⌋-sym ] A₂ → B₁ ↝[ ⌊ k ⌋-sym ] B₂ →
  (A₁ ∥⊎∥ᴱ B₁) ≃ᴱ (A₂ ∥⊎∥ᴱ B₂)
A₁↝A₂ ∥⊎∥ᴱ-cong B₁↝B₂ = ∥∥ᴱ-cong (A₁↝A₂ ⊎-cong B₁↝B₂)

_ : A₁ ≃ᴱ A₂ → B₁ ≃ᴱ B₂ → (A₁ ∥⊎∥ᴱ B₁) ≃ᴱ (A₂ ∥⊎∥ᴱ B₂)
_ = _∥⊎∥ᴱ-cong_

-- _∥⊎∥ᴱ_ is commutative.

∥⊎∥ᴱ-comm : A ∥⊎∥ᴱ B ↔ B ∥⊎∥ᴱ A
∥⊎∥ᴱ-comm = record
  { surjection = record
    { logical-equivalence = record
      { to   = swap′
      ; from = swap′
      }
    ; right-inverse-of = swap′∘swap′
    }
  ; left-inverse-of = swap′∘swap′
  }
  where
  swap′ : A ∥⊎∥ᴱ B → B ∥⊎∥ᴱ A
  swap′ = rec λ where
    .∣∣ʳ → P.[ ∣inj₂∣ , ∣inj₁∣ ]
    .truncation-is-propositionʳ →
      ∥⊎∥ᴱ-propositional

  swap′∘swap′ : (x : A ∥⊎∥ᴱ B) → swap′ (swap′ x) ≡ x
  swap′∘swap′ = elim λ where
    .∣∣ʳ → P.[ (λ _ → refl _) , (λ _ → refl _) ]
    .truncation-is-propositionʳ _ →
      mono₁ 1 ∥⊎∥ᴱ-propositional

-- If one truncates the types to the left or right of _∥⊎∥ᴱ_, then one
-- ends up with an isomorphic type.

truncate-left-∥⊎∥ᴱ : A ∥⊎∥ᴱ B ↔ ∥ A ∥ᴱ ∥⊎∥ᴱ B
truncate-left-∥⊎∥ᴱ =
  inverse $
  flatten′
    (λ F → F _ ⊎ _)
    (λ f → ⊎-map f id)
    P.[ ∥∥ᴱ-map inj₁ , ∣inj₂∣ ]
    P.[ (λ _ → refl _) , (λ _ → refl _) ]
    P.[ (elim λ where
           .∣∣ʳ _ → refl _
           .truncation-is-propositionʳ _ →
             mono₁ 1 ∥⊎∥ᴱ-propositional)
      , (λ _ → refl _)
      ]

truncate-right-∥⊎∥ᴱ : A ∥⊎∥ᴱ B ↔ A ∥⊎∥ᴱ ∥ B ∥ᴱ
truncate-right-∥⊎∥ᴱ {A = A} {B = B} =
  A ∥⊎∥ᴱ B       ↝⟨ ∥⊎∥ᴱ-comm ⟩
  B ∥⊎∥ᴱ A       ↝⟨ truncate-left-∥⊎∥ᴱ ⟩
  ∥ B ∥ᴱ ∥⊎∥ᴱ A  ↝⟨ ∥⊎∥ᴱ-comm ⟩□
  A ∥⊎∥ᴱ ∥ B ∥ᴱ  □

-- _∥⊎∥ᴱ_ is associative.

∥⊎∥ᴱ-assoc : A ∥⊎∥ᴱ (B ∥⊎∥ᴱ C) ↔ (A ∥⊎∥ᴱ B) ∥⊎∥ᴱ C
∥⊎∥ᴱ-assoc {A = A} {B = B} {C = C} =
  ∥ A ⊎ ∥ B ⊎ C ∥ᴱ ∥ᴱ  ↝⟨ inverse truncate-right-∥⊎∥ᴱ ⟩
  ∥ A ⊎ B ⊎ C ∥ᴱ       ↝⟨ lemma ⟩
  ∥ (A ⊎ B) ⊎ C ∥ᴱ     ↝⟨ truncate-left-∥⊎∥ᴱ ⟩□
  ∥ ∥ A ⊎ B ∥ᴱ ⊎ C ∥ᴱ  □
  where
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to = rec λ where
            .∣∣ʳ → P.[ ∣inj₁∣ ∘ inj₁ , P.[ ∣inj₁∣ ∘ inj₂ , ∣inj₂∣ ] ]
            .truncation-is-propositionʳ → ∥⊎∥ᴱ-propositional
        ; from = rec λ where
            .∣∣ʳ → P.[ P.[ ∣inj₁∣ , ∣inj₂∣ ∘ inj₁ ] , ∣inj₂∣ ∘ inj₂ ]
            .truncation-is-propositionʳ → ∥⊎∥ᴱ-propositional
        }
      ; right-inverse-of = elim λ where
          .∣∣ʳ → P.[ P.[ (λ _ → refl _) , (λ _ → refl _) ]
                   , (λ _ → refl _)
                   ]
          .truncation-is-propositionʳ _ →
            mono₁ 1 ∥⊎∥ᴱ-propositional
      }
    ; left-inverse-of = elim λ where
        .∣∣ʳ → P.[ (λ _ → refl _)
                 , P.[ (λ _ → refl _) , (λ _ → refl _) ]
                 ]
        .truncation-is-propositionʳ _ →
          mono₁ 1 ∥⊎∥ᴱ-propositional
    }

-- ⊥ is a left and right identity of _∥⊎∥ᴱ_ if the other argument is a
-- proposition.

∥⊎∥ᴱ-left-identity : @0 Is-proposition A → ⊥ {ℓ = ℓ} ∥⊎∥ᴱ A ↔ A
∥⊎∥ᴱ-left-identity {A = A} A-prop =
  ∥ ⊥ ⊎ A ∥ᴱ  ↝⟨ lemma ⟩
  ∥ A ∥ᴱ      ↝⟨ ∥∥ᴱ↔ A-prop ⟩□
  A          □
  where
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to = rec λ where
            .∣∣ʳ → P.[ ⊥-elim , ∣_∣ ]
            .truncation-is-propositionʳ → truncation-is-proposition
        ; from = rec λ where
            .∣∣ʳ → ∣inj₂∣
            .truncation-is-propositionʳ → ∥⊎∥ᴱ-propositional
        }
      ; right-inverse-of = elim λ where
          .∣∣ʳ _ → refl _
          .truncation-is-propositionʳ _ →
            mono₁ 1 truncation-is-proposition
      }
    ; left-inverse-of = elim λ where
        .∣∣ʳ → P.[ (λ x → ⊥-elim x) , (λ _ → refl _) ]
        .truncation-is-propositionʳ _ →
          mono₁ 1 ∥⊎∥ᴱ-propositional
    }

∥⊎∥ᴱ-right-identity : @0 Is-proposition A → A ∥⊎∥ᴱ ⊥ {ℓ = ℓ} ↔ A
∥⊎∥ᴱ-right-identity {A = A} A-prop =
  A ∥⊎∥ᴱ ⊥  ↔⟨ ∥⊎∥ᴱ-comm ⟩
  ⊥ ∥⊎∥ᴱ A  ↔⟨ ∥⊎∥ᴱ-left-identity A-prop ⟩□
  A         □

-- _∥⊎∥ᴱ_ is idempotent for propositions (up to equivalences with
-- erased proofs).

∥⊎∥ᴱ-idempotent : @0 Is-proposition A → (A ∥⊎∥ᴱ A) ≃ᴱ A
∥⊎∥ᴱ-idempotent {A = A} A-prop =
  ∥ A ⊎ A ∥ᴱ  ↝⟨ idempotent ⟩
  ∥ A ∥ᴱ      ↔⟨ ∥∥ᴱ↔ A-prop ⟩□
  A           □

-- Sometimes a truncated binary sum is equivalent (with erased proofs)
-- to one of its summands.

drop-left-∥⊎∥ᴱ :
  @0 Is-proposition B → (A → B) → (A ∥⊎∥ᴱ B) ≃ᴱ B
drop-left-∥⊎∥ᴱ B-prop A→B = EEq.⇔→≃ᴱ
  ∥⊎∥ᴱ-propositional
  B-prop
  (rec λ where
     .∣∣ʳ → P.[ A→B , id ]
     .truncation-is-propositionʳ → B-prop)
  ∣inj₂∣

drop-right-∥⊎∥ᴱ :
  @0 Is-proposition A → (B → A) → (A ∥⊎∥ᴱ B) ≃ᴱ A
drop-right-∥⊎∥ᴱ {A = A} {B = B} A-prop B→A =
  A ∥⊎∥ᴱ B  ↔⟨ ∥⊎∥ᴱ-comm ⟩
  B ∥⊎∥ᴱ A  ↝⟨ drop-left-∥⊎∥ᴱ A-prop B→A ⟩□
  A        □

-- Sometimes a truncated binary sum is isomorphic to one of its
-- summands.

drop-⊥-right-∥⊎∥ᴱ :
  @0 Is-proposition A → ¬ B → A ∥⊎∥ᴱ B ↔ A
drop-⊥-right-∥⊎∥ᴱ A-prop ¬B = record
  { surjection = record
    { logical-equivalence = record
      { to = rec λ where
          .∣∣ʳ → P.[ id , ⊥-elim ∘ ¬B ]
          .truncation-is-propositionʳ → A-prop
      ; from = ∣inj₁∣
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = elim λ where
      .∣∣ʳ → P.[ (λ _ → refl _) , ⊥-elim ∘ ¬B ]
      .truncation-is-propositionʳ _ →
        mono₁ 1 ∥⊎∥ᴱ-propositional
  }

drop-⊥-left-∥⊎∥ᴱ :
  @0 Is-proposition B → ¬ A → A ∥⊎∥ᴱ B ↔ B
drop-⊥-left-∥⊎∥ᴱ B-prop ¬A = record
  { surjection = record
    { logical-equivalence = record
      { to = rec λ where
          .∣∣ʳ → P.[ ⊥-elim ∘ ¬A , id ]
          .truncation-is-propositionʳ → B-prop
      ; from = ∣inj₂∣
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = elim λ where
      .∣∣ʳ → P.[ ⊥-elim ∘ ¬A , (λ _ → refl _) ]
      .truncation-is-propositionʳ _ →
        mono₁ 1 ∥⊎∥ᴱ-propositional
  }

-- A type of functions from a truncated binary sum to a family of
-- propositions can be expressed as a binary product of function
-- types.

Π∥⊎∥ᴱ↔Π×Π :
  @0 (∀ x → Is-proposition (P x)) →
  ((x : A ∥⊎∥ᴱ B) → P x)
    ↔
  ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))
Π∥⊎∥ᴱ↔Π×Π {A = A} {B = B} {P = P} P-prop =
  ((x : A ∥⊎∥ᴱ B) → P x)                               ↔⟨ universal-property-Π P-prop ⟩
  ((x : A ⊎ B) → P ∣ x ∣)                              ↝⟨ Π⊎↔Π×Π ext ⟩□
  ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))  □

-- Two distributivity laws for Σ and _∥⊎∥ᴱ_.

Σ-∥⊎∥ᴱ-distrib-left :
  @0 Is-proposition A →
  Σ A (λ x → P x ∥⊎∥ᴱ Q x) ↔ Σ A P ∥⊎∥ᴱ Σ A Q
Σ-∥⊎∥ᴱ-distrib-left {P = P} {Q = Q} A-prop =
  (∃ λ x → ∥ P x ⊎ Q x ∥ᴱ)       ↝⟨ inverse $ ∥∥ᴱ↔ (Σ-closure 1 A-prop λ _ → ∥⊎∥ᴱ-propositional) ⟩
  ∥ (∃ λ x → ∥ P x ⊎ Q x ∥ᴱ) ∥ᴱ  ↝⟨ flatten′
                                      (λ F → (∃ λ x → F (P x ⊎ Q x)))
                                      (λ f → Σ-map id f)
                                      (uncurry λ x → ∥∥ᴱ-map (x ,_))
                                      (λ _ → refl _)
                                      (uncurry λ _ → elim λ where
                                         .∣∣ʳ _ → refl _
                                         .truncation-is-propositionʳ _ →
                                           mono₁ 1 truncation-is-proposition) ⟩
  ∥ (∃ λ x → P x ⊎ Q x) ∥ᴱ       ↝⟨ lemma ⟩□
  ∥ ∃ P ⊎ ∃ Q ∥ᴱ                 □
  where
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to = rec λ where
            .∣∣ʳ → ∣_∣ ∘ _↔_.to ∃-⊎-distrib-left
            .truncation-is-propositionʳ →
              ∥⊎∥ᴱ-propositional
        ; from = rec λ where
            .∣∣ʳ → ∣_∣ ∘ _↔_.from ∃-⊎-distrib-left
            .truncation-is-propositionʳ →
              truncation-is-proposition
        }
      ; right-inverse-of = elim λ where
        .∣∣ʳ → P.[ (λ _ → refl _) , (λ _ → refl _) ]
        .truncation-is-propositionʳ _ →
          mono₁ 1 ∥⊎∥ᴱ-propositional
      }
    ; left-inverse-of = elim λ where
        .∣∣ʳ → uncurry λ _ → P.[ (λ _ → refl _) , (λ _ → refl _) ]
        .truncation-is-propositionʳ _ →
          mono₁ 1 truncation-is-proposition
    }

Σ-∥⊎∥ᴱ-distrib-right :
  @0 (∀ x → Is-proposition (P x)) →
  Σ (A ∥⊎∥ᴱ B) P ↔ Σ A (P ∘ ∣inj₁∣) ∥⊎∥ᴱ Σ B (P ∘ ∣inj₂∣)
Σ-∥⊎∥ᴱ-distrib-right {A = A} {B = B} {P = P} P-prop = record
  { surjection = record
    { logical-equivalence = record
      { to = uncurry $ elim λ where
          .∣∣ʳ → curry (∣_∣ ∘ _↔_.to ∃-⊎-distrib-right)
          .truncation-is-propositionʳ _ →
            Π-closure ext 1 λ _ →
            ∥⊎∥ᴱ-propositional
      ; from = rec λ where
          .∣∣ʳ → Σ-map ∣_∣ id ∘ _↔_.from ∃-⊎-distrib-right
          .truncation-is-propositionʳ → prop
      }
    ; right-inverse-of = elim λ where
      .∣∣ʳ → P.[ (λ _ → refl _) , (λ _ → refl _) ]
      .truncation-is-propositionʳ _ →
        mono₁ 1 ∥⊎∥ᴱ-propositional
    }
  ; left-inverse-of = uncurry $ elim λ where
      .∣∣ʳ → P.[ (λ _ _ → refl _) , (λ _ _ → refl _) ]
      .truncation-is-propositionʳ _ →
        Π-closure ext 1 λ _ →
        mono₁ 1 prop
  }
  where
  @0 prop : _
  prop = Σ-closure 1 ∥⊎∥ᴱ-propositional P-prop

-- A variant of one of De Morgan's laws.

¬∥⊎∥ᴱ¬↔¬× :
  Dec A → Dec B →
  (¬ A ∥⊎∥ᴱ ¬ B) ≃ᴱ (¬ (A × B))
¬∥⊎∥ᴱ¬↔¬× {A = A} {B = B} dec-A dec-B = EEq.⇔→≃ᴱ
  ∥⊎∥ᴱ-propositional
  (¬-propositional ext)
  (rec λ where
     .∣∣ʳ → ¬⊎¬→×¬
     .truncation-is-propositionʳ → ¬-propositional ext)
  (∣_∣ ∘ _↠_.from (¬⊎¬↠¬× ext dec-A dec-B))
