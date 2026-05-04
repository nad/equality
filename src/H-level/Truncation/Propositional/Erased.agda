------------------------------------------------------------------------
-- A variant of the propositional truncation operator with an erased
-- truncation constructor
------------------------------------------------------------------------

-- Partly following the HoTT book, but adapted for erasure.

{-# OPTIONS --cubical=no-glue --safe #-}

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

open import Accessibility equality-with-J as A using (Acc)
open import Bijection equality-with-J as Bijection using (_↔_)
import Colimit.Sequential.Very-erased eq as C
open import Embedding equality-with-J as Emb using (Is-embedding)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased equality-with-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages equality-with-J
  as ECP using (Contractibleᴱ; _⁻¹ᴱ_)
open import Equivalence.Path-split equality-with-J as PS
  using (Is-∞-extendable-along-[_])
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as Er
  using (Erased; [_]; erased; Very-stableᴱ-≡; Erased-singleton)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.Erased.Axiomatised
  equality-with-J
open import H-level.Truncation.Propositional.One-step eq as O
  using (∥_∥¹-out-^)
import H-level.Truncation.Propositional.Non-recursive.Erased eq as N
open import Modality.Basics equality-with-J
open import Monad equality-with-J
import Nat equality-with-J as Nat
open import Preimage equality-with-J using (_⁻¹_)
open import Surjection equality-with-J as S
  using (_↠_; Split-surjective)

private
  variable
    a b ℓ p r         : Level
    A A₁ A₂ B B₁ B₂ C : Type a
    P Q               : A → Type p
    R                 : A → A → Type r
    f g k x y         : A

------------------------------------------------------------------------
-- The type former

-- A propositional truncation operator with an erased higher
-- constructor.

data ∥_∥ᴱ (A : Type a) : Type a where
  ∣_∣                           : A → ∥ A ∥ᴱ
  @0 truncation-is-propositionᴾ : P.Is-proposition ∥ A ∥ᴱ

-- The truncation produces propositions (in erased contexts).

@0 truncation-is-proposition : Is-proposition ∥ A ∥ᴱ
truncation-is-proposition =
  _↔_.from (H-level↔H-level 1) truncation-is-propositionᴾ

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ′ {A : Type a} (P : ∥ A ∥ᴱ → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    ∣∣ʳ : (x : A) → P ∣ x ∣

    @0 truncation-is-propositionʳ :
      (p : P x) (q : P y) →
      P.[ (λ i → P (truncation-is-propositionᴾ x y i)) ] p ≡ q

open Elimᴾ′ public

elimᴾ′ : Elimᴾ′ P → (x : ∥ A ∥ᴱ) → P x
elimᴾ′ {A} {P} e = helper
  where
  module E = Elimᴾ′ e

  helper : (x : ∥ A ∥ᴱ) → P x
  helper ∣ x ∣                              = E.∣∣ʳ x
  helper (truncation-is-propositionᴾ x y i) =
    E.truncation-is-propositionʳ (helper x) (helper y) i

-- A possibly more useful dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : ∥ A ∥ᴱ → Type p) : Type (a ⊔ p) where
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

record Recᴾ (A : Type a) (B : Type b) : Type (a ⊔ b) where
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

------------------------------------------------------------------------
-- An instantiation of Truncationᴱ

-- ∥_∥ᴱ is a truncation operator.

truncation : Truncationᴱ
truncation .Truncationᴱ.∥_∥ᴱ                      = ∥_∥ᴱ
truncation .Truncationᴱ.∣_∣                       = ∣_∣
truncation .Truncationᴱ.truncation-is-proposition =
  truncation-is-proposition
truncation .Truncationᴱ.eliminator f p = elimᴾ λ where
  .∣∣ʳ                        → f
  .truncation-is-propositionʳ → _↔_.to (H-level↔H-level 1) ∘ p
truncation .Truncationᴱ.eliminator-∣∣ = refl _

open Truncationᴱ truncation public
  hiding (∥_∥ᴱ; ∣_∣; truncation-is-proposition)

------------------------------------------------------------------------
-- Conversion functions

opaque
  unfolding elim rec

  -- ∥_∥ᴱ is pointwise equivalent to N.∥_∥ᴱ.

  ∥∥ᴱ≃∥∥ᴱ : ∥ A ∥ᴱ ≃ N.∥ A ∥ᴱ
  ∥∥ᴱ≃∥∥ᴱ = Eq.↔→≃
    (rec λ where
       .∣∣ʳ                        → N.∣_∣
       .truncation-is-propositionʳ → N.∥∥ᴱ-proposition)
    (N.elim λ where
       .N.∣∣ʳ               → ∣_∣
       .N.is-propositionʳ _ → truncation-is-proposition)
    (N.elim λ where
       .N.∣∣ʳ _             → refl _
       .N.is-propositionʳ _ → mono₁ 1 N.∥∥ᴱ-proposition)
    (elim λ where
       .∣∣ʳ _                        → refl _
       .truncation-is-propositionʳ _ → mono₁ 1 truncation-is-proposition)

------------------------------------------------------------------------
-- Some lemmas

-- Functions from ∥ A ∥ᴱ can be expressed as functions from A along
-- with some erased data.

∥∥ᴱ→≃ :
  (∥ A ∥ᴱ → B)
    ≃
  (∃ λ (f : A → B) →
     Erased (∃ λ (g : ∀ n → ∥ A ∥¹-out-^ (suc n) → B) →
               (∀ x → g zero O.∣ x ∣ ≡ f x) ×
               (∀ n x → g (suc n) O.∣ x ∣ ≡ g n x)))
∥∥ᴱ→≃ {A} {B} =
  (∥ A ∥ᴱ → B)                                           ↝⟨ →-cong ext ∥∥ᴱ≃∥∥ᴱ F.id ⟩

  (N.∥ A ∥ᴱ → B)                                         ↝⟨ C.universal-property ⟩□

  (∃ λ (f : A → B) →
     Erased (∃ λ (g : ∀ n → ∥ A ∥¹-out-^ (suc n) → B) →
               (∀ x → g zero O.∣ x ∣ ≡ f x) ×
               (∀ n x → g (suc n) O.∣ x ∣ ≡ g n x)))     □

opaque
  unfolding ∥∥ᴱ≃∥∥ᴱ

  -- A function of type (x : ∥ A ∥ᴱ) → P x, along with an erased proof
  -- showing that the function is equal to some erased function, is
  -- equivalent to a function of type (x : A) → P ∣ x ∣, along with an
  -- erased equality proof.

  Σ-Π-∥∥ᴱ-Erased-≡-≃ :
    {@0 g : (x : ∥ A ∥ᴱ) → P x} →
    (∃ λ (f : (x : ∥ A ∥ᴱ) → P x) → Erased (f ≡ g)) ≃
    (∃ λ (f : (x : A) → P ∣ x ∣) → Erased (f ≡ g ∘ ∣_∣))
  Σ-Π-∥∥ᴱ-Erased-≡-≃ {A} {P} {g} =
    (∃ λ (f : (x : ∥ A ∥ᴱ) → P x) → Erased (f ≡ g))       ↝⟨ (Σ-cong lemma λ _ → Er.Erased-cong (inverse $ Eq.≃-≡ lemma)) ⟩

    (∃ λ (f : (x : N.∥ A ∥ᴱ) → P (_≃_.from ∥∥ᴱ≃∥∥ᴱ x)) →
       Erased (f ≡ g ∘ _≃_.from ∥∥ᴱ≃∥∥ᴱ))                 ↝⟨ N.Σ-Π-∥∥ᴱ-Erased-≡-≃ ⟩□

    (∃ λ (f : (x : A) → P ∣ x ∣) → Erased (f ≡ g ∘ ∣_∣))  □
    where
    lemma :
      ((x : ∥ A ∥ᴱ) → P x) ≃ ((x : N.∥ A ∥ᴱ) → P (_≃_.from ∥∥ᴱ≃∥∥ᴱ x))
    lemma = Π-cong-contra ext (inverse ∥∥ᴱ≃∥∥ᴱ) λ _ → Eq.id
