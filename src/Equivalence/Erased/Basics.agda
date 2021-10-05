------------------------------------------------------------------------
-- Equivalences with erased "proofs"
------------------------------------------------------------------------

-- This module contains some basic definitions with few dependencies.
-- See Equivalence.Erased for more definitions. The definitions below
-- are reexported from Equivalence.Erased.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence.Erased.Basics
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; [_,_]) renaming (_∘_ to _⊚_)

open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence.Half-adjoint eq as HA
open import Erased.Basics
open import Preimage eq as Preimage using (_⁻¹_)

private
  variable
    a b d ℓ p : Level
    A B C     : Type a
    P Q       : A → Type p
    x y       : A
    f g       : (x : A) → P x

------------------------------------------------------------------------
-- Is-equivalenceᴱ

-- Is-equivalence with erased proofs.

Is-equivalenceᴱ : {A : Type a} {B : Type b} → @0 (A → B) → Type (a ⊔ b)
Is-equivalenceᴱ {A = A} {B = B} f =
  ∃ λ (f⁻¹ : B → A) → Erased (HA.Proofs f f⁻¹)

------------------------------------------------------------------------
-- Some conversion lemmas

-- Conversions between Is-equivalence and Is-equivalenceᴱ.

Is-equivalence→Is-equivalenceᴱ : Is-equivalence f → Is-equivalenceᴱ f
Is-equivalence→Is-equivalenceᴱ = Σ-map P.id [_]→

@0 Is-equivalenceᴱ→Is-equivalence :
  Is-equivalenceᴱ f → Is-equivalence f
Is-equivalenceᴱ→Is-equivalence = Σ-map P.id erased

-- See also Equivalence.Erased.Is-equivalence≃Is-equivalenceᴱ.

------------------------------------------------------------------------
-- _≃ᴱ_

private
 module Dummy where

  -- Equivalences with erased proofs.

  infix 4 _≃ᴱ_

  record _≃ᴱ_ (A : Type a) (B : Type b) : Type (a ⊔ b) where
    constructor ⟨_,_⟩
    field
      to             : A → B
      is-equivalence : Is-equivalenceᴱ to

open Dummy public using (_≃ᴱ_; ⟨_,_⟩) hiding (module _≃ᴱ_)

-- A variant of the constructor of _≃ᴱ_ with erased type arguments.

⟨_,_⟩₀ :
  {@0 A : Type a} {@0 B : Type b}
  (to : A → B) → Is-equivalenceᴱ to → A ≃ᴱ B
⟨ to , eq ⟩₀ = ⟨ to , eq ⟩

-- Note that the type arguments A and B are erased. This is not the
-- case for the record module Dummy._≃ᴱ_.

module _≃ᴱ_ {@0 A : Type a} {@0 B : Type b} (A≃B : A ≃ᴱ B) where

  -- The "left-to-right" direction of the equivalence.

  to : A → B
  to = let ⟨ to , _ ⟩ = A≃B in to

  -- The function to is an equivalence.

  is-equivalence : Is-equivalenceᴱ to
  is-equivalence = let ⟨ _ , eq ⟩ = A≃B in eq

  -- The "right-to-left" direction of the equivalence.

  from : B → A
  from = let from , _ = is-equivalence in from

  -- The underlying logical equivalence.

  logical-equivalence : A ⇔ B
  logical-equivalence = record
    { to   = to
    ; from = from
    }

  -- In an erased context one can construct a corresponding
  -- equivalence.

  @0 equivalence : A ≃ B
  equivalence =
    Eq.⟨ to , Is-equivalenceᴱ→Is-equivalence is-equivalence ⟩

  -- In an erased context the function from is a right inverse of to.

  @0 right-inverse-of : ∀ y → to (from y) ≡ y
  right-inverse-of = _≃_.right-inverse-of equivalence

  -- In an erased context the function from is a left inverse of to.

  @0 left-inverse-of : ∀ x → from (to x) ≡ x
  left-inverse-of = _≃_.left-inverse-of equivalence

  -- Two coherence properties.

  @0 left-right-lemma :
    ∀ x → cong to (left-inverse-of x) ≡ right-inverse-of (to x)
  left-right-lemma = _≃_.left-right-lemma equivalence

  @0 right-left-lemma :
    ∀ x → cong from (right-inverse-of x) ≡ left-inverse-of (from x)
  right-left-lemma = _≃_.right-left-lemma equivalence

------------------------------------------------------------------------
-- More conversion lemmas

-- Equivalences are equivalent to pairs.

≃ᴱ-as-Σ : (A ≃ᴱ B) ≃ (∃ λ (f : A → B) → Is-equivalenceᴱ f)
≃ᴱ-as-Σ = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { ⟨ f , is ⟩ → f , is }
      ; from = uncurry ⟨_,_⟩
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  })

-- Conversions between _≃_ and _≃ᴱ_.

≃→≃ᴱ : A ≃ B → A ≃ᴱ B
≃→≃ᴱ Eq.⟨ f , is-equiv ⟩ =
  ⟨ f , Is-equivalence→Is-equivalenceᴱ is-equiv ⟩

@0 ≃ᴱ→≃ : A ≃ᴱ B → A ≃ B
≃ᴱ→≃ = _≃ᴱ_.equivalence

-- Data corresponding to the erased proofs of an equivalence with
-- erased proofs.

record Erased-proofs {A : Type a} {B : Type b}
                     (to : A → B) (from : B → A) : Type (a ⊔ b) where
  field
    proofs : HA.Proofs to from

-- Extracts "erased proofs" from a regular equivalence.

[proofs] :
  (A≃B : A ≃ B) → Erased-proofs (_≃_.to A≃B) (_≃_.from A≃B)
[proofs] A≃B .Erased-proofs.proofs = proj₂ (_≃_.is-equivalence A≃B)

-- Converts two functions and some erased proofs to an equivalence
-- with erased proofs.
--
-- Note that Agda can in many cases infer "to" and "from" from the
-- first explicit argument, see (for instance) ↔→≃ᴱ below.

[≃]→≃ᴱ :
  {to : A → B} {from : B → A} →
  @0 Erased-proofs to from →
  A ≃ᴱ B
[≃]→≃ᴱ {to = to} {from = from} ep =
  ⟨ to , (from , [ ep .Erased-proofs.proofs ]) ⟩

-- A function with a quasi-inverse with erased proofs can be turned
-- into an equivalence with erased proofs.

↔→≃ᴱ :
  (f : A → B) (g : B → A) →
  @0 (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  A ≃ᴱ B
↔→≃ᴱ {A = A} {B = B} f g f∘g g∘f = [≃]→≃ᴱ ([proofs] A≃B)
  where
  @0 A≃B : A ≃ B
  A≃B = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = f
        ; from = g
        }
      ; right-inverse-of = f∘g
      }
    ; left-inverse-of = g∘f
    })

-- A variant of ↔→≃ᴱ.

⇔→≃ᴱ :
  ∀ {a b} {A : Type a} {B : Type b} →
  @0 Is-proposition A → @0 Is-proposition B →
  (A → B) → (B → A) →
  A ≃ᴱ B
⇔→≃ᴱ A-prop B-prop to from =
  [≃]→≃ᴱ ([proofs] (Eq.⇔→≃ A-prop B-prop to from))

------------------------------------------------------------------------
-- Equivalences with erased proofs form an equivalence relation

-- Identity.

id : A ≃ᴱ A
id = ≃→≃ᴱ Eq.id

-- Inverse.

inverse : A ≃ᴱ B → B ≃ᴱ A
inverse A≃B = [≃]→≃ᴱ ([proofs] (Eq.inverse (≃ᴱ→≃ A≃B)))

-- Composition.

infixr 9 _∘_

_∘_ : B ≃ᴱ C → A ≃ᴱ B → A ≃ᴱ C
f ∘ g = [≃]→≃ᴱ ([proofs] (≃ᴱ→≃ f Eq.∘ ≃ᴱ→≃ g))
