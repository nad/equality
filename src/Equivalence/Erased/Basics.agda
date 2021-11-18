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
open import Equivalence.Erased.Contractible-preimages.Basics eq as ECP
  using (Contractibleᴱ; _⁻¹ᴱ_)
import Equivalence.Half-adjoint eq as HA
open import Erased.Basics
open import Preimage eq as Preimage using (_⁻¹_)

private
  variable
    a b c d ℓ : Level
    A B C     : Type a
    p x y     : A
    P Q       : A → Type p
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
--
-- See also Equivalence.Erased.Is-equivalence≃Is-equivalenceᴱ.

Is-equivalence→Is-equivalenceᴱ :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  Is-equivalence f → Is-equivalenceᴱ f
Is-equivalence→Is-equivalenceᴱ = Σ-map P.id [_]→

@0 Is-equivalenceᴱ→Is-equivalence :
  Is-equivalenceᴱ f → Is-equivalence f
Is-equivalenceᴱ→Is-equivalence = Σ-map P.id erased

-- Is-equivalenceᴱ f is logically equivalent to ECP.Is-equivalenceᴱ f.

Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  Is-equivalenceᴱ f ⇔ ECP.Is-equivalenceᴱ f
Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP {f = f} =
  record { to = to; from = from }
  where
  to : Is-equivalenceᴱ f → ECP.Is-equivalenceᴱ f
  to eq y =
      (proj₁₀ eq y , [ erased (proj₂ $ proj₁ eq′) ])
    , [ erased (proj₂ eq′) ]
    where
    @0 eq′ : Contractibleᴱ (f ⁻¹ᴱ y)
    eq′ =
      ECP.Is-equivalence→Is-equivalenceᴱ
        (_⇔_.to HA.Is-equivalence⇔Is-equivalence-CP $
         Is-equivalenceᴱ→Is-equivalence eq)
        y

  from : ECP.Is-equivalenceᴱ f → Is-equivalenceᴱ f
  from eq =
      proj₁₀ ⊚ proj₁₀ ⊚ eq
    , [ erased $ proj₂ $
        Is-equivalence→Is-equivalenceᴱ $
        _⇔_.from HA.Is-equivalence⇔Is-equivalence-CP $
        ECP.Is-equivalenceᴱ→Is-equivalence eq
      ]

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

private
  variable
    A≃B : A ≃ᴱ B

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

≃→≃ᴱ :
  {@0 A : Type a} {@0 B : Type b} →
  A ≃ B → A ≃ᴱ B
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
  {@0 A : Type a} {@0 B : Type b}
  (A≃B : A ≃ B) → Erased-proofs (_≃_.to A≃B) (_≃_.from A≃B)
[proofs] A≃B .Erased-proofs.proofs =
  let record { is-equivalence = is-equivalence } = A≃B in
  proj₂₀ is-equivalence

-- Converts two functions and some erased proofs to an equivalence
-- with erased proofs.
--
-- Note that Agda can in many cases infer "to" and "from" from the
-- first explicit argument, see (for instance) ↔→≃ᴱ below.

[≃]→≃ᴱ :
  {@0 A : Type a} {@0 B : Type b} {to : A → B} {from : B → A} →
  @0 Erased-proofs to from →
  A ≃ᴱ B
[≃]→≃ᴱ {to = to} {from = from} ep =
  ⟨ to , (from , [ ep .Erased-proofs.proofs ]) ⟩

-- A function with a quasi-inverse with erased proofs can be turned
-- into an equivalence with erased proofs.

↔→≃ᴱ :
  {@0 A : Type a} {@0 B : Type b}
  (f : A → B) (g : B → A) →
  @0 (∀ x → f (g x) ≡ x) →
  @0 (∀ x → g (f x) ≡ x) →
  A ≃ᴱ B
↔→≃ᴱ {A = A} {B = B} f g f∘g g∘f = [≃]→≃ᴱ ([proofs] A≃B′)
  where
  @0 A≃B′ : A ≃ B
  A≃B′ = Eq.↔⇒≃ (record
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
  {@0 A : Type a} {@0 B : Type b} →
  @0 Is-proposition A → @0 Is-proposition B →
  (A → B) → (B → A) →
  A ≃ᴱ B
⇔→≃ᴱ A-prop B-prop to from =
  [≃]→≃ᴱ ([proofs] (Eq.⇔→≃ A-prop B-prop to from))

------------------------------------------------------------------------
-- Equivalences with erased proofs form an equivalence relation

-- Identity.

id : {@0 A : Type a} → A ≃ᴱ A
id = [≃]→≃ᴱ ([proofs] Eq.id)

-- Inverse.

inverse :
  {@0 A : Type a} {@0 B : Type b} →
  A ≃ᴱ B → B ≃ᴱ A
inverse A≃B = [≃]→≃ᴱ ([proofs] (Eq.inverse (≃ᴱ→≃ A≃B)))

-- Composition.

infixr 9 _∘_

_∘_ :
  {@0 A : Type a} {@0 B : Type b} {@0 C : Type c} →
  B ≃ᴱ C → A ≃ᴱ B → A ≃ᴱ C
f ∘ g = [≃]→≃ᴱ ([proofs] (≃ᴱ→≃ f Eq.∘ ≃ᴱ→≃ g))

------------------------------------------------------------------------
-- A preservation lemma

-- Is-equivalenceᴱ f is logically equivalent to Is-equivalenceᴱ g if f
-- and g are pointwise equal.
--
-- See also Equivalence.Erased.[]-cong₂-⊔.Is-equivalenceᴱ-cong.

Is-equivalenceᴱ-cong-⇔ :
  {@0 A : Type a} {@0 B : Type b} {@0 f g : A → B} →
  @0 (∀ x → f x ≡ g x) →
  Is-equivalenceᴱ f ⇔ Is-equivalenceᴱ g
Is-equivalenceᴱ-cong-⇔ {f = f} {g = g} f≡g =
  record { to = to f≡g; from = to (sym ⊚ f≡g) }
  where
  to :
    {@0 A : Type a} {@0 B : Type b} {@0 f g : A → B} →
    @0 (∀ x → f x ≡ g x) →
    Is-equivalenceᴱ f → Is-equivalenceᴱ g
  to f≡g f-eq@(f⁻¹ , _) =
    ( f⁻¹
    , [ erased $ proj₂ $
        Is-equivalence→Is-equivalenceᴱ $
        Eq.respects-extensional-equality f≡g $
        Is-equivalenceᴱ→Is-equivalence f-eq
      ]
    )

----------------------------------------------------------------------
-- The left-to-right and right-to-left components of an equivalence
-- with erased proofs can be replaced with extensionally equal
-- functions

-- The forward direction of an equivalence with erased proofs can be
-- replaced by an extensionally equal function.

with-other-function :
  {@0 A : Type a} {@0 B : Type b}
  (A≃B : A ≃ᴱ B) (f : A → B) →
  @0 (∀ x → _≃ᴱ_.to A≃B x ≡ f x) →
  A ≃ᴱ B
with-other-function ⟨ g , is-equivalence ⟩ f g≡f =
  ⟨ f
  , (let record { to = to } = Is-equivalenceᴱ-cong-⇔ g≡f in
     to is-equivalence)
  ⟩₀

_ : _≃ᴱ_.to (with-other-function A≃B f p) ≡ f
_ = refl _

_ : _≃ᴱ_.from (with-other-function A≃B f p) ≡ _≃ᴱ_.from A≃B
_ = refl _

-- The same applies to the other direction.

with-other-inverse :
  {@0 A : Type a} {@0 B : Type b}
  (A≃B : A ≃ᴱ B) (g : B → A) →
  @0 (∀ x → _≃ᴱ_.from A≃B x ≡ g x) →
  A ≃ᴱ B
with-other-inverse A≃B g ≡g =
  inverse $ with-other-function (inverse A≃B) g ≡g

_ : _≃ᴱ_.from (with-other-inverse A≃B g p) ≡ g
_ = refl _

_ : _≃ᴱ_.to (with-other-inverse A≃B f p) ≡ _≃ᴱ_.to A≃B
_ = refl _
