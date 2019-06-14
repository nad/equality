------------------------------------------------------------------------
-- Squashing
------------------------------------------------------------------------

{-# OPTIONS --cubical --prop --safe #-}

open import Equality

module Squash {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Bijection eq using (_↔_)
open import Function-universe eq hiding (_∘_)
open import H-level eq
open import H-level.Truncation.Propositional eq as Trunc using (∥_∥)
open import Monad eq

private
  variable
    a ℓ : Level
    A B : Set a

-- Any two elements of type Squash′ A are definitionally equal.

data Squash′ (A : Set a) : Prop a where
  squash′ : A → Squash′ A

-- However, Squash′ A does not have type Set a. The following wrapper
-- makes it possible to use squashed types in, say, lists.

record Squash (A : Set a) : Set a where
  constructor squash
  field
    squashed : Squash′ A

pattern [_] x = squash (squash′ x)

private

  -- A unit test.

  test : [ 4 ] ∷ [ 5 ] ∷ [] ≡ [ 3 ] ∷ [ 9 ] ∷ []
  test = refl _

-- Squashed types are propositions.

Squash-propositional : Is-proposition (Squash A)
Squash-propositional = λ _ _ → refl _

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : Squash A → (A → Squash B) → Squash B
_>>=′_ {A = A} {B = B} (squash x) f = squash (lemma x)
  where
  lemma : Squash′ A → Squash′ B
  lemma (squash′ x) = Squash.squashed (f x)

instance

  -- Squash is a monad.

  raw-monad : Raw-monad {c = ℓ} Squash
  Raw-monad.return raw-monad = [_]
  Raw-monad._>>=_  raw-monad = _>>=′_

  monad : Monad {c = ℓ} Squash
  Monad.raw-monad      monad = raw-monad
  Monad.left-identity  monad = λ _ _ → refl _
  Monad.right-identity monad = λ _ → refl _
  Monad.associativity  monad = λ _ _ _ → refl _

-- Squash ⊥ is isomorphic to ⊥.

Squash-⊥↔⊥ : Squash (⊥ {ℓ = ℓ}) ↔ ⊥ {ℓ = ℓ}
Squash-⊥↔⊥ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ x → ⊥-in-prop→⊥ (Squash-⊥→⊥-in-prop x)
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ _ → refl _
  }
  where

  -- An empty type in Prop.

  data ⊥-in-prop : Prop where

  -- Squash ⊥ implies ⊥-in-prop.

  Squash-⊥→⊥-in-prop : Squash (⊥ {ℓ = ℓ}) → ⊥-in-prop
  Squash-⊥→⊥-in-prop [ () ]

  -- ⊥-in-prop implies ⊥.

  ⊥-in-prop→⊥ : ⊥-in-prop → ⊥ {ℓ = ℓ}
  ⊥-in-prop→⊥ ()

-- ∥ A ∥ implies Squash A.

∥∥→Squash : ∥ A ∥ → Squash A
∥∥→Squash = Trunc.rec Squash-propositional [_]

-- Squash A implies ¬ ¬ A.

Squash→¬¬ : Squash A → ¬ ¬ A
Squash→¬¬ {A = A} = curry (
  Squash A × ¬ A  ↝⟨ (λ { (x , f) → x >>=′ return ∘ f }) ⟩
  Squash ⊥        ↔⟨ Squash-⊥↔⊥ ⟩□
  ⊥               □)
