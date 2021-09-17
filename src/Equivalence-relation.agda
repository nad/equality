------------------------------------------------------------------------
-- Equivalence relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence-relation
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import H-level eq
open import H-level.Closure eq

private
  variable
    a r r₁ r₂         : Level
    A A₁ A₂ B B₁ B₂ C : Type a
    R R₁ R₂           : A → B → Type r

------------------------------------------------------------------------
-- The definition

-- The definition of "equivalence relation".

record Is-equivalence-relation
         {A : Type a} (R : A → A → Type r) : Type (a ⊔ r) where
  field
    reflexive  : ∀ {x} → R x x
    symmetric  : ∀ {x y} → R x y → R y x
    transitive : ∀ {x y z} → R x y → R y z → R x z

------------------------------------------------------------------------
-- Some examples of equivalence relations/equivalence relation
-- transformers

-- A trivial binary relation.

Trivial : A → B → Type r
Trivial _ _ = ↑ _ ⊤

-- Homogeneous instances of Trivial are equivalence relations.

Trivial-is-equivalence-relation :
  Is-equivalence-relation (Trivial {A = A} {r = r})
Trivial-is-equivalence-relation = _

-- Trivial is propositional.

Trivial-is-propositional :
  {x y : A} → Is-proposition (Trivial {r = r} x y)
Trivial-is-propositional = ↑-closure 1 (mono₁ 0 ⊤-contractible)

-- The superscript P used in the names of the definitions in this
-- section stands for "pointwise".

-- Lifts binary relations from B to A → B.

infix 0 _→ᴾ_

_→ᴾ_ :
  (A : Type a) →
  (B → C → Type r) →
  ((A → B) → (A → C) → Type (a ⊔ r))
(_ →ᴾ R) f g = ∀ x → R (f x) (g x)

-- _→ᴾ_ preserves equivalence relations.

→ᴾ-preserves-Is-equivalence-relation :
  Is-equivalence-relation R →
  Is-equivalence-relation (A →ᴾ R)
→ᴾ-preserves-Is-equivalence-relation R-equiv = record
  { reflexive  = λ _ → reflexive
  ; symmetric  = λ f∼g x → symmetric (f∼g x)
  ; transitive = λ f∼g g∼h x → transitive (f∼g x) (g∼h x)
  }
  where
  open Is-equivalence-relation R-equiv

-- _→ᴾ_ preserves Is-proposition (assuming extensionality).

→ᴾ-preserves-Is-proposition :
  {A : Type a} (R : B → C → Type r) →
  Extensionality a r →
  (∀ {x y} → Is-proposition (R x y)) →
  ∀ {f g} → Is-proposition ((A →ᴾ R) f g)
→ᴾ-preserves-Is-proposition _ ext R-prop =
  Π-closure ext 1 λ _ →
  R-prop

-- Lifts binary relations from A and B to A ⊎ B.

infixr 1 _⊎ᴾ_

_⊎ᴾ_ :
  (A₁ → A₂ → Type r) →
  (B₁ → B₂ → Type r) →
  (A₁ ⊎ B₁ → A₂ ⊎ B₂ → Type r)
(P ⊎ᴾ Q) (inj₁ x) (inj₁ y) = P x y
(P ⊎ᴾ Q) (inj₂ x) (inj₂ y) = Q x y
(P ⊎ᴾ Q) _        _        = ⊥

-- _⊎ᴾ_ preserves Is-equivalence-relation.

⊎ᴾ-preserves-Is-equivalence-relation :
  Is-equivalence-relation R₁ →
  Is-equivalence-relation R₂ →
  Is-equivalence-relation (R₁ ⊎ᴾ R₂)
⊎ᴾ-preserves-Is-equivalence-relation R₁-equiv R₂-equiv = record
  { reflexive  = λ { {x = inj₁ _} → reflexive R₁-equiv
                   ; {x = inj₂ _} → reflexive R₂-equiv
                   }
  ; symmetric  = λ { {x = inj₁ _} {y = inj₁ _} → symmetric R₁-equiv
                   ; {x = inj₂ _} {y = inj₂ _} → symmetric R₂-equiv
                   ; {x = inj₁ _} {y = inj₂ _} ()
                   ; {x = inj₂ _} {y = inj₁ _} ()
                   }
  ; transitive = λ
     { {x = inj₁ _} {y = inj₁ _} {z = inj₁ _} → transitive R₁-equiv
     ; {x = inj₂ _} {y = inj₂ _} {z = inj₂ _} → transitive R₂-equiv

     ; {x = inj₁ _} {y = inj₂ _} ()
     ; {x = inj₂ _} {y = inj₁ _} ()
     ; {y = inj₁ _} {z = inj₂ _} _ ()
     ; {y = inj₂ _} {z = inj₁ _} _ ()
     }
  }
  where
  open Is-equivalence-relation

-- _⊎ᴾ_ preserves Is-proposition.

⊎ᴾ-preserves-Is-proposition :
  (∀ {x y} → Is-proposition (R₁ x y)) →
  (∀ {x y} → Is-proposition (R₂ x y)) →
  ∀ {x y} → Is-proposition ((R₁ ⊎ᴾ R₂) x y)
⊎ᴾ-preserves-Is-proposition = λ where
  R₁-prop R₂-prop {inj₁ _} {inj₁ _} → R₁-prop
  R₁-prop R₂-prop {inj₁ _} {inj₂ _} → ⊥-propositional
  R₁-prop R₂-prop {inj₂ _} {inj₁ _} → ⊥-propositional
  R₁-prop R₂-prop {inj₂ _} {inj₂ _} → R₂-prop

-- Lifts a binary relation from A to Maybe A.

Maybeᴾ :
  (A → B → Type r) →
  (Maybe A → Maybe B → Type r)
Maybeᴾ R = Trivial ⊎ᴾ R

-- Maybeᴾ preserves Is-equivalence-relation.

Maybeᴾ-preserves-Is-equivalence-relation :
  Is-equivalence-relation R →
  Is-equivalence-relation (Maybeᴾ R)
Maybeᴾ-preserves-Is-equivalence-relation =
  ⊎ᴾ-preserves-Is-equivalence-relation Trivial-is-equivalence-relation

-- Maybeᴾ preserves Is-proposition.

Maybeᴾ-preserves-Is-proposition :
  (∀ {x y} → Is-proposition (R x y)) →
  ∀ {x y} → Is-proposition (Maybeᴾ R x y)
Maybeᴾ-preserves-Is-proposition =
  ⊎ᴾ-preserves-Is-proposition λ {x} →
  Trivial-is-propositional {x = x}

-- Lifts binary relations from A and B to A × B.

infixr 2 _×ᴾ_

_×ᴾ_ :
  (A₁ → B₁ → Type r₁) →
  (A₂ → B₂ → Type r₂) →
  (A₁ × A₂ → B₁ × B₂ → Type (r₁ ⊔ r₂))
(P ×ᴾ Q) (x₁ , x₂) (y₁ , y₂) = P x₁ y₁ × Q x₂ y₂

-- _×ᴾ_ preserves Is-equivalence-relation.

×ᴾ-preserves-Is-equivalence-relation :
  Is-equivalence-relation R₁ →
  Is-equivalence-relation R₂ →
  Is-equivalence-relation (R₁ ×ᴾ R₂)
×ᴾ-preserves-Is-equivalence-relation R₁-equiv R₂-equiv = λ where
    .Is-equivalence-relation.reflexive →
      E₁.reflexive , E₂.reflexive
    .Is-equivalence-relation.symmetric →
      Σ-map E₁.symmetric E₂.symmetric
    .Is-equivalence-relation.transitive →
      Σ-zip E₁.transitive E₂.transitive
  where
  module E₁ = Is-equivalence-relation R₁-equiv
  module E₂ = Is-equivalence-relation R₂-equiv

-- _×ᴾ_ preserves Is-proposition.

×ᴾ-preserves-Is-proposition :
  (∀ {x y} → Is-proposition (R₁ x y)) →
  (∀ {x y} → Is-proposition (R₂ x y)) →
  ∀ {x y} → Is-proposition ((R₁ ×ᴾ R₂) x y)
×ᴾ-preserves-Is-proposition R₁-prop R₂-prop =
  ×-closure 1 R₁-prop R₂-prop
