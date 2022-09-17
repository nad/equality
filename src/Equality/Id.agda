------------------------------------------------------------------------
-- The cubical identity type
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

module Equality.Id where

open import Equality
import Equality.Path as P
open import Prelude

import Agda.Builtin.Cubical.Id as Id

------------------------------------------------------------------------
-- Equality

infix 4 _≡_

_≡_ : ∀ {a} {A : Type a} → A → A → Type a
_≡_ = Id.Id

refl : ∀ {a} {A : Type a} {x : A} → x ≡ x
refl = Id.conid P.1̲ P.refl

------------------------------------------------------------------------
-- Various derived definitions and properties

reflexive-relation : ∀ ℓ → Reflexive-relation ℓ
Reflexive-relation._≡_  (reflexive-relation _) = _≡_
Reflexive-relation.refl (reflexive-relation _) = λ _ → refl

equality-with-J₀ : ∀ {a p} → Equality-with-J₀ a p reflexive-relation
Equality-with-J₀.elim      equality-with-J₀ = λ P r →
                                                Id.IdJ (λ _ → P) (r _)
Equality-with-J₀.elim-refl equality-with-J₀ = λ _ _ → refl

equivalence-relation⁺ : ∀ ℓ → Equivalence-relation⁺ ℓ
equivalence-relation⁺ _ = J₀⇒Equivalence-relation⁺ equality-with-J₀

equality-with-paths :
  ∀ {a p} → P.Equality-with-paths a p equivalence-relation⁺
equality-with-paths =
  P.Equality-with-J₀⇒Equality-with-paths equality-with-J₀

open P.Derived-definitions-and-properties equality-with-paths public
  hiding (_≡_; refl; reflexive-relation; equality-with-J₀)

open import Equality.Path.Isomorphisms equality-with-paths public
