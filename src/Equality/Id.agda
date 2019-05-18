------------------------------------------------------------------------
-- The cubical identity type
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Equality.Id where

open import Equality
import Equality.Path as P

import Agda.Builtin.Cubical.Id as Id

------------------------------------------------------------------------
-- Equality

infix 4 _≡_

_≡_ : ∀ {a} {A : Set a} → A → A → Set a
_≡_ = Id.Id

refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
refl = Id.conid P.1̲ P.refl

------------------------------------------------------------------------
-- Various derived definitions and properties

reflexive-relation : ∀ ℓ → Reflexive-relation ℓ
Reflexive-relation._≡_  (reflexive-relation _) = _≡_
Reflexive-relation.refl (reflexive-relation _) = λ _ → refl

equality-with-J₀ : ∀ {a p} → Equality-with-J₀ a p reflexive-relation
Equality-with-J₀.elim      equality-with-J₀ = λ P r → Id.primIdJ
                                                        (λ _ → P) (r _)
Equality-with-J₀.elim-refl equality-with-J₀ = λ _ _ → refl

congruence⁺ : ∀ ℓ → Congruence⁺ ℓ
congruence⁺ _ = J₀⇒Congruence⁺ equality-with-J₀

equality-with-J : ∀ {a p} → Equality-with-J a p congruence⁺
equality-with-J = J₀⇒J equality-with-J₀

open Derived-definitions-and-properties (J₀⇒J equality-with-J₀) public
  hiding (_≡_; refl; reflexive-relation; equality-with-J₀)

open import Equality.Path.Isomorphisms equality-with-J public
