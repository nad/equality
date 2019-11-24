------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Equality.Propositional where

open import Equality
open import Logical-equivalence hiding (_∘_)
open import Prelude

------------------------------------------------------------------------
-- Equality

open import Agda.Builtin.Equality public using (_≡_; refl)

private

  refl′ : ∀ {a} {A : Set a} (x : A) → x ≡ x
  refl′ x = refl

  elim : ∀ {a p} {A : Set a} {x y}
         (P : {x y : A} → x ≡ y → Set p) →
         (∀ x → P (refl′ x)) →
         (x≡y : x ≡ y) → P x≡y
  elim P r refl = r _

  elim-refl : ∀ {a p} {A : Set a} {x}
              (P : {x y : A} → x ≡ y → Set p)
              (r : ∀ x → P (refl′ x)) →
              elim P r (refl′ x) ≡ r x
  elim-refl P r = refl

------------------------------------------------------------------------
-- Various derived definitions and properties

reflexive-relation : ∀ ℓ → Reflexive-relation ℓ
Reflexive-relation._≡_  (reflexive-relation _) = _≡_
Reflexive-relation.refl (reflexive-relation _) = refl′

equality-with-J₀ : ∀ {a p} → Equality-with-J₀ a p reflexive-relation
Equality-with-J₀.elim      equality-with-J₀ = elim
Equality-with-J₀.elim-refl equality-with-J₀ = elim-refl

equivalence-relation⁺ : ∀ ℓ → Equivalence-relation⁺ ℓ
equivalence-relation⁺ _ = J₀⇒Equivalence-relation⁺ equality-with-J₀

equality-with-J : ∀ {a p} → Equality-with-J a p equivalence-relation⁺
equality-with-J = J₀⇒J equality-with-J₀

open Derived-definitions-and-properties (J₀⇒J equality-with-J₀) public
  hiding (_≡_; refl; reflexive-relation; equality-with-J₀)
