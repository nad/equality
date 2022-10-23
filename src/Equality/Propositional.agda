------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Equality.Propositional where

open import Equality
open import Logical-equivalence hiding (_∘_)
open import Prelude

------------------------------------------------------------------------
-- Equality

open import Agda.Builtin.Equality public using (_≡_; refl)

private

  refl′ : ∀ {a} {A : Type a} (x : A) → x ≡ x
  refl′ x = refl

  elim : ∀ {a p} {A : Type a} {x y}
         (P : {x y : A} → x ≡ y → Type p) →
         (∀ x → P (refl′ x)) →
         (x≡y : x ≡ y) → P x≡y
  elim P r refl = r _

  elim-refl : ∀ {a p} {A : Type a} {x}
              (P : {x y : A} → x ≡ y → Type p)
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

-- The following definition has been expanded in order to ensure that
-- it does not reduce (unless a projection is applied to it).

equality-with-J : ∀ {a p} → Equality-with-J a p equivalence-relation⁺
equality-with-J .Equality-with-J.equality-with-J₀ = J₀⇒J equality-with-J₀ .Equality-with-J.equality-with-J₀
equality-with-J .Equality-with-J.cong             = J₀⇒J equality-with-J₀ .Equality-with-J.cong
equality-with-J .Equality-with-J.cong-refl        = J₀⇒J equality-with-J₀ .Equality-with-J.cong-refl
equality-with-J .Equality-with-J.subst            = J₀⇒J equality-with-J₀ .Equality-with-J.subst
equality-with-J .Equality-with-J.subst-refl       = J₀⇒J equality-with-J₀ .Equality-with-J.subst-refl
equality-with-J .Equality-with-J.dcong            = J₀⇒J equality-with-J₀ .Equality-with-J.dcong
equality-with-J .Equality-with-J.dcong-refl       = J₀⇒J equality-with-J₀ .Equality-with-J.dcong-refl

open Derived-definitions-and-properties equality-with-J public
  hiding (_≡_; refl; reflexive-relation; equality-with-J₀)
