------------------------------------------------------------------------
-- Results related to accessibility that are implemented using
-- --erased-matches
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --erased-matches #-}

open import Equality

module Accessibility.Erased-matches
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open import Erased.Basics as Erased
open import Prelude

open import Accessibility eq

private variable
  a p r : Level

------------------------------------------------------------------------
-- Well-founded induction

-- Well-founded induction for accessible values.
--
-- Note that the accessibility argument is erased.

well-founded-induction-Acc :
  {@0 A : Type a} {@0 _<_ : A → A → Type r}
  (@0 P : A → Type p) →
  (∀ x → (∀ y → @0 y < x → P y) → P x) →
  ∀ x → @0 Acc _<_ x → P x
well-founded-induction-Acc P f x (acc g) =
  f x (λ y y<x → well-founded-induction-Acc P f y (g y y<x))

-- Well-founded induction for well-founded relations.

well-founded-induction :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} →
  @0 Well-founded _<_ →
  (@0 P : A → Type p) →
  (∀ x → (∀ y → @0 y < x → P y) → P x) →
  ∀ x → P x
well-founded-induction wf P f x =
  well-founded-induction-Acc P f x (wf x)

------------------------------------------------------------------------
-- Some types are erasure-stable

-- Acc _<_ x is erasure-stable.

Acc-erasure-stable :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} {@0 x : A} →
  Erased.Stable (Acc _<_ x)
Acc-erasure-stable [ acc f ] =
  acc (λ y y<x → Acc-erasure-stable [ f y y<x ])

-- Well-founded _<_ is erasure-stable.

Well-founded-erasure-stable :
  {@0 A : Type a} {@0 _<_ : A → A → Type r} →
  Erased.Stable (Well-founded _<_)
Well-founded-erasure-stable [ wf ] = λ x →
  Acc-erasure-stable [ wf x ]
