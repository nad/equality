------------------------------------------------------------------------
-- Some theory of Erased, developed using the K rule and propositional
-- equality
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased and
-- Erased.Stability.

{-# OPTIONS --with-K --safe #-}

module Erased.With-K where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Embedding equality-with-J as Emb using (Is-embedding)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Injection equality-with-J using (Injective)

-- Some definitions from Erased are reexported.

open import Erased equality-with-J as Erased public
  hiding (module []-cong₁; module []-cong₂; module []-cong₃)

-- Some definitions from Erased.Stability are reexported.

open import Erased.Stability equality-with-J as Stability public
  hiding (module []-cong)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Code related to the module Erased

-- Given an erased proof of equality of x and y one can show that
-- [ x ] is equal to [ y ].

[]-cong : {@0 A : Set a} {@0 x y : A} →
          Erased (x ≡ y) → [ x ] ≡ [ y ]
[]-cong [ refl ] = refl

-- []-cong is an equivalence.

[]-cong-equivalence :
  {@0 A : Set a} {@0 x y : A} →
  Is-equivalence ([]-cong {x = x} {y = y})
[]-cong-equivalence {x = x} {y = y} = _≃_.is-equivalence (Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = []-cong
      ; from = λ eq → [ cong erased eq ]
      }
    ; right-inverse-of = λ { refl → refl }
    }
  ; left-inverse-of = λ { [ refl ] → refl }
  }))

-- Some reexported definitions.

open Erased.[]-cong₃ []-cong []-cong-equivalence refl public

------------------------------------------------------------------------
-- Code related to the module Erased.Stability

-- Reexported definitions.

open Stability.[]-cong []-cong []-cong-equivalence refl public

------------------------------------------------------------------------
-- Other code

-- [_] is injective.

Injective-[] : {@0 A : Set a} → Injective ([_] {A = A})
Injective-[] refl = refl

-- [_] is an embedding.

Is-embedding-[] : {@0 A : Set a} → Is-embedding ([_] {A = A})
Is-embedding-[] _ _ refl = (refl , refl) , λ { (refl , refl) → refl }

-- If Erased A is a proposition, then A is a proposition.

Is-proposition-Erased→Is-proposition :
  {@0 A : Set a} →
  Is-proposition (Erased A) → Is-proposition A
Is-proposition-Erased→Is-proposition prop x y =
  Injective-[] (prop [ x ] [ y ])

-- Equality is always very stable.

Very-stable-≡-trivial : Very-stable-≡ A
Very-stable-≡-trivial =
  _⇔_.from (Very-stable-≡↔Is-embedding-[] _)
           Is-embedding-[]
