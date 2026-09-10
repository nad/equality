------------------------------------------------------------------------
-- Some theory of Erased, developed using propositional equality and
-- the builtin implementation of []-cong
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased. It is
-- itself re-exported from Erased.With-K.

{-# OPTIONS --safe --cubical-compatible --erased-matches=restricted #-}

module Erased.Box-cong where

import Agda.Builtin.Erased.Box-cong

open import Equality.Propositional
open import Prelude

open import Bijection equality-with-J using (_↔_)
import Erased.Basics as EB
import Erased.Level-1 equality-with-J as E
open import Extensionality equality-with-J

private variable
  a p : Level

------------------------------------------------------------------------
-- Code related to the module Erased

-- Given an erased proof of equality of x and y one can show that
-- [ x ] is equal to [ y ].

[]-cong : {@0 A : Type a} {@0 x y : A} →
          EB.Erased (x ≡ y) → EB.[ x ] ≡ EB.[ y ]
[]-cong EB.[ x≡y ] = Agda.Builtin.Erased.Box-cong.[]-cong x≡y

-- []-cong maps [ refl ] to refl (by definition).

[]-cong-[refl] :
  {@0 A : Type a} {@0 x : A} →
  []-cong EB.[ refl {x = x} ] ≡ refl {x = EB.[ x ]}
[]-cong-[refl] = refl

-- The []-cong axioms can be instantiated.

instance-of-[]-cong-axiomatisation : E.[]-cong-axiomatisation a
instance-of-[]-cong-axiomatisation = λ where
  .E.[]-cong-axiomatisation.[]-cong        → []-cong
  .E.[]-cong-axiomatisation.[]-cong-[refl] → []-cong-[refl]

-- Some reexported definitions.

open import Erased equality-with-J instance-of-[]-cong-axiomatisation
  public
  hiding ([]-cong; []-cong-[refl]; Injective-[];
          Π-Erased≃Π0[]; Π-Erased≃Π0)

------------------------------------------------------------------------
-- Other code

-- The following two results are inspired by a result in
-- Mishra-Linger's PhD thesis (see Section 5.4.1).

-- There is a bijection between (x : Erased A) → P x and
-- (@0 x : A) → P [ x ] (assuming function extensionality).

Π-Erased↔Π0[] :
  {@0 A : Type a} {@0 P : Erased A → Type p} →
  Function-extensionality′ (Erased A) P →
  ((x : Erased A) → P x) ↔ ((@0 x : A) → P [ x ])
Π-Erased↔Π0[] ext = record
  { surjection = record
    { logical-equivalence = Π-Erased⇔Π0[]
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ _ → ext λ { [ _ ] → refl }
  }

-- There is a bijection between (x : Erased A) → P (erased x) and
-- (@0 x : A) → P x (assuming function extensionality).

Π-Erased↔Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  Function-extensionality′ (Erased A) (P ∘ erased) →
  ((x : Erased A) → P (erased x)) ↔ ((@0 x : A) → P x)
Π-Erased↔Π0 = Π-Erased↔Π0[]
