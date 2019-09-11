------------------------------------------------------------------------
-- Some theory of Erased, developed using the K rule and propositional
-- equality
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased and
-- Erased.Stability.

{-# OPTIONS --with-K --safe #-}

module Erased.With-K where

open import Equality.Propositional
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Embedding equality-with-J as Emb using (Is-embedding)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Injection equality-with-J using (Injective)

-- Some definitions from Erased are reexported.

open import Erased equality-with-J as Erased public
  hiding (module []-cong;
          module Erased-≡↔[]≡[]₁;
          module Erased-≡↔[]≡[]₂)

-- Some definitions from Erased.Stability are reexported.

open import Erased.Stability equality-with-J as Stability public
  hiding (module Very-stable→Very-stable-≡)

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

-- There is a bijection between erased equality proofs and equalities
-- between erased values.

Erased-≡↔[]≡[] :
  {@0 A : Set a} {@0 x y : A} →
  Erased (x ≡ y) ↔ [ x ] ≡ [ y ]
Erased-≡↔[]≡[] = record
  { surjection = record
    { logical-equivalence = record
      { to   = []-cong
      ; from = λ eq → [ cong erased eq ]
      }
    ; right-inverse-of = λ { refl → refl }
    }
  ; left-inverse-of = λ { [ refl ] → refl }
  }

-- A rearrangement lemma for Erased-≡↔[]≡[].

to-Erased-≡↔[]≡[]-[refl] :
  {@0 A : Set a} {@0 x : A} →
  _↔_.to Erased-≡↔[]≡[] [ refl ] ≡ refl {x = [ x ]}
to-Erased-≡↔[]≡[]-[refl] = refl

-- Some reexported definitions.

open Erased.Erased-≡↔[]≡[]₂ Erased-≡↔[]≡[] refl public
  hiding ([]-cong)

------------------------------------------------------------------------
-- Code related to the module Erased.Stability

-- Equality is always very stable.

Very-stable-≡-trivial : Very-stable-≡ A
Very-stable-≡-trivial = _≃_.is-equivalence (Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { from = λ { [ refl ] → refl }
      }
    ; right-inverse-of = λ { [ refl ] → refl }
    }
  ; left-inverse-of = λ { refl → refl }
  }))

-- Thus, if A is very stable, then the types of equalities between
-- values of type A are very stable.

Very-stable→Very-stable-≡ : Very-stable A → Very-stable-≡ A
Very-stable→Very-stable-≡ _ = Very-stable-≡-trivial

-- Reexported definitions.

open Stability.Very-stable→Very-stable-≡
  Erased-≡↔[]≡[] to-Erased-≡↔[]≡[]-[refl] Very-stable→Very-stable-≡
  public

------------------------------------------------------------------------
-- Other code

-- [_] is an embedding.

Is-embedding-[] : Is-embedding ([_] {A = A})
Is-embedding-[] x y = _≃_.is-equivalence (Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { from = λ { refl → refl }
      }
    ; right-inverse-of = λ { refl → refl }
    }
  ; left-inverse-of = λ { refl → refl }
  }))

-- [_] is injective.

Injective-[] : {@0 A : Set a} → Injective ([_] {A = A})
Injective-[] refl = refl

-- If Erased A is a proposition, then A is a proposition.

Is-proposition-Erased→Is-proposition :
  {@0 A : Set a} →
  Is-proposition (Erased A) → Is-proposition A
Is-proposition-Erased→Is-proposition prop x y =
  Injective-[] (prop [ x ] [ y ])
