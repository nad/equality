------------------------------------------------------------------------
-- Some theory of Erased, developed using the K rule and propositional
-- equality
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased.

{-# OPTIONS --with-K --safe #-}

module Erased.With-K where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Embedding equality-with-J as Emb using (Is-embedding)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
import Erased.Basics as EB
import Erased.Level-1 equality-with-J as E
open import Extensionality equality-with-J
open import H-level equality-with-J
open import Injection equality-with-J using (Injective)

private
  variable
    a b p : Level
    A     : Type a

------------------------------------------------------------------------
-- Code related to the module Erased

-- Given an erased proof of equality of x and y one can show that
-- [ x ] is equal to [ y ].

[]-cong : {@0 A : Type a} {@0 x y : A} →
          EB.Erased (x ≡ y) → EB.[ x ] ≡ EB.[ y ]
[]-cong EB.[ refl ] = refl

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

-- [_]→ is injective.

Injective-[] : {@0 A : Type a} → Injective [ A ∣_]→
Injective-[] refl = refl

-- [_]→ is an embedding.

Is-embedding-[] : {@0 A : Type a} → Is-embedding [ A ∣_]→
Is-embedding-[] _ _ =
    (λ { refl → refl })
  , (λ { refl → refl })
  , (λ { refl → refl })
  , (λ { refl → refl })

-- If Erased A is a proposition, then A is a proposition.

Is-proposition-Erased→Is-proposition :
  {@0 A : Type a} →
  Is-proposition (Erased A) → Is-proposition A
Is-proposition-Erased→Is-proposition prop x y =
  Injective-[] (prop [ x ] [ y ])

-- A variant of the previous result.

H-level′-1-Erased→H-level′-1 :
  {@0 A : Type a} →
  H-level′ 1 (Erased A) → H-level′ 1 A
H-level′-1-Erased→H-level′-1 prop x y
  with proj₁ (prop [ x ] [ y ])
... | refl = refl , λ { refl → refl }

-- Equality is always very stable.

Very-stable-≡-trivial : Very-stable-≡ A
Very-stable-≡-trivial =
  _⇔_.from (Very-stable-≡↔Is-embedding-[] _)
           Is-embedding-[]

-- The following four results are inspired by a result in
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

-- There is an equivalence between (x : Erased A) → P x and
-- (@0 x : A) → P [ x ] (assuming function extensionality).
--
-- This is not proved by converting Π-Erased↔Π0[] to an equivalence,
-- because the type arguments of the conversion function in
-- Equivalence are not erased, and P can only be used in erased
-- contexts.
--
-- Note that, unlike in the type of E.Π-Erased≃Π0[], the argument P is
-- erased.

Π-Erased≃Π0[] :
  {@0 A : Type a} {@0 P : Erased A → Type p} →
  Function-extensionality′ (Erased A) P →
  ((x : Erased A) → P x) ≃ ((@0 x : A) → P [ x ])
Π-Erased≃Π0[] ext = record
  { to             = λ f x → f [ x ]
  ; is-equivalence =
        (λ { f [ x ] → f x })
      , (λ _ → refl)
      , (λ _ → ext λ { [ _ ] → refl })
      , (λ _ → uip _ _)
  }
  where
  uip : {@0 A : Type a} {@0 x y : A} (@0 p q : x ≡ y) → p ≡ q
  uip refl refl = refl

-- There is a bijection between (x : Erased A) → P (erased x) and
-- (@0 x : A) → P x (assuming function extensionality).

Π-Erased↔Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  Function-extensionality′ (Erased A) (P ∘ erased) →
  ((x : Erased A) → P (erased x)) ↔ ((@0 x : A) → P x)
Π-Erased↔Π0 = Π-Erased↔Π0[]

-- There is an equivalence between (x : Erased A) → P (erased x) and
-- (@0 x : A) → P x (assuming function extensionality).
--
-- Note that, unlike in the type of E.Π-Erased≃Π0, the argument P is
-- erased.

Π-Erased≃Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  Function-extensionality′ (Erased A) (P ∘ erased) →
  ((x : Erased A) → P (erased x)) ≃ ((@0 x : A) → P x)
Π-Erased≃Π0 = Π-Erased≃Π0[]
