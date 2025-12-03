------------------------------------------------------------------------
-- Some theory of Erased, developed using Cubical Agda
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased.

{-# OPTIONS --cubical=no-glue --safe #-}

import Equality.Path as P

module Erased.Cubical
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Bijection equality-with-J using (_↔_)
import Bijection P.equality-with-J as PB
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
import Equivalence P.equality-with-J as PEq
import Erased.Basics as EB
import Erased.Level-1 P.equality-with-J as EP
import Erased.Level-1 equality-with-J as E
open import Function-universe equality-with-J hiding (_∘_)

private
  variable
    a p : Level
    A   : Type a
    x y : A

------------------------------------------------------------------------
-- []-cong

-- Given an erased path from x to y there is a path from [ x ] to
-- [ y ].

[]-cong-Path :
  {@0 A : Type a} {@0 x y : A} →
  EB.Erased (x P.≡ y) → EB.[ x ] P.≡ EB.[ y ]
[]-cong-Path EB.[ eq ] = λ i → EB.[ eq i ]

-- A rearrangement lemma for []-cong-Path (which holds by definition).

[]-cong-Path-[refl] :
  {@0 A : Type a} {@0 x : A} →
  []-cong-Path EB.[ P.refl {x = x} ] P.≡ P.refl {x = EB.[ x ]}
[]-cong-Path-[refl] = P.refl

-- The []-cong axioms can be instantiated.

instance-of-[]-cong-axiomatisation-for-Path : EP.[]-cong-axiomatisation a
instance-of-[]-cong-axiomatisation-for-Path = λ where
  .EP.[]-cong-axiomatisation.[]-cong        → []-cong-Path
  .EP.[]-cong-axiomatisation.[]-cong-[refl] → []-cong-Path-[refl]

-- Given an erased proof of equality of x and y one can show that
-- EB.[ x ] is equal to EB.[ y ].

[]-cong : {@0 A : Type a} {@0 x y : A} →
          EB.Erased (x ≡ y) → EB.[ x ] ≡ EB.[ y ]
[]-cong {x} {y} =
  EB.Erased (x ≡ y)      ↝⟨ (λ (EB.[ eq ]) → EB.[ _↔_.to ≡↔≡ eq ]) ⟩
  EB.Erased (x P.≡ y)    ↝⟨ []-cong-Path ⟩
  EB.[ x ] P.≡ EB.[ y ]  ↔⟨ inverse ≡↔≡ ⟩□
  EB.[ x ] ≡ EB.[ y ]    □

-- A rearrangement lemma for []-cong.

[]-cong-[refl] :
  {@0 A : Type a} {@0 x : A} →
  []-cong EB.[ refl x ] ≡ refl EB.[ x ]
[]-cong-[refl] {x} =
  _↔_.from ≡↔≡ ([]-cong-Path EB.[ _↔_.to ≡↔≡ (refl x) ])  ≡⟨ cong (_↔_.from ≡↔≡ ∘ []-cong-Path) $ []-cong EB.[ to-≡↔≡-refl ] ⟩
  _↔_.from ≡↔≡ ([]-cong-Path EB.[ P.refl {x = x} ])       ≡⟨ cong (_↔_.from ≡↔≡) $ _↔_.from ≡↔≡ []-cong-Path-[refl] ⟩
  _↔_.from ≡↔≡ (P.refl {x = EB.[ x ]})                    ≡⟨ from-≡↔≡-refl ⟩∎
  refl EB.[ x ]                                           ∎

-- The []-cong axioms can be instantiated.

instance-of-[]-cong-axiomatisation : E.[]-cong-axiomatisation a
instance-of-[]-cong-axiomatisation = λ where
  .E.[]-cong-axiomatisation.[]-cong        → []-cong
  .E.[]-cong-axiomatisation.[]-cong-[refl] → []-cong-[refl]

-- Some reexported definitions.

open import Erased equality-with-J instance-of-[]-cong-axiomatisation
  public
  hiding ([]-cong; []-cong-[refl];
          Π-Erased≃Π0[]; Π-Erased≃Π0)

------------------------------------------------------------------------
-- Variants of some of the reexported definitions

private

  -- The lemma push-subst-[], which is reexported above, can be proved
  -- very easily when path equality is used.

  push-subst-[]-Path :
    {@0 P : A → Type p} {@0 p : P x} {x≡y : x P.≡ y} →
    P.subst (λ x → Erased (P x)) x≡y [ p ] ≡ [ P.subst P x≡y p ]
  push-subst-[]-Path = refl _

  -- Is-proposition is closed under Erased.

  Is-proposition-Erased :
    {@0 A : Type a} →
    @0 Is-proposition A → Is-proposition (Erased A)
  Is-proposition-Erased {A} prop =
    _↔_.from (H-level↔H-level 1)
      (Is-proposition-Erased′
         (_↔_.to (H-level↔H-level 1) prop))
    where
    Is-proposition-Erased′ :
      @0 P.Is-proposition A → P.Is-proposition (Erased A)
    Is-proposition-Erased′ prop [ x ] [ y ] = λ i →
      [ prop x y i ]

------------------------------------------------------------------------
-- Some isomorphisms/equivalences

-- The following four results are inspired by a result in
-- Mishra-Linger's PhD thesis (see Section 5.4.1).

-- There is a bijection (with paths for equality, not _≡_) between
-- (x : Erased A) → P x and (@0 x : A) → P [ x ].

Π-Erased↔Π0[] :
  {@0 A : Type a} {@0 P : Erased A → Type p} →
  ((x : Erased A) → P x) PB.↔ ((@0 x : A) → P [ x ])
Π-Erased↔Π0[] = record
  { surjection = record
    { logical-equivalence = EP.Π-Erased⇔Π0[]
    ; right-inverse-of = λ f _ → f
    }
  ; left-inverse-of = λ { f _ [ _ ] → f _ }
  }

-- There is an equivalence (with paths for equality, not _≡_) between
-- (x : Erased A) → P x and (@0 x : A) → P [ x ].
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
  ((x : Erased A) → P x) PEq.≃ ((@0 x : A) → P [ x ])
Π-Erased≃Π0[] = record
  { to             = λ f x → f [ x ]
  ; is-equivalence =
        (λ { f [ x ] → f x })
      , (λ f _ → f)
      , (λ { f _ [ _ ] → f _ })
      , (λ f _ _ x → f [ x ])
  }

-- There is a bijection (with paths for equality, not _≡_) between
-- (x : Erased A) → P (erased x) and (@0 x : A) → P x.

Π-Erased↔Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  ((x : Erased A) → P (erased x)) PB.↔ ((@0 x : A) → P x)
Π-Erased↔Π0 = Π-Erased↔Π0[]

-- There is an equivalence (with paths for equality, not _≡_) between
-- (x : Erased A) → P (erased x) and (@0 x : A) → P x.
--
-- Note that, unlike in the type of E.Π-Erased≃Π0, the argument P is
-- erased.

Π-Erased≃Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  ((x : Erased A) → P (erased x)) PEq.≃ ((@0 x : A) → P x)
Π-Erased≃Π0 = Π-Erased≃Π0[]
