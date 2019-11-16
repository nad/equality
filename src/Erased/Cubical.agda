------------------------------------------------------------------------
-- Some theory of Erased, developed using Cubical Agda
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased and
-- Erased.Stability.

{-# OPTIONS --cubical --safe #-}

open import Equality

module Erased.Cubical
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

import Equality.Path as P
open import Prelude

open import Bijection eq using (_↔_)
import Bijection P.equality-with-J as PB
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
import Equivalence P.equality-with-J as PEq
open import Function-universe eq
open import H-level.Closure eq
open import Quotient eq as Quotient hiding ([_])

-- Some definitions from Erased are reexported.

open import Erased eq as Erased public
  hiding (module []-cong₁; module []-cong₂; module []-cong₃;
          Π-Erased↔Π0[])

-- Some definitions from Erased.Stability are reexported.

open import Erased.Stability eq as Stability public
  hiding (module []-cong)

private
  variable
    a p r : Level
    A     : Set a
    R     : A → A → Set r
    x y   : A

------------------------------------------------------------------------
-- Code related to the module Erased

-- Given an erased path from x to y there is a path from [ x ] to
-- [ y ].

[]-cong-Path :
  {@0 A : Set a} {@0 x y : A} →
  Erased (x P.≡ y) → [ x ] P.≡ [ y ]
[]-cong-Path [ eq ] = λ i → [ eq i ]

-- []-cong-Path is an equivalence.

[]-cong-Path-equivalence :
  {@0 A : Set a} {@0 x y : A} →
  Is-equivalence ([]-cong-Path {x = x} {y = y})
[]-cong-Path-equivalence =
  _≃_.is-equivalence $ Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ eq → [ P.cong erased eq ]
        }
      ; right-inverse-of = λ _ → refl _
      }
    ; left-inverse-of = λ _ → refl _
    })

-- A rearrangement lemma for []-cong-Path (which holds by definition).

[]-cong-Path-[refl] :
  {@0 A : Set a} {@0 x : A} →
  []-cong-Path [ P.refl {x = x} ] P.≡ P.refl {x = [ x ]}
[]-cong-Path-[refl] = P.refl

-- Given an erased proof of equality of x and y one can show that
-- [ x ] is equal to [ y ].

[]-cong : {@0 A : Set a} {@0 x y : A} →
          Erased (x ≡ y) → [ x ] ≡ [ y ]
[]-cong {x = x} {y = y} =
  Erased (x ≡ y)    ↝⟨ map (_↔_.to ≡↔≡) ⟩
  Erased (x P.≡ y)  ↝⟨ []-cong-Path ⟩
  [ x ] P.≡ [ y ]   ↔⟨ inverse ≡↔≡ ⟩□
  [ x ] ≡ [ y ]     □

-- []-cong is an equivalence.

[]-cong-equivalence :
  {@0 A : Set a} {@0 x y : A} →
  Is-equivalence ([]-cong {x = x} {y = y})
[]-cong-equivalence {x = x} {y = y} = _≃_.is-equivalence (
  Erased (x ≡ y)    ↔⟨ Erased.[]-cong₁.Erased-cong-↔ []-cong ≡↔≡ ⟩
  Erased (x P.≡ y)  ↔⟨ Eq.⟨ _ , []-cong-Path-equivalence ⟩ ⟩
  [ x ] P.≡ [ y ]   ↔⟨ inverse ≡↔≡ ⟩□
  [ x ] ≡ [ y ]     □)

-- A rearrangement lemma for []-cong.

[]-cong-[refl] :
  {@0 A : Set a} {@0 x : A} →
  []-cong [ refl x ] ≡ refl [ x ]
[]-cong-[refl] {x = x} =
  sym $ _↔_.to (from≡↔≡to Eq.⟨ _ , []-cong-equivalence ⟩) (
    [ _↔_.from ≡↔≡ (P.cong erased (_↔_.to ≡↔≡ (refl [ x ]))) ]  ≡⟨ []-cong [ sym cong≡cong ] ⟩
    [ cong erased (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ (refl [ x ]))) ]    ≡⟨ []-cong [ cong (cong erased) (_↔_.left-inverse-of ≡↔≡ _) ] ⟩
    [ cong erased (refl [ x ]) ]                                ≡⟨ []-cong [ cong-refl _ ] ⟩∎
    [ refl x ]                                                  ∎)

-- Some reexported definitions.

open Erased.[]-cong₃ []-cong []-cong-equivalence []-cong-[refl] public
  hiding ([]-cong-[refl])

private

  -- The lemma push-subst-[], which is reexported above, can be proved
  -- very easily when path equality is used.

  push-subst-[]-Path :
    {@0 P : A → Set p} {@0 p : P x} {x≡y : x P.≡ y} →
    P.subst (λ x → Erased (P x)) x≡y [ p ] ≡ [ P.subst P x≡y p ]
  push-subst-[]-Path = refl _

  -- Above a lemma H-level-Erased is reexported. That lemma is proved
  -- in a certain way. The following two lemmas are included to
  -- illustrate a somewhat different proof technique that works for
  -- individual h-levels (given by closed natural numbers).

  -- Is-proposition is closed under Erased.

  Is-proposition-Erased :
    {@0 A : Set a} →
    @0 Is-proposition A → Is-proposition (Erased A)
  Is-proposition-Erased {A = A} prop =
    _↔_.from (H-level↔H-level 1)
      (Is-proposition-Erased′
         (_↔_.to (H-level↔H-level 1) prop))
    where
    Is-proposition-Erased′ :
      @0 P.Is-proposition A → P.Is-proposition (Erased A)
    Is-proposition-Erased′ prop x y = λ i →
      [ prop (erased x) (erased y) i ]

  -- Is-set is closed under Erased.

  Is-set-Erased :
    {@0 A : Set a} →
    @0 Is-set A → Is-set (Erased A)
  Is-set-Erased {A = A} set =
    _↔_.from (H-level↔H-level 2)
      (Is-set-Erased′
         (_↔_.to (H-level↔H-level 2) set))
    where
    Is-set-Erased′ : @0 P.Is-set A → P.Is-set (Erased A)
    Is-set-Erased′ set p q = λ i j →
      [ set (P.cong erased p) (P.cong erased q) i j ]

-- The following four results are inspired by a result in
-- Mishra-Linger's PhD thesis (see Section 5.4.1).

-- There is a bijection (with paths for equality, not _≡_) between
-- (x : Erased A) → P x and (@0 x : A) → P [ x ].
--
-- This is a strengthening of the result of the same name from Erased.

Π-Erased↔Π0[] :
  {@0 A : Set a} {@0 P : Erased A → Set p} →
  ((x : Erased A) → P x) PB.↔ ((@0 x : A) → P [ x ])
Π-Erased↔Π0[] = record
  { surjection = record
    { logical-equivalence = Π-Erased⇔Π0
    ; right-inverse-of = λ f _ → f
    }
  ; left-inverse-of = λ f _ → f
  }

-- There is an equivalence (with paths for equality, not _≡_) between
-- (x : Erased A) → P x and (@0 x : A) → P [ x ].
--
-- This is not proved by converting Π-Erased↔Π0[] to an equivalence,
-- because the type arguments of the conversion function in
-- Equivalence are not erased, and A and P can only be used in erased
-- contexts.

Π-Erased≃Π0[] :
  {@0 A : Set a} {@0 P : Erased A → Set p} →
  ((x : Erased A) → P x) PEq.≃ ((@0 x : A) → P [ x ])
Π-Erased≃Π0[] = record
  { to             = λ f x → f [ x ]
  ; is-equivalence = λ f →
      ( (λ ([ x ]) → f x)
      , (λ _ → f)
      )
      , λ (g , eq) i →
            (λ ([ x ]) → eq (P.- i) x)
          , (λ j → eq (P.max (P.- i) j))
  }

-- There is a bijection (with paths for equality, not _≡_) between
-- (x : Erased A) → P (erased x) and (@0 x : A) → P x.

Π-Erased↔Π0 :
  {@0 A : Set a} {@0 P : A → Set p} →
  ((x : Erased A) → P (erased x)) PB.↔ ((@0 x : A) → P x)
Π-Erased↔Π0 = Π-Erased↔Π0[]

-- There is an equivalence (with paths for equality, not _≡_) between
-- (x : Erased A) → P (erased x) and (@0 x : A) → P x.

Π-Erased≃Π0 :
  {@0 A : Set a} {@0 P : A → Set p} →
  ((x : Erased A) → P (erased x)) PEq.≃ ((@0 x : A) → P x)
Π-Erased≃Π0 = Π-Erased≃Π0[]

------------------------------------------------------------------------
-- Code related to the module Erased.Stability

-- Reexported definitions.

open Stability.[]-cong []-cong []-cong-equivalence []-cong-[refl]
  public

-- If R is a propositional equivalence relation that is pointwise
-- stable, then equality is very stable for A / R.

Very-stable-≡-/ :
  Is-equivalence-relation R →
  (∀ x y → Is-proposition (R x y)) →
  (∀ x y → Stable (R x y)) →
  Very-stable-≡ (A / R)
Very-stable-≡-/ {A = A} {R = R} equiv prop s =
  Quotient.elim-Prop
    _
    (λ x → Quotient.elim-Prop
       _
       (λ y →                                            $⟨ s _ _ ⟩
          Stable (R x y)                                 ↝⟨ flip Stable-proposition→Very-stable (prop _ _) ⟩
          Very-stable (R x y)                            ↝⟨ Very-stable-cong _ (related≃[equal] equiv (prop _ _)) ⟩□
          Very-stable (Quotient.[ x ] ≡ Quotient.[ y ])  □)
       (λ _ → Very-stable-propositional ext))
    (λ _ →
       Π-closure ext 1 λ _ →
       Very-stable-propositional ext)
