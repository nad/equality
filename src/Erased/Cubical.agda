------------------------------------------------------------------------
-- Some theory of Erased, developed using Cubical Agda
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased and
-- Erased.Stability.

{-# OPTIONS --cubical --safe #-}

open import Equality

module Erased.Cubical
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

import Equality.Path as P
open import Prelude

open import Bijection eq using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_)
import Equivalence P.equality-with-J as PEq
open import Function-universe eq

-- Some definitions from Erased are reexported.

open import Erased eq as Erased public
  hiding (module []-cong;
          module Erased-≡↔[]≡[]₁;
          module Erased-≡↔[]≡[]₂)

-- Some definitions from Erased.Stability are reexported.

open import Erased.Stability eq as Stability public
  hiding (module Very-stable→Very-stable-≡)

private
  variable
    a p : Level
    A   : Set a
    x y : A

------------------------------------------------------------------------
-- Code related to the module Erased

-- There is a bijection between erased paths and paths between
-- erased values.

Erased-Path↔Path-[]-[] :
  {@0 A : Set a} {@0 x y : A} →
  Erased (x P.≡ y) ↔ [ x ] P.≡ [ y ]
Erased-Path↔Path-[]-[] = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [ eq ] i → [ eq i ] }
      ; from = λ eq → [ P.cong erased eq ]
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

private

  -- The following lemma is not exported, but a lemma []-cong with the
  -- same type is reexported below.

  -- Given an erased proof of equality of x and y one can show that
  -- [ x ] is equal to [ y ].

  []-cong′ : {@0 A : Set a} {@0 x y : A} →
             Erased (x ≡ y) → [ x ] ≡ [ y ]
  []-cong′ {x = x} {y = y} =
    Erased (x ≡ y)    ↝⟨ (λ { [ eq ] → [ _↔_.to ≡↔≡ eq ] }) ⟩
    Erased (x P.≡ y)  ↔⟨ Erased-Path↔Path-[]-[] ⟩
    [ x ] P.≡ [ y ]   ↔⟨ inverse ≡↔≡ ⟩□
    [ x ] ≡ [ y ]     □

-- There is a bijection between erased equality proofs and equalities
-- between erased values.

Erased-≡↔[]≡[] :
  {@0 A : Set a} {@0 x y : A} →
  Erased (x ≡ y) ↔ [ x ] ≡ [ y ]
Erased-≡↔[]≡[] {x = x} {y = y} =
  Erased (x ≡ y)    ↝⟨ Erased.[]-cong.Erased-cong-↔ []-cong′ ≡↔≡ ⟩
  Erased (x P.≡ y)  ↝⟨ Erased-Path↔Path-[]-[] ⟩
  [ x ] P.≡ [ y ]   ↝⟨ inverse ≡↔≡ ⟩□
  [ x ] ≡ [ y ]     □

-- A rearrangement lemma for Erased-≡↔[]≡[].

to-Erased-≡↔[]≡[]-[refl] :
  _↔_.to Erased-≡↔[]≡[] [ refl x ] ≡ refl [ x ]
to-Erased-≡↔[]≡[]-[refl] {x = x} =
  _↔_.from ≡↔≡ (P.cong [_] (_↔_.to ≡↔≡ (refl x)))  ≡⟨ sym cong≡cong ⟩
  cong [_] (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ (refl x)))    ≡⟨ cong (cong [_]) $ _↔_.left-inverse-of ≡↔≡ _ ⟩
  cong [_] (refl x)                                ≡⟨ cong-refl _ ⟩∎
  refl [ x ]                                       ∎

-- Some reexported definitions.

open Erased.Erased-≡↔[]≡[]₂ Erased-≡↔[]≡[] to-Erased-≡↔[]≡[]-[refl]
  public

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

------------------------------------------------------------------------
-- Code related to the module Erased.Stability

private

  -- If A is very stable, then the types of paths between values of
  -- type A are very stable.

  Very-stable→Very-stable-Path :
    {x y : A} → Very-stable A → Very-stable (x P.≡ y)
  Very-stable→Very-stable-Path {x = x} {y = y} s = _≃_.is-equivalence (
    x P.≡ y           ↝⟨ inverse $ _↔_.from ≃↔≃ $ PEq.≃-≡ $ _↔_.to ≃↔≃ $ Eq.⟨ _ , s ⟩ ⟩
    [ x ] P.≡ [ y ]   ↔⟨ inverse Erased-Path↔Path-[]-[] ⟩□
    Erased (x P.≡ y)  □)

-- If A is very stable, then the types of equalities between values
-- of type A are very stable.

Very-stable→Very-stable-≡ : Very-stable A → Very-stable-≡ A
Very-stable→Very-stable-≡ s {x = x} {y = y} =
  _≃_.is-equivalence $
  Eq.with-other-function
    (x ≡ y             ↔⟨ ≡↔≡ ⟩
     x P.≡ y           ↝⟨ inverse $ Very-stable→Stable (Very-stable→Very-stable-Path s) ⟩
     Erased (x P.≡ y)  ↔⟨ Erased-cong (inverse ≡↔≡) ⟩□
     Erased (x ≡ y)    □)
    [_]
    (λ eq →
      [ _↔_.from ≡↔≡ (_↔_.to ≡↔≡ eq) ]  ≡⟨ cong [_] (_↔_.left-inverse-of ≡↔≡ eq) ⟩∎
      [ eq ]                            ∎)

private

  -- Some examples showing how Very-stable→Very-stable-≡ can be
  -- used.

  -- Equalities between erased values are very stable.

  Very-stable-≡₀ : {@0 A : Set a} → Very-stable-≡ (Erased A)
  Very-stable-≡₀ = Very-stable→Very-stable-≡ Very-stable-Erased

  -- Equalities between equalities between erased values are very
  -- stable.

  Very-stable-≡₁ :
    {@0 A : Set a} {x y : Erased A} →
    Very-stable-≡ (x ≡ y)
  Very-stable-≡₁ = Very-stable→Very-stable-≡ Very-stable-≡₀

  -- And so on…

-- Reexported definitions.

open Stability.Very-stable→Very-stable-≡
  Erased-≡↔[]≡[] to-Erased-≡↔[]≡[]-[refl] Very-stable→Very-stable-≡
  public
