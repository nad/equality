------------------------------------------------------------------------
-- Some theory of Erased, developed using Cubical Agda
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased.

{-# OPTIONS --erased-cubical --safe #-}

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
open import Function-universe equality-with-J

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

-- []-cong-Path is an equivalence.

[]-cong-Path-equivalence :
  {@0 A : Type a} {@0 x y : A} →
  PEq.Is-equivalence ([]-cong-Path {x = x} {y = y})
[]-cong-Path-equivalence =
  PEq._≃_.is-equivalence $ PEq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ eq → EB.[ P.cong EB.erased eq ]
        }
      ; right-inverse-of = λ _ → P.refl
      }
    ; left-inverse-of = λ _ → P.refl
    })

-- A rearrangement lemma for []-cong-Path (which holds by definition).

[]-cong-Path-[refl] :
  {@0 A : Type a} {@0 x : A} →
  []-cong-Path EB.[ P.refl {x = x} ] P.≡ P.refl {x = EB.[ x ]}
[]-cong-Path-[refl] = P.refl

-- The []-cong axioms can be instantiated.

instance-of-[]-cong-axiomatisation-for-Path : EP.[]-cong-axiomatisation a
instance-of-[]-cong-axiomatisation-for-Path = λ where
  .EP.[]-cong-axiomatisation.[]-cong             → []-cong-Path
  .EP.[]-cong-axiomatisation.[]-cong-equivalence → []-cong-Path-equivalence
  .EP.[]-cong-axiomatisation.[]-cong-[refl]      → []-cong-Path-[refl]

-- Given an erased proof of equality of x and y one can show that
-- EB.[ x ] is equal to EB.[ y ].

[]-cong : {@0 A : Type a} {@0 x y : A} →
          EB.Erased (x ≡ y) → EB.[ x ] ≡ EB.[ y ]
[]-cong {x = x} {y = y} =
  EB.Erased (x ≡ y)      ↝⟨ (λ (EB.[ eq ]) → EB.[ _↔_.to ≡↔≡ eq ]) ⟩
  EB.Erased (x P.≡ y)    ↝⟨ []-cong-Path ⟩
  EB.[ x ] P.≡ EB.[ y ]  ↔⟨ inverse ≡↔≡ ⟩□
  EB.[ x ] ≡ EB.[ y ]    □

-- []-cong is an equivalence.

[]-cong-equivalence :
  {@0 A : Type a} {@0 x y : A} →
  Is-equivalence ([]-cong {x = x} {y = y})
[]-cong-equivalence {x = x} {y = y} = _≃_.is-equivalence (
  EB.Erased (x ≡ y)      ↔⟨ _≃_.from ↔≃↔ $
                            EP.[]-cong.Erased-cong-↔
                              instance-of-[]-cong-axiomatisation-for-Path
                              (_≃_.to ↔≃↔ ≡↔≡) ⟩
  EB.Erased (x P.≡ y)    ↝⟨ _↔_.from ≃↔≃ PEq.⟨ _ , []-cong-Path-equivalence ⟩ ⟩
  EB.[ x ] P.≡ EB.[ y ]  ↔⟨ inverse ≡↔≡ ⟩□
  EB.[ x ] ≡ EB.[ y ]    □)

-- A rearrangement lemma for []-cong.

[]-cong-[refl] :
  {@0 A : Type a} {@0 x : A} →
  []-cong EB.[ refl x ] ≡ refl EB.[ x ]
[]-cong-[refl] {x = x} =
  sym $ _↔_.to (from≡↔≡to Eq.⟨ _ , []-cong-equivalence ⟩) (
    EB.[ _↔_.from ≡↔≡ (P.cong EB.erased (_↔_.to ≡↔≡ (refl EB.[ x ]))) ]  ≡⟨ []-cong EB.[ sym cong≡cong ] ⟩
    EB.[ cong EB.erased (_↔_.from ≡↔≡ (_↔_.to ≡↔≡ (refl EB.[ x ]))) ]    ≡⟨ []-cong EB.[ cong (cong EB.erased) (_↔_.left-inverse-of ≡↔≡ _) ] ⟩
    EB.[ cong EB.erased (refl EB.[ x ]) ]                                ≡⟨ []-cong EB.[ cong-refl _ ] ⟩∎
    EB.[ refl x ]                                                        ∎)

-- The []-cong axioms can be instantiated.

instance-of-[]-cong-axiomatisation : E.[]-cong-axiomatisation a
instance-of-[]-cong-axiomatisation = λ where
  .E.[]-cong-axiomatisation.[]-cong             → []-cong
  .E.[]-cong-axiomatisation.[]-cong-equivalence → []-cong-equivalence
  .E.[]-cong-axiomatisation.[]-cong-[refl]      → []-cong-[refl]

-- Some reexported definitions.

open import Erased equality-with-J instance-of-[]-cong-axiomatisation
  public
  hiding ([]-cong; []-cong-equivalence; []-cong-[refl]; Π-Erased≃Π0[])

------------------------------------------------------------------------
-- Variants of some of the reexported definitions

private

  -- The lemma push-subst-[], which is reexported above, can be proved
  -- very easily when path equality is used.

  push-subst-[]-Path :
    {@0 P : A → Type p} {@0 p : P x} {x≡y : x P.≡ y} →
    P.subst (λ x → Erased (P x)) x≡y [ p ] ≡ [ P.subst P x≡y p ]
  push-subst-[]-Path = refl _

  -- Above a lemma H-level-Erased is reexported. That lemma is proved
  -- in a certain way. The following two lemmas are included to
  -- illustrate a somewhat different proof technique that works for
  -- individual h-levels (given by closed natural numbers).

  -- Is-proposition is closed under Erased.

  Is-proposition-Erased :
    {@0 A : Type a} →
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
    {@0 A : Type a} →
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
-- Some isomorphisms/equivalences

-- The following four results are inspired by a result in
-- Mishra-Linger's PhD thesis (see Section 5.4.1).

-- There is a bijection (with paths for equality, not _≡_) between
-- (x : Erased A) → P x and (@0 x : A) → P [ x ].
--
-- This is a strengthening of the result of the same name from Erased.

Π-Erased↔Π0[] :
  {@0 A : Type a} {@0 P : Erased A → Type p} →
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
  {@0 A : Type a} {@0 P : Erased A → Type p} →
  ((x : Erased A) → P x) PEq.≃ ((@0 x : A) → P [ x ])
Π-Erased≃Π0[] = record
  { to             = λ f x → f [ x ]
  ; is-equivalence =
        (λ f ([ x ]) → f x)
      , (λ f _ → f)
      , (λ f _ → f)
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

Π-Erased≃Π0 :
  {@0 A : Type a} {@0 P : A → Type p} →
  ((x : Erased A) → P (erased x)) PEq.≃ ((@0 x : A) → P x)
Π-Erased≃Π0 = Π-Erased≃Π0[]
