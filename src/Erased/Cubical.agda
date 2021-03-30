------------------------------------------------------------------------
-- Some theory of Erased, developed using Cubical Agda
------------------------------------------------------------------------

-- This module instantiates and reexports code from Erased.

{-# OPTIONS --cubical --safe #-}

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
open import Equivalence-relation equality-with-J
import Erased.Basics equality-with-J as EB
import Erased.Level-1 equality-with-J as E₁
open import Function-universe equality-with-J as F
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as Trunc using (∥_∥)
open import Quotient eq as Quotient hiding ([_])
open import Surjection equality-with-J as Surjection using (_↠_)

private
  variable
    a p r : Level
    A B   : Type a
    R     : A → A → Type r
    x y   : A
    A↠B   : A ↠ B

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
  Is-equivalence ([]-cong-Path {x = x} {y = y})
[]-cong-Path-equivalence =
  _≃_.is-equivalence $ Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ eq → EB.[ P.cong EB.erased eq ]
        }
      ; right-inverse-of = λ _ → refl _
      }
    ; left-inverse-of = λ _ → refl _
    })

-- A rearrangement lemma for []-cong-Path (which holds by definition).

[]-cong-Path-[refl] :
  {@0 A : Type a} {@0 x : A} →
  []-cong-Path EB.[ P.refl {x = x} ] P.≡ P.refl {x = EB.[ x ]}
[]-cong-Path-[refl] = P.refl

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
  EB.Erased (x ≡ y)      ↔⟨ E₁.[]-cong₁.Erased-cong-↔ []-cong ≡↔≡ ⟩
  EB.Erased (x P.≡ y)    ↔⟨ Eq.⟨ _ , []-cong-Path-equivalence ⟩ ⟩
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

instance-of-[]-cong-axiomatisation : EB.[]-cong-axiomatisation a
instance-of-[]-cong-axiomatisation = λ where
  .EB.[]-cong-axiomatisation.[]-cong             → []-cong
  .EB.[]-cong-axiomatisation.[]-cong-equivalence → []-cong-equivalence
  .EB.[]-cong-axiomatisation.[]-cong-[refl]      → []-cong-[refl]

-- Some reexported definitions.

open import Erased equality-with-J instance-of-[]-cong-axiomatisation
  public
  hiding ([]-cong; []-cong-equivalence; []-cong-[refl]; Π-Erased↔Π0[])

private
  variable
    s : Very-stableᴱ-≡ A

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

------------------------------------------------------------------------
-- A closure property

-- If R is a propositional equivalence relation that is pointwise
-- stable, then equality is very stable for A / R.

Very-stable-≡-/ :
  Is-equivalence-relation R →
  (∀ x y → Is-proposition (R x y)) →
  (∀ x y → Stable (R x y)) →
  Very-stable-≡ (A / R)
Very-stable-≡-/ {A = A} {R = R} equiv prop s =
  Quotient.elim-prop λ where
    .[]ʳ x → Quotient.elim-prop λ where
       .[]ʳ y →                                         $⟨ s _ _ ⟩
         Stable (R x y)                                 ↝⟨ flip Stable-proposition→Very-stable (prop _ _) ⟩
         Very-stable (R x y)                            ↝⟨ Very-stable-cong _ (related≃[equal] equiv (prop _ _)) ⟩□
         Very-stable (Quotient.[ x ] ≡ Quotient.[ y ])  □
       .is-propositionʳ _ → Very-stable-propositional ext
    .is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      Very-stable-propositional ext

------------------------------------------------------------------------
-- Code related to Erased-singleton

-- A corollary of erased-singleton-with-erased-center-propositional.

↠→↔Erased-singleton :
  {@0 y : B}
  (A↠B : A ↠ B) →
  Very-stableᴱ-≡ B →
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥ ↔ Erased-singleton y
↠→↔Erased-singleton {A = A} {y = y} A↠B s =
  ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥  ↝⟨ Trunc.∥∥-cong-⇔ (Surjection.Σ-cong-⇔ A↠B λ _ → F.id) ⟩
  ∥ Erased-singleton y ∥                         ↝⟨ Trunc.∥∥↔ (erased-singleton-with-erased-center-propositional s) ⟩□
  Erased-singleton y                             □

mutual

  -- The right-to-left direction of the previous lemma does not depend
  -- on the assumption of stability.

  ↠→Erased-singleton→ :
    {@0 y : B}
    (A↠B : A ↠ B) →
    Erased-singleton y →
    ∥ (∃ λ (x : A) → Erased (_↠_.to A↠B x ≡ y)) ∥
  ↠→Erased-singleton→ = _  -- Agda can infer the definition.

  _ : _↔_.from (↠→↔Erased-singleton A↠B s) x ≡
      ↠→Erased-singleton→ A↠B x
  _ = refl _

-- A corollary of Σ-Erased-Erased-singleton↔ and ↠→↔Erased-singleton.

Σ-Erased-∥-Σ-Erased-≡-∥↔ :
  (A↠B : A ↠ B) →
  Very-stableᴱ-≡ B →
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥) ↔
  B
Σ-Erased-∥-Σ-Erased-≡-∥↔ {A = A} {B = B} A↠B s =
  (∃ λ (x : Erased B) →
     ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥)  ↝⟨ (∃-cong λ _ → ↠→↔Erased-singleton A↠B s) ⟩

  (∃ λ (x : Erased B) → Erased-singleton (erased x))        ↝⟨ Σ-Erased-Erased-singleton↔ ⟩□

  B                                                         □

mutual

  -- Again the right-to-left direction of the previous lemma does not
  -- depend on the assumption of stability.

  →Σ-Erased-∥-Σ-Erased-≡-∥ :
    (A↠B : A ↠ B) →
    B →
    ∃ λ (x : Erased B) →
      ∥ (∃ λ (y : A) → Erased (_↠_.to A↠B y ≡ erased x)) ∥
  →Σ-Erased-∥-Σ-Erased-≡-∥ = _  -- Agda can infer the definition.

  _ : _↔_.from (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) x ≡
      →Σ-Erased-∥-Σ-Erased-≡-∥ A↠B x
  _ = refl _

-- In an erased context the left-to-right direction of
-- Σ-Erased-∥-Σ-Erased-≡-∥↔ returns the erased first component.

@0 to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ :
  ∀ (A↠B : A ↠ B) (s : Very-stableᴱ-≡ B) x →
  _↔_.to (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) x ≡ erased (proj₁ x)
to-Σ-Erased-∥-Σ-Erased-≡-∥↔≡ A↠B s ([ x ] , y) =
  _↔_.to (Σ-Erased-∥-Σ-Erased-≡-∥↔ A↠B s) ([ x ] , y)  ≡⟨⟩
  proj₁ (_↔_.to (↠→↔Erased-singleton A↠B s) y)         ≡⟨ erased (proj₂ (_↔_.to (↠→↔Erased-singleton A↠B s) y)) ⟩∎
  x                                                    ∎
