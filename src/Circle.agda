------------------------------------------------------------------------
-- The "circle"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly following the HoTT book.

open import Equality

module Circle
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

import Equality.Path as P
open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq hiding (elim)
open import Equality.Path.Isomorphisms eq
open import Function-universe eq
open import H-level eq
open import H-level.Truncation.Propositional eq hiding (elim; rec)
open import Nat eq
open import Univalence-axiom eq

-- The circle.

data S¹ : Set where
  base  : S¹
  loop′ : base P.≡ base

loop : base ≡ base
loop = _↔_.from ≡↔≡ loop′

-- A dependent eliminator.

module Elim
  {p}
  (P : S¹ → Set p)
  (b : P base)
  (ℓ : subst P loop b ≡ b)
  where

  elim : (x : S¹) → P x
  elim base      = b
  elim (loop′ i) = subst≡→[]≡ ℓ i

  -- "Computation" rule for loop.

  elim-loop : dcong elim loop ≡ ℓ
  elim-loop = dcong-subst≡→[]≡ (refl _)

open Elim public

-- A non-dependent eliminator.

module Rec
  {p} {P : Set p}
  (b : P)
  (ℓ : b ≡ b)
  where

  private
    module E = Elim
      (λ _ → P)
      b
      (subst (λ _ → P) loop b  ≡⟨ subst-const _ ⟩
       b                       ≡⟨ ℓ ⟩∎
       b                       ∎)

  rec : S¹ → P
  rec = E.elim

  rec-loop : cong rec loop ≡ ℓ
  rec-loop = dcong≡→cong≡ E.elim-loop

open Rec public

-- The equality loop is not equal to refl base.

loop≢refl : loop ≢ refl base
loop≢refl loop≡refl = ¬-Set-set univ Set-set
  where
  refl≡ : (A : Set) (A≡A : A ≡ A) → refl A ≡ A≡A
  refl≡ A A≡A =
    refl A                  ≡⟨⟩
    refl (R.rec base)       ≡⟨ sym $ cong-refl _ ⟩
    cong R.rec (refl base)  ≡⟨ cong (cong R.rec) $ sym loop≡refl ⟩
    cong R.rec loop         ≡⟨ R.rec-loop ⟩∎
    A≡A                     ∎
    where
    module R = Rec A A≡A

  Set-set : Is-set Set
  Set-set {x = A} {y = B} =
    elim¹ (λ p → ∀ q → p ≡ q)
          (refl≡ A)

-- Thus the circle is not a set.

¬-S¹-set : ¬ Is-set S¹
¬-S¹-set =
  Is-set S¹                     ↝⟨ (λ h → h) ⟩
  Is-proposition (base ≡ base)  ↝⟨ (λ h → h _ _) ⟩
  loop ≡ refl base              ↝⟨ loop≢refl ⟩□
  ⊥                             □

-- Every element of the circle is /merely/ equal to the base point.
--
-- This lemma was mentioned by Mike Shulman in a blog post
-- (http://homotopytypetheory.org/2013/07/24/cohomology/).

all-points-on-the-circle-are-merely-equal :
  (x : S¹) → ∥ x ≡ base ∥
all-points-on-the-circle-are-merely-equal =
  elim _
       ∣ refl base ∣
       (truncation-is-proposition _ _)

-- However, it is not the case that every point on the circle is
-- /equal/ to the base point.

¬-all-points-on-the-circle-are-equal :
  ¬ ((x : S¹) → x ≡ base)
¬-all-points-on-the-circle-are-equal =
  ((x : S¹) → x ≡ base)  ↝⟨ (λ hyp x y → x     ≡⟨ hyp x ⟩
                                         base  ≡⟨ sym (hyp y) ⟩∎
                                         y     ∎) ⟩
  Is-proposition S¹      ↝⟨ mono₁ 1 ⟩
  Is-set S¹              ↝⟨ ¬-S¹-set ⟩□
  ⊥                      □

-- H-level.Closure.proj₁-closure cannot be generalised by replacing
-- the assumption ∀ a → B a with ∀ a → ∥ B a ∥.
--
-- This observation is due to Andrea Vezzosi.

¬-generalised-proj₁-closure :
  ¬ ({A : Set} {B : A → Set} →
     (∀ a → ∥ B a ∥) →
     ∀ n → H-level n (Σ A B) → H-level n A)
¬-generalised-proj₁-closure generalised-proj₁-closure =
                                 $⟨ singleton-contractible _ ⟩
  Contractible (Σ S¹ (_≡ base))  ↝⟨ generalised-proj₁-closure
                                      all-points-on-the-circle-are-merely-equal
                                      0 ⟩
  Contractible S¹                ↝⟨ mono (zero≤ 2) ⟩
  Is-set S¹                      ↝⟨ ¬-S¹-set ⟩□
  ⊥                              □
