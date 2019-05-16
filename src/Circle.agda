------------------------------------------------------------------------
-- The "circle"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly following the HoTT book.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the circle uses path equality, but
-- the supplied notion of equality is used for many other things.

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

private
  variable
    p : Level
    A : Set p

-- The circle.

data 𝕊¹ : Set where
  base  : 𝕊¹
  loop′ : base P.≡ base

loop : base ≡ base
loop = _↔_.from ≡↔≡ loop′

-- A dependent eliminator.

module Elim
  (P : 𝕊¹ → Set p)
  (b : P base)
  (ℓ : subst P loop b ≡ b)
  where

  elim : (x : 𝕊¹) → P x
  elim base      = b
  elim (loop′ i) = subst≡→[]≡ ℓ i

  -- "Computation" rule for loop.

  elim-loop : dcong elim loop ≡ ℓ
  elim-loop = dcong-subst≡→[]≡ (refl _)

open Elim public

-- A non-dependent eliminator.

module Rec (b : A) (ℓ : b ≡ b) where

  rec : 𝕊¹ → A
  rec base      = b
  rec (loop′ i) = _↔_.to ≡↔≡ ℓ i

  rec-loop : cong rec loop ≡ ℓ
  rec-loop = cong-≡↔≡ (refl _)

private

  -- An alternative non-dependent eliminator.

  module Rec′ (b : A) (ℓ : b ≡ b) where

    private
      module E = Elim
        (const A)
        b
        (subst (const A) loop b  ≡⟨ subst-const _ ⟩
         b                       ≡⟨ ℓ ⟩∎
         b                       ∎)

    rec : 𝕊¹ → A
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

¬-𝕊¹-set : ¬ Is-set 𝕊¹
¬-𝕊¹-set =
  Is-set 𝕊¹                     ↝⟨ (λ h → h) ⟩
  Is-proposition (base ≡ base)  ↝⟨ (λ h → h _ _) ⟩
  loop ≡ refl base              ↝⟨ loop≢refl ⟩□
  ⊥                             □

-- Every element of the circle is /merely/ equal to the base point.
--
-- This lemma was mentioned by Mike Shulman in a blog post
-- (http://homotopytypetheory.org/2013/07/24/cohomology/).

all-points-on-the-circle-are-merely-equal :
  (x : 𝕊¹) → ∥ x ≡ base ∥
all-points-on-the-circle-are-merely-equal =
  elim _
       ∣ refl base ∣
       (truncation-is-proposition _ _)

-- However, it is not the case that every point on the circle is
-- /equal/ to the base point.

¬-all-points-on-the-circle-are-equal :
  ¬ ((x : 𝕊¹) → x ≡ base)
¬-all-points-on-the-circle-are-equal =
  ((x : 𝕊¹) → x ≡ base)  ↝⟨ (λ hyp x y → x     ≡⟨ hyp x ⟩
                                         base  ≡⟨ sym (hyp y) ⟩∎
                                         y     ∎) ⟩
  Is-proposition 𝕊¹      ↝⟨ mono₁ 1 ⟩
  Is-set 𝕊¹              ↝⟨ ¬-𝕊¹-set ⟩□
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
  Contractible (Σ 𝕊¹ (_≡ base))  ↝⟨ generalised-proj₁-closure
                                      all-points-on-the-circle-are-merely-equal
                                      0 ⟩
  Contractible 𝕊¹                ↝⟨ mono (zero≤ 2) ⟩
  Is-set 𝕊¹                      ↝⟨ ¬-𝕊¹-set ⟩□
  ⊥                              □
