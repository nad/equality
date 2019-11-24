------------------------------------------------------------------------
-- The "circle"
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly following the HoTT book.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the circle uses path equality, but
-- the supplied notion of equality is used for many other things.

open import Equality

module Circle {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

import Equality.Path as P
open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq hiding (elim)
open import Equality.Path.Isomorphisms eq
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; ∣_∣)
open import Nat eq
open import Univalence-axiom eq

private
  variable
    p   : Level
    A   : Set p
    P   : A → Set p
    b ℓ : A

-- The circle.

data 𝕊¹ : Set where
  base  : 𝕊¹
  loopᴾ : base P.≡ base

loop : base ≡ base
loop = _↔_.from ≡↔≡ loopᴾ

-- A dependent eliminator, expressed using paths.

elimᴾ :
  (P : 𝕊¹ → Set p)
  (b : P base) →
  P.[ (λ i → P (loopᴾ i)) ] b ≡ b →
  (x : 𝕊¹) → P x
elimᴾ P b ℓ base      = b
elimᴾ P b ℓ (loopᴾ i) = ℓ i

-- A non-dependent eliminator, expressed using paths.

recᴾ : (b : A) → b P.≡ b → 𝕊¹ → A
recᴾ = elimᴾ _

-- A dependent eliminator.

elim :
  (P : 𝕊¹ → Set p)
  (b : P base) →
  subst P loop b ≡ b →
  (x : 𝕊¹) → P x
elim P b ℓ = elimᴾ P b (subst≡→[]≡ ℓ)

-- A "computation" rule.

elim-loop : dcong (elim P b ℓ) loop ≡ ℓ
elim-loop = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

rec : (b : A) → b ≡ b → 𝕊¹ → A
rec b ℓ = recᴾ b (_↔_.to ≡↔≡ ℓ)

-- A "computation" rule.

rec-loop : cong (rec b ℓ) loop ≡ ℓ
rec-loop = cong-≡↔≡ (refl _)

-- An alternative non-dependent eliminator.

rec′ :  (b : A) → b ≡ b → 𝕊¹ → A
rec′ {A = A} b ℓ = elim
  (const A)
  b
  (subst (const A) loop b  ≡⟨ subst-const _ ⟩
   b                       ≡⟨ ℓ ⟩∎
   b                       ∎)

-- A "computation" rule.

rec′-loop : cong (rec′ b ℓ) loop ≡ ℓ
rec′-loop = dcong≡→cong≡ elim-loop

-- The equality loop is not equal to refl base.

loop≢refl : loop ≢ refl base
loop≢refl loop≡refl = ¬-Set-set univ Set-set
  where
  refl≡ : (A : Set) (A≡A : A ≡ A) → refl A ≡ A≡A
  refl≡ A A≡A =
    refl A                        ≡⟨⟩
    refl (rec A A≡A base)         ≡⟨ sym $ cong-refl _ ⟩
    cong (rec A A≡A) (refl base)  ≡⟨ cong (cong (rec A A≡A)) $ sym loop≡refl ⟩
    cong (rec A A≡A) loop         ≡⟨ rec-loop ⟩∎
    A≡A                           ∎

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
       (Trunc.truncation-is-proposition _ _)

-- Thus every element of the circle is not not equal to the base
-- point.

all-points-on-the-circle-are-¬¬-equal :
  (x : 𝕊¹) → ¬ ¬ x ≡ base
all-points-on-the-circle-are-¬¬-equal x =
  x ≢ base        ↝⟨ Trunc.rec ⊥-propositional ⟩
  ¬ ∥ x ≡ base ∥  ↝⟨ _$ all-points-on-the-circle-are-merely-equal x ⟩□
  ⊥               □

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

-- Thus double-negation shift for Set-valued predicates over 𝕊¹ does
-- not hold in general.

¬-double-negation-shift :
  ¬ ({P : 𝕊¹ → Set} → ((x : 𝕊¹) → ¬ ¬ P x) → ¬ ¬ ((x : 𝕊¹) → P x))
¬-double-negation-shift =
  ({P : 𝕊¹ → Set} → ((x : 𝕊¹) → ¬ ¬ P x) → ¬ ¬ ((x : 𝕊¹) → P x))  ↝⟨ _$ all-points-on-the-circle-are-¬¬-equal ⟩
  ¬ ¬ ((x : 𝕊¹) → x ≡ base)                                       ↝⟨ _$ ¬-all-points-on-the-circle-are-equal ⟩□
  ⊥                                                               □

-- Furthermore excluded middle for arbitrary types (in Set) does not
-- hold.

¬-excluded-middle : ¬ ({A : Set} → Dec A)
¬-excluded-middle =
  ({A : Set} → Dec A)                                             ↝⟨ (λ em ¬¬a → [ id , ⊥-elim ∘ ¬¬a ] em) ⟩
  ({A : Set} → ¬ ¬ A → A)                                         ↝⟨ (λ dne → flip _$_ ∘ (dne ∘_)) ⟩
  ({P : 𝕊¹ → Set} → ((x : 𝕊¹) → ¬ ¬ P x) → ¬ ¬ ((x : 𝕊¹) → P x))  ↝⟨ ¬-double-negation-shift ⟩□
  ⊥                                                               □

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
