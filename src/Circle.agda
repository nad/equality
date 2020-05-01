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
import Bijection P.equality-with-J as PB
open Derived-definitions-and-properties eq hiding (elim)
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; ∣_∣)
open import Nat eq
open import Tactic.By.Parametrised eq
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

------------------------------------------------------------------------
-- An alternative approach to defining eliminators and proving
-- computation rules for arbitrary notions of equality, based on an
-- anonymous reviewer's suggestion

-- Circle eq p is an axiomatisation of the circle, for the given
-- notion of equality eq, eliminating into Set p.
--
-- Note that the statement of the computation rule for "loop" is more
-- complicated than above (elim-loop). The reason is that the
-- computation rule for "base" does not hold definitionally.

Circle :
  ∀ {e⁺} →
  (∀ {a p} → Equality-with-J a p e⁺) → (p : Level) → Set (lsuc p)
Circle eq p =
  ∃ λ (𝕊¹ : Set) →
  ∃ λ (base : 𝕊¹) →
  ∃ λ (loop : base E.≡ base) →
    (P : 𝕊¹ → Set p)
    (b : P base)
    (ℓ : E.subst P loop b E.≡ b) →
    ∃ λ (elim : (x : 𝕊¹) → P x) →
    ∃ λ (elim-base : elim base E.≡ b) →
      E.subst (λ b → E.subst P loop b E.≡ b)
              elim-base
              (E.dcong elim loop)
        E.≡
      ℓ
  where
  module E = Derived-definitions-and-properties eq

-- A circle defined for paths (P.equality-with-J) is equivalent to one
-- defined for eq.

Circle≃Circle : Circle P.equality-with-J p ≃ Circle eq p
Circle≃Circle =
  ∃-cong λ _ →
  ∃-cong λ _ →
  Σ-cong (inverse ≡↔≡) λ loop →
  ∀-cong ext λ P →
  ∀-cong ext λ b →
  Π-cong-contra ext subst≡↔subst≡ λ ℓ →
  ∃-cong λ f →
  Σ-cong (inverse ≡↔≡) λ f-base →
  let lemma = P.elim¹
        (λ eq → _↔_.from subst≡↔subst≡
                  (P.subst
                     (λ b → P.subst P loop b P.≡ b)
                     eq
                     (P.dcong f loop)) ≡
                P.subst
                  (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
                  eq
                  (_↔_.from subst≡↔subst≡ (P.dcong f loop)))
        (_↔_.from subst≡↔subst≡
           (P.subst
              (λ b → P.subst P loop b P.≡ b)
              P.refl
              (P.dcong f loop))                       ≡⟨ cong (_↔_.from subst≡↔subst≡) $ _↔_.from ≡↔≡ $
                                                         P.subst-refl (λ b → P.subst P loop b P.≡ b) _ ⟩

         _↔_.from subst≡↔subst≡ (P.dcong f loop)      ≡⟨ sym $ _↔_.from ≡↔≡ $
                                                         P.subst-refl (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b) _ ⟩∎
         P.subst
           (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
           P.refl
           (_↔_.from subst≡↔subst≡ (P.dcong f loop))  ∎)
        _
  in
  P.subst
    (λ b → P.subst P loop b P.≡ b)
    f-base
    (P.dcong f loop) P.≡
  _↔_.to subst≡↔subst≡ ℓ                           ↔⟨ ≡↔≡ F.∘ inverse (from≡↔≡to (Eq.↔⇒≃ subst≡↔subst≡)) F.∘ inverse ≡↔≡ ⟩

  _↔_.from subst≡↔subst≡
    (P.subst
       (λ b → P.subst P loop b P.≡ b)
       f-base
       (P.dcong f loop)) P.≡
  ℓ                                                ↝⟨ ≡⇒↝ _ (cong (P._≡ _) lemma) ⟩

  P.subst
    (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
    f-base
    (_↔_.from subst≡↔subst≡ (P.dcong f loop)) P.≡
  ℓ                                                ↝⟨ ≡⇒↝ _ $ cong (λ eq → P.subst (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b) f-base eq P.≡ ℓ) $
                                                      _↔_.from-to (inverse subst≡↔subst≡) dcong≡dcong ⟩
  P.subst
    (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
    f-base
    (dcong f (_↔_.from ≡↔≡ loop)) P.≡
  ℓ                                                ↔⟨ inverse subst≡↔subst≡ ⟩□

  subst
    (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
    (_↔_.from ≡↔≡ f-base)
    (dcong f (_↔_.from ≡↔≡ loop)) ≡
  ℓ                                                □

-- An implemention of the circle for paths (P.equality-with-J).

circleᴾ : Circle P.equality-with-J p
circleᴾ =
    𝕊¹
  , base
  , loopᴾ
  , λ P b ℓ →
      let h↔h = P.heterogeneous↔homogeneous _
          f   = elimᴾ P b ∘ PB._↔_.from h↔h
      in
        f ℓ
      , P.refl
      , (P.subst (λ b → P.subst P loopᴾ b P.≡ b) P.refl
           (P.dcong (f ℓ) loopᴾ)                         P.≡⟨ P.subst-refl (λ b → P.subst P loopᴾ b P.≡ b) _ ⟩

         P.dcong (f ℓ) loopᴾ                             P.≡⟨ P.dcong≡hcong (f ℓ) ⟩

         PB._↔_.to h↔h (P.hcong (f ℓ) loopᴾ)             P.≡⟨⟩

         PB._↔_.to h↔h (PB._↔_.from h↔h ℓ)               P.≡⟨ PB._↔_.right-inverse-of h↔h _ ⟩∎

         ℓ                                               ∎)

-- An implementation of the circle for eq.

circle : Circle eq p
circle = _≃_.to Circle≃Circle circleᴾ

-- The latter implementation computes in the right way for "base".

_ :
  let _ , base′ , _ , elim′ = circle {p = p} in
  ∀ {P b ℓ} →
  proj₁ (elim′ P b ℓ) base′ ≡ b
_ = refl _

-- The usual computation rule for "loop" can be derived.

elim-loop-circle :
  let _ , _ , loop′ , elim′ = circle {p = p} in
  ∀ {P b ℓ} →
  dcong (proj₁ (elim′ P b ℓ)) loop′ ≡ ℓ
elim-loop-circle {P = P} {b = b} {ℓ = ℓ} =
  let _ , _ , loop′ , elim′           = circle
      elim″ , elim″-base , elim″-loop = elim′ P b ℓ

      lemma =
        refl _                                  ≡⟨ cong (_$ refl _) $ sym $ _↔_.from ≡↔≡ $ P.transport-refl P.0̲ ⟩
        P.transport (λ _ → b ≡ b) P.0̲ (refl _)  ≡⟨⟩
        elim″-base                              ∎
  in
  dcong elim″ loop′                                                 ≡⟨ sym $ subst-refl _ _ ⟩
  subst (λ b → subst P loop′ b ≡ b) ⟨ refl _ ⟩ (dcong elim″ loop′)  ≡⟨ ⟨by⟩ lemma ⟩
  subst (λ b → subst P loop′ b ≡ b) elim″-base (dcong elim″ loop′)  ≡⟨ elim″-loop ⟩∎
  ℓ                                                                 ∎

-- An alternative to Circle≃Circle that does not give the "right"
-- computational behaviour for circle′ below.

Circle≃Circle′ : Circle P.equality-with-J p ≃ Circle eq p
Circle≃Circle′ =
  ∃-cong λ _ →
  ∃-cong λ _ →
  Σ-cong (inverse ≡↔≡) λ loop →
  ∀-cong ext λ P →
  ∀-cong ext λ b →
  Π-cong ext (inverse subst≡↔subst≡) λ ℓ →
  ∃-cong λ f →
  Σ-cong (inverse ≡↔≡) λ f-base →
  let lemma = P.elim¹
        (λ eq → _↔_.from subst≡↔subst≡
                  (P.subst
                     (λ b → P.subst P loop b P.≡ b)
                     eq
                     (P.dcong f loop)) ≡
                P.subst
                  (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
                  eq
                  (_↔_.from subst≡↔subst≡ (P.dcong f loop)))
        (_↔_.from subst≡↔subst≡
           (P.subst
              (λ b → P.subst P loop b P.≡ b)
              P.refl
              (P.dcong f loop))                       ≡⟨ cong (_↔_.from subst≡↔subst≡) $ _↔_.from ≡↔≡ $
                                                         P.subst-refl (λ b → P.subst P loop b P.≡ b) _ ⟩

         _↔_.from subst≡↔subst≡ (P.dcong f loop)      ≡⟨ sym $ _↔_.from ≡↔≡ $
                                                         P.subst-refl (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b) _ ⟩∎
         P.subst
           (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
           P.refl
           (_↔_.from subst≡↔subst≡ (P.dcong f loop))  ∎)
        _
  in
  P.subst
    (λ b → P.subst P loop b P.≡ b)
    f-base
    (P.dcong f loop) P.≡
  ℓ                                                ↔⟨ ≡↔≡ F.∘ from-isomorphism (inverse $ Eq.≃-≡ $ Eq.↔⇒≃ $ inverse subst≡↔subst≡) F.∘ inverse ≡↔≡ ⟩

  _↔_.from subst≡↔subst≡
    (P.subst
       (λ b → P.subst P loop b P.≡ b)
       f-base
       (P.dcong f loop)) P.≡
  _↔_.from subst≡↔subst≡ ℓ                         ↝⟨ ≡⇒↝ _ (cong (P._≡ _↔_.from subst≡↔subst≡ ℓ) lemma) ⟩

  P.subst
    (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
    f-base
    (_↔_.from subst≡↔subst≡ (P.dcong f loop)) P.≡
  _↔_.from subst≡↔subst≡ ℓ                         ↝⟨ ≡⇒↝ _ $ cong (λ eq → P.subst (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b) f-base eq P.≡ _↔_.from subst≡↔subst≡ ℓ) $
                                                      _↔_.from-to (inverse subst≡↔subst≡) dcong≡dcong ⟩
  P.subst
    (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
    f-base
    (dcong f (_↔_.from ≡↔≡ loop)) P.≡
  _↔_.from subst≡↔subst≡ ℓ                         ↔⟨ inverse subst≡↔subst≡ ⟩□

  subst
    (λ b → subst P (_↔_.from ≡↔≡ loop) b ≡ b)
    (_↔_.from ≡↔≡ f-base)
    (dcong f (_↔_.from ≡↔≡ loop)) ≡
  _↔_.from subst≡↔subst≡ ℓ                         □

-- An alternative implementation of the circle for eq.

circle′ : Circle eq p
circle′ = _≃_.to Circle≃Circle′ circleᴾ

-- This implementation does not compute in the right way for "base".
-- The following code is (at the time of writing) rejected by Agda.

-- _ :
--   let _ , base′ , _ , elim′ = circle′ {p = p} in
--   ∀ {P b ℓ} →
--   proj₁ (elim′ P b ℓ) base′ ≡ b
-- _ = refl _
