------------------------------------------------------------------------
-- The "circle"
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly following the HoTT book.

open import Equality

module Circle
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (module _⇔_)
open import Prelude

open Derived-definitions-and-properties eq hiding (elim)
open import Equality.Groupoid eq as EG
open import Function-universe eq hiding (_∘_)
open import Groupoid eq
open import H-level eq
open import H-level.Truncation eq hiding (rec)
open import Univalence-axiom eq

-- Circle p is an axiomatisation of the circle, eliminating into
-- Set p.

Circle : (p : Level) → Set (lsuc p)
Circle p =
  ∃ λ (S¹ : Set) →
  ∃ λ (base : S¹) →
  ∃ λ (loop : base ≡ base) →
    (P : S¹ → Set p)
    (b : P base)
    (ℓ : subst P loop b ≡ b) →
    ∃ λ (f : ∀ x → P x) →
    ∃ λ (f-base : f base ≡ b) →
      subst (λ b → subst P loop b ≡ b)
            f-base
            (dependent-cong f loop) ≡
      ℓ

module Circle {p} (C : Circle p) where

  -- The circle.

  S¹ : Set
  S¹ = proj₁ C

  base : S¹
  base = proj₁ (proj₂ C)

  loop : base ≡ base
  loop = proj₁ (proj₂ (proj₂ C))

  -- Dependent eliminator.

  elim :
    (P : S¹ → Set p)
    (b : P base)
    (ℓ : subst P loop b ≡ b) →
    ∃ λ (f : ∀ x → P x) →
    ∃ λ (f-base : f base ≡ b) →
      subst (λ b → subst P loop b ≡ b)
            f-base
            (dependent-cong f loop) ≡
      ℓ
  elim = proj₂ (proj₂ (proj₂ C))

  -- Non-dependent eliminator.

  rec :
    (P : Set p)
    (b : P)
    (ℓ : b ≡ b) →
    ∃ λ (f : S¹ → P) →
    ∃ λ (f-base : f base ≡ b) →
      subst (λ b → b ≡ b) f-base (cong f loop) ≡ ℓ
  rec P b ℓ =
    let f , f-base , f-loop =
          elim (const P) b (subst (const P) loop b  ≡⟨ subst-const loop ⟩
                            b                       ≡⟨ ℓ ⟩∎
                            b                       ∎)

        lemma₁ =
          trans (subst-const loop)
                (subst (λ b → b ≡ b) (refl _) (cong f loop))  ≡⟨ cong (trans _) $ subst-refl _ _ ⟩

          trans (subst-const loop) (cong f loop)              ≡⟨ sym $ subst-refl _ _ ⟩∎

          subst (λ b → subst (const P) loop b ≡ b)
                (refl _)
                (trans (subst-const loop) (cong f loop))      ∎

        lemma₂ =
          trans (subst-const loop)
                (subst (λ b → b ≡ b) f-base (cong f loop))  ≡⟨ elim¹ (λ eq → trans (subst-const loop)
                                                                                   (subst (λ b → b ≡ b) eq (cong f loop))
                                                                               ≡
                                                                             subst (λ b → subst (const P) loop b ≡ b)
                                                                                   eq
                                                                                   (trans (subst-const loop) (cong f loop)))
                                                                      lemma₁
                                                                      f-base  ⟩
          subst (λ b → subst (const P) loop b ≡ b)
                f-base
                (trans (subst-const loop) (cong f loop))    ≡⟨ cong (subst _ _) $ sym $ dependent-cong-subst-const-cong _ _ ⟩

          subst (λ b → subst (const P) loop b ≡ b)
                f-base
                (dependent-cong f loop)                     ≡⟨ f-loop ⟩∎

          trans (subst-const loop) ℓ                        ∎

    in
    f , f-base , (
      subst (λ b → b ≡ b) f-base (cong f loop)  ≡⟨ Groupoid.right-cancellative (EG.groupoid _) lemma₂ ⟩∎
      ℓ                                         ∎)

-- For circles that eliminate into universes with positive universe
-- levels loop is not equal to refl base (assuming univalence).

loop≢refl :
  ∀ {p} →
  Univalence p →
  (C : Circle (lsuc p)) →
  let open Circle C in
  loop ≢ refl base
loop≢refl {p} univ C loop≡refl = ¬-Set-set-↑ univ Set-set
  where
  open Circle C

  refl≡ : (A : Set p) (A≡A : A ≡ A) → refl A ≡ A≡A
  refl≡ A A≡A =
    let
      (f , f-base , f-loop) = rec (Set p) A A≡A

      lemma =
        trans (refl (f base)) f-base  ≡⟨ trans-reflˡ _ ⟩
        f-base                        ≡⟨ sym $ trans-reflʳ _ ⟩∎
        trans f-base (refl A)         ∎
    in
    refl A                                           ≡⟨ sym $ ≡⇒→ (sym [subst≡]≡[trans≡trans]) lemma ⟩
    subst (λ b → b ≡ b) f-base (refl (f base))       ≡⟨ cong (subst (λ b → b ≡ b) f-base) $ sym $ cong-refl _ ⟩
    subst (λ b → b ≡ b) f-base (cong f (refl base))  ≡⟨ cong (subst (λ b → b ≡ b) f-base ∘ cong f) $ sym loop≡refl ⟩
    subst (λ b → b ≡ b) f-base (cong f loop)         ≡⟨ f-loop ⟩∎
    A≡A                                              ∎

  Set-set : Is-set (Set p)
  Set-set A B = _⇔_.from propositional⇔irrelevant
    (elim¹ (λ p → ∀ q → p ≡ q)
           (refl≡ A))

-- Thus circles that eliminate into universes with positive universe
-- levels are not sets (assuming univalence).

¬-S¹-set :
  ∀ {p} →
  Univalence p →
  (C : Circle (lsuc p)) →
  let open Circle C in
  ¬ Is-set S¹
¬-S¹-set univ C =
  Is-set S¹                     ↝⟨ (λ h → h _ _) ⟩
  Is-proposition (base ≡ base)  ↝⟨ (λ h → _⇔_.to propositional⇔irrelevant h _ _) ⟩
  loop ≡ refl base              ↝⟨ loop≢refl univ C ⟩□
  ⊥                             □
  where
  open Circle C

-- Every element of a circle that eliminates into a universe with a
-- positive universe level is /merely/ equal to the base point
-- (assuming extensionality).
--
-- This lemma (more or less) was mentioned by Mike Shulman in a blog
-- post (http://homotopytypetheory.org/2013/07/24/cohomology/).

all-points-on-the-circle-are-merely-equal :
  ∀ {ℓ} →
  Extensionality (lsuc ℓ) ℓ →
  (C : Circle (lsuc ℓ)) →
  let open Circle C in
  (x : S¹) → ∥ x ≡ base ∥ 1 ℓ
all-points-on-the-circle-are-merely-equal ext C =
  proj₁ $
  elim _ ∣ refl base ∣
       (_⇔_.to propositional⇔irrelevant
          (truncation-has-correct-h-level 1 ext)
          _ _)
  where
  open Circle C

-- H-level.Closure.proj₁-closure cannot be generalised by replacing
-- the assumption ∀ a → B a with ∀ a → ∥ B a ∥ 1 (# 0) (assuming
-- extensionality, univalence and the presence of a certain kind of
-- circle).
--
-- This observation is due to Andrea Vezzosi.

¬-generalised-proj₁-closure :
  Extensionality (# 1) (# 0) →
  Univalence (# 0) →
  Circle (# 1) →
  ¬ ({A : Set} {B : A → Set} →
     (∀ a → ∥ B a ∥ 1 (# 0)) →
     ∀ n → H-level n (Σ A B) → H-level n A)
¬-generalised-proj₁-closure ext univ C generalised-proj₁-closure =
                                 $⟨ singleton-contractible _ ⟩
  Contractible (Σ S¹ (_≡ base))  ↝⟨ generalised-proj₁-closure
                                      (all-points-on-the-circle-are-merely-equal ext C)
                                      0 ⟩
  Contractible S¹                ↝⟨ mono (zero≤ 2) ⟩
  Is-set S¹                      ↝⟨ ¬-S¹-set univ C ⟩□
  ⊥                              □
  where
  open Circle C
