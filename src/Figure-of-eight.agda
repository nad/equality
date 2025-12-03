------------------------------------------------------------------------
-- The figure of eight
------------------------------------------------------------------------

{-# OPTIONS --cubical=erased --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the circle uses path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Figure-of-eight
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

import Equality.Path.Univalence as EPU
open import Prelude

open import Bijection equality-with-J using (_↔_)
import Bijection P.equality-with-J as PB
open import Circle eq as Circle using (𝕊¹; base; loopᴾ)
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
import Equality.Tactic P.equality-with-J as PT
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence P.equality-with-J as PE
open import Erased.Cubical eq
open import Function-universe equality-with-J hiding (_∘_)
open import Pushout eq as Pushout using (Wedge; inl; inr; glueᴾ)
import Univalence-axiom P.equality-with-J as PU

private
  variable
    a p   : Level
    A     : Type a
    P     : A → Type p
    e r x : A

------------------------------------------------------------------------
-- The type

-- The figure of eight
-- (https://topospaces.subwiki.org/wiki/Wedge_of_two_circles).

data ∞ : Type where
  base          : ∞
  loop₁ᴾ loop₂ᴾ : base P.≡ base

-- The higher constructors.

loop₁ : base ≡ base
loop₁ = _↔_.from ≡↔≡ loop₁ᴾ

loop₂ : base ≡ base
loop₂ = _↔_.from ≡↔≡ loop₂ᴾ

------------------------------------------------------------------------
-- Eliminators

-- An eliminator, expressed using paths.

record Elimᴾ (P : ∞ → Type p) : Type p where
  no-eta-equality
  field
    baseʳ  : P base
    loop₁ʳ : P.[ (λ i → P (loop₁ᴾ i)) ] baseʳ ≡ baseʳ
    loop₂ʳ : P.[ (λ i → P (loop₂ᴾ i)) ] baseʳ ≡ baseʳ

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : ∞) → P x
elimᴾ {P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : ∞) → P x
  helper base       = E.baseʳ
  helper (loop₁ᴾ i) = E.loop₁ʳ i
  helper (loop₂ᴾ i) = E.loop₂ʳ i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Type a) : Type a where
  no-eta-equality
  field
    baseʳ         : A
    loop₁ʳ loop₂ʳ : baseʳ P.≡ baseʳ

open Recᴾ public

recᴾ : Recᴾ A → ∞ → A
recᴾ r = elimᴾ λ where
    .baseʳ  → R.baseʳ
    .loop₁ʳ → R.loop₁ʳ
    .loop₂ʳ → R.loop₂ʳ
  where
  module R = Recᴾ r

-- An eliminator.

record Elim (P : ∞ → Type p) : Type p where
  no-eta-equality
  field
    baseʳ  : P base
    loop₁ʳ : subst P loop₁ baseʳ ≡ baseʳ
    loop₂ʳ : subst P loop₂ baseʳ ≡ baseʳ

open Elim public

elim : Elim P → (x : ∞) → P x
elim e = elimᴾ λ where
    .baseʳ  → E.baseʳ
    .loop₁ʳ → subst≡→[]≡ E.loop₁ʳ
    .loop₂ʳ → subst≡→[]≡ E.loop₂ʳ
  where
  module E = Elim e

-- Two "computation" rules.

elim-loop₁ : dcong (elim e) loop₁ ≡ e .Elim.loop₁ʳ
elim-loop₁ = dcong-subst≡→[]≡ (refl _)

elim-loop₂ : dcong (elim e) loop₂ ≡ e .Elim.loop₂ʳ
elim-loop₂ = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec (A : Type a) : Type a where
  no-eta-equality
  field
    baseʳ         : A
    loop₁ʳ loop₂ʳ : baseʳ ≡ baseʳ

open Rec public

rec : Rec A → ∞ → A
rec r = recᴾ λ where
    .baseʳ  → R.baseʳ
    .loop₁ʳ → _↔_.to ≡↔≡ R.loop₁ʳ
    .loop₂ʳ → _↔_.to ≡↔≡ R.loop₂ʳ
  where
  module R = Rec r

-- Two "computation" rules.

rec-loop₁ : cong (rec r) loop₁ ≡ r .Rec.loop₁ʳ
rec-loop₁ = cong-≡↔≡ (refl _)

rec-loop₂ : cong (rec r) loop₂ ≡ r .Rec.loop₂ʳ
rec-loop₂ = cong-≡↔≡ (refl _)

------------------------------------------------------------------------
-- Some negative results

-- The two higher constructors are not equal.
--
-- The proof is based on the one from the HoTT book that shows that
-- the circle's higher constructor is not equal to reflexivity.

loop₁≢loop₂ : loop₁ ≢ loop₂
loop₁≢loop₂ =
  Stable-¬
    [ loop₁ ≡ loop₂      ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse ≡↔≡)) ⟩
      loop₁ᴾ ≡ loop₂ᴾ    ↔⟨ ≡↔≡ ⟩
      loop₁ᴾ P.≡ loop₂ᴾ  ↝⟨ PU.¬-Type-set EPU.univ ∘ Type-set ⟩□
      ⊥                  □
    ]
  where
  module _ (hyp : loop₁ᴾ P.≡ loop₂ᴾ) where
    refl≡ : (A : Type) (A≡A : A P.≡ A) → P.refl P.≡ A≡A
    refl≡ A A≡A =
      P.refl           P.≡⟨⟩
      P.cong F loop₁ᴾ  P.≡⟨ P.cong (P.cong F) hyp ⟩
      P.cong F loop₂ᴾ  P.≡⟨⟩
      A≡A              P.∎
      where
      F : ∞ → Type
      F base       = A
      F (loop₁ᴾ i) = P.refl i
      F (loop₂ᴾ i) = A≡A i

    Type-set : P.Is-set Type
    Type-set {x = A} {y = B} =
      P.elim¹ (λ p → ∀ q → p P.≡ q)
              (refl≡ A)

-- The two higher constructors provide a counterexample to
-- commutativity of transitivity.
--
-- This proof is a minor variant of a proof due to Andrea Vezzosi.

trans-not-commutative : trans loop₁ loop₂ ≢ trans loop₂ loop₁
trans-not-commutative =
  Stable-¬
    [ trans loop₁ loop₂ ≡ trans loop₂ loop₁          ↝⟨ (λ hyp → trans (sym (_↔_.from-to ≡↔≡ (sym trans≡trans)))
                                                                   (trans (cong (_↔_.to ≡↔≡) hyp) (_↔_.from-to ≡↔≡ (sym trans≡trans)))) ⟩

      P.trans loop₁ᴾ loop₂ᴾ ≡ P.trans loop₂ᴾ loop₁ᴾ  ↝⟨ cong (P.subst F) ⟩

      P.subst F (P.trans loop₁ᴾ loop₂ᴾ) ≡
      P.subst F (P.trans loop₂ᴾ loop₁ᴾ)              ↝⟨ (λ hyp → trans (sym (_↔_.from ≡↔≡ lemma₁₂))
                                                                   (trans hyp (_↔_.from ≡↔≡ lemma₂₁))) ⟩
      PE._≃_.to eq₂ ∘ PE._≃_.to eq₁ ≡
      PE._≃_.to eq₁ ∘ PE._≃_.to eq₂                  ↝⟨ cong (_$ fzero) ⟩

      fzero ≡ fsuc fzero                             ↝⟨ ⊎.inj₁≢inj₂ ⟩□

      ⊥                                              □
    ]
  where
  eq₁ : Fin 3 PE.≃ Fin 3
  eq₁ = PE.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = λ where
                   fzero               → fsuc (fsuc fzero)
                   (fsuc fzero)        → fsuc fzero
                   (fsuc (fsuc fzero)) → fzero
        ; from = λ where
                   fzero               → fsuc (fsuc fzero)
                   (fsuc fzero)        → fsuc fzero
                   (fsuc (fsuc fzero)) → fzero
        }
      ; right-inverse-of = λ where
          fzero               → P.refl
          (fsuc fzero)        → P.refl
          (fsuc (fsuc fzero)) → P.refl
      }
    ; left-inverse-of = λ where
        fzero               → P.refl
        (fsuc fzero)        → P.refl
        (fsuc (fsuc fzero)) → P.refl
    })

  eq₂ : Fin 3 PE.≃ Fin 3
  eq₂ = PE.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = λ where
                   fzero               → fsuc fzero
                   (fsuc fzero)        → fsuc (fsuc fzero)
                   (fsuc (fsuc fzero)) → fzero
        ; from = λ where
                   fzero               → fsuc (fsuc fzero)
                   (fsuc fzero)        → fzero
                   (fsuc (fsuc fzero)) → fsuc fzero
        }
      ; right-inverse-of = λ where
          fzero               → P.refl
          (fsuc fzero)        → P.refl
          (fsuc (fsuc fzero)) → P.refl
      }
    ; left-inverse-of = λ where
        fzero               → P.refl
        (fsuc fzero)        → P.refl
        (fsuc (fsuc fzero)) → P.refl
    })

  @0 F : ∞ → Type
  F base       = Fin 3
  F (loop₁ᴾ i) = EPU.≃⇒≡ eq₁ i
  F (loop₂ᴾ i) = EPU.≃⇒≡ eq₂ i

  lemma₁₂ :
    P.subst F (P.trans loop₁ᴾ loop₂ᴾ) P.≡
    PE._≃_.to eq₂ ∘ PE._≃_.to eq₁
  lemma₁₂ _ i@fzero               = PE._≃_.to eq₂ (PE._≃_.to eq₁ i)
  lemma₁₂ _ i@(fsuc fzero)        = PE._≃_.to eq₂ (PE._≃_.to eq₁ i)
  lemma₁₂ _ i@(fsuc (fsuc fzero)) = PE._≃_.to eq₂ (PE._≃_.to eq₁ i)

  lemma₂₁ :
    P.subst F (P.trans loop₂ᴾ loop₁ᴾ) P.≡
    PE._≃_.to eq₁ ∘ PE._≃_.to eq₂
  lemma₂₁ _ i@fzero               = PE._≃_.to eq₁ (PE._≃_.to eq₂ i)
  lemma₂₁ _ i@(fsuc fzero)        = PE._≃_.to eq₁ (PE._≃_.to eq₂ i)
  lemma₂₁ _ i@(fsuc (fsuc fzero)) = PE._≃_.to eq₁ (PE._≃_.to eq₂ i)

private

  -- A lemma used below.

  trans-sometimes-commutative′ :
    {p q : x ≡ x} (f : (x : ∞) → x ≡ x) →
    f x ≡ p →
    trans p q ≡ trans q p
  trans-sometimes-commutative′ {x} {p} {q} f f-x≡p =
    trans p q      ≡⟨ cong (flip trans _) $ sym f-x≡p ⟩
    trans (f x) q  ≡⟨ trans-sometimes-commutative f ⟩
    trans q (f x)  ≡⟨ cong (trans q) f-x≡p ⟩∎
    trans q p      ∎

-- There is no function of type (x : ∞) → x ≡ x which returns loop₁
-- when applied to base.

¬-base↦loop₁ : ¬ ∃ λ (f : (x : ∞) → x ≡ x) → f base ≡ loop₁
¬-base↦loop₁ (f , f-base≡loop₁) =
  trans-not-commutative (
    trans loop₁ loop₂  ≡⟨ trans-sometimes-commutative′ f f-base≡loop₁ ⟩∎
    trans loop₂ loop₁  ∎)

-- There is no function of type (x : ∞) → x ≡ x which returns loop₂
-- when applied to base.

¬-base↦loop₂ : ¬ ∃ λ (f : (x : ∞) → x ≡ x) → f base ≡ loop₂
¬-base↦loop₂ (f , f-base≡loop₂) =
  trans-not-commutative (
    trans loop₁ loop₂  ≡⟨ sym $ trans-sometimes-commutative′ f f-base≡loop₂ ⟩∎
    trans loop₂ loop₁  ∎)

-- There is no function of type (x : ∞) → x ≡ x which returns
-- trans loop₁ loop₂ when applied to base.

¬-base↦trans-loop₁-loop₂ :
  ¬ ∃ λ (f : (x : ∞) → x ≡ x) → f base ≡ trans loop₁ loop₂
¬-base↦trans-loop₁-loop₂ (f , f-base≡trans-loop₁-loop₂) =
  trans-not-commutative (
    trans loop₁ loop₂                                    ≡⟨ sym $ trans-reflˡ _ ⟩
    trans (refl _) (trans loop₁ loop₂)                   ≡⟨ cong (flip trans _) $ sym $ trans-symˡ _ ⟩
    trans (trans (sym loop₁) loop₁) (trans loop₁ loop₂)  ≡⟨ trans-assoc _ _ _ ⟩
    trans (sym loop₁) (trans loop₁ (trans loop₁ loop₂))  ≡⟨ cong (trans (sym loop₁)) $ sym $
                                                            trans-sometimes-commutative′ f f-base≡trans-loop₁-loop₂ ⟩
    trans (sym loop₁) (trans (trans loop₁ loop₂) loop₁)  ≡⟨ cong (trans (sym loop₁)) $ trans-assoc _ _ _ ⟩
    trans (sym loop₁) (trans loop₁ (trans loop₂ loop₁))  ≡⟨ sym $ trans-assoc _ _ _ ⟩
    trans (trans (sym loop₁) loop₁) (trans loop₂ loop₁)  ≡⟨ cong (flip trans _) $ trans-symˡ _ ⟩
    trans (refl _) (trans loop₂ loop₁)                   ≡⟨ trans-reflˡ _ ⟩∎
    trans loop₂ loop₁                                    ∎)

-- There is no function of type (x : ∞) → x ≡ x which returns
-- trans loop₂ loop₁ when applied to base.

¬-base↦trans-loop₂-loop₁ :
  ¬ ∃ λ (f : (x : ∞) → x ≡ x) → f base ≡ trans loop₂ loop₁
¬-base↦trans-loop₂-loop₁ (f , f-base≡trans-loop₂-loop₁) =
  trans-not-commutative (
    trans loop₁ loop₂                                    ≡⟨ sym $ trans-reflˡ _ ⟩
    trans (refl _) (trans loop₁ loop₂)                   ≡⟨ cong (flip trans _) $ sym $ trans-symˡ _ ⟩
    trans (trans (sym loop₂) loop₂) (trans loop₁ loop₂)  ≡⟨ trans-assoc _ _ _ ⟩
    trans (sym loop₂) (trans loop₂ (trans loop₁ loop₂))  ≡⟨ cong (trans (sym loop₂)) $ sym $ trans-assoc _ _ _ ⟩
    trans (sym loop₂) (trans (trans loop₂ loop₁) loop₂)  ≡⟨ cong (trans (sym loop₂)) $
                                                            trans-sometimes-commutative′ f f-base≡trans-loop₂-loop₁ ⟩
    trans (sym loop₂) (trans loop₂ (trans loop₂ loop₁))  ≡⟨ sym $ trans-assoc _ _ _ ⟩
    trans (trans (sym loop₂) loop₂) (trans loop₂ loop₁)  ≡⟨ cong (flip trans _) $ trans-symˡ _ ⟩
    trans (refl _) (trans loop₂ loop₁)                   ≡⟨ trans-reflˡ _ ⟩∎
    trans loop₂ loop₁                                    ∎)

-- TODO: Can one prove that functions of type (x : ∞) → x ≡ x must map
-- base to refl base?

------------------------------------------------------------------------
-- A positive result

-- The figure of eight can be expressed as a wedge of two circles.
--
-- This result was suggested to me by Anders Mörtberg.

∞≃Wedge-𝕊¹-𝕊¹ : ∞ ≃ Wedge (𝕊¹ , base) (𝕊¹ , base)
∞≃Wedge-𝕊¹-𝕊¹ = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = _↔_.from ≡↔≡ ∘ from∘to
  })
  where
  lemma : inl base P.≡ inl base
  lemma =
    inl base  P.≡⟨ glueᴾ tt ⟩
    inr base  P.≡⟨ P.sym (P.cong inr loopᴾ) ⟩
    inr base  P.≡⟨ P.sym (glueᴾ tt) ⟩∎
    inl base  ∎

  Glue  = PT.Lift (glueᴾ tt)
  Loop  = PT.Lift (P.cong inr loopᴾ)
  Loop₂ = PT.Lift loop₂ᴾ
  Lemma =
    PT.Trans Glue $
    PT.Trans (PT.Sym Loop) $
    PT.Sym Glue

  to : ∞ → Wedge (𝕊¹ , base) (𝕊¹ , base)
  to base       = inl base
  to (loop₁ᴾ i) = P.cong inl loopᴾ i
  to (loop₂ᴾ i) = P.sym lemma i

  from : Wedge (𝕊¹ , base) (𝕊¹ , base) → ∞
  from = Pushout.recᴾ
    (Circle.recᴾ base loop₁ᴾ)
    (Circle.recᴾ base loop₂ᴾ)
    (λ _ → P.refl)

  to∘from : ∀ x → to (from x) ≡ x
  to∘from =
    _↔_.from ≡↔≡ ∘
    Pushout.elimᴾ _
      (Circle.elimᴾ _ P.refl (λ _ → P.refl))
      (Circle.elimᴾ _ (glueᴾ _)
         (PB._↔_.from (P.heterogeneous↔homogeneous _)
         (P.transport (λ i → P.sym lemma i P.≡ inr (loopᴾ i))
            P.0̲ (glueᴾ tt)                                       P.≡⟨ P.transport-≡ (glueᴾ tt) ⟩

          P.trans lemma (P.trans (glueᴾ tt) (P.cong inr loopᴾ))  P.≡⟨ PT.prove
                                                                        (PT.Trans Lemma (PT.Trans Glue Loop))
                                                                        (PT.Trans Glue (PT.Trans (PT.Sym Loop)
                                                                                          (PT.Trans (PT.Trans (PT.Sym Glue) Glue) Loop)))
                                                                        P.refl ⟩
          P.trans (glueᴾ tt)
            (P.trans (P.sym (P.cong inr loopᴾ))
               (P.trans (P.trans (P.sym (glueᴾ tt)) (glueᴾ tt))
                  (P.cong inr loopᴾ)))                           P.≡⟨ P.cong (λ eq → P.trans (glueᴾ tt) (P.trans (P.sym (P.cong inr loopᴾ))
                                                                                                           (P.trans eq (P.cong inr loopᴾ)))) $
                                                                      P.trans-symˡ _ ⟩
          P.trans (glueᴾ tt)
            (P.trans (P.sym (P.cong inr loopᴾ))
               (P.trans P.refl
                  (P.cong inr loopᴾ)))                           P.≡⟨ P.cong (λ eq → P.trans (glueᴾ tt)
                                                                                       (P.trans (P.sym (P.cong inr loopᴾ)) eq)) $
                                                                      P.trans-reflˡ _ ⟩
          P.trans (glueᴾ tt)
            (P.trans (P.sym (P.cong inr loopᴾ))
               (P.cong inr loopᴾ))                               P.≡⟨ P.cong (P.trans (glueᴾ tt)) $ P.trans-symˡ _ ⟩

          P.trans (glueᴾ tt) P.refl                              P.≡⟨ P.trans-reflʳ _ ⟩∎


          glueᴾ tt                                               ∎)))
      (λ _ → PB._↔_.from (P.heterogeneous↔homogeneous _) (
         P.subst (inl base P.≡_) (glueᴾ tt) P.refl  P.≡⟨ P.sym $ P.trans-subst {x≡y = P.refl} ⟩
         P.trans P.refl (glueᴾ tt)                  P.≡⟨ P.trans-reflˡ _ ⟩∎
         glueᴾ tt                                   ∎))

  from∘to : ∀ x → from (to x) P.≡ x
  from∘to base       = P.refl
  from∘to (loop₁ᴾ i) = P.refl
  from∘to (loop₂ᴾ i) = lemma′ i
    where
    lemma′ : P.[ (λ i → P.cong from (P.sym lemma) i P.≡ loop₂ᴾ i) ]
               P.refl ≡ P.refl
    lemma′ = PB._↔_.from (P.heterogeneous↔homogeneous _) (
      P.transport (λ i → P.cong from (P.sym lemma) i P.≡ loop₂ᴾ i)
        P.0̲ P.refl                                                     P.≡⟨ P.transport-≡ P.refl ⟩

      P.trans (P.cong from lemma) (P.trans P.refl loop₂ᴾ)              P.≡⟨ PT.prove
                                                                              (PT.Trans (PT.Cong from Lemma) (PT.Trans PT.Refl Loop₂))
                                                                              (PT.Trans (PT.Trans (PT.Cong from Glue)
                                                                                           (PT.Trans (PT.Cong from (PT.Sym Loop))
                                                                                              (PT.Cong from (PT.Sym Glue))))
                                                                                 Loop₂)
                                                                              P.refl ⟩
      P.trans (P.trans (P.cong from (glueᴾ tt))
                 (P.trans (P.cong from (P.sym (P.cong inr loopᴾ)))
                    (P.cong from (P.sym (glueᴾ tt)))))
        loop₂ᴾ                                                         P.≡⟨⟩

      P.trans (P.trans P.refl (P.trans (P.sym loop₂ᴾ) P.refl)) loop₂ᴾ  P.≡⟨ P.cong (flip P.trans loop₂ᴾ) $
                                                                            P.trans-reflˡ (P.trans (P.sym loop₂ᴾ) P.refl) ⟩

      P.trans (P.trans (P.sym loop₂ᴾ) P.refl) loop₂ᴾ                   P.≡⟨ P.cong (flip P.trans loop₂ᴾ) $
                                                                            P.trans-reflʳ (P.sym loop₂ᴾ) ⟩

      P.trans (P.sym loop₂ᴾ) loop₂ᴾ                                    P.≡⟨ P.trans-symˡ _ ⟩∎

      P.refl                                                           ∎)
