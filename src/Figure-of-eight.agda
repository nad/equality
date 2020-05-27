------------------------------------------------------------------------
-- The figure of eight
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the circle uses path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Figure-of-eight
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude

open import Bijection equality-with-J using (_↔_)
import Bijection P.equality-with-J as PB
open import Circle eq as Circle
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
import Equality.Tactic P.equality-with-J as PT
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence P.equality-with-J as PE
open import Function-universe equality-with-J hiding (_∘_)
open import Pushout eq as Pushout
import Univalence-axiom P.equality-with-J as PU

-- The figure of eight
-- (https://topospaces.subwiki.org/wiki/Wedge_of_two_circles).

data ∞ : Set where
  base          : ∞
  loop₁ᴾ loop₂ᴾ : base P.≡ base

-- The higher constructors.

loop₁ : base ≡ base
loop₁ = _↔_.from ≡↔≡ loop₁ᴾ

loop₂ : base ≡ base
loop₂ = _↔_.from ≡↔≡ loop₂ᴾ

-- The two higher constructors are not equal.
--
-- The proof is based on the one from the HoTT book that shows that
-- the circle's higher constructor is not equal to reflexivity.

loop₁≢loop₂ : loop₁ ≢ loop₂
loop₁≢loop₂ =
  loop₁ ≡ loop₂      ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ (inverse ≡↔≡)) ⟩
  loop₁ᴾ ≡ loop₂ᴾ    ↔⟨ ≡↔≡ ⟩
  loop₁ᴾ P.≡ loop₂ᴾ  ↝⟨ PU.¬-Set-set P.univ ∘ Set-set ⟩□
  ⊥                  □
  where
  module _ (hyp : loop₁ᴾ P.≡ loop₂ᴾ) where
    refl≡ : (A : Set) (A≡A : A P.≡ A) → P.refl P.≡ A≡A
    refl≡ A A≡A =
      P.refl           P.≡⟨⟩
      P.cong F loop₁ᴾ  P.≡⟨ P.cong (P.cong F) hyp ⟩
      P.cong F loop₂ᴾ  P.≡⟨⟩
      A≡A              P.∎
      where
      F : ∞ → Set
      F base       = A
      F (loop₁ᴾ i) = P.refl i
      F (loop₂ᴾ i) = A≡A i

    Set-set : P.Is-set Set
    Set-set {x = A} {y = B} =
      P.elim¹ (λ p → ∀ q → p P.≡ q)
              (refl≡ A)

-- The two higher constructors provide a counterexample to
-- commutativity of transitivity.
--
-- This proof is a minor variant of a proof due to Andrea Vezzosi.

trans-not-commutative : trans loop₁ loop₂ ≢ trans loop₂ loop₁
trans-not-commutative =
  trans loop₁ loop₂ ≡ trans loop₂ loop₁          ↝⟨ (λ hyp → trans (sym (_↔_.from-to ≡↔≡ (sym trans≡trans)))
                                                               (trans (cong (_↔_.to ≡↔≡) hyp) (_↔_.from-to ≡↔≡ (sym trans≡trans)))) ⟩

  P.trans loop₁ᴾ loop₂ᴾ ≡ P.trans loop₂ᴾ loop₁ᴾ  ↝⟨ cong (P.subst F) ⟩

  P.subst F (P.trans loop₁ᴾ loop₂ᴾ) ≡
  P.subst F (P.trans loop₂ᴾ loop₁ᴾ)              ↝⟨ (λ hyp → trans (sym (_↔_.from ≡↔≡ lemma₁₂))
                                                               (trans hyp (_↔_.from ≡↔≡ lemma₂₁))) ⟩
  PE._≃_.to eq₂ ∘ PE._≃_.to eq₁ ≡
  PE._≃_.to eq₁ ∘ PE._≃_.to eq₂                  ↝⟨ cong (_$ fzero) ⟩

  fzero ≡ fsuc fzero                             ↝⟨ ⊎.inj₁≢inj₂ ⟩□

  ⊥                                              □
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

  F : ∞ → Set
  F base       = Fin 3
  F (loop₁ᴾ i) = P.≃⇒≡ eq₁ i
  F (loop₂ᴾ i) = P.≃⇒≡ eq₂ i

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
