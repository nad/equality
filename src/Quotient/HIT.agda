------------------------------------------------------------------------
-- Quotients (set-quotients), defined using a higher inductive type
------------------------------------------------------------------------

-- Note that this module is experimental: it uses rewrite rules and
-- postulates to encode a higher inductive type.

{-# OPTIONS --without-K --rewriting #-}

-- Partly following the HoTT book.

module Quotient.HIT where

open import Equality.Propositional hiding (elim)
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (_∘_; id)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
import H-level.Truncation equality-with-J as Trunc
open import H-level.Truncation.Propositional hiding (rec; elim)
import Quotient equality-with-J as Quotient
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

------------------------------------------------------------------------
-- Quotients

-- I have tried to follow the rules for HITs specified in the
-- HoTT-Agda library
-- (https://github.com/HoTT/HoTT-Agda/blob/master/lib/types/HIT_README.txt).

-- The quotient type constructor.

infix 5 _/_

postulate
  _/_ : ∀ {a r} (A : Set a) → (A → A → Proposition r) → Set (a ⊔ r)

module _ {a r} {A : Set a} {R : A → A → Proposition r} where

  postulate

    -- Constructors.

    [_]                  : A → A / R
    []-respects-relation : ∀ {x y} → proj₁ (R x y) → [ x ] ≡ [ y ]
    /-is-set             : Is-set (A / R)

    -- Eliminator.

    elim :
      ∀ {p} (P : A / R → Set p) →
      (p-[] : ∀ x → P [ x ]) →
      (∀ {x y} (r : proj₁ (R x y)) →
       subst P ([]-respects-relation r) (p-[] x) ≡ p-[] y) →
      (∀ x → Is-set (P x)) →
      ∀ x → P x

-- Computation rules.
--
-- NOTE: There is no computation rule corresponding to /-is-set, and
-- rewriting has not been activated for the "computation" rule
-- corresponding to []-respects-relation.

module _ {a r p}
         {A : Set a} {R : A → A → Proposition r} {P : A / R → Set p}
         {p-[] : ∀ x → P [ x ]}
         {p-[]-respects-relation :
            ∀ {x y} (r : proj₁ (R x y)) →
            subst P ([]-respects-relation r) (p-[] x) ≡ p-[] y}
         {is-set : ∀ x → Is-set (P x)}
         where

  -- Computation rule for [_].

  postulate
    elim-[] :
      ∀ x → elim P p-[] p-[]-respects-relation is-set [ x ] ≡ p-[] x

  {-# REWRITE elim-[] #-}

  -- "Computation" rule for []-respects-relation.

  postulate
    elim-[]-respects-relation :
      ∀ {x y} (r : proj₁ (R x y)) →
      dependent-cong (elim P p-[] p-[]-respects-relation is-set)
                     ([]-respects-relation r) ≡
      p-[]-respects-relation r

-- A non-dependent eliminator.

rec :
  ∀ {a r p} {A : Set a} {R : A → A → Proposition r} {P : Set p}
  (f : A → P) →
  (∀ {x y} → proj₁ (R x y) → f x ≡ f y) →
  Is-set P →
  A / R → P
rec {P = P} f resp P-set = elim
  _
  f
  (λ {x y} r →
     subst (const P) ([]-respects-relation r) (f x)  ≡⟨ subst-const ([]-respects-relation r) ⟩
     f x                                             ≡⟨ resp r ⟩∎
     f y                                             ∎)
  (λ _ → P-set)

-- A variant of elim that can be used if the motive composed with [_]
-- is a family of propositions.
--
-- I took the idea for this eliminator from Nicolai Kraus.

elim-Prop :
  ∀ {a r} {A : Set a} {R : A → A → Proposition r} {p}
  (P : A / R → Set p) →
  (p-[] : ∀ x → P [ x ]) →
  (∀ x → Is-proposition (P [ x ])) →
  ∀ x → P x
elim-Prop P p-[] P-prop = elim
  P p-[]
  (λ _ → _⇔_.to propositional⇔irrelevant (P-prop _) _ _)
  (elim
     _
     (mono₁ 1 ∘ P-prop)
     (λ _ → _⇔_.to propositional⇔irrelevant
              (H-level-propositional ext 2) _ _)
     (λ _ → mono₁ 1 (H-level-propositional ext 2)))

-- A variant of rec that can be used if the motive is a proposition.

rec-Prop :
  ∀ {a r} {A : Set a} {R : A → A → Proposition r} {p} {P : Set p} →
  (A → P) →
  Is-proposition P →
  A / R → P
rec-Prop p-[] P-prop = elim-Prop (const _) p-[] (const P-prop)

------------------------------------------------------------------------
-- Some properties

module _ {a r} {A : Set a} {R : A → A → Proposition r} where

  -- [_] is surjective.

  []-surjective : Surjective ([_] {R = R})
  []-surjective = elim-Prop
    _
    (λ x → ∣ x , refl ∣)
    (λ _ → truncation-is-proposition)

  -- If the relation is an equivalence relation, then it is equivalent
  -- to equality under [_].
  --
  -- The basic structure of this proof is that of Proposition 2 in
  -- "Quotienting the Delay Monad by Weak Bisimilarity" by Chapman,
  -- Uustalu and Veltri.

  related≃[equal] :
    Univalence r →
    (∀ {x} → proj₁ (R x x)) →
    (∀ {x y} → proj₁ (R x y) → proj₁ (R y x)) →
    (∀ {x y z} → proj₁ (R x y) → proj₁ (R y z) → proj₁ (R x z)) →
    ∀ {x y} → proj₁ (R x y) ≃ _≡_ {A = A / R} [ x ] [ y ]
  related≃[equal] univ R-refl R-sym R-trans {x} {y} =
    _↠_.from (Eq.≃↠⇔ (proj₂ (R x y)) (/-is-set _ _))
      (record
        { to   = []-respects-relation
        ; from = λ [x]≡[y] →
                                $⟨ R-refl ⟩
            proj₁ (R′ x [ x ])  ↝⟨ ≡⇒→ (cong (proj₁ ∘ R′ x) [x]≡[y]) ⟩
            proj₁ (R′ x [ y ])  ↝⟨ id ⟩□
            proj₁ (R x y)       □
        })
    where
    lemma : ∀ {x y z} → proj₁ (R y z) → R x y ≡ R x z
    lemma {x} {y} {z} r =            $⟨ record
                                          { to   = flip R-trans r
                                          ; from = flip R-trans (R-sym r)
                                          } ⟩
      proj₁ (R x y) ⇔ proj₁ (R x z)  ↝⟨ ⇔↔≡ ext univ (proj₂ (R x y)) (proj₂ (R x z)) ⟩
      proj₁ (R x y) ≡ proj₁ (R x z)  ↝⟨ ignore-propositional-component (H-level-propositional ext 1) ⟩□
      R x y ≡ R x z                  □

    R′ : A → A / R → Proposition r
    R′ x = rec
      (λ y → R x y)
      lemma
      (∃-H-level-H-level-1+ ext univ 1)

-- Quotienting with equality (for a set) amounts to the same thing as
-- not quotienting at all.

/≡↔ :
  ∀ {a} {A : Set a} →
  (A-set : Is-set A) →
  (A / λ x y → (x ≡ y) , A-set x y) ↔ A
/≡↔ A-set = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec id id A-set
      ; from = [_]
      }
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = elim-Prop _ (λ _ → refl) (λ _ → /-is-set _ _)
  }

-- If the relation is a propositional equivalence relation of a
-- certain size, then there is a split surjection from the definition
-- of quotients given in Quotient to the one given here (assuming
-- extensionality and univalence).
--
-- I don't know if this result can be strengthened to an isomorphism:
-- I encountered size issues when trying to prove this.

/↠/ : ∀ {a} {A : Set a} {R : A → A → Set a} →
      Univalence a →
      Univalence (# 0) →
      (∀ {x} → R x x) →
      (∀ {x y} → R x y → R y x) →
      (∀ {x y z} → R x y → R y z → R x z) →
      (R-prop : ∀ x y → Is-proposition (R x y)) →
      A Quotient./ R ↠ A / (λ x y → R x y , R-prop x y)
/↠/ {a} {A} {R} univ univ₀ R-refl R-sym R-trans R-prop = record
  { logical-equivalence = record
    { to   = to
    ; from = from
    }
  ; right-inverse-of = to∘from
  }
  where
  R′ : A → A → Proposition a
  R′ x y = R x y , R-prop x y

  R-is-strong-equivalence : Quotient.Strong-equivalence R
  R-is-strong-equivalence =
    Quotient.propositional-equivalence⇒strong-equivalence
      ext univ R-refl R-sym R-trans R-prop

  []-respects-R : ∀ {x y} → R x y → Quotient.[ x ] ≡ Quotient.[ y ]
  []-respects-R =
    _↔_.to (Quotient.related↔[equal] ext R-is-strong-equivalence)

  to : A Quotient./ R → A / R′
  to = Quotient.rec
    ext
    R-refl
    _
    /-is-set
    [_]
    []-respects-relation

  from : A / R′ → A Quotient./ R
  from = rec
    Quotient.[_]
    []-respects-R
    (Quotient.quotient's-h-level-is-1-+-relation's-h-level
       ext univ univ₀ 1 R-prop)

  to∘from : ∀ x → to (from x) ≡ x
  to∘from = elim-Prop
    _
    (λ _ → refl)
    (λ _ → /-is-set _ _)

-- Two applications of _/_ are isomorphic if the underlying types are
-- isomorphic and the relations are pointwise logically equivalent.

infix 5 _/-cong_

_/-cong_ :
  ∀ {k a₁ a₂ r₁ r₂} {A₁ : Set a₁} {A₂ : Set a₂}
    {R₁ : A₁ → A₁ → Proposition r₁}
    {R₂ : A₂ → A₂ → Proposition r₂} →
  (A₁↔A₂ : A₁ ↔[ k ] A₂) →
  (∀ x y →
     proj₁ (R₁ x y) ⇔
     proj₁ (R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y))) →
  A₁ / R₁ ↔[ k ] A₂ / R₂
_/-cong_ {k} {R₁ = R₁} {R₂} A₁↔A₂ R₁⇔R₂ = from-bijection (record
  { surjection = record
    { logical-equivalence = record
      { to   = rec
                 ([_] ∘ to)
                 ([]-respects-relation ∘ _⇔_.to (R₁⇔R₂′ _ _))
                 /-is-set
      ; from = rec
                 ([_] ∘ from)
                 (λ {x y} →
                    proj₁ (R₂ x y)                          ↝⟨ ≡⇒↝ _ (sym $ cong₂ (λ x y → proj₁ (R₂ x y))
                                                                                  (right-inverse-of x)
                                                                                  (right-inverse-of y)) ⟩
                    proj₁ (R₂ (to (from x)) (to (from y)))  ↝⟨ _⇔_.from (R₁⇔R₂′ _ _) ⟩
                    proj₁ (R₁ (from x) (from y))            ↝⟨ []-respects-relation ⟩□
                    [ from x ] ≡ [ from y ]                 □)
                 /-is-set
      }
    ; right-inverse-of = elim-Prop
        _
        (λ x →
          [ to (from x) ]  ≡⟨ cong [_] $ right-inverse-of x ⟩∎
          [ x ]            ∎)
        (λ _ → /-is-set _ _)
    }
  ; left-inverse-of = elim-Prop
      _
      (λ x →
        [ from (to x) ]  ≡⟨ cong [_] $ left-inverse-of x ⟩∎
        [ x ]            ∎)
      (λ _ → /-is-set _ _)
  })
  where
  open _↔_ (from-isomorphism A₁↔A₂)

  R₁⇔R₂′ = λ x y →
    proj₁ (R₁ x y)                                                ↝⟨ R₁⇔R₂ x y ⟩
    proj₁ (R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y))  ↝⟨ ≡⇒↝ _ $ cong₂ (λ f g → proj₁ (R₂ (f x) (g y)))
                                                                                   (to-implication∘from-isomorphism k bijection)
                                                                                   (to-implication∘from-isomorphism k bijection) ⟩□
    proj₁ (R₂ (to x) (to y))                                      □
