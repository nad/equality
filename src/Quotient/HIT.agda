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

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (_∘_; id)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional as Trunc hiding (rec; elim)
open import Preimage equality-with-J using (_⁻¹_)
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
-- Equivalence relations

-- The definition of an equivalence relation.

Is-equivalence-relation :
  ∀ {a r} {A : Set a} (R : A → A → Proposition r) → Set (a ⊔ r)
Is-equivalence-relation R =
  Quotient.Is-equivalence-relation (λ x y → proj₁ (R x y))

open Quotient public using (module Is-equivalence-relation)

-- A trivial, propositional binary relation.

Trivial : ∀ {a r} {A : Set a} → A → A → Proposition r
Trivial _ _ = ↑ _ ⊤ , ↑-closure 1 (mono₁ 0 ⊤-contractible)

-- This relation is an equivalence relation.

Trivial-is-equivalence-relation :
  ∀ {a r} {A : Set a} →
  Is-equivalence-relation (Trivial {r = r} {A = A})
Trivial-is-equivalence-relation = _

------------------------------------------------------------------------
-- Pointwise liftings of binary relations

-- The superscript P used in the names of the definitions in this
-- section stands for "pointwise".

-- Lifts binary, propositional relations from B to A → B.

infix 0 _→ᴾ_

_→ᴾ_ :
  ∀ {a b r} (A : Set a) {B : Set b} →
  (B → B → Proposition r) →
  ((A → B) → (A → B) → Proposition (a ⊔ r))
(_ →ᴾ R) f g =
    (∀ x → proj₁ (R (f x) (g x)))
  , Π-closure ext 1 λ _ →
    proj₂ (R _ _)

-- _→ᴾ_ preserves equivalence relations.

→ᴾ-preserves-Is-equivalence-relation :
  ∀ {a b r} {A : Set a} {B : Set b} {R : B → B → Proposition r} →
  Is-equivalence-relation R →
  Is-equivalence-relation (A →ᴾ R)
→ᴾ-preserves-Is-equivalence-relation R-equiv = record
  { reflexive  = λ _ → reflexive
  ; symmetric  = λ f∼g x → symmetric (f∼g x)
  ; transitive = λ f∼g g∼h x → transitive (f∼g x) (g∼h x)
  }
  where
  open Is-equivalence-relation R-equiv

-- Lifts binary, propositional relations from A and B to A ⊎ B.

infixr 1 _⊎ᴾ_

_⊎ᴾ_ :
  ∀ {a b r} {A : Set a} {B : Set b} →
  (A → A → Proposition r) →
  (B → B → Proposition r) →
  (A ⊎ B → A ⊎ B → Proposition r)
(P ⊎ᴾ Q) (inj₁ x) (inj₁ y) = P x y
(P ⊎ᴾ Q) (inj₂ x) (inj₂ y) = Q x y
(P ⊎ᴾ Q) _        _        = ⊥ , ⊥-propositional

-- _⊎ᴾ_ preserves Is-equivalence-relation.

⊎ᴾ-preserves-Is-equivalence-relation :
  ∀ {a b r} {A : Set a} {B : Set b}
    {P : A → A → Proposition r} {Q : B → B → Proposition r} →
  Is-equivalence-relation P →
  Is-equivalence-relation Q →
  Is-equivalence-relation (P ⊎ᴾ Q)
⊎ᴾ-preserves-Is-equivalence-relation P-equiv Q-equiv = record
  { reflexive  = λ { {x = inj₁ _} → reflexive P-equiv
                   ; {x = inj₂ _} → reflexive Q-equiv
                   }
    ; symmetric  = λ { {x = inj₁ _} {y = inj₁ _} → symmetric P-equiv
                     ; {x = inj₂ _} {y = inj₂ _} → symmetric Q-equiv
                     ; {x = inj₁ _} {y = inj₂ _} ()
                     ; {x = inj₂ _} {y = inj₁ _} ()
                     }
  ; transitive = λ
     { {x = inj₁ _} {y = inj₁ _} {z = inj₁ _} → transitive P-equiv
     ; {x = inj₂ _} {y = inj₂ _} {z = inj₂ _} → transitive Q-equiv

     ; {x = inj₁ _} {y = inj₂ _} ()
     ; {x = inj₂ _} {y = inj₁ _} ()
     ; {y = inj₁ _} {z = inj₂ _} _ ()
     ; {y = inj₂ _} {z = inj₁ _} _ ()
     }
  }
  where
  open Is-equivalence-relation

-- Lifts a binary, propositional relation from A to Maybe A.

Maybeᴾ :
  ∀ {a r} {A : Set a} →
  (A → A → Proposition r) →
  (Maybe A → Maybe A → Proposition r)
Maybeᴾ R = Trivial ⊎ᴾ R

-- Maybeᴾ preserves Is-equivalence-relation.

Maybeᴾ-preserves-Is-equivalence-relation :
  ∀ {a r} {A : Set a} {R : A → A → Proposition r} →
  Is-equivalence-relation R →
  Is-equivalence-relation (Maybeᴾ R)
Maybeᴾ-preserves-Is-equivalence-relation =
  ⊎ᴾ-preserves-Is-equivalence-relation Trivial-is-equivalence-relation

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
    Is-equivalence-relation R →
    ∀ {x y} → proj₁ (R x y) ≃ _≡_ {A = A / R} [ x ] [ y ]
  related≃[equal] univ R-equiv {x} {y} =
    _↠_.from (Eq.≃↠⇔ (proj₂ (R x y)) (/-is-set _ _))
      (record
        { to   = []-respects-relation
        ; from = λ [x]≡[y] →
                                $⟨ reflexive ⟩
            proj₁ (R′ x [ x ])  ↝⟨ ≡⇒→ (cong (proj₁ ∘ R′ x) [x]≡[y]) ⟩
            proj₁ (R′ x [ y ])  ↝⟨ id ⟩□
            proj₁ (R x y)       □
        })
    where
    open Is-equivalence-relation R-equiv

    lemma : ∀ {x y z} → proj₁ (R y z) → R x y ≡ R x z
    lemma {x} {y} {z} r =            $⟨ record
                                          { to   = flip transitive r
                                          ; from = flip transitive (symmetric r)
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

-- Quotienting with a trivial relation amounts to the same thing as
-- using the propositional truncation.

/trivial↔∥∥ :
  ∀ {a r} {A : Set a} {R : A → A → Proposition r} →
  (∀ x y → proj₁ (R x y)) →
  A / R ↔ ∥ A ∥
/trivial↔∥∥ {A = A} {R} trivial = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec-Prop ∣_∣ truncation-is-proposition
      ; from = Trunc.rec /-prop [_]
      }
    ; right-inverse-of = Trunc.elim
        _
        (λ _ → mono₁ 0 (truncation-is-proposition _ _))
        (λ _ → refl)
    }
  ; left-inverse-of = elim-Prop _ (λ _ → refl) (λ _ → /-is-set _ _)
  }
  where
  /-prop : Is-proposition (A / R)
  /-prop = _⇔_.from propositional⇔irrelevant $
    elim-Prop _
      (λ x → elim-Prop _
         (λ y → []-respects-relation (trivial x y))
         (λ _ → /-is-set _ _))
      (λ _ → Π-closure ext 1 λ _ →
             /-is-set _ _)

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
      Quotient.Is-equivalence-relation R →
      (R-prop : ∀ x y → Is-proposition (R x y)) →
      A Quotient./ R ↠ A / (λ x y → R x y , R-prop x y)
/↠/ {a} {A} {R} univ univ₀ R-equiv R-prop = record
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
      ext univ R-equiv R-prop

  []-respects-R : ∀ {x y} → R x y → Quotient.[ x ] ≡ Quotient.[ y ]
  []-respects-R =
    _↔_.to (Quotient.related↔[equal] ext R-is-strong-equivalence)

  to : A Quotient./ R → A / R′
  to = Quotient.rec
    ext
    (Is-equivalence-relation.reflexive R-equiv)
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

------------------------------------------------------------------------
-- Various type formers commute with quotients

-- _⊎_ commutes with quotients.

⊎/-comm :
  ∀ {a b r} {A : Set a} {B : Set b}
    {P : A → A → Proposition r} {Q : B → B → Proposition r} →
  (A ⊎ B) / (P ⊎ᴾ Q) ↔ A / P ⊎ B / Q
⊎/-comm = record
  { surjection = record
    { logical-equivalence = record
      { to = rec
          (⊎-map [_] [_])
          (λ { {x = inj₁ _} {y = inj₁ _} → cong inj₁ ∘
                                           []-respects-relation
             ; {x = inj₂ _} {y = inj₂ _} → cong inj₂ ∘
                                           []-respects-relation
             ; {x = inj₁ _} {y = inj₂ _} ()
             ; {x = inj₂ _} {y = inj₁ _} ()
             })
          (⊎-closure 0 /-is-set /-is-set)
      ; from = Prelude.[ rec ([_] ∘ inj₁) []-respects-relation /-is-set
                       , rec ([_] ∘ inj₂) []-respects-relation /-is-set
                       ]
      }
    ; right-inverse-of =
        Prelude.[ elim-Prop
                    _
                    (λ _ → refl)
                    (λ _ → ⊎-closure 0 /-is-set /-is-set _ _)
                , elim-Prop
                    _
                    (λ _ → refl)
                    (λ _ → ⊎-closure 0 /-is-set /-is-set _ _)
                ]
    }
  ; left-inverse-of = elim-Prop
      _
      Prelude.[ (λ _ → refl) , (λ _ → refl) ]
      (λ _ → /-is-set _ _)
  }

-- Maybe commutes with quotients.
--
-- Chapman, Uustalu and Veltri mention a similar result in
-- "Quotienting the Delay Monad by Weak Bisimilarity".

Maybe/-comm :
  ∀ {a r} {A : Set a} {R : A → A → Proposition r} →
  Maybe A / Maybeᴾ R ↔ Maybe (A / R)
Maybe/-comm {A = A} {R} =
  Maybe A / Maybeᴾ R   ↝⟨ ⊎/-comm ⟩
  ⊤ / Trivial ⊎ A / R  ↝⟨ /trivial↔∥∥ _ ⊎-cong F.id ⟩
  ∥ ⊤ ∥ ⊎ A / R        ↝⟨ ∥∥↔ (mono₁ 0 ⊤-contractible) ⊎-cong F.id ⟩□
  Maybe (A / R)        □

-- The sigma type former commutes (kind of) with quotients, assuming
-- that the second projections come from propositional types.

Σ/-comm :
  ∀ {a r p}
    {A : Set a} {R : A → A → Proposition r} {P : A / R → Set p} →
  (∀ x → Is-proposition (P x)) →
  Σ (A / R) P ↔ Σ A (P ∘ [_]) / (R on proj₁)
Σ/-comm {A = A} {R} {P} P-prop = record
  { surjection = record
    { logical-equivalence = record
      { to = uncurry $ elim
          (λ x → P x → Σ A (P ∘ [_]) / (R on proj₁))
          (curry [_])
          (λ {x y} r → ext λ P[y] →
             subst (λ x → P x → Σ A (P ∘ [_]) / (R on proj₁))
                   ([]-respects-relation r)
                   (curry [_] x) P[y]                               ≡⟨ cong (_$ P[y]) $ subst-→-domain _ ([]-respects-relation r) ⟩

             [ (x , subst P (sym $ []-respects-relation r) P[y]) ]  ≡⟨ []-respects-relation r ⟩∎

             [ (y , P[y]) ]                                         ∎)
          (λ _ → Π-closure ext 2 λ _ →
                 /-is-set)
      ; from = rec
          (Σ-map [_] id)
          (λ { {x = (x₁ , x₂)} {y = (y₁ , y₂)} →
               proj₁ (R x₁ y₁)                ↝⟨ []-respects-relation ⟩
               [ x₁ ] ≡ [ y₁ ]                ↔⟨ ignore-propositional-component (P-prop _) ⟩
               ([ x₁ ] , x₂) ≡ ([ y₁ ] , y₂)  □
             })
          (Σ-closure 2 /-is-set (mono₁ 1 ∘ P-prop))
      }
    ; right-inverse-of = elim-Prop
        _
        (λ _ → refl)
        (λ _ → /-is-set _ _)
    }
  ; left-inverse-of = uncurry $ elim-Prop
      _
      (λ _ _ → refl)
      (λ _ → Π-closure ext 1 λ _ →
             (Σ-closure 2 /-is-set (mono₁ 1 ∘ P-prop)) _ _)
  }

-- The type former λ X → ℕ → X commutes with quotients, assuming that
-- the quotient relation is an equivalence relation, and also assuming
-- univalence and countable choice.
--
-- This result is very similar to Proposition 5 in "Quotienting the
-- Delay Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

-- The forward component of the isomorphism. This component can be
-- defined without any extra assumptions.

ℕ→/-comm-to :
  ∀ {a r} {A : Set a} {R : A → A → Proposition r} →
  (ℕ → A) / (ℕ →ᴾ R) → (ℕ → A / R)
ℕ→/-comm-to = rec
  (λ f n → [ f n ])
  (λ r → ext ([]-respects-relation ∘ r))
  (Π-closure ext 2 λ _ →
   /-is-set)

-- The isomorphism.

ℕ→/-comm :
  ∀ {a r} {A : Set a} {R : A → A → Proposition r} →
  Univalence r →
  Axiom-of-countable-choice (a ⊔ r) →
  Is-equivalence-relation R →
  (ℕ → A) / (ℕ →ᴾ R) ↔ (ℕ → A / R)
ℕ→/-comm {A = A} {R} univ cc R-equiv = record
  { surjection = record
    { logical-equivalence = record
      { to   = ℕ→/-comm-to
      ; from = from unit
      }
    ; right-inverse-of = to∘from unit
    }
  ; left-inverse-of = from∘to unit
  }
  where
  [_]→ : (ℕ → A) → (ℕ → A / R)
  [ f ]→ n = [ f n ]

  -- A module that is introduced to ensure that []→-surjective is not
  -- in the same abstract block as the abstract definitions below.

  module Dummy where

    abstract

      []→-surjective : Surjective [_]→
      []→-surjective f =                    $⟨ []-surjective ⟩
        Surjective [_]                      ↝⟨ (λ surj → surj ∘ f) ⟩
        (∀ n → ∥ (∃ λ x → [ x ] ≡ f n) ∥)   ↔⟨ countable-choice-bijection cc ⟩
        ∥ (∀ n → ∃ λ x → [ x ] ≡ f n) ∥     ↔⟨ ∥∥-cong ΠΣ-comm ⟩
        ∥ (∃ λ g → ∀ n → [ g n ] ≡ f n) ∥   ↔⟨ Bijection.id ⟩
        ∥ (∃ λ g → ∀ n → [ g ]→ n ≡ f n) ∥  ↔⟨ ∥∥-cong (∃-cong λ _ → Eq.extensionality-isomorphism ext) ⟩□
        ∥ (∃ λ g → [ g ]→ ≡ f) ∥            □

  open Dummy

  from₁ : ∀ f → [_]→ ⁻¹ f → ℕ→/-comm-to ⁻¹ f
  from₁ f (g , [g]→≡f) =
      [ g ]
    , (ℕ→/-comm-to [ g ]  ≡⟨⟩
       [ g ]→             ≡⟨ [g]→≡f ⟩∎
       f                  ∎)

  from₁-constant : ∀ f → Constant (from₁ f)
  from₁-constant f (g₁ , [g₁]→≡f) (g₂ , [g₂]→≡f) =
                                             $⟨ (λ n → cong (_$ n) (
        [ g₁ ]→                                    ≡⟨ [g₁]→≡f ⟩
        f                                          ≡⟨ sym [g₂]→≡f ⟩∎
        [ g₂ ]→                                    ∎)) ⟩

    (∀ n → [ g₁ ]→ n ≡ [ g₂ ]→ n)            ↔⟨ Bijection.id ⟩

    (∀ n → [ g₁ n ] ≡ [ g₂ n ])              ↔⟨ Eq.∀-preserves ext (λ _ → inverse $ related≃[equal] {R = R} univ R-equiv) ⟩

    (∀ n → proj₁ (R (g₁ n) (g₂ n)))          ↔⟨ Bijection.id ⟩

    proj₁ ((ℕ →ᴾ R) g₁ g₂)                   ↝⟨ []-respects-relation ⟩

    [ g₁ ] ≡ [ g₂ ]                          ↔⟨ ignore-propositional-component
                                                  ((Π-closure ext 2 λ _ →
                                                    /-is-set) _ _) ⟩□
    ([ g₁ ] , [g₁]→≡f) ≡ ([ g₂ ] , [g₂]→≡f)  □

  from₂ : Unit → ∀ f → ∥ [_]→ ⁻¹ f ∥ → ℕ→/-comm-to ⁻¹ f
  from₂ unit f =
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited
              (Σ-closure 2 /-is-set λ _ →
               mono₁ 1 (Π-closure ext 2 (λ _ → /-is-set) _ _)))
           (from₁ f , from₁-constant f)

  unblock-from₂ : ∀ x f p → from₂ x f ∣ p ∣ ≡ from₁ f p
  unblock-from₂ unit _ _ = refl

  abstract

    from₃ : Unit → ∀ f → ℕ→/-comm-to ⁻¹ f
    from₃ x f = from₂ x f ([]→-surjective f)

    from : Unit → (ℕ → A / R) → (ℕ → A) / (ℕ →ᴾ R)
    from x f = proj₁ (from₃ x f)

    to∘from : ∀ x f → ℕ→/-comm-to (from x f) ≡ f
    to∘from x f = proj₂ (from₃ x f)

    from∘to : ∀ x f → from x (ℕ→/-comm-to f) ≡ f
    from∘to x = elim-Prop
      (λ f → from x (ℕ→/-comm-to f) ≡ f)
      (λ f →
         from x (ℕ→/-comm-to [ f ])                      ≡⟨⟩

         proj₁ (from₂ x [ f ]→ ([]→-surjective [ f ]→))  ≡⟨ cong (proj₁ ∘ from₂ x [ f ]→) $
                                                              _⇔_.to propositional⇔irrelevant truncation-is-proposition _ _ ⟩
         proj₁ (from₂ x [ f ]→ ∣ f , refl ∣)             ≡⟨ cong proj₁ $ unblock-from₂ x _ (f , refl) ⟩

         proj₁ (from₁ [ f ]→ (f , refl))                 ≡⟨⟩

         [ f ]                                           ∎)
      (λ _ → /-is-set _ _)
