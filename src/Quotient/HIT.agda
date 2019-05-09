------------------------------------------------------------------------
-- Quotients (set-quotients), defined using a higher inductive type
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly following the HoTT book.
--
-- Unlike the HoTT book, but following the cubical library (in which
-- set quotients were implemented by Zesen Qian and Anders Mörtberg),
-- the quotienting relations are not (always) required to be
-- propositional.

-- The module is parametrised by a notion of equality. The higher
-- constructors of the HIT defining quotients use path equality, but
-- the supplied notion of equality is used for many other things.

open import Equality

module Quotient.HIT
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

private
  open module D = Derived-definitions-and-properties eq hiding (elim)

import Equality.Path as P
import H-level
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Equality.Decidable-UIP eq
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (_∘_; id)
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  hiding (rec; elim)
open import Preimage eq using (_⁻¹_)
import Quotient eq as Quotient
open import Surjection eq using (_↠_)
open import Univalence-axiom eq

private
  module PH = H-level P.equality-with-J
  open module H = H-level eq

private
  variable
    a a₁ a₂ p r r₁ r₂ : Level
    k                 : Isomorphism-kind
    A B               : Set a
    P Q R             : A → A → Set r
    x y               : A

------------------------------------------------------------------------
-- Quotients

-- The quotient type constructor.

infix 5 _/_

data _/_ (A : Set a) (R : A → A → Set r) : Set (a ⊔ r) where
  [_]                   : A → A / R
  []-respects-relation′ : R x y → [ x ] P.≡ [ y ]
  /-is-set′             : P.Is-set (A / R)

-- [_] respects the quotient relation.

[]-respects-relation : R x y → _≡_ {A = A / R} [ x ] [ y ]
[]-respects-relation = _↔_.from ≡↔≡ ∘ []-respects-relation′

-- Quotients are sets.

/-is-set : Is-set (A / R)
/-is-set = _↔_.from (H-level↔H-level 2) /-is-set′

-- An eliminator.

module _
  (P : A / R → Set p)
  (p-[] : ∀ x → P [ x ])
  (p-[]-respects-relation :
     ∀ {x y} (r : R x y) →
     subst P ([]-respects-relation r) (p-[] x) ≡ p-[] y)
  (P-set : ∀ x → Is-set (P x))
  where

  elim : ∀ x → P x
  elim [ x ] = p-[] x

  elim ([]-respects-relation′ r i) =
    subst≡→[]≡ (p-[]-respects-relation r) i

  elim (/-is-set′ {x = x} {y = y} p q i j) = lemma i j
    where
    lemma :
      P.[ (λ i → P.[ (λ j → P (/-is-set′ p q i j)) ] elim x ≡ elim y) ]
        (λ i → elim (p i)) ≡ (λ i → elim (q i))
    lemma = P.heterogeneous-UIP (_↔_.to (H-level↔H-level 2) ∘ P-set) _

  -- "Computation" rule for []-respects-relation.
  --
  -- (This result is perhaps not very useful, because P is assumed to
  -- be a family of sets. It is included here to illustrate how
  -- dependent-cong-subst≡→[]≡ can be used.)

  elim-[]-respects-relation :
    (r : R x y) →
    dependent-cong elim ([]-respects-relation r) ≡
    p-[]-respects-relation r
  elim-[]-respects-relation _ = dependent-cong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

rec :
  {P : Set p}
  (p-[] : A → P) →
  (∀ {x y} → R x y → p-[] x ≡ p-[] y) →
  Is-set P →
  A / R → P
rec {P = P} p-[] p-[]-respects-relation P-set = elim
  (λ _ → P)
  p-[]
  (λ {x y} r →
     subst (λ _ → P) ([]-respects-relation r) (p-[] x)  ≡⟨ subst-const _ ⟩
     p-[] x                                             ≡⟨ p-[]-respects-relation r ⟩∎
     p-[] y                                             ∎)
  (λ _ → P-set)

-- A variant of elim that can be used if the motive composed with [_]
-- is a family of propositions.
--
-- I took the idea for this eliminator from Nicolai Kraus.

elim-Prop :
  (P : A / R → Set p) →
  (p-[] : ∀ x → P [ x ]) →
  (∀ x → Is-proposition (P [ x ])) →
  ∀ x → P x
elim-Prop P p-[] P-prop = elim
  P p-[]
  (λ _ → P-prop _ _ _)
  (elim
     _
     (mono₁ 1 ∘ P-prop)
     (λ _ → H-level-propositional ext 2 _ _)
     (λ _ → mono₁ 1 (H-level-propositional ext 2)))

-- A variant of rec that can be used if the motive is a proposition.

rec-Prop :
  {P : Set p} →
  (A → P) →
  Is-proposition P →
  A / R → P
rec-Prop p-[] P-prop = elim-Prop (const _) p-[] (const P-prop)

------------------------------------------------------------------------
-- Equivalence relations

-- The definition of an equivalence relation.

Is-equivalence-relation :
  {A : Set a} (R : A → A → Set r) → Set (a ⊔ r)
Is-equivalence-relation = Quotient.Is-equivalence-relation

open Quotient public using (module Is-equivalence-relation)

-- A trivial binary relation.

Trivial : A → A → Set r
Trivial _ _ = ↑ _ ⊤

-- This relation is an equivalence relation.

Trivial-is-equivalence-relation :
  Is-equivalence-relation (Trivial {A = A} {r = r})
Trivial-is-equivalence-relation = _

-- It is also propositional.

Trivial-is-propositional :
  {x y : A} → Is-proposition (Trivial {r = r} x y)
Trivial-is-propositional = ↑-closure 1 (mono₁ 0 ⊤-contractible)

------------------------------------------------------------------------
-- Pointwise liftings of binary relations

-- The superscript P used in the names of the definitions in this
-- section stands for "pointwise".

-- Lifts binary relations from B to A → B.

infix 0 _→ᴾ_

_→ᴾ_ :
  (A : Set a) →
  (B → B → Set r) →
  ((A → B) → (A → B) → Set (a ⊔ r))
(_ →ᴾ R) f g = ∀ x → R (f x) (g x)

-- _→ᴾ_ preserves equivalence relations.

→ᴾ-preserves-Is-equivalence-relation :
  Is-equivalence-relation R →
  Is-equivalence-relation (A →ᴾ R)
→ᴾ-preserves-Is-equivalence-relation R-equiv = record
  { reflexive  = λ _ → reflexive
  ; symmetric  = λ f∼g x → symmetric (f∼g x)
  ; transitive = λ f∼g g∼h x → transitive (f∼g x) (g∼h x)
  }
  where
  open Is-equivalence-relation R-equiv

-- _→ᴾ_ preserves Is-proposition.

→ᴾ-preserves-Is-proposition :
  (∀ {x y} → Is-proposition (R x y)) →
  ∀ {f g} → Is-proposition ((A →ᴾ R) f g)
→ᴾ-preserves-Is-proposition R-prop =
  Π-closure ext 1 λ _ →
  R-prop

-- Lifts binary relations from A and B to A ⊎ B.

infixr 1 _⊎ᴾ_

_⊎ᴾ_ :
  (A → A → Set r) →
  (B → B → Set r) →
  (A ⊎ B → A ⊎ B → Set r)
(P ⊎ᴾ Q) (inj₁ x) (inj₁ y) = P x y
(P ⊎ᴾ Q) (inj₂ x) (inj₂ y) = Q x y
(P ⊎ᴾ Q) _        _        = ⊥

-- _⊎ᴾ_ preserves Is-equivalence-relation.

⊎ᴾ-preserves-Is-equivalence-relation :
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

-- _⊎ᴾ_ preserves Is-proposition.

⊎ᴾ-preserves-Is-proposition :
  (∀ {x y} → Is-proposition (P x y)) →
  (∀ {x y} → Is-proposition (Q x y)) →
  ∀ {x y} → Is-proposition ((P ⊎ᴾ Q) x y)
⊎ᴾ-preserves-Is-proposition = λ where
  P-prop Q-prop {inj₁ _} {inj₁ _} → P-prop
  P-prop Q-prop {inj₁ _} {inj₂ _} → ⊥-propositional
  P-prop Q-prop {inj₂ _} {inj₁ _} → ⊥-propositional
  P-prop Q-prop {inj₂ _} {inj₂ _} → Q-prop

-- Lifts a binary relation from A to Maybe A.

Maybeᴾ :
  (A → A → Set r) →
  (Maybe A → Maybe A → Set r)
Maybeᴾ R = Trivial ⊎ᴾ R

-- Maybeᴾ preserves Is-equivalence-relation.

Maybeᴾ-preserves-Is-equivalence-relation :
  Is-equivalence-relation R →
  Is-equivalence-relation (Maybeᴾ R)
Maybeᴾ-preserves-Is-equivalence-relation =
  ⊎ᴾ-preserves-Is-equivalence-relation Trivial-is-equivalence-relation

-- Maybeᴾ preserves Is-proposition.

Maybeᴾ-preserves-Is-proposition :
  (∀ {x y} → Is-proposition (R x y)) →
  ∀ {x y} → Is-proposition (Maybeᴾ R x y)
Maybeᴾ-preserves-Is-proposition =
  ⊎ᴾ-preserves-Is-proposition λ {x} →
  Trivial-is-propositional {x = x}

------------------------------------------------------------------------
-- Some properties

-- [_] is surjective.

[]-surjective : Surjective ([_] {R = R})
[]-surjective = elim-Prop
  _
  (λ x → ∣ x , refl _ ∣)
  (λ _ → truncation-is-proposition)

-- If the relation is a propositional equivalence relation, then it is
-- equivalent to equality under [_].
--
-- The basic structure of this proof is that of Proposition 2 in
-- "Quotienting the Delay Monad by Weak Bisimilarity" by Chapman,
-- Uustalu and Veltri.

related≃[equal] :
  {R : A → A → Set r} →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  ∀ {x y} → R x y ≃ _≡_ {A = A / R} [ x ] [ y ]
related≃[equal] {A = A} {r = r} {R = R}
                R-equiv R-prop {x} {y} =
  _↠_.from (Eq.≃↠⇔ R-prop /-is-set)
    (record
      { to   = []-respects-relation
      ; from = λ [x]≡[y] →
                              $⟨ reflexive ⟩
          proj₁ (R′ x [ x ])  ↝⟨ ≡⇒→ (cong (proj₁ ∘ R′ x) [x]≡[y]) ⟩
          proj₁ (R′ x [ y ])  ↝⟨ id ⟩□
          R x y               □
      })
  where
  open Is-equivalence-relation R-equiv

  lemma : ∀ {x y z} → R y z → (R x y , R-prop) ≡ (R x z , R-prop)
  lemma {x} {y} {z} r =                  $⟨ record
                                              { to   = flip transitive r
                                              ; from = flip transitive (symmetric r)
                                              } ⟩
    R x y ⇔ R x z                        ↝⟨ ⇔↔≡′ ext univ ⟩
    (R x y , R-prop) ≡ (R x z , R-prop)  □

  R′ : A → A / R → Proposition r
  R′ x = rec
    (λ y → R x y , R-prop)
    lemma
    (Is-set-∃-Is-proposition ext prop-ext)

-- Quotienting with equality (for a set) amounts to the same thing as
-- not quotienting at all.

/≡↔ : Is-set A → A / _≡_ ↔ A
/≡↔ A-set = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec id id A-set
      ; from = [_]
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = elim-Prop _ (λ _ → refl _) (λ _ → /-is-set)
  }

-- Quotienting with a trivial relation amounts to the same thing as
-- using the propositional truncation.

/trivial↔∥∥ : (∀ x y → R x y) → A / R ↔ ∥ A ∥
/trivial↔∥∥ {A = A} {R = R} trivial = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec-Prop ∣_∣ truncation-is-proposition
      ; from = Trunc.rec /-prop [_]
      }
    ; right-inverse-of = Trunc.elim
        _
        (λ _ → mono₁ 0 (+⇒≡ truncation-is-proposition))
        (λ _ → refl _)
    }
  ; left-inverse-of = elim-Prop _ (λ _ → refl _) (λ _ → /-is-set)
  }
  where
  /-prop : Is-proposition (A / R)
  /-prop =
    elim-Prop _
      (λ x → elim-Prop _
         (λ y → []-respects-relation (trivial x y))
         (λ _ → /-is-set))
      (λ _ → Π-closure ext 1 λ _ →
             /-is-set)

-- If the relation is a propositional equivalence relation of a
-- certain size, then there is a split surjection from the definition
-- of quotients given in Quotient to the one given here.
--
-- I don't know if this result can be strengthened to an isomorphism:
-- I encountered size issues when trying to prove this.

/↠/ : {A : Set a} {R : A → A → Set a} →
      Quotient.Is-equivalence-relation R →
      (R-prop : ∀ {x y} → Is-proposition (R x y)) →
      A Quotient./ R ↠ A / R
/↠/ {a = a} {A = A} {R} R-equiv R-prop = record
  { logical-equivalence = record
    { to   = to
    ; from = from
    }
  ; right-inverse-of = to∘from
  }
  where
  R-is-strong-equivalence : Quotient.Strong-equivalence R
  R-is-strong-equivalence =
    Quotient.propositional-equivalence⇒strong-equivalence
      ext univ R-equiv (λ _ _ → R-prop)

  []-respects-R : ∀ {x y} → R x y → Quotient.[ x ] ≡ Quotient.[ y ]
  []-respects-R =
    _↔_.to (Quotient.related↔[equal] ext R-is-strong-equivalence)

  to : A Quotient./ R → A / R
  to = Quotient.rec
    ext
    (Is-equivalence-relation.reflexive R-equiv)
    _
    /-is-set
    [_]
    []-respects-relation

  from : A / R → A Quotient./ R
  from = rec
    Quotient.[_]
    []-respects-R
    (Quotient.quotient's-h-level-is-1-+-relation's-h-level
       ext univ univ 1 (λ _ _ → R-prop))

  to∘from : ∀ x → to (from x) ≡ x
  to∘from = elim-Prop
    _
    (λ _ → refl _)
    (λ _ → /-is-set)

-- Two applications of _/_ are isomorphic if the underlying types are
-- isomorphic and the relations are pointwise logically equivalent.

infix 5 _/-cong_

_/-cong_ :
  {A₁ : Set a₁} {A₂ : Set a₂}
  {R₁ : A₁ → A₁ → Set r₁}
  {R₂ : A₂ → A₂ → Set r₂} →
  (A₁↔A₂ : A₁ ↔[ k ] A₂) →
  (∀ x y →
     R₁ x y ⇔ R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y)) →
  A₁ / R₁ ↔[ k ] A₂ / R₂
_/-cong_ {k = k} {R₁ = R₁} {R₂} A₁↔A₂ R₁⇔R₂ = from-bijection (record
  { surjection = record
    { logical-equivalence = record
      { to   = rec
                 ([_] ∘ to)
                 ([]-respects-relation ∘ _⇔_.to (R₁⇔R₂′ _ _))
                 /-is-set
      ; from = rec
                 ([_] ∘ from)
                 (λ {x y} →
                    R₂ x y                          ↝⟨ ≡⇒↝ _ (sym $ cong₂ R₂ (right-inverse-of x) (right-inverse-of y)) ⟩
                    R₂ (to (from x)) (to (from y))  ↝⟨ _⇔_.from (R₁⇔R₂′ _ _) ⟩
                    R₁ (from x) (from y)            ↝⟨ []-respects-relation ⟩□
                    [ from x ] ≡ [ from y ]         □)
                 /-is-set
      }
    ; right-inverse-of = elim-Prop
        _
        (λ x →
          [ to (from x) ]  ≡⟨ cong [_] $ right-inverse-of x ⟩∎
          [ x ]            ∎)
        (λ _ → /-is-set)
    }
  ; left-inverse-of = elim-Prop
      _
      (λ x →
        [ from (to x) ]  ≡⟨ cong [_] $ left-inverse-of x ⟩∎
        [ x ]            ∎)
      (λ _ → /-is-set)
  })
  where
  open _↔_ (from-isomorphism A₁↔A₂)

  R₁⇔R₂′ : ∀ _ _ → _
  R₁⇔R₂′ x y =
    R₁ x y                                                ↝⟨ R₁⇔R₂ x y ⟩
    R₂ (to-implication A₁↔A₂ x) (to-implication A₁↔A₂ y)  ↝⟨ ≡⇒↝ _ $ cong₂ (λ f g → R₂ (f x) (g y))
                                                                           (to-implication∘from-isomorphism k bijection)
                                                                           (to-implication∘from-isomorphism k bijection) ⟩□
    R₂ (to x) (to y)                                      □

------------------------------------------------------------------------
-- Various type formers commute with quotients

-- _⊎_ commutes with quotients.

⊎/-comm : (A ⊎ B) / (P ⊎ᴾ Q) ↔ A / P ⊎ B / Q
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
                    (λ _ → refl _)
                    (λ _ → ⊎-closure 0 /-is-set /-is-set)
                , elim-Prop
                    _
                    (λ _ → refl _)
                    (λ _ → ⊎-closure 0 /-is-set /-is-set)
                ]
    }
  ; left-inverse-of = elim-Prop
      _
      Prelude.[ (λ _ → refl _) , (λ _ → refl _) ]
      (λ _ → /-is-set)
  }

-- Maybe commutes with quotients.
--
-- Chapman, Uustalu and Veltri mention a similar result in
-- "Quotienting the Delay Monad by Weak Bisimilarity".

Maybe/-comm : Maybe A / Maybeᴾ R ↔ Maybe (A / R)
Maybe/-comm {A = A} {R = R} =
  Maybe A / Maybeᴾ R   ↝⟨ ⊎/-comm ⟩
  ⊤ / Trivial ⊎ A / R  ↝⟨ /trivial↔∥∥ _ ⊎-cong F.id ⟩
  ∥ ⊤ ∥ ⊎ A / R        ↝⟨ ∥∥↔ (mono₁ 0 ⊤-contractible) ⊎-cong F.id ⟩□
  Maybe (A / R)        □

-- A simplification lemma for Maybe/-comm.

Maybe/-comm-[] : _↔_.to Maybe/-comm ∘ [_] ≡ ⊎-map id ([_] {R = R})
Maybe/-comm-[] =
  _↔_.to Maybe/-comm ∘ [_]                             ≡⟨⟩

  ⊎-map _ id ∘
  ⊎-map (rec-Prop ∣_∣ truncation-is-proposition) id ∘
  ⊎-map [_] [_]                                        ≡⟨ cong (_∘ ⊎-map [_] [_]) ⊎-map-∘ ⟩

  ⊎-map _ id ∘ ⊎-map [_] [_]                           ≡⟨ ⊎-map-∘ ⟩∎

  ⊎-map id [_]                                         ∎
  where
  ⊎-map-∘ : ∀ {a₁ b₁ c₁} {A₁ : Set a₁} {B₁ : Set b₁} {C₁ : Set c₁}
              {a₂ b₂ c₂} {A₂ : Set a₂} {B₂ : Set b₂} {C₂ : Set c₂}
              {f₁ : B₁ → C₁} {g₁ : A₁ → B₁}
              {f₂ : B₂ → C₂} {g₂ : A₂ → B₂} →
            ⊎-map f₁ f₂ ∘ ⊎-map g₁ g₂ ≡ ⊎-map (f₁ ∘ g₁) (f₂ ∘ g₂)
  ⊎-map-∘ = ⟨ext⟩ Prelude.[ (λ _ → refl _) , (λ _ → refl _) ]

-- The sigma type former commutes (kind of) with quotients, assuming
-- that the second projections come from propositional types.

Σ/-comm :
  {P : A / R → Set p} →
  (∀ {x} → Is-proposition (P x)) →
  Σ (A / R) P ↔ Σ A (P ∘ [_]) / (R on proj₁)
Σ/-comm {A = A} {R = R} {P = P} P-prop = record
  { surjection = record
    { logical-equivalence = record
      { to = uncurry $ elim
          (λ x → P x → Σ A (P ∘ [_]) / (R on proj₁))
          (curry [_])
          (λ {x y} r → ⟨ext⟩ λ P[y] →
             subst (λ x → P x → Σ A (P ∘ [_]) / (R on proj₁))
                   ([]-respects-relation r)
                   (curry [_] x) P[y]                               ≡⟨ cong (_$ P[y]) $
                                                                       subst-→-domain P {f = curry [_] _} ([]-respects-relation r) ⟩

             [ (x , subst P (sym $ []-respects-relation r) P[y]) ]  ≡⟨ []-respects-relation r ⟩∎

             [ (y , P[y]) ]                                         ∎)
          (λ _ → Π-closure ext 2 λ _ →
                 /-is-set)
      ; from = rec
          (Σ-map [_] id)
          (λ { {x = (x₁ , x₂)} {y = (y₁ , y₂)} →
               R x₁ y₁                        ↝⟨ []-respects-relation ⟩
               [ x₁ ] ≡ [ y₁ ]                ↔⟨ ignore-propositional-component P-prop ⟩
               ([ x₁ ] , x₂) ≡ ([ y₁ ] , y₂)  □
             })
          (Σ-closure 2 /-is-set (λ _ → mono₁ 1 P-prop))
      }
    ; right-inverse-of = elim-Prop
        _
        (λ _ → refl _)
        (λ _ → /-is-set)
    }
  ; left-inverse-of = uncurry $ elim-Prop
      _
      (λ _ _ → refl _)
      (λ _ → Π-closure ext 1 λ _ →
             Σ-closure 2 /-is-set (λ _ → mono₁ 1 P-prop))
  }

-- The type former λ X → ℕ → X commutes with quotients, assuming that
-- the quotient relation is a propositional equivalence relation, and
-- also assuming countable choice.
--
-- This result is very similar to Proposition 5 in "Quotienting the
-- Delay Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

-- The forward component of the isomorphism. This component can be
-- defined without any extra assumptions.

ℕ→/-comm-to : (ℕ → A) / (ℕ →ᴾ R) → (ℕ → A / R)
ℕ→/-comm-to = rec
  (λ f n → [ f n ])
  (λ r → ⟨ext⟩ ([]-respects-relation ∘ r))
  (Π-closure ext 2 λ _ →
   /-is-set)

-- The isomorphism.

ℕ→/-comm :
  {A : Set a} {R : A → A → Set r} →
  Axiom-of-countable-choice (a ⊔ r) →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  (ℕ → A) / (ℕ →ᴾ R) ↔ (ℕ → A / R)
ℕ→/-comm {A = A} {R} cc R-equiv R-prop = record
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
        Surjective [_]                      ↝⟨ (λ surj → surj ∘ f) ⦂ (_ → _) ⟩
        (∀ n → ∥ (∃ λ x → [ x ] ≡ f n) ∥)   ↔⟨ countable-choice-bijection cc ⟩
        ∥ (∀ n → ∃ λ x → [ x ] ≡ f n) ∥     ↔⟨ ∥∥-cong ΠΣ-comm ⟩
        ∥ (∃ λ g → ∀ n → [ g n ] ≡ f n) ∥   ↔⟨⟩
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

    (∀ n → [ g₁ ]→ n ≡ [ g₂ ]→ n)            ↔⟨⟩

    (∀ n → [ g₁ n ] ≡ [ g₂ n ])              ↔⟨ ∀-cong ext (λ _ → inverse $ related≃[equal] R-equiv R-prop) ⟩

    (∀ n → R (g₁ n) (g₂ n))                  ↔⟨⟩

    (ℕ →ᴾ R) g₁ g₂                           ↝⟨ []-respects-relation ⟩

    [ g₁ ] ≡ [ g₂ ]                          ↔⟨ ignore-propositional-component
                                                  (Π-closure ext 2 λ _ →
                                                   /-is-set) ⟩□
    ([ g₁ ] , [g₁]→≡f) ≡ ([ g₂ ] , [g₂]→≡f)  □

  from₂ : Unit → ∀ f → ∥ [_]→ ⁻¹ f ∥ → ℕ→/-comm-to ⁻¹ f
  from₂ unit f =
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited
              (Σ-closure 2 /-is-set λ _ →
               mono₁ 1 (Π-closure ext 2 (λ _ → /-is-set))))
           (from₁ f , from₁-constant f)

  unblock-from₂ : ∀ x f p → from₂ x f ∣ p ∣ ≡ from₁ f p
  unblock-from₂ unit _ _ = refl _

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
         proj₁ (from₂ x [ f ]→ ([]→-surjective [ f ]→))  ≡⟨ cong (proj₁ ∘ from₂ x [ f ]→) $ truncation-is-proposition _ _ ⟩
         proj₁ (from₂ x [ f ]→ ∣ f , refl _ ∣)           ≡⟨ cong proj₁ $ unblock-from₂ x _ (f , refl _) ⟩
         proj₁ (from₁ [ f ]→ (f , refl _))               ≡⟨⟩
         [ f ]                                           ∎)
      (λ _ → /-is-set)

------------------------------------------------------------------------
-- Quotient-like eliminators

-- If there is a split surjection from a quotient type to some other
-- type, then one can construct a quotient-like eliminator for the
-- other type.
--
-- This kind of construction is used in "Quotienting the Delay Monad
-- by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

↠-eliminator :
  (surj : A / R ↠ B)
  (P : B → Set p)
  (p-[] : ∀ x → P (_↠_.to surj [ x ])) →
  (∀ {x y} (r : R x y) →
   subst P (cong (_↠_.to surj) ([]-respects-relation r)) (p-[] x) ≡
   p-[] y) →
  (∀ x → Is-set (P x)) →
  ∀ x → P x
↠-eliminator surj P p-[] ok P-set x =
  subst P (_↠_.right-inverse-of surj x) p′
  where
  p′ : P (_↠_.to surj (_↠_.from surj x))
  p′ = elim
    (P ∘ _↠_.to surj)
    p-[]
    (λ {x y} r →
       subst (P ∘ _↠_.to surj) ([]-respects-relation r) (p-[] x)       ≡⟨ subst-∘ P (_↠_.to surj) ([]-respects-relation r) ⟩
       subst P (cong (_↠_.to surj) ([]-respects-relation r)) (p-[] x)  ≡⟨ ok r ⟩∎
       p-[] y                                                          ∎)
    (λ _ → P-set _)
    (_↠_.from surj x)

-- The eliminator "computes" in the "right" way for elements that
-- satisfy a certain property.

↠-eliminator-[] :
  ∀ (surj : A / R ↠ B)
  (P : B → Set p)
  (p-[] : ∀ x → P (_↠_.to surj [ x ]))
  (ok : ∀ {x y} (r : R x y) →
        subst P (cong (_↠_.to surj) ([]-respects-relation r)) (p-[] x) ≡
        p-[] y)
  (P-set : ∀ x → Is-set (P x)) x →
  _↠_.from surj (_↠_.to surj [ x ]) ≡ [ x ] →
  ↠-eliminator surj P p-[] ok P-set (_↠_.to surj [ x ]) ≡ p-[] x
↠-eliminator-[] {R = R} surj P p-[] ok P-set x hyp =
  subst P (_↠_.right-inverse-of surj (_↠_.to surj [ x ]))
    (elim (P ∘ _↠_.to surj) p-[] ok′ (λ _ → P-set _)
          (_↠_.from surj (_↠_.to surj [ x ])))                          ≡⟨ cong (λ p → subst P p (elim (P ∘ _↠_.to surj) _ ok′ _ _)) $
                                                                           H.respects-surjection surj 2 /-is-set
                                                                             (_↠_.right-inverse-of surj (_↠_.to surj [ x ]))
                                                                             (cong (_↠_.to surj) hyp) ⟩
  subst P (cong (_↠_.to surj) hyp)
    (elim (P ∘ _↠_.to surj) p-[] ok′ (λ _ → P-set _)
          (_↠_.from surj (_↠_.to surj [ x ])))                          ≡⟨ D.elim
                                                                             (λ {x y} p → subst P (cong (_↠_.to surj) p)
                                                                                            (elim (P ∘ _↠_.to surj) p-[] ok′ (λ _ → P-set _) x) ≡
                                                                                          elim (P ∘ _↠_.to surj) p-[] ok′ (λ _ → P-set _) y)
                                                                             (λ y →
      subst P (cong (_↠_.to surj) (refl _))
        (elim (P ∘ _↠_.to surj) p-[] ok′ (λ _ → P-set _) y)                     ≡⟨ cong (λ p → subst P p
                                                                                                 (elim (P ∘ _↠_.to surj) _ ok′ (λ _ → P-set _) _)) $
                                                                                   cong-refl (_↠_.to surj) ⟩
      subst P (refl _)
        (elim (P ∘ _↠_.to surj) p-[] ok′ (λ _ → P-set _) y)                     ≡⟨ subst-refl P _ ⟩∎

      elim (P ∘ _↠_.to surj) p-[] ok′ (λ _ → P-set _) y                         ∎)
                                                                             hyp ⟩
  elim (P ∘ _↠_.to surj) p-[] ok′ (λ _ → P-set _) [ x ]                 ≡⟨⟩

  p-[] x                                                                ∎
  where
  ok′ : ∀ {x y} (r : R x y) → _
  ok′ = λ r →
    trans (subst-∘ P (_↠_.to surj) ([]-respects-relation r)) (ok r)

-- If there is a bijection from a quotient type to some other type,
-- then one can also construct a quotient-like eliminator for the
-- other type.

↔-eliminator :
  (bij : A / R ↔ B)
  (P : B → Set p)
  (p-[] : ∀ x → P (_↔_.to bij [ x ])) →
  (∀ {x y} (r : R x y) →
   subst P (cong (_↔_.to bij) ([]-respects-relation r)) (p-[] x) ≡
   p-[] y) →
  (∀ x → Is-set (P x)) →
  ∀ x → P x
↔-eliminator bij = ↠-eliminator (_↔_.surjection bij)

-- This latter eliminator always "computes" in the "right" way.

↔-eliminator-[] :
  ∀ (bij : A / R ↔ B)
  (P : B → Set p)
  (p-[] : ∀ x → P (_↔_.to bij [ x ]))
  (ok : ∀ {x y} (r : R x y) →
        subst P (cong (_↔_.to bij) ([]-respects-relation r)) (p-[] x) ≡
        p-[] y)
  (P-set : ∀ x → Is-set (P x)) x →
  ↔-eliminator bij P p-[] ok P-set (_↔_.to bij [ x ]) ≡ p-[] x
↔-eliminator-[] bij P p-[] ok P-set x =
  ↠-eliminator-[] (_↔_.surjection bij) P p-[] ok P-set x
    (_↔_.left-inverse-of bij [ x ])

-- A quotient-like eliminator for functions of type ℕ → A / R, where R
-- is a propositional equivalence relation. Defined using countable
-- choice.
--
-- This eliminator is taken from Corollary 1 in "Quotienting the Delay
-- Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

ℕ→/-elim :
  {A : Set a} {R : A → A → Set r} →
  Axiom-of-countable-choice (a ⊔ r) →
  Is-equivalence-relation R →
  (∀ {x y} → Is-proposition (R x y)) →
  (P : (ℕ → A / R) → Set p)
  (p-[] : ∀ f → P (λ n → [ f n ])) →
  (∀ {f g} (r : (ℕ →ᴾ R) f g) →
   subst P (cong ℕ→/-comm-to ([]-respects-relation r)) (p-[] f) ≡
   p-[] g) →
  (∀ f → Is-set (P f)) →
  ∀ f → P f
ℕ→/-elim cc R-equiv R-prop =
  ↔-eliminator (ℕ→/-comm cc R-equiv R-prop)

-- The eliminator "computes" in the "right" way.

ℕ→/-elim-[] :
  ∀ {A : Set a} {R : A → A → Set r}
  (cc : Axiom-of-countable-choice (a ⊔ r))
  (R-equiv : Is-equivalence-relation R)
  (R-prop : ∀ {x y} → Is-proposition (R x y))
  (P : (ℕ → A / R) → Set p)
  (p-[] : ∀ f → P (λ n → [ f n ]))
  (ok : ∀ {f g} (r : (ℕ →ᴾ R) f g) →
        subst P (cong ℕ→/-comm-to ([]-respects-relation r)) (p-[] f) ≡
        p-[] g)
  (P-set : ∀ f → Is-set (P f)) f →
  ℕ→/-elim cc R-equiv R-prop P p-[] ok P-set (λ n → [ f n ]) ≡
  p-[] f
ℕ→/-elim-[] cc R-equiv R-prop =
  ↔-eliminator-[] (ℕ→/-comm cc R-equiv R-prop)