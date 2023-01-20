------------------------------------------------------------------------
-- An alternative definition of listed finite subsets
------------------------------------------------------------------------

-- The code in this module is based on Frumin, Geuvers, Gondelman and
-- van der Weide's "Finite Sets in Homotopy Type Theory". However, the
-- type of subsets is defined mutually with a membership predicate,
-- and two higher constructors have been replaced by a constructor
-- that states that extensionally equal subsets are equal.
--
-- The type in this module is perhaps harder to work with than the one
-- in Finite-subset.Listed: the "natural" eliminator only works for
-- motives that are propositional. However, the two types are shown to
-- be equivalent.

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Finite-subset.Listed.Alternative
  {c⁺} (eq : ∀ {a p} → P.Equality-with-paths a p c⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

import Equality.Path.Univalence as EPU
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (_∷_; swap)

open import Bijection equality-with-J using (_↔_)
import Bijection P.equality-with-J as PB
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
import Equivalence P.equality-with-J as PEq
import Finite-subset.Listed eq as Listed
import Finite-subset.Listed.Membership eq as LM
open import Function-universe equality-with-J as F hiding (id; _∘_)
import H-level P.equality-with-J as PH
open import H-level.Closure equality-with-J
import H-level.Closure P.equality-with-J as PHC
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; _∥⊎∥_)
open import Injection equality-with-J using (Injective)
import Univalence-axiom P.equality-with-J as PU

private
  variable
    a b p                 : Level
    A B                   : Type a
    P                     : A → Type p
    x x∼y y y₁ y₂ z z₁ z₂ : A

------------------------------------------------------------------------
-- Listed finite subsets

mutual

  -- Listed finite subsets of a given type, defined mutually with a
  -- membership predicate.

  infixr 5 _∷_

  data Finite-subset-of (A : Type a) : Type a where
    []              : Finite-subset-of A
    _∷_             : A → Finite-subset-of A → Finite-subset-of A
    extensionalityᴾ : x ∼ y → x P.≡ y
    is-setᴾ         : P.Is-set (Finite-subset-of A)

  private

    Membership :
      {A : Type a} → A → Finite-subset-of A → PH.Proposition a

  -- Membership.

  infix 4 _∈_

  _∈_ : {A : Type a} → A → Finite-subset-of A → Type a
  x ∈ y = proj₁ (Membership x y)

  -- Membership is propositional.

  ∈-propositionalᴾ : ∀ y → P.Is-proposition (x ∈ y)
  ∈-propositionalᴾ y = proj₂ (Membership _ y)

  -- Extensional equality.

  infix 4 _∼_

  _∼_ :
    {A : Type a} → Finite-subset-of A → Finite-subset-of A → Type a
  x ∼ y = ∀ z → z ∈ x ⇔ z ∈ y

  Membership x [] =
    ⊥ , PHC.⊥-propositional

  Membership x (y ∷ z) =
    (x ≡ y ∥⊎∥ x ∈ z) , Trunc.truncation-is-propositionᴾ

  Membership x (extensionalityᴾ {x = y} {y = z} y∼z i) =
    lemma i
    where
    lemma : Membership x y P.≡ Membership x z
    lemma = P.Σ-≡,≡→≡
      (x ∈ y  P.≡⟨ PEq._≃_.from
                     (PU.Propositional-extensionality-is-univalence-for-propositions P.ext)
                     (λ _ _ → EPU.univ)
                     (∈-propositionalᴾ y)
                     (∈-propositionalᴾ z)
                     (y∼z x) ⟩∎
       x ∈ z  ∎)
      (PHC.H-level-propositional P.ext 1 _ _)

  Membership x (is-setᴾ {x = y} {y = z} p q i j) =
    P.heterogeneous-UIP₀₀
      {x = λ _ → Membership x y}
      {y = λ _ → Membership x z}
      {p = λ i → Membership x (p i)}
      {q = λ i → Membership x (q i)}
      (PU.∃-H-level-H-level-1+ P.ext EPU.univ 1)
      i j

-- Variants of some of the constructors.

extensionality : x ∼ y → x ≡ y
extensionality = _↔_.from ≡↔≡ ∘ extensionalityᴾ

is-set : Is-set (Finite-subset-of A)
is-set =
  _↔_.from (H-level↔H-level 2) Finite-subset-of.is-setᴾ

-- Membership is propositional.

∈-propositional : ∀ y → Is-proposition (x ∈ y)
∈-propositional = _↔_.from (H-level↔H-level 1) ∘ ∈-propositionalᴾ

-- Unit tests documenting some of the computational behaviour of _∈_.

_ : (x ∈ []) ≡ ⊥
_ = refl _

_ : (x ∈ y ∷ z) ≡ (x ≡ y ∥⊎∥ x ∈ z)
_ = refl _

------------------------------------------------------------------------
-- Eliminators

private

  -- The following dependent eliminator is not exported, because the
  -- motive is necessarily pointwise propositional (see
  -- motive-propositional below).

  record Elimᴾ′ {A : Type a} (P : Finite-subset-of A → Type p) :
                Type (a ⊔ p) where
    no-eta-equality
    field
      []ʳ             : P []
      ∷ʳ              : ∀ x → P y → P (x ∷ y)
      is-setʳ         : ∀ x → P.Is-set (P x)
      extensionalityʳ :
        (p : P x) (q : P y) →
        P.[ (λ i → P (extensionalityᴾ {x = x} {y = y} x∼y i)) ] p ≡ q

  open Elimᴾ′

  elimᴾ′ : Elimᴾ′ P → (x : Finite-subset-of A) → P x
  elimᴾ′ {A} {P} e = helper
    where
    module E = Elimᴾ′ e

    helper : (x : Finite-subset-of A) → P x
    helper []      = E.[]ʳ
    helper (x ∷ y) = E.∷ʳ x (helper y)

    helper (extensionalityᴾ {x} {y} _ i) =
      E.extensionalityʳ (helper x) (helper y) i

    helper (is-setᴾ x y i j) =
      P.heterogeneous-UIP
        E.is-setʳ (is-setᴾ x y)
        (λ i → helper (x i)) (λ i → helper (y i)) i j

  -- The motive is necessarily pointwise propositional.

  motive-propositional :
    Elimᴾ′ P → ∀ x → P.Is-proposition (P x)
  motive-propositional {P} e x p q =
    p                                         P.≡⟨ P.sym $ P.subst-refl P _ ⟩
    P.subst P P.refl p                        P.≡⟨ P.cong (λ eq → P.subst P eq p) $ is-setᴾ _ _ ⟩
    P.subst P (extensionalityᴾ λ _ → F.id) p  P.≡⟨ PB._↔_.to (P.heterogeneous↔homogeneous _)
                                                     (e .extensionalityʳ {x∼y = λ _ → F.id} p q) ⟩∎
    q                                         ∎

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : Finite-subset-of A → Type p) :
             Type (a ⊔ p) where
  no-eta-equality
  field
    []ʳ             : P []
    ∷ʳ              : ∀ x → P y → P (x ∷ y)
    is-propositionʳ : ∀ x → P.Is-proposition (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : Finite-subset-of A) → P x
elimᴾ {A} {P} e = elimᴾ′ e′
  where
  module E = Elimᴾ e

  e′ : Elimᴾ′ _
  e′ .[]ʳ                 = e .[]ʳ
  e′ .∷ʳ                  = e .∷ʳ
  e′ .is-setʳ             = PH.mono₁ 1 ∘ e .is-propositionʳ
  e′ .extensionalityʳ _ _ =
    PB._↔_.from (P.heterogeneous↔homogeneous _)
      (e .is-propositionʳ _ _ _)

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    []ʳ             : B
    ∷ʳ              : A → Finite-subset-of A → B → B
    is-propositionʳ : P.Is-proposition B

open Recᴾ public

recᴾ : Recᴾ A B → Finite-subset-of A → B
recᴾ {A} {B} r = elimᴾ e
  where
  module R = Recᴾ r

  e : Elimᴾ _
  e .[]ʳ               = R.[]ʳ
  e .∷ʳ {y} x          = R.∷ʳ x y
  e .is-propositionʳ _ = R.is-propositionʳ

-- A dependent eliminator, expressed using equality.

record Elim
         {A : Type a} (P : Finite-subset-of A → Type p) :
         Type (a ⊔ p) where
  field
    []ʳ             : P []
    ∷ʳ              : ∀ x → P y → P (x ∷ y)
    is-propositionʳ : ∀ x → Is-proposition (P x)

open Elim public

elim : Elim P → (x : Finite-subset-of A) → P x
elim e = elimᴾ e′
  where
  module E = Elim e

  e′ : Elimᴾ _
  e′ .[]ʳ             = E.[]ʳ
  e′ .∷ʳ              = E.∷ʳ
  e′ .is-propositionʳ = _↔_.to (H-level↔H-level 1) ∘ E.is-propositionʳ

-- A non-dependent eliminator, expressed using equality.

record Rec (A : Type a) (B : Type b) : Type (a ⊔ b) where
  field
    []ʳ             : B
    ∷ʳ              : A → Finite-subset-of A → B → B
    is-propositionʳ : Is-proposition B

open Rec public

rec : Rec A B → Finite-subset-of A → B
rec r = elim e
  where
  module R = Rec r

  e : Elim _
  e .[]ʳ               = R.[]ʳ
  e .∷ʳ {y} x          = R.∷ʳ x y
  e .is-propositionʳ _ = R.is-propositionʳ

------------------------------------------------------------------------
-- Some lemmas

-- If A is inhabited, then Finite-subset-of A is not a proposition.

¬-proposition : A → ¬ Is-proposition (Finite-subset-of A)
¬-proposition {A} x =
  Is-proposition (Finite-subset-of A)  ↝⟨ (λ hyp → hyp _ _) ⟩
  x ∷ [] ≡ []                          ↝⟨ (λ hyp → subst (x ∈_) hyp (Trunc.∣inj₁∣ (refl _))) ⟩
  x ∈ []                               ↔⟨ ⊥↔⊥ ⟩□
  ⊥                                    □

abstract

  -- Duplicated elements can be dropped.

  drop : x ∷ x ∷ y ≡ x ∷ y
  drop {x} {y} = extensionality λ z →
    z ≡ x ∥⊎∥ (z ≡ x ∥⊎∥ z ∈ y)  ↔⟨ Trunc.drop-left-∥⊎∥ Trunc.∥⊎∥-propositional Trunc.∣inj₁∣ ⟩□
    z ≡ x ∥⊎∥ z ∈ y              □

  -- The "first" two elements can be swapped.

  swap : x ∷ y ∷ z ≡ y ∷ x ∷ z
  swap {x} {y} {z} = extensionality λ u →
    u ≡ x ∥⊎∥ (u ≡ y ∥⊎∥ u ∈ z)  ↔⟨ Trunc.∥⊎∥-assoc ⟩
    (u ≡ x ∥⊎∥ u ≡ y) ∥⊎∥ u ∈ z  ↔⟨ Trunc.∥⊎∥-comm Trunc.∥⊎∥-cong F.id ⟩
    (u ≡ y ∥⊎∥ u ≡ x) ∥⊎∥ u ∈ z  ↔⟨ inverse Trunc.∥⊎∥-assoc ⟩□
    u ≡ y ∥⊎∥ (u ≡ x ∥⊎∥ u ∈ z)  □

-- If x is a member of y, then x ∷ y is equal to y.

∈→∷≡ : x ∈ y → x ∷ y ≡ y
∈→∷≡ {x} = elim e _
  where
  e : Elim (λ y → x ∈ y → x ∷ y ≡ y)
  e .∷ʳ {y} z hyp =
    Trunc.rec is-set
      [ (λ x≡z →
           x ∷ z ∷ y  ≡⟨ cong (λ x → x ∷ _) x≡z ⟩
           z ∷ z ∷ y  ≡⟨ drop ⟩∎
           z ∷ y      ∎)
      , (λ x∈y →
           x ∷ z ∷ y  ≡⟨ swap ⟩
           z ∷ x ∷ y  ≡⟨ cong (_ ∷_) (hyp x∈y) ⟩∎
           z ∷ y      ∎)
      ]

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    is-set

------------------------------------------------------------------------
-- Some operations

-- Singleton subsets.

singleton : A → Finite-subset-of A
singleton x = x ∷ []

-- A lemma characterising singleton.

∈singleton≃ :
  (x ∈ singleton y) ≃ ∥ x ≡ y ∥
∈singleton≃ {x} {y} =
  x ∈ singleton y  ↔⟨⟩
  x ≡ y ∥⊎∥ ⊥      ↔⟨ Trunc.∥∥-cong $ drop-⊥-right ⊥↔⊥ ⟩□
  ∥ x ≡ y ∥        □

-- If truncated equality is decidable, then membership is also
-- decidable.

member? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec (x ∈ y)
member? equal? x = elim e
  where
  e : Elim _
  e .[]ʳ          = no λ ()
  e .∷ʳ {y = z} y = case equal? x y of
    [ (λ  ∥x≡y∥ _ → yes (Trunc.∥∥-map inj₁ ∥x≡y∥))
    , (λ ¬∥x≡y∥ →
         [ (λ x∈z → yes (Trunc.∣inj₂∣ x∈z))
         , (λ x∉z → no (
              x ∈ y ∷ z        ↔⟨⟩
              x ≡ y ∥⊎∥ x ∈ z  ↝⟨ Trunc.∥∥-map [ ¬∥x≡y∥ ∘ Trunc.∣_∣ , x∉z ] ⟩
              ∥ ⊥ ∥            ↔⟨ Trunc.not-inhabited⇒∥∥↔⊥ id ⟩□
              ⊥                □))
         ])
    ]
  e .is-propositionʳ y =
    Dec-closure-propositional ext (∈-propositional y)

------------------------------------------------------------------------
-- The union operation

private

  -- A specification of what it means for a subset to be the union of
  -- two subsets.

  Is-union-of :
    {A : Type a} (_ _ _ : Finite-subset-of A) → Type a
  Is-union-of x y z = ∀ u → (u ∈ z) ≃ (u ∈ x ∥⊎∥ u ∈ y)

  -- Is-union-of x y is functional.

  Is-union-of-functional :
    (x y : Finite-subset-of A) →
    Is-union-of x y z₁ → Is-union-of x y z₂ →
    z₁ ≡ z₂
  Is-union-of-functional {z₁} {z₂} x y p₁ p₂ =
    extensionality λ u →
      u ∈ z₁           ↔⟨ p₁ u ⟩
      u ∈ x ∥⊎∥ u ∈ y  ↔⟨ inverse $ p₂ u ⟩□
      u ∈ z₂           □

  -- Is-union-of is propositional.

  Is-union-of-propositional :
    (x y z : Finite-subset-of A) →
    Is-proposition (Is-union-of x y z)
  Is-union-of-propositional x y z =
    Π-closure ext 1 λ _ →
    Eq.left-closure ext 0 (∈-propositional z)

  -- The union operation, along with a correctness proof.

  union : (x y : Finite-subset-of A) → ∃ (Is-union-of x y)
  union = elim e
    where
    e : Elim _
    e .[]ʳ y =
        y
      , λ u →
          u ∈ y        ↔⟨ inverse $ Trunc.∥⊎∥-left-identity (∈-propositional y) ⟩□
          ⊥ ∥⊎∥ u ∈ y  □

    e .∷ʳ {y} x hyp z =
        x ∷ proj₁ (hyp z)
      , λ u →
          u ∈ x ∷ proj₁ (hyp z)        ↔⟨⟩
          u ≡ x ∥⊎∥ u ∈ proj₁ (hyp z)  ↝⟨ F.id Trunc.∥⊎∥-cong proj₂ (hyp z) u ⟩
          u ≡ x ∥⊎∥ (u ∈ y ∥⊎∥ u ∈ z)  ↔⟨ Trunc.∥⊎∥-assoc ⟩
          (u ≡ x ∥⊎∥ u ∈ y) ∥⊎∥ u ∈ z  ↔⟨⟩
          u ∈ x ∷ y ∥⊎∥ u ∈ z          □

    e .is-propositionʳ x f g = ⟨ext⟩ λ y →
      Σ-≡,≡→≡
        (Is-union-of-functional x y (proj₂ (f y)) (proj₂ (g y)))
        (Is-union-of-propositional x y (proj₁ (g y)) _ _)

-- The union of two finite subsets.

infixr 5 _∪_

_∪_ :
  Finite-subset-of A → Finite-subset-of A →
  Finite-subset-of A
x ∪ y = proj₁ (union x y)

-- Unit tests documenting some of the computational behaviour of _∪_.

_ : [] ∪ x ≡ x
_ = refl _

_ : (x ∷ y) ∪ z ≡ x ∷ (y ∪ z)
_ = refl _

-- Membership of a union of two subsets can be expressed in terms of
-- membership of the subsets.

∈∪≃∈∥⊎∥∈ : ∀ y → (x ∈ y ∪ z) ≃ (x ∈ y ∥⊎∥ x ∈ z)
∈∪≃∈∥⊎∥∈ {z} y = proj₂ (union y z) _

-- If x is a member of y, then x is a member of y ∪ z.

∈→∈∪ˡ : ∀ y → x ∈ y → x ∈ y ∪ z
∈→∈∪ˡ y = _≃_.from (∈∪≃∈∥⊎∥∈ y) ∘ Trunc.∣inj₁∣

-- If x is a member of z, then x is a member of y ∪ z.

∈→∈∪ʳ : ∀ y → x ∈ z → x ∈ y ∪ z
∈→∈∪ʳ y = _≃_.from (∈∪≃∈∥⊎∥∈ y) ∘ Trunc.∣inj₂∣

-- [] is a right identity of _∪_.

∪[] :
  (x : Finite-subset-of A) →
  x ∪ [] ≡ x
∪[] = elim e
  where
  e : Elim _
  e .is-propositionʳ _ = is-set
  e .[]ʳ               = refl _
  e .∷ʳ {y} x hyp      =
    x ∷ y ∪ []  ≡⟨ cong (x ∷_) hyp ⟩∎
    x ∷ y        ∎

-- A lemma relating _∪_ and _∷_.

∪∷ :
  (x : Finite-subset-of A) →
  x ∪ (y ∷ z) ≡ y ∷ x ∪ z
∪∷ {y} {z} = elim e
  where
  e : Elim _
  e .is-propositionʳ _ = is-set

  e .[]ʳ = refl _

  e .∷ʳ {y = u} x hyp =
    (x ∷ u) ∪ (y ∷ z)  ≡⟨⟩
    x ∷ u ∪ (y ∷ z)    ≡⟨ cong (x ∷_) hyp ⟩
    x ∷ y ∷ u ∪ z      ≡⟨ swap ⟩
    y ∷ x ∷ u ∪ z      ≡⟨⟩
    y ∷ (x ∷ u) ∪ z    ∎

-- The union operator is associative.

∪-assoc :
  (x : Finite-subset-of A) →
  x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
∪-assoc {y} {z} = elim e
  where
  e : Elim _
  e .is-propositionʳ _ = is-set

  e .[]ʳ = refl _

  e .∷ʳ {y = u} x hyp =
    x ∷ u ∪ (y ∪ z)  ≡⟨ cong (x ∷_) hyp ⟩∎
    x ∷ (u ∪ y) ∪ z  ∎

-- The union operator is commutative.

∪-comm :
  (x : Finite-subset-of A) →
  x ∪ y ≡ y ∪ x
∪-comm {y} = elim e
  where
  e : Elim _
  e .is-propositionʳ _ = is-set

  e .[]ʳ =
    [] ∪ y  ≡⟨⟩
    y       ≡⟨ sym (∪[] y) ⟩∎
    y ∪ []  ∎

  e .∷ʳ {y = z} x hyp =
    x ∷ z ∪ y    ≡⟨ cong (x ∷_) hyp ⟩
    x ∷ y ∪ z    ≡⟨ sym (∪∷ y) ⟩∎
    y ∪ (x ∷ z)  ∎

-- The union operator is idempotent.

∪-idem : (x : Finite-subset-of A) → x ∪ x ≡ x
∪-idem = elim e
  where
  e : Elim _
  e .[]ʳ =
    [] ∪ []  ≡⟨⟩
    []       ∎

  e .∷ʳ {y} x hyp =
    (x ∷ y) ∪ (x ∷ y)  ≡⟨⟩
    x ∷ y ∪ x ∷ y      ≡⟨ cong (_ ∷_) (∪∷ y) ⟩
    x ∷ x ∷ y ∪ y      ≡⟨ drop ⟩
    x ∷ y ∪ y          ≡⟨ cong (_ ∷_) hyp ⟩∎
    x ∷ y              ∎

  e .is-propositionʳ = λ _ → is-set

-- The union operator distributes from the left and right over itself.

∪-distrib-left : ∀ x → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ (x ∪ z)
∪-distrib-left {y} {z} x =
  x ∪ (y ∪ z)        ≡⟨ cong (_∪ _) $ sym (∪-idem x) ⟩
  (x ∪ x) ∪ (y ∪ z)  ≡⟨ sym $ ∪-assoc x ⟩
  x ∪ (x ∪ (y ∪ z))  ≡⟨ cong (x ∪_) $ ∪-assoc x ⟩
  x ∪ ((x ∪ y) ∪ z)  ≡⟨ cong ((x ∪_) ∘ (_∪ _)) $ ∪-comm x ⟩
  x ∪ ((y ∪ x) ∪ z)  ≡⟨ cong (x ∪_) $ sym $ ∪-assoc y ⟩
  x ∪ (y ∪ (x ∪ z))  ≡⟨ ∪-assoc x ⟩∎
  (x ∪ y) ∪ (x ∪ z)  ∎

∪-distrib-right : ∀ x → (x ∪ y) ∪ z ≡ (x ∪ z) ∪ (y ∪ z)
∪-distrib-right {y} {z} x =
  (x ∪ y) ∪ z        ≡⟨ ∪-comm (x ∪ _) ⟩
  z ∪ (x ∪ y)        ≡⟨ ∪-distrib-left z ⟩
  (z ∪ x) ∪ (z ∪ y)  ≡⟨ cong₂ _∪_ (∪-comm z) (∪-comm z) ⟩∎
  (x ∪ z) ∪ (y ∪ z)  ∎

------------------------------------------------------------------------
-- Subsets of subsets

-- Subsets.

infix 4 _⊆_

_⊆_ : {A : Type a} → Finite-subset-of A → Finite-subset-of A → Type a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- _⊆_ is pointwise propositional.

⊆-propositional :
  (x y : Finite-subset-of A) → Is-proposition (x ⊆ y)
⊆-propositional x y =
  Π-closure ext 1 λ _ →
  Π-closure ext 1 λ _ →
  ∈-propositional y

-- The function x ∷_ is monotone with respect to _⊆_.

∷-cong-⊆ : ∀ y z → y ⊆ z → x ∷ y ⊆ x ∷ z
∷-cong-⊆ {x} y z y⊆z = λ u →
  u ∈ x ∷ y        ↔⟨⟩
  u ≡ x ∥⊎∥ u ∈ y  ↝⟨ id Trunc.∥⊎∥-cong y⊆z _ ⟩
  u ≡ x ∥⊎∥ u ∈ z  ↔⟨⟩
  u ∈ x ∷ z        □

-- The union operator is monotone with respect to _⊆_.

∪-mono-⊆ : ∀ x₁ x₂ → x₁ ⊆ x₂ → y₁ ⊆ y₂ → x₁ ∪ y₁ ⊆ x₂ ∪ y₂
∪-mono-⊆ {y₁} {y₂} x₁ x₂ x₁⊆x₂ y₁⊆y₂ = λ u →
  u ∈ x₁ ∪ y₁        ↔⟨ ∈∪≃∈∥⊎∥∈ x₁ ⟩
  u ∈ x₁ ∥⊎∥ u ∈ y₁  ↝⟨ x₁⊆x₂ u Trunc.∥⊎∥-cong y₁⊆y₂ u ⟩
  u ∈ x₂ ∥⊎∥ u ∈ y₂  ↔⟨ inverse $ ∈∪≃∈∥⊎∥∈ x₂ ⟩□
  u ∈ x₂ ∪ y₂        □

-- The subset property can be expressed using _∪_ and _≡_.

⊆≃∪≡ : ∀ x → (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {y} x = Eq.⇔→≃
  (⊆-propositional x y)
  is-set
  (elim e x)
  (λ p z →
     z ∈ x      ↝⟨ ∈→∈∪ˡ x ⟩
     z ∈ x ∪ y  ↝⟨ ≡⇒↝ _ (cong (z ∈_) p) ⟩□
     z ∈ y      □)
  where
  e : Elim (λ x → x ⊆ y → x ∪ y ≡ y)
  e .[]ʳ _ =
    [] ∪ y  ≡⟨⟩
    y       ∎

  e .∷ʳ {y = z} x hyp x∷z⊆y =
    x ∷ z ∪ y  ≡⟨ cong (x ∷_) (hyp (λ _ → x∷z⊆y _ ∘ Trunc.∣inj₂∣)) ⟩
    x ∷ y      ≡⟨ ∈→∷≡ (x∷z⊆y x (Trunc.∣inj₁∣ (refl _))) ⟩∎
    y          ∎

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    is-set

-- _⊆_ is a partial order.

⊆-refl : x ⊆ x
⊆-refl _ = id

⊆-trans : x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans x⊆y y⊆z _ = y⊆z _ ∘ x⊆y _

⊆-antisymmetric : x ⊆ y → y ⊆ x → x ≡ y
⊆-antisymmetric x⊆y y⊆x =
  extensionality λ z →
    record { to = x⊆y z; from = y⊆x z }

------------------------------------------------------------------------
-- Another lemma

-- Equality can be expressed using _⊆_.

≡≃⊆×⊇ : (x ≡ y) ≃ (x ⊆ y × y ⊆ x)
≡≃⊆×⊇ {x} {y} =
  x ≡ y                  ↝⟨ Eq.⇔→≃
                              is-set
                              (×-closure 1 is-set is-set)
                              (λ x≡y →
                                   (x ∪ y  ≡⟨ cong (_∪ _) x≡y ⟩
                                    y ∪ y  ≡⟨ ∪-idem y ⟩∎
                                    y      ∎)
                                 , (y ∪ x  ≡⟨ cong (_∪ _) $ sym x≡y ⟩
                                    x ∪ x  ≡⟨ ∪-idem x ⟩∎
                                    x      ∎))
                              (λ (p , q) →
                                 x      ≡⟨ sym q ⟩
                                 y ∪ x  ≡⟨ ∪-comm y ⟩
                                 x ∪ y  ≡⟨ p ⟩∎
                                 y      ∎) ⟩
  x ∪ y ≡ y × y ∪ x ≡ x  ↝⟨ inverse $ ⊆≃∪≡ x ×-cong ⊆≃∪≡ y ⟩□
  x ⊆ y × y ⊆ x          □

-- Extensional equality is equivalent to equality.

∼≃≡ : (x ∼ y) ≃ (x ≡ y)
∼≃≡ {x} {y} =
  x ∼ y                                      ↔⟨⟩
  (∀ z → z ∈ x ⇔ z ∈ y)                      ↔⟨ (∀-cong ext λ _ → ⇔↔→×→) ⟩
  (∀ z → (z ∈ x → z ∈ y) × (z ∈ y → z ∈ x))  ↔⟨ ΠΣ-comm ⟩
  x ⊆ y × y ⊆ x                              ↝⟨ inverse ≡≃⊆×⊇ ⟩□
  x ≡ y                                      □

------------------------------------------------------------------------
-- Definitions related to the listed finite subsets defined in Listed

-- Some lemmas used below.

private

  module Listed≃Listed where

    -- Converts one kind of finite subset to another.

    from : Listed.Finite-subset-of A → Finite-subset-of A
    from = Listed.rec r
      where
      r : Listed.Rec _ _
      r .Listed.Rec.[]ʳ           = []
      r .Listed.Rec.∷ʳ x _ y      = x ∷ y
      r .Listed.Rec.dropʳ _ _ _   = drop
      r .Listed.Rec.swapʳ _ _ _ _ = swap
      r .Listed.Rec.is-setʳ       = is-set

    -- A lemma relating from, _∈_ and LM._∈_.

    ∈from≃ : ∀ x → (z ∈ from x) ≃ (z LM.∈ x)
    ∈from≃ {z} = Listed.elim-prop e
      where
      e : Listed.Elim-prop _
      e .Listed.Elim-prop.[]ʳ =
        z ∈ from Listed.[]  ↔⟨⟩
        ⊥                   ↔⟨ ⊥↔⊥ ⟩
        ⊥₀                  ↝⟨ inverse $ LM.∈[]≃ ⟩
        z LM.∈ Listed.[]    □

      e .Listed.Elim-prop.∷ʳ {y} x hyp =
        z ∈ from (x Listed.∷ y)  ↔⟨⟩
        z ≡ x ∥⊎∥ z ∈ from y     ↝⟨ F.id Trunc.∥⊎∥-cong hyp ⟩
        z ≡ x ∥⊎∥ z LM.∈ y       ↝⟨ inverse LM.∈∷≃ ⟩□
        z LM.∈ x Listed.∷ y      □

      e .Listed.Elim-prop.is-propositionʳ _ =
        Eq.right-closure ext 0 LM.∈-propositional

    -- A lemma relating from, _⊆_ and Listed._⊆_.

    from⊆from→ :
      (x y : Listed.Finite-subset-of A) →
      from x ⊆ from y → x LM.⊆ y
    from⊆from→ = Listed.elim-prop e
      where
      e : Listed.Elim-prop _
      e .Listed.Elim-prop.[]ʳ = Listed.elim-prop e′
        where
        e′ : Listed.Elim-prop _
        e′ .Listed.Elim-prop.[]ʳ _ = LM.⊆-refl

        e′ .Listed.Elim-prop.∷ʳ {y} x _ _ z =
          z LM.∈ Listed.[]     ↔⟨ LM.∈[]≃ ⟩
          ⊥₀                   ↝⟨ ⊥-elim ⟩□
          z LM.∈ x Listed.∷ y  □

        e′ .Listed.Elim-prop.is-propositionʳ _ =
          Π-closure ext 1 λ _ →
          LM.⊆-propositional

      e .Listed.Elim-prop.∷ʳ {y = y₁} x hyp₁ y₂ =
        from (x Listed.∷ y₁) ⊆ from y₂               ↔⟨⟩
        (∀ z → z ≡ x ∥⊎∥ z ∈ from y₁ → z ∈ from y₂)  ↝⟨ (λ hyp₂ z → Trunc.rec LM.∈-propositional
                                                                      [ (
            z ≡ x                                                        ↝⟨ Trunc.∣inj₁∣ ⟩
            z ≡ x ∥⊎∥ z ∈ from y₁                                        ↝⟨ hyp₂ z ⟩
            z ∈ from y₂                                                  ↔⟨ ∈from≃ _ ⟩□
            z LM.∈ y₂                                                    □)
                                                                      , ($⟨ (λ z → hyp₂ z ∘ Trunc.∣inj₂∣) ⟩
            from y₁ ⊆ from y₂                                            ↝⟨ hyp₁ y₂ ⟩
            y₁ LM.⊆ y₂                                                   ↝⟨ _$ z ⟩□
            (z LM.∈ y₁ → z LM.∈ y₂)                                      □)
                                                                      ]) ⟩
        (∀ z → z ≡ x ∥⊎∥ z LM.∈ y₁ → z LM.∈ y₂)      ↔⟨ (∀-cong ext λ _ → →-cong ext (inverse LM.∈∷≃) F.id) ⟩□
        x Listed.∷ y₁ LM.⊆ y₂                        □

      e .Listed.Elim-prop.is-propositionʳ _ =
        Π-closure ext 1 λ _ →
        Π-closure ext 1 λ _ →
        LM.⊆-propositional

    -- The function from is injective.

    from-injective : Injective (from {A = A})
    from-injective {x} {y} =
      from x ≡ from y                    ↔⟨ ≡≃⊆×⊇ ⟩
      from x ⊆ from y × from y ⊆ from x  ↝⟨ Σ-map (from⊆from→ _ _) (from⊆from→ _ _) ⟩
      x LM.⊆ y × y LM.⊆ x                ↝⟨ uncurry LM.⊆-antisymmetric ⟩□
      x ≡ y                              □

    -- Converts one kind of finite subset to another, and returns a
    -- partial correctness result.

    to :
      (x : Finite-subset-of A) →
      ∃ λ (y : Listed.Finite-subset-of A) → from y ≡ x
    to = elim e
      where
      e : Elim _
      e .Elim.[]ʳ = Listed.[] , refl _

      e .Elim.∷ʳ x (y , eq) = x Listed.∷ y , cong (x ∷_) eq

      e .Elim.is-propositionʳ x (y₁ , eq₁) (y₂ , eq₂) =
        Σ-≡,≡→≡
          (from-injective
             (from y₁  ≡⟨ eq₁ ⟩
              x        ≡⟨ sym eq₂ ⟩∎
              from y₂  ∎))
          (is-set _ _)

    -- Another correctness result.

    to-from :
      (x : Listed.Finite-subset-of A) →
      proj₁ (to (from x)) ≡ x
    to-from = Listed.elim-prop e
      where
      e : Listed.Elim-prop _
      e .Listed.Elim-prop.[]ʳ               = refl _
      e .Listed.Elim-prop.∷ʳ x              = cong (x Listed.∷_)
      e .Listed.Elim-prop.is-propositionʳ _ = Listed.is-set

-- The type of listed finite subsets defined above is pointwise
-- equivalent to the type of listed finite subsets defined in Listed.

Listed≃Listed : Finite-subset-of A ≃ Listed.Finite-subset-of A
Listed≃Listed = Eq.↔→≃ (proj₁ ∘ to) from to-from (proj₂ ∘ to)
  where
  open Listed≃Listed

-- The equivalence preserves membership.

∈≃∈ : ∀ y → (x ∈ y) ≃ (x LM.∈ _≃_.to Listed≃Listed y)
∈≃∈ {x} y =
  x ∈ y                                                ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $ sym $ _≃_.left-inverse-of Listed≃Listed y ⟩
  x ∈ _≃_.from Listed≃Listed (_≃_.to Listed≃Listed y)  ↝⟨ ∈from≃ _ ⟩□
  x LM.∈ _≃_.to Listed≃Listed y                        □
  where
  open Listed≃Listed

-- Another dependent eliminator (expressed using equality).
--
-- Note that the motive is not required to be propositional.

record Elim′ {A : Type a} (P : Finite-subset-of A → Type p) :
             Type (a ⊔ p) where
  no-eta-equality
  field
    []ʳ     : P []
    ∷ʳ      : ∀ x → P y → P (x ∷ y)
    dropʳ   : ∀ x (p : P y) →
              subst P (drop {x = x} {y = y}) (∷ʳ x (∷ʳ x p)) ≡ ∷ʳ x p
    swapʳ   : ∀ x y (p : P z) →
              subst P (swap {x = x} {y = y} {z = z}) (∷ʳ x (∷ʳ y p)) ≡
              ∷ʳ y (∷ʳ x p)
    is-setʳ : ∀ x → Is-set (P x)

open Elim′ public

elim′ : Elim′ P → (x : Finite-subset-of A) → P x
elim′ {P} e x =
  subst P (_≃_.left-inverse-of Listed≃Listed x)
    (Listed.elim e′ (_≃_.to Listed≃Listed x))
  where
  module E = Elim′ e

  e′ : Listed.Elim (P ∘ _≃_.from Listed≃Listed)
  e′ .Listed.[]ʳ = E.[]ʳ

  e′ .Listed.∷ʳ = E.∷ʳ

  e′ .Listed.dropʳ x p =
    subst (P ∘ _≃_.from Listed≃Listed)
      Listed.drop
      (e .∷ʳ x (e .∷ʳ x p))                        ≡⟨ subst-∘ _ _ _ ⟩

    subst P
      (cong (_≃_.from Listed≃Listed) Listed.drop)
      (e .∷ʳ x (e .∷ʳ x p))                        ≡⟨ cong (flip (subst P) _) $ is-set _ _ ⟩

    subst P drop (e .∷ʳ x (e .∷ʳ x p))             ≡⟨ e .dropʳ x p ⟩∎

    e .∷ʳ x p                                      ∎

  e′ .Listed.swapʳ x y p =
    subst (P ∘ _≃_.from Listed≃Listed)
      Listed.swap
      (e .∷ʳ x (e .∷ʳ y p))                        ≡⟨ subst-∘ _ _ _ ⟩

    subst P
      (cong (_≃_.from Listed≃Listed) Listed.swap)
      (e .∷ʳ x (e .∷ʳ y p))                        ≡⟨ cong (flip (subst P) _) $ is-set _ _ ⟩

    subst P swap (e .∷ʳ x (e .∷ʳ y p))             ≡⟨ e .swapʳ x y p ⟩∎

    e .∷ʳ y (e .∷ʳ x p)                            ∎

  e′ .Listed.is-setʳ _ = E.is-setʳ _
