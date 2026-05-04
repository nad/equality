------------------------------------------------------------------------
-- Listed finite subsets, defined using a HIT with erased higher
-- constructors
------------------------------------------------------------------------

-- Based on Frumin, Geuvers, Gondelman and van der Weide's "Finite
-- Sets in Homotopy Type Theory".

{-# OPTIONS --cubical=erased --safe #-}

import Equality.Path as P

module Finite-subset.Listed.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Dec
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (swap)

open import Bag-equivalence equality-with-J as BE using (_∼[_]_; set)
open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Erased.Cubical eq as EC
  using (Erased; [_]; Dec-Erased; Dec→Dec-Erased)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; ∣_∣; _∥⊎∥_)
open import Injection equality-with-J using (Injective)
import List equality-with-J as L
import Maybe equality-with-J as Maybe
open import Monad equality-with-J as M using (Raw-monad; Monad; _=<<_)
open import Nat equality-with-J as Nat using (_<_)
open import Quotient.Erased eq as Q using (_/ᴱ_)
import Univalence-axiom equality-with-J as Univ

private
  variable
    a b                                     : Level
    A B                                     : Type a
    H ms p q x x₁ x₂ y y₁ y₂ ys z z₁ z₂ _≟_ : A
    P                                       : A → Type p
    f g                                     : (x : A) → P x
    m n                                     : ℕ

------------------------------------------------------------------------
-- Listed finite subsets

-- Listed finite subsets of a given type.

infixr 5 _∷_

data Finite-subset-of (A : Type a) : Type a where
  []         : Finite-subset-of A
  _∷_        : A → Finite-subset-of A → Finite-subset-of A
  @0 dropᴾ   : x ∷ x ∷ y P.≡ x ∷ y
  @0 swapᴾ   : x ∷ y ∷ z P.≡ y ∷ x ∷ z
  @0 is-setᴾ : P.Is-set (Finite-subset-of A)

-- Variants of some of the constructors.

@0 drop :
  {x : A} {y : Finite-subset-of A} →
  x ∷ x ∷ y ≡ x ∷ y
drop = _↔_.from ≡↔≡ dropᴾ

@0 swap :
  {x y : A} {z : Finite-subset-of A} →
  x ∷ y ∷ z ≡ y ∷ x ∷ z
swap = _↔_.from ≡↔≡ swapᴾ

@0 is-set : Is-set (Finite-subset-of A)
is-set =
  _↔_.from (H-level↔H-level 2) Finite-subset-of.is-setᴾ

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : Finite-subset-of A → Type p) :
             Type (a ⊔ p) where
  no-eta-equality
  field
    []ʳ        : P []
    ∷ʳ         : ∀ x → P y → P (x ∷ y)
    @0 dropʳ   : ∀ x (p : P y) →
                 P.[ (λ i → P (dropᴾ {x = x} {y = y} i)) ]
                   ∷ʳ x (∷ʳ x p) ≡ ∷ʳ x p
    @0 swapʳ   : ∀ x y (p : P z) →
                 P.[ (λ i → P (swapᴾ {x = x} {y = y} {z = z} i)) ]
                   ∷ʳ x (∷ʳ y p) ≡ ∷ʳ y (∷ʳ x p)
    @0 is-setʳ : ∀ x → P.Is-set (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : Finite-subset-of A) → P x
elimᴾ {A} {P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Finite-subset-of A) → P x
  helper []                    = E.[]ʳ
  helper (x ∷ y)               = E.∷ʳ x (helper y)
  helper (dropᴾ {x} {y} i)     = E.dropʳ x (helper y) i
  helper (swapᴾ {x} {y} {z} i) = E.swapʳ x y (helper z) i
  helper (is-setᴾ x y i j)     =
    P.heterogeneous-UIP
      E.is-setʳ (Finite-subset-of.is-setᴾ x y)
      (λ i → helper (x i)) (λ i → helper (y i)) i j

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    []ʳ        : B
    ∷ʳ         : A → Finite-subset-of A → B → B
    @0 dropʳ   : ∀ x y p →
                 ∷ʳ x (x ∷ y) (∷ʳ x y p) P.≡ ∷ʳ x y p
    @0 swapʳ   : ∀ x y z p →
                 ∷ʳ x (y ∷ z) (∷ʳ y z p) P.≡ ∷ʳ y (x ∷ z) (∷ʳ x z p)
    @0 is-setʳ : P.Is-set B

open Recᴾ public

recᴾ : Recᴾ A B → Finite-subset-of A → B
recᴾ r = elimᴾ e
  where
  module R = Recᴾ r

  e : Elimᴾ _
  e .[]ʳ           = R.[]ʳ
  e .∷ʳ {y} x      = R.∷ʳ x y
  e .dropʳ {y} x   = R.dropʳ x y
  e .swapʳ {z} x y = R.swapʳ x y z
  e .is-setʳ _     = R.is-setʳ

-- A dependent eliminator, expressed using equality.

record Elim {A : Type a} (P : Finite-subset-of A → Type p) :
            Type (a ⊔ p) where
  no-eta-equality
  field
    []ʳ        : P []
    ∷ʳ         : ∀ x → P y → P (x ∷ y)
    @0 dropʳ   : ∀ x (p : P y) →
                 subst P (drop {x = x} {y = y}) (∷ʳ x (∷ʳ x p)) ≡ ∷ʳ x p
    @0 swapʳ   : ∀ x y (p : P z) →
                 subst P (swap {x = x} {y = y} {z = z}) (∷ʳ x (∷ʳ y p))
                   ≡
                 ∷ʳ y (∷ʳ x p)
    @0 is-setʳ : ∀ x → Is-set (P x)

open Elim public

elim : Elim P → (x : Finite-subset-of A) → P x
elim {P} e = elimᴾ e′
  where
  module E = Elim e

  e′ : Elimᴾ P
  e′ .[]ʳ         = E.[]ʳ
  e′ .∷ʳ          = E.∷ʳ
  e′ .dropʳ x p   = subst≡→[]≡ (E.dropʳ x p)
  e′ .swapʳ x y p = subst≡→[]≡ (E.swapʳ x y p)
  e′ .is-setʳ x   = _↔_.to (H-level↔H-level 2) (E.is-setʳ x)

-- A non-dependent eliminator, expressed using equality.

record Rec (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    []ʳ        : B
    ∷ʳ         : A → Finite-subset-of A → B → B
    @0 dropʳ   : ∀ x y p →
                 ∷ʳ x (x ∷ y) (∷ʳ x y p) ≡ ∷ʳ x y p
    @0 swapʳ   : ∀ x y z p →
                 ∷ʳ x (y ∷ z) (∷ʳ y z p) ≡ ∷ʳ y (x ∷ z) (∷ʳ x z p)
    @0 is-setʳ : Is-set B

open Rec public

rec : Rec A B → Finite-subset-of A → B
rec r = recᴾ r′
  where
  module R = Rec r

  r′ : Recᴾ _ _
  r′ .[]ʳ           = R.[]ʳ
  r′ .∷ʳ            = R.∷ʳ
  r′ .dropʳ x y p   = _↔_.to ≡↔≡ (R.dropʳ x y p)
  r′ .swapʳ x y z p = _↔_.to ≡↔≡ (R.swapʳ x y z p)
  r′ .is-setʳ       = _↔_.to (H-level↔H-level 2) R.is-setʳ

-- A dependent eliminator for propositions.

record Elim-prop
         {A : Type a} (P : Finite-subset-of A → Type p) :
         Type (a ⊔ p) where
  no-eta-equality
  field
    []ʳ                : P []
    ∷ʳ                 : ∀ x → P y → P (x ∷ y)
    @0 is-propositionʳ : ∀ x → Is-proposition (P x)

open Elim-prop public

elim-prop : Elim-prop P → (x : Finite-subset-of A) → P x
elim-prop e = elim e′
  where
  module E = Elim-prop e

  e′ : Elim _
  e′ .[]ʳ         = E.[]ʳ
  e′ .∷ʳ          = E.∷ʳ
  e′ .dropʳ _ _   = E.is-propositionʳ _ _ _
  e′ .swapʳ _ _ _ = E.is-propositionʳ _ _ _
  e′ .is-setʳ _   = H-level.mono₁ 1 (E.is-propositionʳ _)

-- A non-dependent eliminator for propositions.

record Rec-prop (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    []ʳ                : B
    ∷ʳ                 : A → Finite-subset-of A → B → B
    @0 is-propositionʳ : Is-proposition B

open Rec-prop public

rec-prop : Rec-prop A B → Finite-subset-of A → B
rec-prop r = elim-prop e
  where
  module R = Rec-prop r

  e : Elim-prop _
  e .[]ʳ               = R.[]ʳ
  e .∷ʳ {y} x          = R.∷ʳ x y
  e .is-propositionʳ _ = R.is-propositionʳ

------------------------------------------------------------------------
-- Some operations

-- Singleton subsets.

singleton : A → Finite-subset-of A
singleton x = x ∷ []

-- The union of two finite subsets.

infixr 5 _∪_

_∪_ :
  Finite-subset-of A → Finite-subset-of A →
  Finite-subset-of A
[]                  ∪ y = y
(x ∷ y)             ∪ z = x ∷ (y ∪ z)
dropᴾ {x} {y} i     ∪ z = dropᴾ {x = x} {y = y ∪ z} i
swapᴾ {x} {y} {z} i ∪ u = swapᴾ {x = x} {y = y} {z = z ∪ u} i
is-setᴾ x y i j     ∪ z = is-setᴾ (λ i → x i ∪ z) (λ i → y i ∪ z) i j

-- [] is a right identity for _∪_.

∪[] :
  (x : Finite-subset-of A) →
  x ∪ [] ≡ x
∪[] = elim-prop e
  where
  e : Elim-prop _
  e .is-propositionʳ _ = is-set
  e .[]ʳ               = refl _
  e .∷ʳ {y} x hyp      =
    x ∷ y ∪ []  ≡⟨ cong (x ∷_) hyp ⟩∎
    x ∷ y       ∎

-- A lemma relating _∪_ and _∷_.

@0 ∪∷ :
  (x : Finite-subset-of A) →
  x ∪ (y ∷ z) ≡ y ∷ x ∪ z
∪∷ {y} {z} = elim-prop e
  where
  e : Elim-prop _
  e .is-propositionʳ _ = is-set

  e .[]ʳ = refl _

  e .∷ʳ {y = u} x hyp =
    (x ∷ u) ∪ (y ∷ z)  ≡⟨⟩
    x ∷ u ∪ (y ∷ z)    ≡⟨ cong (x ∷_) hyp ⟩
    x ∷ y ∷ u ∪ z      ≡⟨ swap ⟩
    y ∷ x ∷ u ∪ z      ≡⟨⟩
    y ∷ (x ∷ u) ∪ z    ∎

-- Union is associative.

assoc :
  (x : Finite-subset-of A) →
  x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
assoc {y} {z} = elim-prop e
  where
  e : Elim-prop _
  e .is-propositionʳ _ = is-set

  e .[]ʳ = refl _

  e .∷ʳ {y = u} x hyp =
    x ∷ u ∪ (y ∪ z)  ≡⟨ cong (x ∷_) hyp ⟩∎
    x ∷ (u ∪ y) ∪ z  ∎

-- Union is commutative (in erased contexts).

@0 comm :
  (x : Finite-subset-of A) →
  x ∪ y ≡ y ∪ x
comm {y} = elim-prop e
  where
  e : Elim-prop _
  e .is-propositionʳ _ = is-set

  e .[]ʳ =
    [] ∪ y  ≡⟨⟩
    y       ≡⟨ sym (∪[] y) ⟩∎
    y ∪ []  ∎

  e .∷ʳ {y = z} x hyp =
    x ∷ z ∪ y    ≡⟨ cong (x ∷_) hyp ⟩
    x ∷ y ∪ z    ≡⟨ sym (∪∷ y) ⟩∎
    y ∪ (x ∷ z)  ∎

-- Union is idempotent (in erased contexts).

@0 idem : (x : Finite-subset-of A) → x ∪ x ≡ x
idem = elim-prop e
  where
  e : Elim-prop _
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

-- Union distributes from the left and right over union (in erased
-- contexts).

@0 ∪-distrib-left : ∀ x → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ (x ∪ z)
∪-distrib-left {y} {z} x =
  x ∪ (y ∪ z)        ≡⟨ cong (_∪ _) $ sym (idem x) ⟩
  (x ∪ x) ∪ (y ∪ z)  ≡⟨ sym $ assoc x ⟩
  x ∪ (x ∪ (y ∪ z))  ≡⟨ cong (x ∪_) $ assoc x ⟩
  x ∪ ((x ∪ y) ∪ z)  ≡⟨ cong ((x ∪_) ∘ (_∪ _)) $ comm x ⟩
  x ∪ ((y ∪ x) ∪ z)  ≡⟨ cong (x ∪_) $ sym $ assoc y ⟩
  x ∪ (y ∪ (x ∪ z))  ≡⟨ assoc x ⟩∎
  (x ∪ y) ∪ (x ∪ z)  ∎

@0 ∪-distrib-right : ∀ x → (x ∪ y) ∪ z ≡ (x ∪ z) ∪ (y ∪ z)
∪-distrib-right {y} {z} x =
  (x ∪ y) ∪ z        ≡⟨ comm (x ∪ _) ⟩
  z ∪ (x ∪ y)        ≡⟨ ∪-distrib-left z ⟩
  (z ∪ x) ∪ (z ∪ y)  ≡⟨ cong₂ _∪_ (comm z) (comm z) ⟩∎
  (x ∪ z) ∪ (y ∪ z)  ∎

-- A map function.

map : (A → B) → Finite-subset-of A → Finite-subset-of B
map f = recᴾ r
  where
  r : Recᴾ _ _
  r .[]ʳ           = []
  r .∷ʳ x _ y      = f x ∷ y
  r .dropʳ _ _ _   = dropᴾ
  r .swapʳ _ _ _ _ = swapᴾ
  r .is-setʳ       = is-setᴾ

-- Join.

join : Finite-subset-of (Finite-subset-of A) → Finite-subset-of A
join = rec r
  where
  r : Rec _ _
  r .[]ʳ           = []
  r .∷ʳ x _        = x ∪_
  r .dropʳ x y z   = x ∪ x ∪ z    ≡⟨ assoc x ⟩
                     (x ∪ x) ∪ z  ≡⟨ cong (_∪ _) (idem x) ⟩∎
                     x ∪ z        ∎
  r .swapʳ x y z u = x ∪ y ∪ u    ≡⟨ assoc x ⟩
                     (x ∪ y) ∪ u  ≡⟨ cong (_∪ _) (comm x) ⟩
                     (y ∪ x) ∪ u  ≡⟨ sym (assoc y) ⟩∎
                     y ∪ x ∪ u    ∎
  r .is-setʳ       = is-set

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ :
  Finite-subset-of A → (A → Finite-subset-of B) → Finite-subset-of B
x >>=′ f = join (map f x)

-- Bind distributes from the right over union.

>>=-right-distributive :
  ∀ x → (x ∪ y) >>=′ f ≡ (x >>=′ f) ∪ (y >>=′ f)
>>=-right-distributive {y} {f} = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ               = refl _
  e .is-propositionʳ _ = is-set
  e .∷ʳ {y = z} x hyp  =
    ((x ∷ z) ∪ y) >>=′ f             ≡⟨⟩
    f x ∪ ((z ∪ y) >>=′ f)           ≡⟨ cong (f x ∪_) hyp ⟩
    f x ∪ ((z >>=′ f) ∪ (y >>=′ f))  ≡⟨ assoc (f x) ⟩
    (f x ∪ (z >>=′ f)) ∪ (y >>=′ f)  ≡⟨⟩
    ((x ∷ z) >>=′ f) ∪ (y >>=′ f)    ∎

-- Bind distributes from the left over union (in erased contexts).

@0 >>=-left-distributive :
  ∀ x → (x >>=′ λ x → f x ∪ g x) ≡ (x >>=′ f) ∪ (x >>=′ g)
>>=-left-distributive {f} {g} = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ               = refl _
  e .is-propositionʳ _ = is-set
  e .∷ʳ {y} x hyp      =
    (x ∷ y) >>=′ (λ x → f x ∪ g x)           ≡⟨⟩
    (f x ∪ g x) ∪ (y >>=′ λ x → f x ∪ g x)   ≡⟨ cong ((f x ∪ g x) ∪_) hyp ⟩
    (f x ∪ g x) ∪ ((y >>=′ f) ∪ (y >>=′ g))  ≡⟨ sym (assoc (f x)) ⟩
    f x ∪ (g x ∪ ((y >>=′ f) ∪ (y >>=′ g)))  ≡⟨ cong (f x ∪_) (assoc (g x)) ⟩
    f x ∪ ((g x ∪ (y >>=′ f)) ∪ (y >>=′ g))  ≡⟨ cong ((f x ∪_) ∘ (_∪ (y >>=′ g))) (comm (g x)) ⟩
    f x ∪ (((y >>=′ f) ∪ g x) ∪ (y >>=′ g))  ≡⟨ cong (f x ∪_) (sym (assoc (y >>=′ f))) ⟩
    f x ∪ ((y >>=′ f) ∪ (g x ∪ (y >>=′ g)))  ≡⟨ assoc (f x) ⟩
    (f x ∪ (y >>=′ f)) ∪ (g x ∪ (y >>=′ g))  ≡⟨⟩
    ((x ∷ y) >>=′ f) ∪ ((x ∷ y) >>=′ g)      ∎

-- Monad laws.

singleton->>= :
  (f : A → Finite-subset-of B) →
  singleton x >>=′ f ≡ f x
singleton->>= {x} f =
  f x ∪ []  ≡⟨ ∪[] _ ⟩∎
  f x       ∎

>>=-singleton : x >>=′ singleton ≡ x
>>=-singleton = elim-prop e _
  where
  e : Elim-prop (λ x → x >>=′ singleton ≡ x)
  e .[]ʳ               = refl _
  e .is-propositionʳ _ = is-set
  e .∷ʳ {y} x hyp      =
    x ∷ (y >>=′ singleton)  ≡⟨ cong (_ ∷_) hyp ⟩∎
    x ∷ y                   ∎

>>=-assoc : ∀ x → x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
>>=-assoc {f} {g} = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ               = refl _
  e .is-propositionʳ _ = is-set
  e .∷ʳ {y} x hyp      =
    (x ∷ y) >>=′ (λ x → f x >>=′ g)           ≡⟨⟩
    (f x >>=′ g) ∪ (y >>=′ λ x → f x >>=′ g)  ≡⟨ cong ((f x >>=′ g) ∪_) hyp ⟩
    (f x >>=′ g) ∪ (y >>=′ f >>=′ g)          ≡⟨ sym (>>=-right-distributive (f x)) ⟩
    (f x ∪ (y >>=′ f)) >>=′ g                 ≡⟨⟩
    (x ∷ y) >>=′ f >>=′ g                     ∎

-- A monad instance.

instance

  raw-monad : Raw-monad {d = a} Finite-subset-of
  raw-monad .M.return = singleton
  raw-monad .M._>>=_  = _>>=′_

  monad : Monad {d = a} Finite-subset-of
  monad .M.Monad.raw-monad           = raw-monad
  monad .M.Monad.left-identity _     = singleton->>=
  monad .M.Monad.right-identity _    = >>=-singleton
  monad .M.Monad.associativity x _ _ = >>=-assoc x

------------------------------------------------------------------------
-- Membership

private

  -- Membership is used to define _∈_ and ∈-propositional below.
  --
  -- The definition uses _∥⊎∥_. If it suffices for ∈-propositional to
  -- be erased, then one can use
  -- H-level.Truncation.Propositional.Erased._∥⊎∥ᴱ_ instead of _∥⊎∥_.
  -- However, in practice it might make sense to erase all membership
  -- proofs, in which case it does not matter whether the code uses
  -- _∥⊎∥_ or H-level.Truncation.Propositional.Erased._∥⊎∥ᴱ_.

  Membership :
    {A : Type a} →
    A → Finite-subset-of A → Proposition a
  Membership x = rec r
    where
    r : Rec _ _
    r .[]ʳ = ⊥ , ⊥-propositional

    r .∷ʳ y z (x∈z , _) =
      (x ≡ y ∥⊎∥ x∈z) , Trunc.truncation-is-proposition

    r .dropʳ y z (P , P-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (x ≡ y ∥⊎∥ x ≡ y ∥⊎∥ P    ↔⟨ Trunc.∥⊎∥-assoc ⟩
         (x ≡ y ∥⊎∥ x ≡ y) ∥⊎∥ P  ↔⟨ Trunc.idempotent Trunc.∥⊎∥-cong F.id ⟩
         ∥ x ≡ y ∥ ∥⊎∥ P          ↔⟨ inverse Trunc.truncate-left-∥⊎∥ ⟩□
         x ≡ y ∥⊎∥ P              □)

    r .swapʳ y z u (P , P-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (x ≡ y ∥⊎∥ x ≡ z ∥⊎∥ P    ↔⟨ Trunc.∥⊎∥-assoc ⟩
         (x ≡ y ∥⊎∥ x ≡ z) ∥⊎∥ P  ↔⟨ (Trunc.∥⊎∥-comm Trunc.∥⊎∥-cong F.id) ⟩
         (x ≡ z ∥⊎∥ x ≡ y) ∥⊎∥ P  ↔⟨ inverse Trunc.∥⊎∥-assoc ⟩□
         x ≡ z ∥⊎∥ x ≡ y ∥⊎∥ P    □)

    r .is-setʳ =
      Univ.∃-H-level-H-level-1+ ext univ 1

-- Membership.
--
-- The type is wrapped to make it easier for Agda to infer the subset
-- argument.

private module Dummy where

  infix 4 _∈_

  record _∈_
    {A : Type a} (x : A) (y : Finite-subset-of A) : Type a where
    constructor box
    field
      unbox : proj₁ (Membership x y)

open Dummy public using (_∈_) hiding (module _∈_)

-- The negation of membership.

infix 4 _∉_

_∉_ : {A : Type a} → A → Finite-subset-of A → Type a
x ∉ y = ¬ x ∈ y

private

  -- An unfolding lemma.

  ∈≃ : (x ∈ y) ≃ proj₁ (Membership x y)
  ∈≃ = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = Dummy._∈_.unbox
        ; from = Dummy.box
        }
      ; right-inverse-of = refl
      }
    ; left-inverse-of = refl
    })

-- Membership is propositional.

∈-propositional : Is-proposition (x ∈ y)
∈-propositional {x} {y} =                  $⟨ proj₂ (Membership x y) ⟩
  Is-proposition (proj₁ (Membership x y))  →⟨ H-level-cong _ 1 (inverse ∈≃) ⟩□
  Is-proposition (x ∈ y)                   □

-- A lemma characterising [].

∈[]≃ : (x ∈ []) ≃ ⊥₀
∈[]≃ {x} =
  x ∈ []  ↝⟨ ∈≃ ⟩
  ⊥       ↔⟨ ⊥↔⊥ ⟩□
  ⊥₀      □

-- A lemma characterising _∷_.

∈∷≃ : (x ∈ y ∷ z) ≃ (x ≡ y ∥⊎∥ x ∈ z)
∈∷≃ {x} {y} {z} =
  x ∈ y ∷ z                         ↝⟨ ∈≃ ⟩
  x ≡ y ∥⊎∥ proj₁ (Membership x z)  ↝⟨ F.id Trunc.∥⊎∥-cong inverse ∈≃ ⟩□
  x ≡ y ∥⊎∥ x ∈ z                   □

-- A variant.

∈≢∷≃ : x ≢ y → (x ∈ y ∷ z) ≃ (x ∈ z)
∈≢∷≃ {x} {y} {z} x≢y =
  x ∈ y ∷ z        ↝⟨ ∈∷≃ ⟩
  x ≡ y ∥⊎∥ x ∈ z  ↔⟨ Trunc.drop-⊥-left-∥⊎∥ ∈-propositional x≢y ⟩□
  x ∈ z            □

-- A lemma characterising singleton.

∈singleton≃ :
  (x ∈ singleton y) ≃ ∥ x ≡ y ∥
∈singleton≃ {x} {y} =
  x ∈ singleton y   ↝⟨ ∈∷≃ ⟩
  x ≡ y ∥⊎∥ x ∈ []  ↔⟨ Trunc.∥∥-cong $ drop-⊥-right ∈[]≃ ⟩□
  ∥ x ≡ y ∥         □

-- Some "introduction rules" for _∈_.

∈→∈∷ : x ∈ z → x ∈ y ∷ z
∈→∈∷ {x} {z} {y} =
  x ∈ z            →⟨ ∣_∣ ∘ inj₂ ⟩
  x ≡ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∷≃ ⟩□
  x ∈ y ∷ z        □

∥≡∥→∈∷ : ∥ x ≡ y ∥ → x ∈ y ∷ z
∥≡∥→∈∷ {x} {y} {z} =
  ∥ x ≡ y ∥        →⟨ Trunc.∥∥-map inj₁ ⟩
  x ≡ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∷≃ ⟩□
  x ∈ y ∷ z        □

≡→∈∷ : x ≡ y → x ∈ y ∷ z
≡→∈∷ = ∥≡∥→∈∷ ∘ ∣_∣

∥≡∥→∈singleton : ∥ x ≡ y ∥ → x ∈ singleton y
∥≡∥→∈singleton = ∥≡∥→∈∷

≡→∈singleton : x ≡ y → x ∈ singleton y
≡→∈singleton = ≡→∈∷

-- Membership of a union of two subsets can be expressed in terms of
-- membership of the subsets.

∈∪≃ : (x ∈ y ∪ z) ≃ (x ∈ y ∥⊎∥ x ∈ z)
∈∪≃ {x} {y} {z} = elim-prop e y
  where
  e : Elim-prop (λ y → (x ∈ y ∪ z) ≃ (x ∈ y ∥⊎∥ x ∈ z))
  e .[]ʳ =
    x ∈ z             ↔⟨ inverse $ Trunc.∥∥↔ ∈-propositional ⟩
    ∥ x ∈ z ∥         ↔⟨ Trunc.∥∥-cong (inverse $ drop-⊥-left ∈[]≃) ⟩□
    x ∈ [] ∥⊎∥ x ∈ z  □

  e .∷ʳ {y = u} y hyp =
    x ∈ y ∷ u ∪ z                ↝⟨ ∈∷≃ ⟩
    x ≡ y ∥⊎∥ x ∈ u ∪ z          ↝⟨ F.id Trunc.∥⊎∥-cong hyp ⟩
    x ≡ y ∥⊎∥ x ∈ u ∥⊎∥ x ∈ z    ↔⟨ Trunc.∥⊎∥-assoc ⟩
    (x ≡ y ∥⊎∥ x ∈ u) ∥⊎∥ x ∈ z  ↝⟨ Trunc.∥∥-cong (inverse ∈∷≃ ⊎-cong F.id) ⟩□
    x ∈ y ∷ u ∥⊎∥ x ∈ z          □

  e .is-propositionʳ _ =
    Eq.left-closure ext 0 ∈-propositional

-- More "introduction rules".

∈→∈∪ˡ : x ∈ y → x ∈ y ∪ z
∈→∈∪ˡ {x} {y} {z} =
  x ∈ y            →⟨ ∣_∣ ∘ inj₁ ⟩
  x ∈ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∪≃ ⟩□
  x ∈ y ∪ z        □

∈→∈∪ʳ : ∀ y → x ∈ z → x ∈ y ∪ z
∈→∈∪ʳ {x} {z} y =
  x ∈ z            →⟨ ∣_∣ ∘ inj₂ ⟩
  x ∈ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∪≃ ⟩□
  x ∈ y ∪ z        □

-- A lemma characterising join.

∈join≃ : (x ∈ join z) ≃ ∥ (∃ λ y → x ∈ y × y ∈ z) ∥
∈join≃ {x} = elim-prop e _
  where
  e : Elim-prop (λ z → (x ∈ join z) ≃ ∥ (∃ λ y → x ∈ y × y ∈ z) ∥)
  e .[]ʳ =
    x ∈ join []                   ↔⟨⟩
    x ∈ []                        ↝⟨ ∈[]≃ ⟩
    ⊥                             ↔⟨ inverse $ Trunc.∥∥↔ ⊥-propositional ⟩
    ∥ ⊥ ∥                         ↔⟨ Trunc.∥∥-cong (inverse (×-right-zero {ℓ₁ = lzero} F.∘
                                                             ∃-cong (λ _ → ×-right-zero))) ⟩
    ∥ (∃ λ y → x ∈ y × ⊥) ∥       ↝⟨ Trunc.∥∥-cong (∃-cong λ _ → ∃-cong λ _ → inverse ∈[]≃) ⟩□
    ∥ (∃ λ y → x ∈ y × y ∈ []) ∥  □
  e .∷ʳ {y = z} u hyp =
    x ∈ join (u ∷ z)                                     ↔⟨⟩
    x ∈ u ∪ join z                                       ↝⟨ ∈∪≃ ⟩
    x ∈ u ∥⊎∥ x ∈ join z                                 ↝⟨ F.id Trunc.∥⊎∥-cong hyp ⟩
    x ∈ u ∥⊎∥ ∥ (∃ λ y → x ∈ y × y ∈ z) ∥                ↔⟨ inverse Trunc.truncate-right-∥⊎∥ ⟩
    x ∈ u ∥⊎∥ (∃ λ y → x ∈ y × y ∈ z)                    ↔⟨ ∃-intro _ _ Trunc.∥⊎∥-cong F.id ⟩
    (∃ λ y → x ∈ y × y ≡ u) ∥⊎∥ (∃ λ y → x ∈ y × y ∈ z)  ↔⟨ Trunc.∥∥-cong $ inverse $
                                                            ∃-⊎-distrib-left F.∘
                                                            (∃-cong λ _ → ∃-⊎-distrib-left) ⟩
    ∥ (∃ λ y → x ∈ y × (y ≡ u ⊎ y ∈ z)) ∥                ↔⟨ inverse $
                                                            Trunc.flatten′
                                                              (λ F → ∃ λ y → x ∈ y × F (y ≡ u ⊎ y ∈ z))
                                                              (λ f → Σ-map id (Σ-map id f))
                                                              (λ (y , p , q) → Trunc.∥∥-map (λ q → y , p , q) q) ⟩
    ∥ (∃ λ y → x ∈ y × (y ≡ u ∥⊎∥ y ∈ z)) ∥              ↝⟨ (Trunc.∥∥-cong $ ∃-cong λ _ → ∃-cong λ _ → inverse ∈∷≃) ⟩□
    ∥ (∃ λ y → x ∈ y × y ∈ u ∷ z) ∥                      □
  e .is-propositionʳ _ =
    Eq.left-closure ext 0 ∈-propositional

-- If truncated equality is decidable, then membership is also
-- decidable.

member? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec (x ∈ y)
member? equal? x = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ          = no λ ()
  e .∷ʳ {y = z} y = case equal? x y of λ where
    (yes ∥x≡y∥) _ → yes (∥≡∥→∈∷ ∥x≡y∥)
    (no ¬∥x≡y∥)   →
      P.[ (λ x∈z → yes (∈→∈∷ x∈z))
        , (λ x∉z → no (
             x ∈ y ∷ z        ↔⟨ ∈∷≃ ⟩
             x ≡ y ∥⊎∥ x ∈ z  →⟨ Trunc.∥∥-map P.[ ¬∥x≡y∥ ∘ ∣_∣ , x∉z ] ⟩
             ∥ ⊥ ∥            ↔⟨ Trunc.not-inhabited⇒∥∥↔⊥ id ⟩□
             ⊥                □))
        ]
  e .is-propositionʳ y =
    Dec-closure-propositional ext ∈-propositional

-- A variant of member? that uses Dec-Erased instead of Dec.

member?ᴱ :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec-Erased (x ∈ y)
member?ᴱ equal? x = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ          = no [ (λ ()) ]
  e .∷ʳ {y = z} y = case equal? x y of λ where
    (yes [ ∥x≡y∥ ]) _ → yes [ ∥≡∥→∈∷ ∥x≡y∥ ]
    (no [ ¬∥x≡y∥ ])   →
      P.[ (λ ([ x∈z ]) → yes [ ∈→∈∷ x∈z ])
        , (λ ([ x∉z ]) → no [
             x ∈ y ∷ z        ↔⟨ ∈∷≃ ⟩
             x ≡ y ∥⊎∥ x ∈ z  →⟨ Trunc.∥∥-map P.[ ¬∥x≡y∥ ∘ ∣_∣ , x∉z ] ⟩
             ∥ ⊥ ∥            ↔⟨ Trunc.not-inhabited⇒∥∥↔⊥ id ⟩□
             ⊥                □ ])
        ]
  e .is-propositionʳ y =
    EC.Is-proposition-Dec-Erased ext ∈-propositional

-- If x is a member of y, then x ∷ y is equal to y (in erased
-- contexts).

@0 ∈→∷≡ : x ∈ y → x ∷ y ≡ y
∈→∷≡ {x} = elim-prop e _
  where
  e : Elim-prop (λ y → x ∈ y → x ∷ y ≡ y)
  e .∷ʳ {y} z hyp =
    x ∈ z ∷ y            ↔⟨ ∈∷≃ ⟩
    x ≡ z ∥⊎∥ x ∈ y      →⟨ id Trunc.∥⊎∥-cong hyp ⟩
    x ≡ z ∥⊎∥ x ∷ y ≡ y  →⟨ Trunc.rec is-set
                              P.[ (λ x≡z →
      x ∷ z ∷ y                    ≡⟨ cong (λ x → x ∷ _) x≡z ⟩
      z ∷ z ∷ y                    ≡⟨ drop ⟩∎
      z ∷ y                        ∎)
                                , (λ x∷y≡y →
      x ∷ z ∷ y                    ≡⟨ swap ⟩
      z ∷ x ∷ y                    ≡⟨ cong (_ ∷_) x∷y≡y ⟩∎
      z ∷ y                        ∎)
                                ] ⟩□
    x ∷ z ∷ y ≡ z ∷ y    □

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    is-set

------------------------------------------------------------------------
-- Subsets of subsets

-- Subsets.

infix 4 _⊆_

_⊆_ : {A : Type a} → Finite-subset-of A → Finite-subset-of A → Type a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- _⊆_ is pointwise propositional.

⊆-propositional : Is-proposition (x ⊆ y)
⊆-propositional =
  Π-closure ext 1 λ _ →
  Π-closure ext 1 λ _ →
  ∈-propositional

-- The subset property can be expressed using _∪_ and _≡_ (in erased
-- contexts).

@0 ⊆≃∪≡ : ∀ x → (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {y} x =
  Eq.⇔→≃
    (Π-closure ext 1 λ _ →
     Π-closure ext 1 λ _ →
     ∈-propositional)
    is-set
    (elim-prop e x)
    (λ p z →
       z ∈ x      →⟨ ∈→∈∪ˡ ⟩
       z ∈ x ∪ y  →⟨ ≡⇒↝ _ (cong (z ∈_) p) ⟩□
       z ∈ y      □)
  where
  e : Elim-prop (λ x → x ⊆ y → x ∪ y ≡ y)
  e .[]ʳ _ =
    [] ∪ y  ≡⟨⟩
    y       ∎

  e .∷ʳ {y = z} x hyp x∷z⊆y =
    x ∷ z ∪ y  ≡⟨ cong (x ∷_) (hyp (λ _ → x∷z⊆y _ ∘ ∈→∈∷)) ⟩
    x ∷ y      ≡⟨ ∈→∷≡ (x∷z⊆y x (≡→∈∷ (refl _))) ⟩∎
    y          ∎

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    is-set

-- A form of extensionality that holds in erased contexts.

@0 extensionality : (x ≡ y) ≃ (∀ z → z ∈ x ⇔ z ∈ y)
extensionality {x} {y} =
  Eq.⇔→≃
    is-set
    (Π-closure ext 1 λ _ →
     ⇔-closure ext 1
       ∈-propositional
       ∈-propositional)
    (λ x≡y z → ≡⇒↝ _ (cong (z ∈_) x≡y))
    ((∀ z → z ∈ x ⇔ z ∈ y)  →⟨ (λ p → _⇔_.to ∘ p , _⇔_.from ∘ p) ⟩
     x ⊆ y × y ⊆ x          ↔⟨ ⊆≃∪≡ x ×-cong ⊆≃∪≡ y ⟩
     x ∪ y ≡ y × y ∪ x ≡ x  →⟨ (λ (p , q) → trans (sym q) (trans (comm y) p)) ⟩□
     x ≡ y                  □)

-- Another way to characterise equality (in erased contexts).

@0 ≡≃⊆×⊇ : (x ≡ y) ≃ (x ⊆ y × y ⊆ x)
≡≃⊆×⊇ {x} {y} =
  x ≡ y                  ↝⟨ extensionality ⟩
  (∀ z → z ∈ x ⇔ z ∈ y)  ↝⟨ Eq.⇔→≃
                              (Π-closure ext 1 λ _ →
                               ⇔-closure ext 1
                                 ∈-propositional
                                 ∈-propositional)
                              (×-closure 1 ⊆-propositional ⊆-propositional)
                              (λ hyp → _⇔_.to ∘ hyp , _⇔_.from ∘ hyp)
                              (λ (x⊆y , y⊆x) z → record { to = x⊆y z ; from = y⊆x z }) ⟩□
  x ⊆ y × y ⊆ x          □

-- The empty set is not equal to a set constructed using _∷_.

[]≢∷ : Finite-subset-of.[] ≢ x ∷ y
[]≢∷ {x} {y} =
  EC.Very-stable→Stable 0 (EC.Very-stable-¬ ext)
    [ [] ≡ x ∷ y                  ↔⟨ extensionality ⟩
      (∀ z → z ∈ [] ⇔ z ∈ x ∷ y)  →⟨ (λ hyp → _⇔_.from (hyp x) (≡→∈∷ (refl _))) ⟩
      x ∈ []                      ↔⟨ ∈[]≃ ⟩□
      ⊥                           □
    ]

-- _⊆_ is a partial order (in erased contexts).

⊆-refl : x ⊆ x
⊆-refl _ = id

⊆-trans : x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans x⊆y y⊆z _ = y⊆z _ ∘ x⊆y _

@0 ⊆-antisymmetric : x ⊆ y → y ⊆ x → x ≡ y
⊆-antisymmetric = curry (_≃_.from ≡≃⊆×⊇)

-- If truncated equality is decidable, then _⊆_ is also decidable.

subset? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x y : Finite-subset-of A) → Dec (x ⊆ y)
subset? equal? x y = elim-prop r x
  where
  r : Elim-prop (λ x → Dec (x ⊆ y))
  r .[]ʳ = yes λ z →
    z ∈ []  ↔⟨ ∈[]≃ ⟩
    ⊥       →⟨ ⊥-elim ⟩□
    z ∈ y   □

  r .∷ʳ {y = x} z =
    Dec (x ⊆ y)                          →⟨ member? equal? z y ,_ ⟩
    Dec (z ∈ y) × Dec (x ⊆ y)            →⟨ uncurry
                                              P.[ (λ z∈y → Dec-map (
        x ⊆ y                                        ↝⟨ record
                                                          { to = λ x⊆y u →
                                                                   P.[ (λ u≡z → subst (_∈ y) (sym u≡z) z∈y)
                                                                     , x⊆y u
                                                                     ]
                                                          ; from = λ hyp u → hyp u ∘ inj₂
                                                          } ⟩
        (∀ u → u ≡ z ⊎ u ∈ x → u ∈ y)                ↔⟨ (∀-cong ext λ _ → inverse $
                                                         Trunc.universal-property ∈-propositional) ⟩
        (∀ u → u ≡ z ∥⊎∥ u ∈ x → u ∈ y)              ↝⟨ (∀-cong _ λ _ → →-cong₁ _ (inverse ∈∷≃)) ⟩
        (∀ u → u ∈ z ∷ x → u ∈ y)                    ↔⟨⟩
        z ∷ x ⊆ y                                    □))
                                                , (λ z∉y _ → no (
        z ∷ x ⊆ y                                    →⟨ (λ z∷x⊆y → z∷x⊆y z (≡→∈∷ (refl _))) ⟩
        z ∈ y                                        →⟨ z∉y ⟩□
        ⊥                                            □))
                                                ] ⟩□
    Dec (z ∷ x ⊆ y)                      □

  r .is-propositionʳ _ =
    Dec-closure-propositional ext ⊆-propositional

-- A variant of subset? that uses Dec-Erased.

subset?ᴱ :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x y : Finite-subset-of A) → Dec-Erased (x ⊆ y)
subset?ᴱ equal? x y = elim-prop r x
  where
  r : Elim-prop (λ x → Dec-Erased (x ⊆ y))
  r .[]ʳ = yes [ (λ z →
    z ∈ []  ↔⟨ ∈[]≃ ⟩
    ⊥       →⟨ ⊥-elim ⟩□
    z ∈ y   □ )]

  r .∷ʳ {y = x} z =
    Dec-Erased (x ⊆ y)                       →⟨ member?ᴱ equal? z y ,_ ⟩
    Dec-Erased (z ∈ y) × Dec-Erased (x ⊆ y)  →⟨ uncurry
                                                P.[ (λ ([ z∈y ]) → EC.Dec-Erased-map (
        x ⊆ y                                          ↝⟨ record
                                                            { to = λ x⊆y u →
                                                                     P.[ (λ u≡z → subst (_∈ y) (sym u≡z) z∈y)
                                                                       , x⊆y u
                                                                       ]
                                                            ; from = λ hyp u → hyp u ∘ inj₂
                                                            } ⟩
        (∀ u → u ≡ z ⊎ u ∈ x → u ∈ y)                  ↔⟨ (∀-cong ext λ _ → inverse $
                                                           Trunc.universal-property ∈-propositional) ⟩
        (∀ u → u ≡ z ∥⊎∥ u ∈ x → u ∈ y)                ↝⟨ (∀-cong _ λ _ → →-cong₁ _ (inverse ∈∷≃)) ⟩
        (∀ u → u ∈ z ∷ x → u ∈ y)                      ↔⟨⟩
        z ∷ x ⊆ y                                      □))
                                                  , (λ ([ z∉y ]) _ → no [
        z ∷ x ⊆ y                                      →⟨ (λ z∷x⊆y → z∷x⊆y z (≡→∈∷ (refl _))) ⟩
        z ∈ y                                          →⟨ z∉y ⟩□
        ⊥                                              □ ])
                                                  ] ⟩□
    Dec-Erased (z ∷ x ⊆ y)                   □

  r .is-propositionʳ _ =
    EC.Is-proposition-Dec-Erased ext ⊆-propositional

-- If truncated equality is decidable, then _≡_ is also decidable (in
-- erased contexts).

@0 equal? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x y : Finite-subset-of A) → Dec (x ≡ y)
equal? eq? x y =             $⟨ subset? eq? x y , subset? eq? y x ⟩
  Dec (x ⊆ y) × Dec (y ⊆ x)  →⟨ uncurry Dec-× ⟩
  Dec (x ⊆ y × y ⊆ x)        →⟨ Dec-map (from-equivalence $ inverse ≡≃⊆×⊇) ⟩□
  Dec (x ≡ y)                □

-- A variant of equal? that uses Dec-Erased, and that is not
-- restricted to erased contexts.

equal?ᴱ :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x y : Finite-subset-of A) → Dec-Erased (x ≡ y)
equal?ᴱ eq? x y =                              $⟨ subset?ᴱ eq? x y , subset?ᴱ eq? y x ⟩
  Dec-Erased (x ⊆ y) × Dec-Erased (y ⊆ x)      →⟨ EC.Dec-Erased↔Dec-Erased _ ×-cong EC.Dec-Erased↔Dec-Erased _ ⟩
  Dec (Erased (x ⊆ y)) × Dec (Erased (y ⊆ x))  →⟨ uncurry Dec-× ⟩
  Dec (Erased (x ⊆ y) × Erased (y ⊆ x))        →⟨ Dec-map (from-isomorphism $ inverse EC.Erased-Σ↔Σ) ⟩
  Dec (Erased (x ⊆ y × y ⊆ x))                 →⟨ _⇔_.from $ EC.Dec-Erased↔Dec-Erased _ ⟩
  Dec-Erased (x ⊆ y × y ⊆ x)                   →⟨ EC.Dec-Erased-map (from-equivalence $ inverse ≡≃⊆×⊇) ⟩□
  Dec-Erased (x ≡ y)                           □

------------------------------------------------------------------------
-- The functions map-Maybe, filter, minus and delete

private

  -- A function used to define map-Maybe.

  map-Maybe-cons : Maybe B → Finite-subset-of B → Finite-subset-of B
  map-Maybe-cons nothing  y = y
  map-Maybe-cons (just x) y = x ∷ y

-- A combination of map and filter.

map-Maybe : (A → Maybe B) → Finite-subset-of A → Finite-subset-of B
map-Maybe f = rec r
  where
  r : Rec _ _
  r .[]ʳ         = []

  r .∷ʳ x _ y    = map-Maybe-cons (f x) y

  r .is-setʳ     = is-set

  r .dropʳ x _ y = lemma (f x)
    where
    lemma :
      ∀ m → map-Maybe-cons m (map-Maybe-cons m y) ≡ map-Maybe-cons m y
    lemma nothing  = refl _
    lemma (just _) = drop

  r .swapʳ x y _ z = lemma (f x) (f y)
    where
    lemma :
      ∀ m₁ m₂ →
      map-Maybe-cons m₁ (map-Maybe-cons m₂ z) ≡
      map-Maybe-cons m₂ (map-Maybe-cons m₁ z)
    lemma (just _) (just _) = swap
    lemma _        nothing  = refl _
    lemma nothing  _        = refl _

-- A lemma characterising map-Maybe.

∈map-Maybe≃ :
  (x ∈ map-Maybe f y) ≃ ∥ (∃ λ z → z ∈ y × f z ≡ just x) ∥
∈map-Maybe≃ {x} {f} = elim-prop e _
  where
  e : Elim-prop (λ y → (x ∈ map-Maybe f y) ≃
                       ∥ (∃ λ z → z ∈ y × f z ≡ just x) ∥)
  e .[]ʳ =
    x ∈ map-Maybe f []                   ↝⟨ ∈[]≃ ⟩
    ⊥                                    ↔⟨ inverse $ Trunc.∥∥↔ ⊥-propositional ⟩
    ∥ ⊥ ∥                                ↔⟨ Trunc.∥∥-cong (inverse (×-right-zero {ℓ₁ = lzero} F.∘
                                                                    ∃-cong (λ _ → ×-left-zero))) ⟩
    ∥ (∃ λ z → ⊥ × f z ≡ just x) ∥       ↝⟨ Trunc.∥∥-cong (∃-cong λ _ → inverse ∈[]≃ ×-cong F.id) ⟩□
    ∥ (∃ λ z → z ∈ [] × f z ≡ just x) ∥  □

  e .∷ʳ {y} z hyp =
    (x ∈ map-Maybe f (z ∷ y))                                          ↝⟨ lemma _ _ ⟩
    f z ≡ just x ∥⊎∥ (x ∈ map-Maybe f y)                               ↝⟨ from-isomorphism (inverse Trunc.truncate-right-∥⊎∥) F.∘
                                                                          (F.id Trunc.∥⊎∥-cong hyp) ⟩
    f z ≡ just x ∥⊎∥ (∃ λ u → u ∈ y × f u ≡ just x)                    ↔⟨ inverse $
                                                                          drop-⊤-left-Σ (_⇔_.to contractible⇔↔⊤ $ singleton-contractible _) F.∘
                                                                          Σ-assoc Trunc.∥⊎∥-cong F.id ⟩
    (∃ λ u → u ≡ z × f u ≡ just x) ∥⊎∥ (∃ λ u → u ∈ y × f u ≡ just x)  ↔⟨ Trunc.∥∥-cong $ inverse ∃-⊎-distrib-left ⟩
    ∥ (∃ λ u → u ≡ z × f u ≡ just x ⊎ u ∈ y × f u ≡ just x) ∥          ↔⟨ Trunc.∥∥-cong (∃-cong λ _ → inverse ∃-⊎-distrib-right) ⟩
    ∥ (∃ λ u → (u ≡ z ⊎ u ∈ y) × f u ≡ just x) ∥                       ↔⟨ inverse $
                                                                          Trunc.flatten′
                                                                            (λ F → (∃ λ u → F (u ≡ z ⊎ u ∈ y) × f u ≡ just x))
                                                                            (λ f → Σ-map id (Σ-map f id))
                                                                            (λ (u , p , q) → Trunc.∥∥-map (λ p → u , p , q) p) ⟩
    ∥ (∃ λ u → (u ≡ z ∥⊎∥ u ∈ y) × f u ≡ just x) ∥                     ↝⟨ Trunc.∥∥-cong (∃-cong λ _ → ×-cong₁ λ _ → inverse ∈∷≃) ⟩□
    ∥ (∃ λ u → u ∈ z ∷ y × f u ≡ just x) ∥                             □
    where
    lemma : ∀ m y → (x ∈ map-Maybe-cons m y) ≃ (m ≡ just x ∥⊎∥ x ∈ y)
    lemma nothing y =
      x ∈ map-Maybe-cons nothing y  ↔⟨⟩
      x ∈ y                         ↔⟨ inverse $ Trunc.drop-⊥-left-∥⊎∥ ∈-propositional ⊎.inj₁≢inj₂ ⟩□
      (nothing ≡ just x ∥⊎∥ x ∈ y)  □
    lemma (just z) y =
      x ∈ map-Maybe-cons (just z) y  ↔⟨⟩
      x ∈ z ∷ y                      ↝⟨ ∈∷≃ ⟩
      x ≡ z ∥⊎∥ x ∈ y                ↔⟨ (Bijection.≡↔inj₂≡inj₂ F.∘ ≡-comm) Trunc.∥⊎∥-cong F.id ⟩□
      just z ≡ just x ∥⊎∥ x ∈ y      □

  e .is-propositionʳ y =
    Eq.left-closure ext 0 ∈-propositional

-- The function map-Maybe f commutes with map-Maybe g if f commutes
-- with g in a certain way.

map-Maybe-comm :
  {A : Type a} {f g : A → Maybe A} →
  (∀ x → f =<< g x ≡ g =<< f x) →
  ∀ x → map-Maybe f (map-Maybe g x) ≡ map-Maybe g (map-Maybe f x)
map-Maybe-comm {A} {f} {g} hyp = elim-prop λ where
    .is-propositionʳ _ → is-set
    .[]ʳ               → refl _
    .∷ʳ {y} x          →
      curry (lemma (g x) (f x) (map-Maybe g y) (map-Maybe f y)) (hyp x)
  where
  lemma :
    ∀ (gx fx : Maybe A) gy fy →
    f =<< gx ≡ g =<< fx ×
    map-Maybe f gy ≡ map-Maybe g fy →
    map-Maybe f (map-Maybe-cons gx gy) ≡
    map-Maybe g (map-Maybe-cons fx fy)
  lemma nothing nothing gy fy =
    nothing ≡ nothing × map-Maybe f gy ≡ map-Maybe g fy  →⟨ proj₂ ⟩□
    map-Maybe f gy ≡ map-Maybe g fy                      □
  lemma nothing (just fx) gy fy =
    nothing ≡ g fx × map-Maybe f gy ≡ map-Maybe g fy         →⟨ (λ (hyp₁ , hyp₂) →
                                                                   trans hyp₂ (cong (flip map-Maybe-cons (map-Maybe g fy)) hyp₁)) ⟩□
    map-Maybe f gy ≡ map-Maybe-cons (g fx) (map-Maybe g fy)  □
  lemma (just gx) nothing gy fy =
    f gx ≡ nothing × map-Maybe f gy ≡ map-Maybe g fy         →⟨ (λ (hyp₁ , hyp₂) →
                                                                   trans (cong (flip map-Maybe-cons (map-Maybe f gy)) hyp₁) hyp₂) ⟩□
    map-Maybe-cons (f gx) (map-Maybe f gy) ≡ map-Maybe g fy  □
  lemma (just gx) (just fx) gy fy =
    f gx ≡ g fx × map-Maybe f gy ≡ map-Maybe g fy  →⟨ uncurry (cong₂ map-Maybe-cons) ⟩□

    map-Maybe-cons (f gx) (map-Maybe f gy) ≡
    map-Maybe-cons (g fx) (map-Maybe g fy)         □

-- The function map-Maybe commutes with union.

map-Maybe-∪ :
  ∀ x → map-Maybe f (x ∪ y) ≡ map-Maybe f x ∪ map-Maybe f y
map-Maybe-∪ {f} = elim-prop λ where
    .is-propositionʳ _ → is-set
    .[]ʳ               → refl _
    .∷ʳ x              → lemma (f x)
  where
  lemma :
    ∀ x → y ≡ z₁ ∪ z₂ →
    map-Maybe-cons x y ≡ map-Maybe-cons x z₁ ∪ z₂
  lemma nothing  = id
  lemma (just x) = cong (x ∷_)

-- One can express map using map-Maybe.

map≡map-Maybe-just :
  (x : Finite-subset-of A) →
  map f x ≡ map-Maybe (just ∘ f) x
map≡map-Maybe-just {f} = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ               = refl _
  e .∷ʳ x              = cong (f x ∷_)
  e .is-propositionʳ _ = is-set

-- A lemma characterising map.

∈map≃ : (x ∈ map f y) ≃ ∥ (∃ λ z → z ∈ y × f z ≡ x) ∥
∈map≃ {x} {f} {y} =
  x ∈ map f y                                ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $ map≡map-Maybe-just y ⟩
  x ∈ map-Maybe (just ∘ f) y                 ↝⟨ ∈map-Maybe≃ ⟩
  ∥ (∃ λ z → z ∈ y × just (f z) ≡ just x) ∥  ↔⟨ Trunc.∥∥-cong (∃-cong λ _ → ∃-cong λ _ → inverse Bijection.≡↔inj₂≡inj₂) ⟩□
  ∥ (∃ λ z → z ∈ y × f z ≡ x) ∥              □

-- Some consequences of the characterisation of map.

∈→∈map :
  {f : A → B} →
  x ∈ y → f x ∈ map f y
∈→∈map {x} {y} {f} =
  x ∈ y                            →⟨ (λ x∈y → ∣ x , x∈y , refl _ ∣) ⟩
  ∥ (∃ λ z → z ∈ y × f z ≡ f x) ∥  ↔⟨ inverse ∈map≃ ⟩□
  f x ∈ map f y                    □

Injective→∈map≃ :
  {f : A → B} →
  Injective f →
  (f x ∈ map f y) ≃ (x ∈ y)
Injective→∈map≃ {x} {y} {f} inj =
  f x ∈ map f y                    ↝⟨ ∈map≃ ⟩
  ∥ (∃ λ z → z ∈ y × f z ≡ f x) ∥  ↝⟨ (Trunc.∥∥-cong-⇔ $ ∃-cong λ _ → ∃-cong λ _ →
                                       record { to = inj; from = cong f }) ⟩
  ∥ (∃ λ z → z ∈ y × z ≡ x) ∥      ↔⟨ Trunc.∥∥-cong $ inverse $ ∃-intro _ _ ⟩
  ∥ x ∈ y ∥                        ↔⟨ Trunc.∥∥↔ ∈-propositional ⟩□
  x ∈ y                            □

-- The function map commutes with union.

map-∪ : ∀ x → map f (x ∪ y) ≡ map f x ∪ map f y
map-∪ {f} {y} x =
  map f (x ∪ y)                                    ≡⟨ map≡map-Maybe-just (x ∪ y) ⟩
  map-Maybe (just ∘ f) (x ∪ y)                     ≡⟨ map-Maybe-∪ x ⟩
  map-Maybe (just ∘ f) x ∪ map-Maybe (just ∘ f) y  ≡⟨ sym $ cong₂ _∪_ (map≡map-Maybe-just x) (map≡map-Maybe-just y) ⟩∎
  map f x ∪ map f y                                ∎

private

  -- A function used to define filter.

  include-if : Bool → A → Maybe A
  include-if b x = if b then just x else nothing

-- A filter function.

filter : (A → Bool) → Finite-subset-of A → Finite-subset-of A
filter p = map-Maybe (λ x → include-if (p x) x)

-- A lemma characterising filter.

∈filter≃ :
  ∀ p → (x ∈ filter p y) ≃ (T (p x) × x ∈ y)
∈filter≃ {x} {y} p =
  x ∈ map-Maybe (λ x → include-if (p x) x) y         ↝⟨ ∈map-Maybe≃ ⟩
  ∥ (∃ λ z → z ∈ y × include-if (p z) z ≡ just x) ∥  ↝⟨ (Trunc.∥∥-cong $ ∃-cong λ _ → ∃-cong λ _ → lemma _ (refl _)) ⟩
  ∥ (∃ λ z → z ∈ y × T (p z) × z ≡ x) ∥              ↔⟨ (Trunc.∥∥-cong $ ∃-cong λ _ →
                                                         (×-cong₁ λ z≡x → ≡⇒↝ _ $ cong (λ z → z ∈ y × T (p z)) z≡x) F.∘
                                                         Σ-assoc) ⟩
  ∥ (∃ λ z → (x ∈ y × T (p x)) × z ≡ x) ∥            ↔⟨ inverse Σ-assoc F.∘
                                                        (×-cong₁ λ _ →
                                                         ×-comm F.∘
                                                         Trunc.∥∥↔ (×-closure 1 ∈-propositional (T-propositional (p x)))) F.∘
                                                        inverse Trunc.∥∥×∥∥↔∥×∥ F.∘
                                                        Trunc.∥∥-cong ∃-comm ⟩
  T (p x) × x ∈ y × ∥ (∃ λ z → z ≡ x) ∥              ↔⟨ (∃-cong λ _ → drop-⊤-right λ _ →
                                                         _⇔_.to contractible⇔↔⊤ (singleton-contractible _) F.∘
                                                         Trunc.∥∥↔ (H-level.mono₁ 0 $ singleton-contractible _)) ⟩□
  T (p x) × x ∈ y                                    □
  where
  lemma :
    ∀ b → p z ≡ b →
    (include-if b z ≡ just x) ≃
    (T b × z ≡ x)
  lemma {z} true eq =
    just z ≡ just x  ↔⟨ inverse Bijection.≡↔inj₂≡inj₂ ⟩
    z ≡ x            ↔⟨ inverse ×-left-identity ⟩□
    ⊤ × z ≡ x        □
  lemma {z} false eq =
    nothing ≡ just x  ↔⟨ Bijection.≡↔⊎ ⟩
    ⊥                 ↔⟨ inverse ×-left-zero ⟩□
    ⊥ × z ≡ x         □

-- The result of filtering is a subset of the original subset.

filter⊆ : ∀ p → filter p x ⊆ x
filter⊆ {x} p z =
  z ∈ filter p x   ↔⟨ ∈filter≃ p ⟩
  T (p z) × z ∈ x  →⟨ proj₂ ⟩□
  z ∈ x            □

-- Filtering commutes with itself.

filter-comm :
  ∀ (p q : A → Bool) x →
  filter p (filter q x) ≡ filter q (filter p x)
filter-comm p q = elim-prop λ where
    .is-propositionʳ _ → is-set
    .[]ʳ               → refl _
    .∷ʳ {y} x          →
      lemma (p x) (q x) (filter p y) (filter q y) (refl _) (refl _)
  where
  lemma :
    ∀ (px qx : Bool) py qy →
    p x ≡ px → qx ≡ q x →
    filter p qy ≡ filter q py →
    filter p (map-Maybe-cons (include-if qx x) qy) ≡
    filter q (map-Maybe-cons (include-if px x) py)
  lemma {x} nothing nothing py qy ≡px qx≡ =
    filter p qy ≡ filter q py                            →⟨ trans (cong (λ px → map-Maybe-cons (include-if px x) (filter p qy)) ≡px) ∘
                                                            flip trans (cong (λ qx → map-Maybe-cons (include-if qx x) (filter q py)) qx≡) ∘
                                                            cong (x ∷_) ⟩□
    map-Maybe-cons (include-if (p x) x) (filter p qy) ≡
    map-Maybe-cons (include-if (q x) x) (filter q py)    □
  lemma {x} nothing (just qx) py qy _ qx≡ =
    filter p qy ≡ filter q py                          →⟨ flip trans (cong (λ qx → map-Maybe-cons (include-if qx x) (filter q py)) qx≡) ⟩□

    filter p qy ≡
    map-Maybe-cons (include-if (q x) x) (filter q py)  □
  lemma {x} (just px) nothing py qy ≡px _ =
    filter p qy ≡ filter q py                            →⟨ trans (cong (λ px → map-Maybe-cons (include-if px x) (filter p qy)) ≡px) ⟩□

    map-Maybe-cons (include-if (p x) x) (filter p qy) ≡
    filter q py                                          □
  lemma (just _) (just _) py qy _ _ =
    filter p qy ≡ filter q py  □

private

  -- The following proof is shorter, but erased.

  @0 filter-comm′ :
    ∀ (p q : A → Bool) x →
    filter p (filter q x) ≡ filter q (filter p x)
  filter-comm′ p q x = _≃_.from extensionality λ y →
    y ∈ filter p (filter q x)    ↔⟨ from-isomorphism Σ-assoc F.∘ (F.id ×-cong ∈filter≃ q) F.∘ ∈filter≃ p ⟩
    (T (p y) × T (q y)) × y ∈ x  ↔⟨ ×-comm ×-cong F.id ⟩
    (T (q y) × T (p y)) × y ∈ x  ↔⟨ inverse $ from-isomorphism Σ-assoc F.∘ (F.id ×-cong ∈filter≃ p) F.∘ ∈filter≃ q ⟩□
    y ∈ filter q (filter p x)    □

-- Filtering commutes with union.

filter-∪ :
  ∀ p x → filter p (x ∪ y) ≡ filter p x ∪ filter p y
filter-∪ _ = map-Maybe-∪

-- If erased truncated equality is decidable, then one subset can be
-- removed from another.

minus :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  Finite-subset-of A → Finite-subset-of A → Finite-subset-of A
minus _≟_ x y =
  filter (λ z → if member?ᴱ _≟_ z y then false else true) x

-- A lemma characterising minus.

∈minus≃ : (x ∈ minus _≟_ y z) ≃ (x ∈ y × x ∉ z)
∈minus≃ {x} {_≟_} {y} {z} =
  x ∈ minus _≟_ y z                                     ↝⟨ ∈filter≃ (λ _ → if member?ᴱ _ _ z then _ else _) ⟩
  T (if member?ᴱ _≟_ x z then false else true) × x ∈ y  ↔⟨ lemma (member?ᴱ _≟_ x z) ×-cong F.id ⟩
  x ∉ z × x ∈ y                                         ↔⟨ ×-comm ⟩□
  x ∈ y × x ∉ z                                         □
  where
  lemma :
    (d : Dec-Erased A) →
    T (if d then false else true) ↔ ¬ A
  lemma {A} d@(yes a) =
    T (if d then false else true)  ↔⟨⟩
    ⊥                              ↝⟨ Bijection.⊥↔uninhabited (_$ a) ⟩
    ¬ EC.Erased A                  ↝⟨ EC.¬-Erased↔¬ ext ⟩□
    ¬ A                            □
  lemma {A} d@(no ¬a) =
    T (if d then false else true) ↔⟨⟩
    ⊤                             ↝⟨ inverse $
                                     _⇔_.to contractible⇔↔⊤ $
                                     propositional⇒inhabited⇒contractible
                                       (¬-propositional ext)
                                       (EC.Stable-¬ ¬a) ⟩□
    ¬ A                           □

-- The result of minus is a subset of the original subset.

minus⊆ : ∀ y → minus _≟_ x y ⊆ x
minus⊆ y =
  filter⊆ (λ _ → if member?ᴱ _ _ y then _ else _)

-- Minus commutes with itself (in a certain sense).

minus-comm :
  ∀ x y z →
  minus _≟_ (minus _≟_ x y) z ≡ minus _≟_ (minus _≟_ x z) y
minus-comm x y z =
  filter-comm
    (λ _ → if member?ᴱ _ _ z then _ else _)
    (λ _ → if member?ᴱ _ _ y then _ else _)
    x

-- Minus commutes with union (in a certain sense).

minus-∪ :
  ∀ x z →
  minus _≟_ (x ∪ y) z ≡ minus _≟_ x z ∪ minus _≟_ y z
minus-∪ x z = filter-∪ (λ _ → if member?ᴱ _ _ z then _ else _) x

-- A lemma relating minus, _⊆_ and _∪_.

minus⊆≃ :
  {_≟_ : (x y : A) → Dec ∥ x ≡ y ∥} →
  ∀ y →
  (minus (λ x y → Dec→Dec-Erased (x ≟ y)) x y ⊆ z) ≃
  (x ⊆ y ∪ z)
minus⊆≃ {x} {z} {_≟_} y =
  Eq.⇔→≃
    ⊆-propositional
    ⊆-propositional
    (λ x-y⊆z u →
       u ∈ x                         →⟨ (λ u∈x →
                                           case member? _≟_ u y of
                                             P.[ Trunc.∣inj₁∣ , Trunc.∣inj₂∣ ∘ (u∈x ,_) ]) ⟩
       u ∈ y ∥⊎∥ (u ∈ x × u ∉ y)     ↔⟨ F.id Trunc.∥⊎∥-cong inverse ∈minus≃ ⟩
       u ∈ y ∥⊎∥ u ∈ minus _≟′_ x y  →⟨ id Trunc.∥⊎∥-cong x-y⊆z u ⟩
       u ∈ y ∥⊎∥ u ∈ z               ↔⟨ inverse ∈∪≃ ⟩□
       u ∈ y ∪ z                     □)
    (λ x⊆y∪z u →
       u ∈ minus _≟′_ x y         ↔⟨ ∈minus≃ ⟩
       u ∈ x × u ∉ y              →⟨ Σ-map (x⊆y∪z _) id ⟩
       u ∈ y ∪ z × u ∉ y          ↔⟨ ∈∪≃ ×-cong F.id ⟩
       (u ∈ y ∥⊎∥ u ∈ z) × u ∉ y  ↔⟨ (×-cong₁ λ u∉y → Trunc.drop-⊥-left-∥⊎∥ ∈-propositional u∉y) ⟩
       u ∈ z × u ∉ y              →⟨ proj₁ ⟩□
       u ∈ z                      □)
  where
  _≟′_ = λ x y → Dec→Dec-Erased (x ≟ y)

-- If erased truncated equality is decidable, then elements can be
-- removed from a subset.

delete :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  A → Finite-subset-of A → Finite-subset-of A
delete _≟_ x y = minus _≟_ y (singleton x)

-- A lemma characterising delete.

∈delete≃ : ∀ _≟_ → (x ∈ delete _≟_ y z) ≃ (x ≢ y × x ∈ z)
∈delete≃ {x} {y} {z} _≟_ =
  x ∈ delete _≟_ y z       ↝⟨ ∈minus≃ {_≟_ = _≟_} ⟩
  x ∈ z × x ∉ singleton y  ↝⟨ F.id ×-cong →-cong₁ ext ∈singleton≃ ⟩
  x ∈ z × ¬ ∥ x ≡ y ∥      ↔⟨ F.id ×-cong Trunc.¬∥∥↔¬ ⟩
  x ∈ z × x ≢ y            ↔⟨ ×-comm ⟩□
  x ≢ y × x ∈ z            □

-- A deleted element is no longer a member of the set.

∉delete : ∀ _≟_ y → x ∉ delete _≟_ x y
∉delete {x} _≟_ y =
  x ∈ delete _≟_ x y  ↔⟨ ∈delete≃ _≟_ ⟩
  x ≢ x × x ∈ y       →⟨ (_$ refl _) ∘ proj₁ ⟩□
  ⊥                   □

-- Deletion commutes with itself (in a certain sense).

delete-comm :
  ∀ _≟_ z →
  delete _≟_ x (delete _≟_ y z) ≡ delete _≟_ y (delete _≟_ x z)
delete-comm _≟_ z =
  minus-comm {_≟_ = _≟_} z (singleton _) (singleton _)

-- Deletion commutes with union.

delete-∪ :
  ∀ _≟_ y →
  delete _≟_ x (y ∪ z) ≡ delete _≟_ x y ∪ delete _≟_ x z
delete-∪ _≟_ y = minus-∪ {_≟_ = _≟_} y (singleton _)

-- A lemma relating delete, _⊆_ and _∷_.

delete⊆≃ :
  (_≟_ : (x y : A) → Dec ∥ x ≡ y ∥) →
  (delete (λ x y → Dec→Dec-Erased (x ≟ y)) x y ⊆ z) ≃ (y ⊆ x ∷ z)
delete⊆≃ _≟_ = minus⊆≃ {_≟_ = _≟_} (singleton _)

------------------------------------------------------------------------
-- Some preservation lemmas for _⊆_

-- Various operations preserve _⊆_.

∷-cong-⊆ : y ⊆ z → x ∷ y ⊆ x ∷ z
∷-cong-⊆ {y} {z} {x} y⊆z u =
  u ∈ x ∷ y        ↔⟨ ∈∷≃ ⟩
  u ≡ x ∥⊎∥ u ∈ y  →⟨ id Trunc.∥⊎∥-cong y⊆z _ ⟩
  u ≡ x ∥⊎∥ u ∈ z  ↔⟨ inverse ∈∷≃ ⟩□
  u ∈ x ∷ z        □

∪-cong-⊆ : x₁ ⊆ x₂ → y₁ ⊆ y₂ → x₁ ∪ y₁ ⊆ x₂ ∪ y₂
∪-cong-⊆ {x₁} {x₂} {y₁} {y₂} x₁⊆x₂ y₁⊆y₂ z =
  z ∈ x₁ ∪ y₁        ↔⟨ ∈∪≃ ⟩
  z ∈ x₁ ∥⊎∥ z ∈ y₁  →⟨ x₁⊆x₂ _ Trunc.∥⊎∥-cong y₁⊆y₂ _ ⟩
  z ∈ x₂ ∥⊎∥ z ∈ y₂  ↔⟨ inverse ∈∪≃ ⟩□
  z ∈ x₂ ∪ y₂        □

filter-cong-⊆ :
  ∀ p q →
  (∀ z → T (p z) → T (q z)) →
  x ⊆ y → filter p x ⊆ filter q y
filter-cong-⊆ {x} {y} p q p⇒q x⊆y z =
  z ∈ filter p x   ↔⟨ ∈filter≃ p ⟩
  T (p z) × z ∈ x  →⟨ Σ-map (p⇒q _) (x⊆y _) ⟩
  T (q z) × z ∈ y  ↔⟨ inverse $ ∈filter≃ q ⟩□
  z ∈ filter q y   □

minus-cong-⊆ : x₁ ⊆ x₂ → y₂ ⊆ y₁ → minus _≟_ x₁ y₁ ⊆ minus _≟_ x₂ y₂
minus-cong-⊆ {x₁} {x₂} {y₂} {y₁} {_≟_} x₁⊆x₂ y₂⊆y₁ z =
  z ∈ minus _≟_ x₁ y₁  ↔⟨ ∈minus≃ ⟩
  z ∈ x₁ × z ∉ y₁      →⟨ Σ-map (x₁⊆x₂ _) (_∘ y₂⊆y₁ _) ⟩
  z ∈ x₂ × z ∉ y₂      ↔⟨ inverse ∈minus≃ ⟩□
  z ∈ minus _≟_ x₂ y₂  □

delete-cong-⊆ : ∀ _≟_ → y ⊆ z → delete _≟_ x y ⊆ delete _≟_ x z
delete-cong-⊆ _≟_ y⊆z =
  minus-cong-⊆ {_≟_ = _≟_} y⊆z (⊆-refl {x = singleton _})

------------------------------------------------------------------------
-- Size

private

  -- This definition is used to define ∣_∣≡ and ∣∣≡-propositional
  -- below.
  --
  -- This definition is not taken from "Finite Sets in Homotopy Type
  -- Theory", but it is based on the size function in that paper.

  Size : {A : Type a} → Finite-subset-of A → ℕ → Proposition a
  Size {a} {A} = rec r
    where

    mutual

      -- The size of x ∷ y is equal to the size of y if x is a member
      -- of y, and otherwise it is equal to the successor of the size
      -- of y.

      Cons′ :
        A → Finite-subset-of A →
        (ℕ → Proposition a) → (ℕ → Type a)
      Cons′ x y ∣y∣≡ n =
        x ∈ y × proj₁ (∣y∣≡ n)
          ⊎
        Cons″ x y ∣y∣≡ n

      Cons″ :
        A → Finite-subset-of A →
        (ℕ → Proposition a) → (ℕ → Type a)
      Cons″ x y ∣y∣≡ zero    = ⊥
      Cons″ x y ∣y∣≡ (suc n) = x ∉ y × proj₁ (∣y∣≡ n)

    Cons′-propositional :
      ∀ Hyp n → Is-proposition (Cons′ x y Hyp n)
    Cons′-propositional Hyp zero =
      ⊎-closure-propositional
        (λ _ ())
        (×-closure 1 ∈-propositional (proj₂ (Hyp 0)))
        ⊥-propositional
    Cons′-propositional Hyp (suc n) =
      ⊎-closure-propositional
        (λ (x∈y , _) (x∉y , _) → x∉y x∈y)
        (×-closure 1 ∈-propositional (proj₂ (Hyp (suc n))))
        (×-closure 1 (¬-propositional ext) (proj₂ (Hyp n)))

    Cons :
      A → Finite-subset-of A →
      (ℕ → Proposition a) → (ℕ → Proposition a)
    Cons x y Hyp n =
        Cons′ x y Hyp n
      , Cons′-propositional _ _

    @0 drop-lemma :
      Cons′ x (x ∷ y) (Cons x y H) n ≃ Cons′ x y H n
    drop-lemma {x} {y} {H} {n} =
      Cons′ x (x ∷ y) (Cons x y H) n   ↔⟨⟩
      x ∈ x ∷ y × Cons′ x y H n ⊎ C n  ↔⟨ drop-⊥-right (C↔⊥ n) ⟩
      x ∈ x ∷ y × Cons′ x y H n        ↔⟨ drop-⊤-left-× (λ _ → x∈x∷y↔⊤) ⟩
      Cons′ x y H n                    □
      where
      C = Cons″ x (x ∷ y) (Cons x y H)

      x∈x∷y↔⊤ : x ∈ x ∷ y ↔ ⊤
      x∈x∷y↔⊤ =
        x ∈ x ∷ y        ↔⟨ ∈∷≃ ⟩
        x ≡ x ∥⊎∥ x ∈ y  ↝⟨ Trunc.inhabited⇒∥∥↔⊤ ∣ inj₁ (refl _) ∣ ⟩□
        ⊤                □

      C↔⊥ : ∀ n → C n ↔ ⊥
      C↔⊥ zero    = ⊥↔⊥
      C↔⊥ (suc n) =
        x ∉ x ∷ y × Cons′ x y H n  ↝⟨ →-cong ext x∈x∷y↔⊤ F.id ×-cong F.id ⟩
        ¬ ⊤ × Cons′ x y H n        ↝⟨ inverse (Bijection.⊥↔uninhabited (_$ _)) ×-cong F.id ⟩
        ⊥₀ × Cons′ x y H n         ↝⟨ ×-left-zero ⟩□
        ⊥                          □

    @0 swap-lemma′ :
      ∀ n →
      x ∈ y ∷ z × Cons′ y z H n ⊎ Cons″ x (y ∷ z) (Cons y z H) n →
      y ∈ x ∷ z × Cons′ x z H n ⊎ Cons″ y (x ∷ z) (Cons x z H) n
    swap-lemma′ {x} {y} {z} {H} = λ @0 where
      n (inj₁ (x∈y∷z , inj₁ (y∈z , p))) →
        inj₁ ( ∈→∈∷ y∈z
             , inj₁
                 ( (                 $⟨ x∈y∷z ⟩
                    x ∈ y ∷ z        ↔⟨ ∈∷≃ ⟩
                    x ≡ y ∥⊎∥ x ∈ z  →⟨ Trunc.∥∥-map P.[ (flip (subst (_∈ z)) y∈z ∘ sym) , id ] ⟩
                    ∥ x ∈ z ∥        ↔⟨ Trunc.∥∥↔ ∈-propositional ⟩□
                    x ∈ z            □)
                 , p
                 )
             )

      (suc n) (inj₁ (x∈y∷z , inj₂ (y∉z , p))) →
        Trunc.rec (Cons′-propositional (Cons x z H) _)
          P.[ (λ x≡y →
                inj₁ ( ≡→∈∷ (sym x≡y)
                     , inj₂ ( (x ∈ z  →⟨ subst (_∈ z) x≡y ⟩
                               y ∈ z  →⟨ y∉z ⟩□
                               ⊥      □)
                            , p
                            )
                     ))
            , (λ x∈z →
                 inj₂ ( (y ∈ x ∷ z        ↔⟨ ∈∷≃ ⟩
                         y ≡ x ∥⊎∥ y ∈ z  →⟨ Trunc.∥∥-map P.[ flip (subst (_∈ z)) x∈z ∘ sym , id ] ⟩
                         ∥ y ∈ z ∥        →⟨ Trunc.∥∥-map y∉z ⟩
                         ∥ ⊥ ∥            ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                         ⊥                □)
                      , inj₁ (x∈z , p)
                      ))
            ]
          (_≃_.to ∈∷≃ x∈y∷z)

      (suc n) (inj₂ (x∉y∷z , inj₁ (y∈z , p))) →
        inj₁ ( ∈→∈∷ y∈z
             , inj₂ ( (x ∈ z      →⟨ ∈→∈∷ ⟩
                       x ∈ y ∷ z  →⟨ x∉y∷z ⟩□
                       ⊥          □)
                    , p
                    )
             )

      (suc (suc n)) (inj₂ (x∉y∷z , inj₂ (y∉z , p))) →
        inj₂ ( (y ∈ x ∷ z            ↔⟨ ∈∷≃ ⟩
                y ≡ x ∥⊎∥ y ∈ z      →⟨ ≡→∈∷ ∘ sym Trunc.∥⊎∥-cong id ⟩
                x ∈ y ∷ z ∥⊎∥ y ∈ z  →⟨ Trunc.∥∥-map P.[ x∉y∷z , y∉z ] ⟩
                ∥ ⊥ ∥                ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                ⊥                    □)
             , inj₂ ( (x ∈ z      →⟨ ∈→∈∷ ⟩
                       x ∈ y ∷ z  →⟨ x∉y∷z ⟩□
                       ⊥          □)
                    , p
                    )
             )

    @0 swap-lemma :
      Cons′ x (y ∷ z) (Cons y z H) n ≃
      Cons′ y (x ∷ z) (Cons x z H) n
    swap-lemma {x} {y} {z} {H} {n} =
      Eq.⇔→≃
        (Cons′-propositional _ _)
        (Cons′-propositional _ _)
        (swap-lemma′ _)
        (swap-lemma′ _)

    r : Rec A (ℕ → Proposition a)
    r .[]ʳ n = ↑ _ (n ≡ 0) , ↑-closure 1 ℕ-set

    r .∷ʳ = Cons

    r .dropʳ x y Hyp = ⟨ext⟩ λ _ →
      _↔_.to (ignore-propositional-component
             (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ drop-lemma

    r .swapʳ x y z Hyp = ⟨ext⟩ λ _ →
      _↔_.to (ignore-propositional-component
             (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ swap-lemma

    r .is-setʳ =
      Π-closure ext 2 λ _ →
      Univ.∃-H-level-H-level-1+ ext univ 1

-- Size.

infix 4 ∣_∣≡_

∣_∣≡_ : {A : Type a} → Finite-subset-of A → ℕ → Type a
∣ x ∣≡ n = proj₁ (Size x n)

-- The size predicate is propositional.

∣∣≡-propositional :
  (x : Finite-subset-of A) → Is-proposition (∣ x ∣≡ n)
∣∣≡-propositional x = proj₂ (Size x _)

-- Unit tests documenting the computational behaviour of ∣_∣≡_.

_ : (∣ [] {A = A} ∣≡ n) ≡ ↑ _ (n ≡ 0)
_ = refl _

_ : ∀ {A : Type a} {x : A} {y} →
    (∣ x ∷ y ∣≡ zero) ≡ (x ∈ y × ∣ y ∣≡ zero ⊎ ⊥)
_ = refl _

_ : (∣ x ∷ y ∣≡ suc n) ≡ (x ∈ y × ∣ y ∣≡ suc n ⊎ x ∉ y × ∣ y ∣≡ n)
_ = refl _

-- The size predicate is functional.

∣∣≡-functional :
  (x : Finite-subset-of A) → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n
∣∣≡-functional x = elim-prop e x _ _
  where
  e : Elim-prop (λ x → ∀ m n → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n)
  e .[]ʳ m n (lift m≡0) (lift n≡0) =
    m  ≡⟨ m≡0 ⟩
    0  ≡⟨ sym n≡0 ⟩∎
    n  ∎

  e .∷ʳ {y} x hyp = λ where
    m n (inj₁ (x∈y , ∣y∣≡m)) (inj₁ (x∈y′ , ∣y∣≡n)) →
      hyp m n ∣y∣≡m ∣y∣≡n

    (suc m) (suc n) (inj₂ (x∉y , ∣y∣≡m)) (inj₂ (x∉y′ , ∣y∣≡n)) →
      cong suc (hyp m n ∣y∣≡m ∣y∣≡n)

    _ (suc _) (inj₁ (x∈y , _)) (inj₂ (x∉y , _)) → ⊥-elim (x∉y x∈y)
    (suc _) _ (inj₂ (x∉y , _)) (inj₁ (x∈y , _)) → ⊥-elim (x∉y x∈y)

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ℕ-set

-- If truncated equality is decidable, then one can compute the size
-- of a finite subset.

size :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : Finite-subset-of A) → ∃ λ n → ∣ x ∣≡ n
size equal? = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ = 0 , lift (refl _)

  e .∷ʳ {y} x (n , ∣y∣≡n) =
    case member? equal? x y of λ x∈?y →
        if x∈?y then n else suc n
      , lemma ∣y∣≡n x∈?y
    where
    lemma :
      ∣ y ∣≡ n →
      (x∈?y : Dec (x ∈ y)) →
      ∣ x ∷ y ∣≡ if x∈?y then n else suc n
    lemma ∣y∣≡n (yes x∈y) = inj₁ (x∈y , ∣y∣≡n)
    lemma ∣y∣≡n (no  x∉y) = inj₂ (x∉y , ∣y∣≡n)

  e .is-propositionʳ x (m , ∣x∣≡m) (n , ∣x∣≡n) =
    Σ-≡,≡→≡ (m  ≡⟨ ∣∣≡-functional x ∣x∣≡m ∣x∣≡n ⟩∎
             n  ∎)
            (∣∣≡-propositional x _ _)

-- A variant of size that uses Erased.

sizeᴱ :
  ((x y : A) → Dec-Erased ∥ x ≡ y ∥) →
  (x : Finite-subset-of A) → ∃ λ n → Erased (∣ x ∣≡ n)
sizeᴱ equal? = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ = 0 , [ lift (refl _) ]

  e .∷ʳ {y} x (n , [ ∣y∣≡n ]) =
    case member?ᴱ equal? x y of λ x∈?y →
        if x∈?y then n else suc n
      , [ lemma ∣y∣≡n x∈?y ]
    where
    @0 lemma :
      ∣ y ∣≡ n →
      (x∈?y : Dec-Erased (x ∈ y)) →
      ∣ x ∷ y ∣≡ if x∈?y then n else suc n
    lemma ∣y∣≡n (yes [ x∈y ]) = inj₁ (x∈y , ∣y∣≡n)
    lemma ∣y∣≡n (no  [ x∉y ]) = inj₂ (x∉y , ∣y∣≡n)

  e .is-propositionʳ x (m , [ ∣x∣≡m ]) (n , [ ∣x∣≡n ]) =
    Σ-≡,≡→≡ (m  ≡⟨ EC.Very-stable→Stable 1
                     (EC.Decidable-equality→Very-stable-≡ Nat._≟_)
                     _ _
                     [ ∣∣≡-functional x ∣x∣≡m ∣x∣≡n ] ⟩∎
             n  ∎)
            (EC.H-level-Erased 1 (∣∣≡-propositional x) _ _)

------------------------------------------------------------------------
-- Finite types

-- A type is finite if there is some finite subset of the type for
-- which every element of the type is a member of the subset.

Is-finite : Type a → Type a
Is-finite A = ∃ λ (s : Finite-subset-of A) → ∀ x → x ∈ s

-- The Is-finite predicate is propositional (in erased contexts).

@0 Is-finite-propositional : Is-proposition (Is-finite A)
Is-finite-propositional (x , p) (y , q) =
                         $⟨ (λ z → record { to = λ _ → q z; from = λ _ → p z }) ⟩
  (∀ z → z ∈ x ⇔ z ∈ y)  ↝⟨ inverse extensionality ⟩
  x ≡ y                  ↔⟨ ignore-propositional-component (Π-closure ext 1 (λ _ → ∈-propositional)) ⟩□
  (x , p) ≡ (y , q)      □

------------------------------------------------------------------------
-- Lists can be converted to finite subsets

-- Converts lists to finite subsets.

from-List : List A → Finite-subset-of A
from-List = L.foldr _∷_ []

-- Membership in the resulting set is equivalent to truncated
-- membership in the list.

∥∈∥≃∈-from-List : ∥ x BE.∈ ys ∥ ≃ (x ∈ from-List ys)
∥∈∥≃∈-from-List {x} {ys} =
  Eq.⇔→≃
    Trunc.truncation-is-proposition
    ∈-propositional
    (to _)
    (from _)
  where
  to : ∀ ys → ∥ x BE.∈ ys ∥ → x ∈ from-List ys
  to []       = Trunc.rec ∈-propositional (λ ())
  to (y ∷ ys) = Trunc.rec ∈-propositional
                  P.[ ≡→∈∷ , ∈→∈∷ ∘ to ys ∘ ∣_∣ ]

  from : ∀ ys → x ∈ from-List ys → ∥ x BE.∈ ys ∥
  from [] ()
  from (y ∷ ys) =
    Trunc.rec
      Trunc.truncation-is-proposition
      P.[ ∣_∣ ∘ inj₁ , Trunc.∥∥-map inj₂ ∘ from ys ] ∘
    _≃_.to ∈∷≃

------------------------------------------------------------------------
-- Some definitions related to the definitions in Bag-equivalence

opaque
  unfolding Q._/ᴱ-map_ Q.rec

  -- Finite subsets can be expressed as lists quotiented by set
  -- equivalence.

  ≃List/ᴱ∼ : Finite-subset-of A ≃ List A /ᴱ _∼[ set ]_
  ≃List/ᴱ∼ = from-bijection (record
    { surjection = record
      { logical-equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of = from∘to
    })
    where
    cons : A → List A /ᴱ _∼[ set ]_ → List A /ᴱ _∼[ set ]_
    cons x = (x ∷_) Q./ᴱ-map λ _ _ → refl _ BE.∷-cong_

    to : Finite-subset-of A → List A /ᴱ _∼[ set ]_
    to = rec r
      where
      r : Rec A (List A /ᴱ _∼[ set ]_)
      r .[]ʳ       = Q.[ [] ]
      r .∷ʳ x _ y  = cons x y
      r .is-setʳ   = Q./ᴱ-is-set
      r .dropʳ x _ = Q.elim-prop λ @0 where
        .Q.[]ʳ xs → Q.[]-respects-relation λ z →
          z BE.∈ x ∷ x ∷ xs      ↝⟨ record { to = P.[ inj₁ , id ]; from = inj₂ } ⟩□
          z BE.∈ x ∷ xs          □
        .Q.is-propositionʳ _ → Q./ᴱ-is-set

      r .swapʳ x y _ = Q.elim-prop λ @0 where
        .Q.[]ʳ xs → Q.[]-respects-relation λ z →
          z BE.∈ x ∷ y ∷ xs  ↔⟨ BE.swap-first-two z ⟩□
          z BE.∈ y ∷ x ∷ xs  □
        .Q.is-propositionʳ _ → Q./ᴱ-is-set

    from : List A /ᴱ _∼[ set ]_ → Finite-subset-of A
    from {A} = Q.rec λ where
      .Q.[]ʳ → from-List

      .Q.[]-respects-relationʳ {x = xs} {y = ys} xs∼ys →
        _≃_.from extensionality λ z →
          z ∈ from-List xs  ↔⟨ inverse ∥∈∥≃∈-from-List ⟩
          ∥ z BE.∈ xs ∥     ↔⟨ Trunc.∥∥-cong-⇔ {k = bijection} (xs∼ys z) ⟩
          ∥ z BE.∈ ys ∥     ↔⟨ ∥∈∥≃∈-from-List ⟩□
          z ∈ from-List ys  □

      .Q.is-setʳ → is-set

    to∘from : (x : List A /ᴱ _∼[ set ]_) → to (from x) ≡ x
    to∘from = Q.elim-prop λ where
        .Q.[]ʳ               → lemma
        .Q.is-propositionʳ _ → Q./ᴱ-is-set
      where
      lemma : (xs : List A) → to (from-List xs) ≡ Q.[ xs ]
      lemma []       = refl _
      lemma (x ∷ xs) =
        to (from-List (x ∷ xs))                               ≡⟨⟩
        ((x ∷_) Q./ᴱ-map _) (to (from-List xs))               ≡⟨ cong ((x ∷_) Q./ᴱ-map _) (lemma xs) ⟩
        ((x ∷_) Q./ᴱ-map λ _ _ → refl _ BE.∷-cong_) Q.[ xs ]  ≡⟨⟩
        Q.[ x ∷ xs ]                                          ∎

    from∘to : (x : Finite-subset-of A) → from (to x) ≡ x
    from∘to = elim-prop e
      where
      e : Elim-prop (λ (x : Finite-subset-of A) → from (to x) ≡ x)
      e .[]ʳ = refl _

      e .∷ʳ {y} x hyp =
        from (to (x ∷ y))     ≡⟨⟩
        from (cons x (to y))  ≡⟨ Q.elim-prop
                                   {P = λ y → from (cons x y) ≡ x ∷ from y}
                                   (λ where
                                      .Q.[]ʳ _             → refl _
                                      .Q.is-propositionʳ _ → is-set)
                                   (to y) ⟩
        x ∷ from (to y)       ≡⟨ cong (x ∷_) hyp ⟩∎
        x ∷ y                 ∎

      e .is-propositionʳ _ = is-set

opaque
  unfolding ≃List/ᴱ∼

  -- A truncated variant of the proof-relevant membership relation from
  -- Bag-equivalence can be expressed in terms of _∈_.

  ∥∈∥≃∈ : ∥ x BE.∈ ys ∥ ≃ (x ∈ _≃_.from ≃List/ᴱ∼ Q.[ ys ])
  ∥∈∥≃∈ = ∥∈∥≃∈-from-List

------------------------------------------------------------------------
-- Fresh numbers

-- One can always find a natural number that is distinct from those in
-- a given finite set of natural numbers.

fresh :
  (ns : Finite-subset-of ℕ) →
  ∃ λ (n : ℕ) → n ∉ ns
fresh ns =
  Σ-map id
    (λ {m} →
       Erased (∀ n → n ∈ ns → n < m)  →⟨ EC.map (_$ m) ⟩
       Erased (m ∈ ns → m < m)        →⟨ EC.map (∀-cong _ λ _ → Nat.+≮ 0) ⟩
       Erased (m ∉ ns)                →⟨ EC.Stable-¬ ⟩□
       m ∉ ns                         □)
    (elim e ns)
  where
  OK : @0 Finite-subset-of ℕ → @0 ℕ → Type
  OK ms m = Erased (∀ n → n ∈ ms → n < m)

  prop : Is-proposition (OK ms m)
  prop =
    EC.H-level-Erased 1 (
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ≤-propositional)

  ∷-max-suc :
    ∀ {ms n m} →
    OK ms n →
    OK (m ∷ ms) (Nat.max (suc m) n)
  ∷-max-suc {ms} {n} {m} [ ub ] =
    [ (λ o →
         o ∈ m ∷ ms                   ↔⟨ ∈∷≃ ⟩
         o ≡ m ∥⊎∥ o ∈ ms             →⟨ Nat.≤-refl′ ∘ cong suc ∘ id Trunc.∥⊎∥-cong ub o ⟩
         o Nat.< suc m ∥⊎∥ o Nat.< n  →⟨ Trunc.rec ≤-propositional
                                           P.[ flip Nat.≤-trans (Nat.ˡ≤max _ n)
                                             , flip Nat.≤-trans (Nat.ʳ≤max (suc m) _)
                                             ] ⟩□
         o Nat.< Nat.max (suc m) n    □)
    ]

  e : Elim (λ ms → ∃ λ m → OK ms m)
  e .[]ʳ =
    0 , [ (λ _ ()) ]

  e .∷ʳ m (n , ub) =
    Nat.max (suc m) n , ∷-max-suc ub

  e .dropʳ {y = ns} m (n , ub) =
    _↔_.to (ignore-propositional-component prop)
      (proj₁ (subst (λ ms → ∃ λ m → OK ms m)
                    (drop {x = m} {y = ns})
                    ( Nat.max (suc m) (Nat.max (suc m) n)
                    , ∷-max-suc (∷-max-suc ub)
                    ))                                     ≡⟨ cong proj₁ $
                                                              push-subst-pair-× {y≡z = drop {x = m} {y = ns}} _
                                                                (λ (ms , m) → OK ms m)
                                                                {p = _ , ∷-max-suc (∷-max-suc ub)} ⟩

       Nat.max (suc m) (Nat.max (suc m) n)                 ≡⟨ Nat.max-assoc (suc m) {n = suc m} {o = n} ⟩

       Nat.max (Nat.max (suc m) (suc m)) n                 ≡⟨ cong (λ m → Nat.max m n) $ Nat.max-idempotent (suc m) ⟩∎

       Nat.max (suc m) n                                   ∎)

  e .swapʳ {z = ns} m n (o , ub) =
    _↔_.to (ignore-propositional-component prop)
      (proj₁ (subst (λ xs → ∃ λ m → OK xs m)
                    (swap {x = m} {y = n} {z = ns})
                    ( Nat.max (suc m) (Nat.max (suc n) o)
                    , ∷-max-suc (∷-max-suc ub)
                    ))                                     ≡⟨ cong proj₁ $
                                                              push-subst-pair-× {y≡z = swap {x = m} {y = n} {z = ns}} _
                                                                (λ (ms , m) → OK ms m)
                                                                {p = _ , ∷-max-suc (∷-max-suc ub)} ⟩

       Nat.max (suc m) (Nat.max (suc n) o)                 ≡⟨ Nat.max-assoc (suc m) {n = suc n} {o = o} ⟩

       Nat.max (Nat.max (suc m) (suc n)) o                 ≡⟨ cong (λ m → Nat.max m o) $ Nat.max-comm (suc m) (suc n) ⟩

       Nat.max (Nat.max (suc n) (suc m)) o                 ≡⟨ sym $ Nat.max-assoc (suc n) {n = suc m} {o = o} ⟩∎

       Nat.max (suc n) (Nat.max (suc m) o)                 ∎)

  e .is-setʳ _ =
    Σ-closure 2 ℕ-set λ _ →
    H-level.mono₁ 1 prop
