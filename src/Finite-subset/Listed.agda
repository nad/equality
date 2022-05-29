------------------------------------------------------------------------
-- Listed finite subsets
------------------------------------------------------------------------

-- Based on Frumin, Geuvers, Gondelman and van der Weide's "Finite
-- Sets in Homotopy Type Theory".

-- A membership relation, and a number of definitions that make use of
-- the membership relation, can be found in
-- Finite-subset.Listed.Membership (which uses --cubical rather than
-- --erased-cubical). An alternative definition of membership can be
-- found in Finite-subset.Listed.Membership.Erased (that definition of
-- membership is erased, but the module uses --erased-cubical).

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Finite-subset.Listed
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude hiding (swap)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J as H-level
import List equality-with-J as L
open import Maybe equality-with-J as Maybe using (maybe)
open import Monad equality-with-J as M using (Raw-monad; Monad; _=<<_)

private
  variable
    a b p       : Level
    A B         : Type a
    x y z z₁ z₂ : A
    P           : A → Type p
    f g         : (x : A) → P x

------------------------------------------------------------------------
-- Listed finite subsets

-- Listed finite subsets of a given type.

infixr 5 _∷_

data Finite-subset-of (A : Type a) : Type a where
  []      : Finite-subset-of A
  _∷_     : A → Finite-subset-of A → Finite-subset-of A
  dropᴾ   : x ∷ x ∷ y P.≡ x ∷ y
  swapᴾ   : x ∷ y ∷ z P.≡ y ∷ x ∷ z
  is-setᴾ : P.Is-set (Finite-subset-of A)

-- Variants of some of the constructors.

drop :
  {x : A} {y : Finite-subset-of A} →
  x ∷ x ∷ y ≡ x ∷ y
drop = _↔_.from ≡↔≡ dropᴾ

swap :
  {x y : A} {z : Finite-subset-of A} →
  x ∷ y ∷ z ≡ y ∷ x ∷ z
swap = _↔_.from ≡↔≡ swapᴾ

is-set : Is-set (Finite-subset-of A)
is-set =
  _↔_.from (H-level↔H-level 2) Finite-subset-of.is-setᴾ

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : Finite-subset-of A → Type p) :
             Type (a ⊔ p) where
  no-eta-equality
  field
    []ʳ     : P []
    ∷ʳ      : ∀ x → P y → P (x ∷ y)
    dropʳ   : ∀ x (p : P y) →
              P.[ (λ i → P (dropᴾ {x = x} {y = y} i)) ]
                ∷ʳ x (∷ʳ x p) ≡ ∷ʳ x p
    swapʳ   : ∀ x y (p : P z) →
              P.[ (λ i → P (swapᴾ {x = x} {y = y} {z = z} i)) ]
                ∷ʳ x (∷ʳ y p) ≡ ∷ʳ y (∷ʳ x p)
    is-setʳ : ∀ x → P.Is-set (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : Finite-subset-of A) → P x
elimᴾ {A = A} {P = P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Finite-subset-of A) → P x
  helper []      = E.[]ʳ
  helper (x ∷ y) = E.∷ʳ x (helper y)

  helper (dropᴾ {x = x} {y = y} i) =
    E.dropʳ x (helper y) i

  helper (swapᴾ {x = x} {y = y} {z = z} i) =
    E.swapʳ x y (helper z) i

  helper (is-setᴾ x y i j) =
    P.heterogeneous-UIP
      E.is-setʳ (Finite-subset-of.is-setᴾ x y)
      (λ i → helper (x i)) (λ i → helper (y i)) i j

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    []ʳ     : B
    ∷ʳ      : A → Finite-subset-of A → B → B
    dropʳ   : ∀ x y p →
              ∷ʳ x (x ∷ y) (∷ʳ x y p) P.≡ ∷ʳ x y p
    swapʳ   : ∀ x y z p →
              ∷ʳ x (y ∷ z) (∷ʳ y z p) P.≡ ∷ʳ y (x ∷ z) (∷ʳ x z p)
    is-setʳ : P.Is-set B

open Recᴾ public

recᴾ : Recᴾ A B → Finite-subset-of A → B
recᴾ r = elimᴾ e
  where
  module R = Recᴾ r

  e : Elimᴾ _
  e .[]ʳ               = R.[]ʳ
  e .∷ʳ {y = y} x      = R.∷ʳ x y
  e .dropʳ {y = y} x   = R.dropʳ x y
  e .swapʳ {z = z} x y = R.swapʳ x y z
  e .is-setʳ _         = R.is-setʳ

-- A dependent eliminator, expressed using equality.

record Elim {A : Type a} (P : Finite-subset-of A → Type p) :
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

open Elim public

elim : Elim P → (x : Finite-subset-of A) → P x
elim e = elimᴾ e′
  where
  module E = Elim e

  e′ : Elimᴾ _
  e′ .[]ʳ         = E.[]ʳ
  e′ .∷ʳ          = E.∷ʳ
  e′ .dropʳ x p   = subst≡→[]≡ (E.dropʳ x p)
  e′ .swapʳ x y p = subst≡→[]≡ (E.swapʳ x y p)
  e′ .is-setʳ x   = _↔_.to (H-level↔H-level 2) (E.is-setʳ x)

-- A non-dependent eliminator, expressed using equality.

record Rec (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    []ʳ     : B
    ∷ʳ      : A → Finite-subset-of A → B → B
    dropʳ   : ∀ x y p →
              ∷ʳ x (x ∷ y) (∷ʳ x y p) ≡ ∷ʳ x y p
    swapʳ   : ∀ x y z p →
              ∷ʳ x (y ∷ z) (∷ʳ y z p) ≡ ∷ʳ y (x ∷ z) (∷ʳ x z p)
    is-setʳ : Is-set B

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
    []ʳ             : P []
    ∷ʳ              : ∀ x → P y → P (x ∷ y)
    is-propositionʳ : ∀ x → Is-proposition (P x)

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
    []ʳ             : B
    ∷ʳ              : A → Finite-subset-of A → B → B
    is-propositionʳ : Is-proposition B

open Rec-prop public

rec-prop : Rec-prop A B → Finite-subset-of A → B
rec-prop r = elim-prop e
  where
  module R = Rec-prop r

  e : Elim-prop _
  e .[]ʳ               = R.[]ʳ
  e .∷ʳ {y = y} x      = R.∷ʳ x y
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
[] ∪ y      = y
(x ∷ y) ∪ z = x ∷ (y ∪ z)

dropᴾ {x = x} {y = y} i ∪ z =
  dropᴾ {x = x} {y = y ∪ z} i

swapᴾ {x = x} {y = y} {z = z} i ∪ u =
  swapᴾ {x = x} {y = y} {z = z ∪ u} i

is-setᴾ x y i j ∪ z =
  is-setᴾ (λ i → x i ∪ z) (λ i → y i ∪ z) i j

-- [] is a right identity for _∪_.

∪[] :
  (x : Finite-subset-of A) →
  x ∪ [] ≡ x
∪[] = elim-prop e
  where
  e : Elim-prop _
  e .is-propositionʳ _ = is-set
  e .[]ʳ               = refl _
  e .∷ʳ {y = y} x hyp  =
    x ∷ y ∪ []  ≡⟨ cong (x ∷_) hyp ⟩∎
    x ∷ y       ∎

-- A lemma relating _∪_ and _∷_.

∪∷ :
  (x : Finite-subset-of A) →
  x ∪ (y ∷ z) ≡ y ∷ x ∪ z
∪∷ {y = y} {z = z} = elim-prop e
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
assoc {y = y} {z = z} = elim-prop e
  where
  e : Elim-prop _
  e .is-propositionʳ _ = is-set

  e .[]ʳ = refl _

  e .∷ʳ {y = u} x hyp =
    x ∷ u ∪ (y ∪ z)  ≡⟨ cong (x ∷_) hyp ⟩∎
    x ∷ (u ∪ y) ∪ z  ∎

-- Union is commutative.

comm :
  (x : Finite-subset-of A) →
  x ∪ y ≡ y ∪ x
comm {y = y} = elim-prop e
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

-- Union is idempotent.

idem : (x : Finite-subset-of A) → x ∪ x ≡ x
idem = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ =
    [] ∪ []  ≡⟨⟩
    []       ∎

  e .∷ʳ {y = y} x hyp =
    (x ∷ y) ∪ (x ∷ y)  ≡⟨⟩
    x ∷ y ∪ x ∷ y      ≡⟨ cong (_ ∷_) (∪∷ y) ⟩
    x ∷ x ∷ y ∪ y      ≡⟨ drop ⟩
    x ∷ y ∪ y          ≡⟨ cong (_ ∷_) hyp ⟩∎
    x ∷ y              ∎

  e .is-propositionʳ = λ _ → is-set

-- Union distributes from the left and right over union.

∪-distrib-left : ∀ x → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ (x ∪ z)
∪-distrib-left {y = y} {z = z} x =
  x ∪ (y ∪ z)        ≡⟨ cong (_∪ _) $ sym (idem x) ⟩
  (x ∪ x) ∪ (y ∪ z)  ≡⟨ sym $ assoc x ⟩
  x ∪ (x ∪ (y ∪ z))  ≡⟨ cong (x ∪_) $ assoc x ⟩
  x ∪ ((x ∪ y) ∪ z)  ≡⟨ cong ((x ∪_) ∘ (_∪ _)) $ comm x ⟩
  x ∪ ((y ∪ x) ∪ z)  ≡⟨ cong (x ∪_) $ sym $ assoc y ⟩
  x ∪ (y ∪ (x ∪ z))  ≡⟨ assoc x ⟩∎
  (x ∪ y) ∪ (x ∪ z)  ∎

∪-distrib-right : ∀ x → (x ∪ y) ∪ z ≡ (x ∪ z) ∪ (y ∪ z)
∪-distrib-right {y = y} {z = z} x =
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
>>=-right-distributive {y = y} {f = f} = elim-prop e
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

-- Bind distributes from the left over union.

>>=-left-distributive :
  ∀ x → (x >>=′ λ x → f x ∪ g x) ≡ (x >>=′ f) ∪ (x >>=′ g)
>>=-left-distributive {f = f} {g = g} = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ               = refl _
  e .is-propositionʳ _ = is-set
  e .∷ʳ {y = y} x hyp  =
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
singleton->>= {x = x} f =
  f x ∪ []  ≡⟨ ∪[] _ ⟩∎
  f x       ∎

>>=-singleton : x >>=′ singleton ≡ x
>>=-singleton = elim-prop e _
  where
  e : Elim-prop (λ x → x >>=′ singleton ≡ x)
  e .[]ʳ               = refl _
  e .is-propositionʳ _ = is-set
  e .∷ʳ {y = y} x hyp  =
    x ∷ (y >>=′ singleton)  ≡⟨ cong (_ ∷_) hyp ⟩∎
    x ∷ y                   ∎

>>=-assoc : ∀ x → x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
>>=-assoc {f = f} {g = g} = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ               = refl _
  e .is-propositionʳ _ = is-set
  e .∷ʳ {y = y} x hyp  =
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

private

  -- A function used to define map-Maybe.

  map-Maybe-cons : Maybe B → Finite-subset-of B → Finite-subset-of B
  map-Maybe-cons = maybe _∷_ id

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

-- The function map-Maybe f commutes with map-Maybe g if f commutes
-- with g in a certain way.

map-Maybe-comm :
  {A : Type a} {f g : A → Maybe A} →
  (∀ x → f =<< g x ≡ g =<< f x) →
  ∀ x → map-Maybe f (map-Maybe g x) ≡ map-Maybe g (map-Maybe f x)
map-Maybe-comm {A = A} {f = f} {g = g} hyp = elim-prop λ where
    .is-propositionʳ _ → is-set
    .[]ʳ               → refl _
    .∷ʳ {y = y} x      →
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
map-Maybe-∪ {f = f} = elim-prop λ where
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
map≡map-Maybe-just {f = f} = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ               = refl _
  e .∷ʳ x              = cong (f x ∷_)
  e .is-propositionʳ _ = is-set

-- The function map commutes with union.

map-∪ : ∀ x → map f (x ∪ y) ≡ map f x ∪ map f y
map-∪ {f = f} {y = y} x =
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

-- Filtering commutes with itself.

filter-comm :
  ∀ (p q : A → Bool) x →
  filter p (filter q x) ≡ filter q (filter p x)
filter-comm p q = elim-prop λ where
    .is-propositionʳ _ → is-set
    .[]ʳ               → refl _
    .∷ʳ {y = y} x      →
      lemma (p x) (q x) (filter p y) (filter q y) (refl _) (refl _)
  where
  lemma :
    ∀ (px qx : Bool) py qy →
    p x ≡ px → qx ≡ q x →
    filter p qy ≡ filter q py →
    filter p (map-Maybe-cons (include-if qx x) qy) ≡
    filter q (map-Maybe-cons (include-if px x) py)
  lemma {x = x} nothing nothing py qy ≡px qx≡ =
    filter p qy ≡ filter q py                            →⟨ trans (cong (λ px → map-Maybe-cons (include-if px x) (filter p qy)) ≡px) ∘
                                                            flip trans (cong (λ qx → map-Maybe-cons (include-if qx x) (filter q py)) qx≡) ∘
                                                            cong (x ∷_) ⟩□
    map-Maybe-cons (include-if (p x) x) (filter p qy) ≡
    map-Maybe-cons (include-if (q x) x) (filter q py)    □
  lemma {x = x} nothing (just qx) py qy _ qx≡ =
    filter p qy ≡ filter q py                          →⟨ flip trans (cong (λ qx → map-Maybe-cons (include-if qx x) (filter q py)) qx≡) ⟩□

    filter p qy ≡
    map-Maybe-cons (include-if (q x) x) (filter q py)  □
  lemma {x = x} (just px) nothing py qy ≡px _ =
    filter p qy ≡ filter q py                            →⟨ trans (cong (λ px → map-Maybe-cons (include-if px x) (filter p qy)) ≡px) ⟩□

    map-Maybe-cons (include-if (p x) x) (filter p qy) ≡
    filter q py                                          □
  lemma (just _) (just _) py qy _ _ =
    filter p qy ≡ filter q py  □

-- Filtering commutes with union.

filter-∪ :
  ∀ p x → filter p (x ∪ y) ≡ filter p x ∪ filter p y
filter-∪ _ = map-Maybe-∪

-- Converts lists to finite subsets.

from-List : List A → Finite-subset-of A
from-List = L.foldr _∷_ []
