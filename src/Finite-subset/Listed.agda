------------------------------------------------------------------------
-- Listed finite subsets
------------------------------------------------------------------------

-- Based on Frumin, Geuvers, Gondelman and van der Weide's "Finite
-- Sets in Homotopy Type Theory".

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Finite-subset.Listed
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (swap)

open import Bag-equivalence equality-with-J as BE using (_∼[_]_; set)
open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; ∣_∣; _∥⊎∥_)
import List equality-with-J as L
open import Monad equality-with-J as M using (Raw-monad; Monad)
open import Quotient eq as Q using (_/_)
open import Surjection equality-with-J using (_↠_)
import Univalence-axiom equality-with-J as Univ

private
  variable
    a b                               : Level
    A B                               : Set a
    H p q x x₁ x₂ xs y y₁ y₂ ys z _≟_ : A
    P                                 : A → Set p
    f g                               : (x : A) → P x
    m n                               : ℕ

------------------------------------------------------------------------
-- Listed finite subsets

-- Listed finite subsets of a given type.

infixr 5 _∷_

data Finite-subset-of (A : Set a) : Set a where
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

record Elimᴾ {A : Set a} (P : Finite-subset-of A → Set p) :
             Set (a ⊔ p) where
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

record Recᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
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

record Elim {A : Set a} (P : Finite-subset-of A → Set p) :
            Set (a ⊔ p) where
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

record Rec (A : Set a) (B : Set b) : Set (a ⊔ b) where
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
         {A : Set a} (P : Finite-subset-of A → Set p) :
         Set (a ⊔ p) where
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
  e′ .is-setʳ _   = mono₁ 1 (E.is-propositionʳ _)

-- A non-dependent eliminator for propositions.

record Rec-prop (A : Set a) (B : Set b) : Set (a ⊔ b) where
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
    x ∷ y        ∎

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

------------------------------------------------------------------------
-- Membership

private

  -- Membership is used to define _∈_ and ∈-propositional below.

  Membership : {A : Set a} → A → Finite-subset-of A → Proposition a
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

    r .is-setʳ = Univ.∃-H-level-H-level-1+ ext univ 1

-- Membership.
--
-- The type is wrapped to make it easier for Agda to infer the subset
-- argument.

private
 module Dummy where

  infix 4 _∈_

  record _∈_ {A : Set a} (x : A) (y : Finite-subset-of A) : Set a where
    constructor box
    field
      unbox : proj₁ (Membership x y)

open Dummy public using (_∈_) hiding (module _∈_)

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
∈-propositional {x = x} {y = y} =          $⟨ proj₂ (Membership x y) ⟩
  Is-proposition (proj₁ (Membership x y))  ↝⟨ H-level-cong _ 1 (inverse ∈≃) ⦂ (_ → _) ⟩□
  Is-proposition (x ∈ y)                   □

-- A lemma characterising [].

∈[]≃ : (x ∈ []) ≃ ⊥₀
∈[]≃ {x = x} =
  x ∈ []  ↝⟨ ∈≃ ⟩
  ⊥       ↔⟨ ⊥↔⊥ ⟩□
  ⊥₀      □

-- A lemma characterising _∷_.

∈∷≃ : (x ∈ y ∷ z) ≃ (x ≡ y ∥⊎∥ x ∈ z)
∈∷≃ {x = x} {y = y} {z = z} =
  x ∈ y ∷ z                         ↝⟨ ∈≃ ⟩
  x ≡ y ∥⊎∥ proj₁ (Membership x z)  ↝⟨ F.id Trunc.∥⊎∥-cong inverse ∈≃ ⟩□
  x ≡ y ∥⊎∥ x ∈ z                   □

-- A variant.

∈≢∷≃ : x ≢ y → (x ∈ y ∷ z) ≃ (x ∈ z)
∈≢∷≃ {x = x} {y = y} {z = z} x≢y =
  x ∈ y ∷ z        ↝⟨ ∈∷≃ ⟩
  x ≡ y ∥⊎∥ x ∈ z  ↔⟨ Trunc.drop-⊥-left-∥⊎∥ ∈-propositional x≢y ⟩□
  x ∈ z            □

-- A lemma characterising singleton.

∈singleton≃ :
  (x ∈ singleton y) ≃ ∥ x ≡ y ∥
∈singleton≃ {x = x} {y = y} =
  x ∈ singleton y   ↝⟨ ∈∷≃ ⟩
  x ≡ y ∥⊎∥ x ∈ []  ↔⟨ Trunc.∥∥-cong $ drop-⊥-right ∈[]≃ ⟩□
  ∥ x ≡ y ∥         □

-- Some "introduction rules" for _∈_.

∈→∈∷ : x ∈ z → x ∈ y ∷ z
∈→∈∷ {x = x} {z = z} {y = y} =
  x ∈ z            ↝⟨ ∣_∣ ∘ inj₂ ⟩
  x ≡ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∷≃ ⟩□
  x ∈ y ∷ z        □

∥≡∥→∈∷ : ∥ x ≡ y ∥ → x ∈ y ∷ z
∥≡∥→∈∷ {x = x} {y = y} {z = z} =
  ∥ x ≡ y ∥        ↝⟨ Trunc.∥∥-map inj₁ ⟩
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
∈∪≃ {x = x} {y = y} {z = z} = elim-prop e y
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
∈→∈∪ˡ {x = x} {y = y} {z = z} =
  x ∈ y            ↝⟨ ∣_∣ ∘ inj₁ ⟩
  x ∈ y ∥⊎∥ x ∈ z  ↔⟨ inverse ∈∪≃ ⟩□
  x ∈ y ∪ z        □

∈→∈∪ʳ : ∀ y → x ∈ z → x ∈ y ∪ z
∈→∈∪ʳ {x = x} {z = z} y =
  x ∈ z      ↝⟨ ∈→∈∪ˡ ⟩
  x ∈ z ∪ y  ↝⟨ ≡⇒↝ _ (cong (_ ∈_) (comm z)) ⟩□
  x ∈ y ∪ z  □

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
      [ (λ x∈z → yes (∈→∈∷ x∈z))
      , (λ x∉z → no (
           x ∈ y ∷ z        ↔⟨ ∈∷≃ ⟩
           x ≡ y ∥⊎∥ x ∈ z  ↝⟨ Trunc.∥∥-map [ ¬∥x≡y∥ ∘ ∣_∣ , x∉z ] ⟩
           ∥ ⊥ ∥            ↔⟨ Trunc.not-inhabited⇒∥∥↔⊥ id ⟩□
           ⊥                □))
      ]
  e .is-propositionʳ y =
    Dec-closure-propositional ext ∈-propositional

-- If x is a member of y, then x ∷ y is equal to y.

∈→∷≡ : x ∈ y → x ∷ y ≡ y
∈→∷≡ {x = x} = elim-prop e _
  where
  e : Elim-prop (λ y → x ∈ y → x ∷ y ≡ y)
  e .∷ʳ {y = y} z hyp =
    x ∈ z ∷ y            ↔⟨ ∈∷≃ ⟩
    x ≡ z ∥⊎∥ x ∈ y      ↝⟨ id Trunc.∥⊎∥-cong hyp ⟩
    x ≡ z ∥⊎∥ x ∷ y ≡ y  ↝⟨ Trunc.rec is-set
                              [ (λ x≡z →
      x ∷ z ∷ y                  ≡⟨ cong (λ x → x ∷ _) x≡z ⟩
      z ∷ z ∷ y                  ≡⟨ drop ⟩∎
      z ∷ y                      ∎)
                              , (λ x∷y≡y →
      x ∷ z ∷ y                  ≡⟨ swap ⟩
      z ∷ x ∷ y                  ≡⟨ cong (_ ∷_) x∷y≡y ⟩∎
      z ∷ y                      ∎)
                              ] ⟩□
    x ∷ z ∷ y ≡ z ∷ y    □

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    is-set

------------------------------------------------------------------------
-- Subsets of subsets

-- Subsets.

infix 4 _⊆_

_⊆_ : {A : Set a} → Finite-subset-of A → Finite-subset-of A → Set a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- _⊆_ is pointwise propositional.

⊆-propositional : Is-proposition (x ⊆ y)
⊆-propositional =
  Π-closure ext 1 λ _ →
  Π-closure ext 1 λ _ →
  ∈-propositional

-- The subset property can be expressed using _∪_ and _≡_.

⊆≃∪≡ : ∀ x → (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {y = y} x =
  _↠_.from
    (Eq.≃↠⇔
       (Π-closure ext 1 λ _ →
        Π-closure ext 1 λ _ →
        ∈-propositional)
       is-set)
    (record
       { to   = elim-prop e x
       ; from = λ p z →
           z ∈ x      ↝⟨ ∈→∈∪ˡ ⟩
           z ∈ x ∪ y  ↝⟨ ≡⇒↝ _ (cong (z ∈_) p) ⟩□
           z ∈ y      □
       })
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

-- Extensionality.

extensionality :
  (x ≡ y) ≃ (∀ z → z ∈ x ⇔ z ∈ y)
extensionality {x = x} {y = y} =
  _↠_.from
    (Eq.≃↠⇔
       is-set
       (Π-closure ext 1 λ _ →
        ⇔-closure ext 1
          ∈-propositional
          ∈-propositional))
    (record
       { to   = λ x≡y z → ≡⇒↝ _ (cong (z ∈_) x≡y)
       ; from =
           (∀ z → z ∈ x ⇔ z ∈ y)  ↝⟨ (λ p → _⇔_.to ∘ p , _⇔_.from ∘ p) ⟩
           x ⊆ y × y ⊆ x          ↔⟨ ⊆≃∪≡ x ×-cong ⊆≃∪≡ y ⟩
           x ∪ y ≡ y × y ∪ x ≡ x  ↝⟨ (λ (p , q) → trans (sym q) (trans (comm y) p)) ⟩□
           x ≡ y                  □
       })

-- _⊆_ is a partial order.

⊆-refl : x ⊆ x
⊆-refl _ = id

⊆-trans : x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans x⊆y y⊆z _ = y⊆z _ ∘ x⊆y _

⊆-antisymmetric : x ⊆ y → y ⊆ x → x ≡ y
⊆-antisymmetric x⊆y y⊆x =
  _≃_.from extensionality λ z →
    record { to = x⊆y z; from = y⊆x z }

------------------------------------------------------------------------
-- The functions filter, minus and delete

-- A filter function.

filter : (A → Bool) → Finite-subset-of A → Finite-subset-of A
filter p = rec r
  where
  r : Rec _ _
  r .[]ʳ         = []
  r .∷ʳ x _ y    = if p x then x ∷ y else y
  r .is-setʳ     = is-set
  r .dropʳ x _ y = lemma (p x)
    where
    lemma :
      ∀ b →
      if b then x ∷ if b then x ∷ y else y else if b then x ∷ y else y ≡
      if b then x ∷ y else y
    lemma true  = drop
    lemma false = refl _

  r .swapʳ x y _ z = lemma (p x) (p y)
    where
    lemma :
      ∀ b₁ b₂ →
      (let u = if b₂ then y ∷ z else z in if b₁ then x ∷ u else u) ≡
      (let u = if b₁ then x ∷ z else z in if b₂ then y ∷ u else u)
    lemma true  true  = swap
    lemma _     false = refl _
    lemma false _     = refl _

-- A lemma characterising filter.

∈filter≃ : (x ∈ filter p y) ≃ (T (p x) × x ∈ y)
∈filter≃ {x = x} {p = p} = elim-prop e _
  where
  e : Elim-prop _
  e .[]ʳ =
    x ∈ filter p []   ↝⟨ ∈[]≃ ⟩
    ⊥                 ↔⟨ inverse ×-right-zero ⟩
    T (p x) × ⊥       ↝⟨ F.id ×-cong inverse ∈[]≃ ⟩□
    T (p x) × x ∈ []  □

  e .∷ʳ {y = y} z hyp =
    x ∈ if p z then z ∷ filter p y else filter p y  ↔⟨ lemma _ (refl _) ⟩
    T (p z) × x ≡ z ∥⊎∥ x ∈ filter p y              ↝⟨ Trunc.∥∥-cong $ (×-cong₁ λ eq → ≡⇒↝ _ $ cong (T ∘ p) (sym eq)) ⊎-cong hyp ⟩
    T (p x) × x ≡ z ∥⊎∥ T (p x) × x ∈ y             ↔⟨ inverse $ Trunc.Σ-∥⊎∥-distrib-left (T-propositional (p x)) ⟩
    T (p x) × (x ≡ z ∥⊎∥ x ∈ y)                     ↝⟨ F.id ×-cong inverse ∈∷≃ ⟩□
    T (p x) × x ∈ z ∷ y                             □
    where
    lemma :
      ∀ b → p z ≡ b →
      (x ∈ if b then z ∷ filter p y else filter p y) ↔
      T b × x ≡ z ∥⊎∥ x ∈ filter p y
    lemma true eq =
      x ∈ z ∷ filter p y            ↔⟨ ∈∷≃ ⟩
      x ≡ z ∥⊎∥ x ∈ filter p y      ↝⟨ inverse ×-left-identity Trunc.∥⊎∥-cong F.id ⟩
      ⊤ × x ≡ z ∥⊎∥ x ∈ filter p y  □
    lemma false eq =
      x ∈ filter p y                ↝⟨ inverse $ Trunc.drop-⊥-left-∥⊎∥ ∈-propositional (to-implication ×-left-zero) ⟩□
      ⊥ × x ≡ z ∥⊎∥ x ∈ filter p y  □

  e .is-propositionʳ y =
    Eq.left-closure ext 0 ∈-propositional

-- The result of filtering is a subset of the original subset.

filter⊆ : filter p x ⊆ x
filter⊆ {p = p} {x = x} z =
  z ∈ filter p x   ↔⟨ ∈filter≃ ⟩
  T (p z) × z ∈ x  ↝⟨ proj₂ ⟩□
  z ∈ x            □

-- Filtering commutes with itself.

filter-comm :
  ∀ x → filter p (filter q x) ≡ filter q (filter p x)
filter-comm {p = p} {q = q} x = _≃_.from extensionality λ y →
  y ∈ filter p (filter q x)    ↔⟨ from-isomorphism Σ-assoc F.∘ (F.id ×-cong ∈filter≃) F.∘ ∈filter≃ ⟩
  (T (p y) × T (q y)) × y ∈ x  ↔⟨ ×-comm ×-cong F.id ⟩
  (T (q y) × T (p y)) × y ∈ x  ↔⟨ inverse $ from-isomorphism Σ-assoc F.∘ (F.id ×-cong ∈filter≃) F.∘ ∈filter≃ ⟩□
  y ∈ filter q (filter p x)    □

-- Filtering commutes with union.

filter-∪ :
  ∀ x → filter p (x ∪ y) ≡ filter p x ∪ filter p y
filter-∪ {p = p} {y = y} x = _≃_.from extensionality λ z →
  z ∈ filter p (x ∪ y)                 ↔⟨ (F.id ×-cong ∈∪≃) F.∘ ∈filter≃ ⟩
  T (p z) × (z ∈ x ∥⊎∥ z ∈ y)          ↔⟨ Trunc.Σ-∥⊎∥-distrib-left (T-propositional (p z)) ⟩
  T (p z) × z ∈ x ∥⊎∥ T (p z) × z ∈ y  ↔⟨ inverse $ Trunc.∥∥-cong (∈filter≃ ⊎-cong ∈filter≃) F.∘ ∈∪≃ ⟩□
  z ∈ filter p x ∪ filter p y          □

-- If truncated equality is decidable, then one subset can be removed
-- from another.

minus :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  Finite-subset-of A → Finite-subset-of A → Finite-subset-of A
minus _≟_ x y =
  filter (λ z → if member? _≟_ z y then false else true) x

-- A lemma characterising minus.

∈minus≃ : (x ∈ minus _≟_ y z) ≃ (x ∈ y × ¬ x ∈ z)
∈minus≃ {x = x} {_≟_ = _≟_} {y = y} {z = z} =
  x ∈ minus _≟_ y z                                    ↝⟨ ∈filter≃ ⟩
  T (if member? _≟_ x z then false else true) × x ∈ y  ↔⟨ lemma (member? _≟_ x z) ×-cong F.id ⟩
  ¬ x ∈ z × x ∈ y                                      ↔⟨ ×-comm ⟩□
  x ∈ y × ¬ x ∈ z                                      □
  where
  lemma :
    (d : Dec A) →
    T (if d then false else true) ↔ ¬ A
  lemma (yes a) = Bijection.⊥↔uninhabited (_$ a)
  lemma (no ¬a) =
    inverse $
    _⇔_.to contractible⇔↔⊤ $
    propositional⇒inhabited⇒contractible
      (¬-propositional ext)
      ¬a

-- The result of minus is a subset of the original subset.

minus⊆ : minus _≟_ x y ⊆ x
minus⊆ = filter⊆

-- Minus commutes with itself (in a certain sense).

minus-comm :
  ∀ x y z →
  minus _≟_ (minus _≟_ x y) z ≡ minus _≟_ (minus _≟_ x z) y
minus-comm x _ _ = filter-comm x

-- Minus commutes with union (in a certain sense).

minus-∪ :
  ∀ x z →
  minus _≟_ (x ∪ y) z ≡ minus _≟_ x z ∪ minus _≟_ y z
minus-∪ x _ = filter-∪ x

-- A lemma relating minus, _⊆_ and _∪_.

minus⊆≃ : ∀ y → (minus _≟_ x y ⊆ z) ≃ (x ⊆ y ∪ z)
minus⊆≃ {_≟_ = _≟_} {x = x} {z = z} y =
  _↠_.from (Eq.≃↠⇔ ⊆-propositional ⊆-propositional) $ record
    { to = λ x-y⊆z u → case member? _≟_ u y of
        [ curry (
            u ∈ y × u ∈ x  ↝⟨ ∈→∈∪ˡ ∘ proj₁ ⟩□
            u ∈ y ∪ z      □)
        , curry (
            ¬ u ∈ y × u ∈ x    ↔⟨ inverse ∈minus≃ F.∘ from-isomorphism ×-comm ⟩
            u ∈ minus _≟_ x y  ↝⟨ x-y⊆z _ ⟩
            u ∈ z              ↝⟨ ∈→∈∪ʳ y ⟩□
            u ∈ y ∪ z          □)
        ]
    ; from = λ x⊆y∪z u →
        u ∈ minus _≟_ x y            ↔⟨ ∈minus≃ ⟩
        u ∈ x × ¬ u ∈ y              ↝⟨ Σ-map (x⊆y∪z _) id ⟩
        u ∈ y ∪ z × ¬ u ∈ y          ↔⟨ ∈∪≃ ×-cong F.id ⟩
        (u ∈ y ∥⊎∥ u ∈ z) × ¬ u ∈ y  ↔⟨ (×-cong₁ λ u∉y → Trunc.drop-⊥-left-∥⊎∥ ∈-propositional u∉y) ⟩
        u ∈ z × ¬ u ∈ y              ↝⟨ proj₁ ⟩□
        u ∈ z                        □
    }

-- If truncated equality is decidable, then elements can be removed
-- from a subset.

delete :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  A → Finite-subset-of A → Finite-subset-of A
delete _≟_ x y = minus _≟_ y (singleton x)

-- A lemma characterising delete.

∈delete≃ : ∀ _≟_ → (x ∈ delete _≟_ y z) ≃ (x ≢ y × x ∈ z)
∈delete≃ {x = x} {y = y} {z = z} _≟_ =
  x ∈ delete _≟_ y z         ↝⟨ ∈minus≃ {_≟_ = _≟_} ⟩
  x ∈ z × ¬ x ∈ singleton y  ↝⟨ F.id ×-cong →-cong₁ ext ∈singleton≃ ⟩
  x ∈ z × ¬ ∥ x ≡ y ∥        ↔⟨ F.id ×-cong Trunc.¬∥∥↔¬ ⟩
  x ∈ z × x ≢ y              ↔⟨ ×-comm ⟩□
  x ≢ y × x ∈ z              □

-- A deleted element is no longer a member of the set.

∉delete : ∀ _≟_ y → ¬ x ∈ delete _≟_ x y
∉delete {x = x} _≟_ y =
  x ∈ delete _≟_ x y  ↔⟨ ∈delete≃ _≟_ ⟩
  x ≢ x × x ∈ y       ↝⟨ (_$ refl _) ∘ proj₁ ⟩□
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

delete⊆≃ : ∀ _≟_ → (delete _≟_ x y ⊆ z) ≃ (y ⊆ x ∷ z)
delete⊆≃ _≟_ = minus⊆≃ {_≟_ = _≟_} (singleton _)

------------------------------------------------------------------------
-- Some preservation lemmas for _⊆_

-- Various operations preserve _⊆_.

∷-cong-⊆ : y ⊆ z → x ∷ y ⊆ x ∷ z
∷-cong-⊆ {y = y} {z = z} {x = x} y⊆z u =
  u ∈ x ∷ y        ↔⟨ ∈∷≃ ⟩
  u ≡ x ∥⊎∥ u ∈ y  ↝⟨ id Trunc.∥⊎∥-cong y⊆z _ ⟩
  u ≡ x ∥⊎∥ u ∈ z  ↔⟨ inverse ∈∷≃ ⟩□
  u ∈ x ∷ z        □

∪-cong-⊆ : x₁ ⊆ x₂ → y₁ ⊆ y₂ → x₁ ∪ y₁ ⊆ x₂ ∪ y₂
∪-cong-⊆ {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂} x₁⊆x₂ y₁⊆y₂ z =
  z ∈ x₁ ∪ y₁        ↔⟨ ∈∪≃ ⟩
  z ∈ x₁ ∥⊎∥ z ∈ y₁  ↝⟨ x₁⊆x₂ _ Trunc.∥⊎∥-cong y₁⊆y₂ _ ⟩
  z ∈ x₂ ∥⊎∥ z ∈ y₂  ↔⟨ inverse ∈∪≃ ⟩□
  z ∈ x₂ ∪ y₂        □

filter-cong-⊆ :
  (∀ z → T (p z) → T (q z)) →
  x ⊆ y → filter p x ⊆ filter q y
filter-cong-⊆ {p = p} {q = q} {x = x} {y = y} p⇒q x⊆y z =
  z ∈ filter p x   ↔⟨ ∈filter≃ ⟩
  T (p z) × z ∈ x  ↝⟨ Σ-map (p⇒q _) (x⊆y _) ⟩
  T (q z) × z ∈ y  ↔⟨ inverse ∈filter≃ ⟩□
  z ∈ filter q y   □

minus-cong-⊆ : x₁ ⊆ x₂ → y₂ ⊆ y₁ → minus _≟_ x₁ y₁ ⊆ minus _≟_ x₂ y₂
minus-cong-⊆ {x₁ = x₁} {x₂ = x₂} {y₂ = y₂} {y₁ = y₁} {_≟_ = _≟_}
             x₁⊆x₂ y₂⊆y₁ z =
  z ∈ minus _≟_ x₁ y₁  ↔⟨ ∈minus≃ ⟩
  z ∈ x₁ × ¬ z ∈ y₁    ↝⟨ Σ-map (x₁⊆x₂ _) (_∘ y₂⊆y₁ _) ⟩
  z ∈ x₂ × ¬ z ∈ y₂    ↔⟨ inverse ∈minus≃ ⟩□
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

  Size : {A : Set a} → Finite-subset-of A → ℕ → Proposition a
  Size {a = a} {A = A} = rec r
    where

    mutual

      -- The size of x ∷ y is equal to the size of y if x is a member
      -- of y, and otherwise it is equal to the successor of the size
      -- of y.

      Cons′ :
        A → Finite-subset-of A →
        (ℕ → Proposition a) → (ℕ → Set a)
      Cons′ x y ∣y∣≡ n =
        x ∈ y × proj₁ (∣y∣≡ n)
          ⊎
        Cons″ x y ∣y∣≡ n

      Cons″ :
        A → Finite-subset-of A →
        (ℕ → Proposition a) → (ℕ → Set a)
      Cons″ x y ∣y∣≡ zero    = ⊥
      Cons″ x y ∣y∣≡ (suc n) = ¬ x ∈ y × proj₁ (∣y∣≡ n)

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

    drop-lemma :
      Cons′ x (x ∷ y) (Cons x y H) n ≃ Cons′ x y H n
    drop-lemma {x = x} {y = y} {H = H} {n = n} =
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
        ¬ x ∈ x ∷ y × Cons′ x y H n  ↝⟨ →-cong ext x∈x∷y↔⊤ F.id ×-cong F.id ⟩
        ¬ ⊤ × Cons′ x y H n          ↝⟨ inverse (Bijection.⊥↔uninhabited (_$ _)) ×-cong F.id ⟩
        ⊥₀ × Cons′ x y H n           ↝⟨ ×-left-zero ⟩□
        ⊥                            □

    swap-lemma′ :
      ∀ n →
      x ∈ y ∷ z × Cons′ y z H n ⊎ Cons″ x (y ∷ z) (Cons y z H) n →
      y ∈ x ∷ z × Cons′ x z H n ⊎ Cons″ y (x ∷ z) (Cons x z H) n
    swap-lemma′ {x = x} {y = y} {z = z} {H = H} = λ where
      n (inj₁ (x∈y∷z , inj₁ (y∈z , p))) →
        inj₁ ( ∈→∈∷ y∈z
             , inj₁
                 ( (                 $⟨ x∈y∷z ⟩
                    x ∈ y ∷ z        ↔⟨ ∈∷≃ ⟩
                    x ≡ y ∥⊎∥ x ∈ z  ↝⟨ Trunc.∥∥-map [ (flip (subst (_∈ z)) y∈z ∘ sym) , id ] ⟩
                    ∥ x ∈ z ∥        ↔⟨ Trunc.∥∥↔ ∈-propositional ⟩□
                    x ∈ z            □)
                 , p
                 )
             )

      (suc n) (inj₁ (x∈y∷z , inj₂ (y∉z , p))) →
        Trunc.rec (Cons′-propositional (Cons x z H) _)
          [ (λ x≡y →
              inj₁ ( ≡→∈∷ (sym x≡y)
                   , inj₂ ( (x ∈ z  ↝⟨ subst (_∈ z) x≡y ⟩
                             y ∈ z  ↝⟨ y∉z ⟩□
                             ⊥      □)
                          , p
                          )
                   ))
          , (λ x∈z →
               inj₂ ( (y ∈ x ∷ z        ↔⟨ ∈∷≃ ⟩
                       y ≡ x ∥⊎∥ y ∈ z  ↝⟨ Trunc.∥∥-map [ flip (subst (_∈ z)) x∈z ∘ sym , id ] ⟩
                       ∥ y ∈ z ∥        ↝⟨ Trunc.∥∥-map y∉z ⟩
                       ∥ ⊥ ∥            ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                       ⊥                □)
                    , inj₁ (x∈z , p)
                    ))
          ]
          (_≃_.to ∈∷≃ x∈y∷z)

      (suc n) (inj₂ (x∉y∷z , inj₁ (y∈z , p))) →
        inj₁ ( ∈→∈∷ y∈z
             , inj₂ ( (x ∈ z      ↝⟨ ∈→∈∷ ⟩
                       x ∈ y ∷ z  ↝⟨ x∉y∷z ⟩□
                       ⊥          □)
                    , p
                    )
             )

      (suc (suc n)) (inj₂ (x∉y∷z , inj₂ (y∉z , p))) →
        inj₂ ( (y ∈ x ∷ z            ↔⟨ ∈∷≃ ⟩
                y ≡ x ∥⊎∥ y ∈ z      ↝⟨ ≡→∈∷ ∘ sym Trunc.∥⊎∥-cong id ⟩
                x ∈ y ∷ z ∥⊎∥ y ∈ z  ↝⟨ Trunc.∥∥-map [ x∉y∷z , y∉z ] ⟩
                ∥ ⊥ ∥                ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                ⊥                    □)
             , inj₂ ( (x ∈ z      ↝⟨ ∈→∈∷ ⟩
                       x ∈ y ∷ z  ↝⟨ x∉y∷z ⟩□
                       ⊥          □)
                    , p
                    )
             )

    swap-lemma :
      Cons′ x (y ∷ z) (Cons y z H) n ≃
      Cons′ y (x ∷ z) (Cons x z H) n
    swap-lemma {x = x} {y = y} {z = z} {H = H} {n = n} =
      _↠_.from
        (Eq.≃↠⇔
           (Cons′-propositional _ _)
           (Cons′-propositional _ _))
        (record { to = swap-lemma′ _; from = swap-lemma′ _ })

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

∣_∣≡_ : {A : Set a} → Finite-subset-of A → ℕ → Set a
∣ x ∣≡ n = proj₁ (Size x n)

-- The size predicate is propositional.

∣∣≡-propositional :
  (x : Finite-subset-of A) → Is-proposition (∣ x ∣≡ n)
∣∣≡-propositional x = proj₂ (Size x _)

-- Unit tests documenting the computational behaviour of ∣_∣≡_.

_ : (∣ [] {A = A} ∣≡ n) ≡ ↑ _ (n ≡ 0)
_ = refl _

_ : ∀ {A : Set a} {x : A} {y} →
    (∣ x ∷ y ∣≡ zero) ≡ (x ∈ y × ∣ y ∣≡ zero ⊎ ⊥)
_ = refl _

_ : (∣ x ∷ y ∣≡ suc n) ≡ (x ∈ y × ∣ y ∣≡ suc n ⊎ ¬ x ∈ y × ∣ y ∣≡ n)
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

  e .∷ʳ {y = y} x hyp = λ where
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

  e .∷ʳ {y = y} x (n , ∣y∣≡n) =
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

------------------------------------------------------------------------
-- Finite types

-- A type is finite if there is some finite subset of the type for
-- which every element of the type is a member of the subset.

is-finite : Set a → Set a
is-finite A = ∃ λ (s : Finite-subset-of A) → ∀ x → x ∈ s

-- The is-finite predicate is propositional.

is-finite-propositional : Is-proposition (is-finite A)
is-finite-propositional (x , p) (y , q) =
                         $⟨ (λ z → record { to = λ _ → q z; from = λ _ → p z }) ⟩
  (∀ z → z ∈ x ⇔ z ∈ y)  ↔⟨ inverse extensionality ⟩
  x ≡ y                  ↝⟨ ignore-propositional-component (Π-closure ext 1 (λ _ → ∈-propositional)) ⟩□
  (x , p) ≡ (y , q)      □

------------------------------------------------------------------------
-- Some definitions related to the definitions in Bag-equivalence

private

  -- A lemma used in the definition of ≃List/∼.

  ∥∈∥≃∈′ : ∥ x BE.∈ ys ∥ ≃ (x ∈ L.foldr _∷_ [] ys)
  ∥∈∥≃∈′ {x = x} {ys = ys} = _↠_.from
    (Eq.≃↠⇔
       Trunc.truncation-is-proposition
       ∈-propositional)
    (record { to = to _; from = from _ })
    where
    to : ∀ ys → ∥ x BE.∈ ys ∥ → x ∈ L.foldr _∷_ [] ys
    to []       = Trunc.rec ∈-propositional (λ ())
    to (y ∷ ys) = Trunc.rec ∈-propositional
                    [ ≡→∈∷ , ∈→∈∷ ∘ to ys ∘ ∣_∣ ]

    from : ∀ ys → x ∈ L.foldr _∷_ [] ys → ∥ x BE.∈ ys ∥
    from [] ()
    from (y ∷ ys) =
      Trunc.rec
        Trunc.truncation-is-proposition
        [ ∣_∣ ∘ inj₁ , Trunc.∥∥-map inj₂ ∘ from ys ] ∘
      _≃_.to ∈∷≃

-- Finite subsets can be expressed as lists quotiented by set
-- equivalence.

≃List/∼ : Finite-subset-of A ≃ List A / _∼[ set ]_
≃List/∼ = from-bijection (record
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
  to : Finite-subset-of A → List A / _∼[ set ]_
  to = rec r
    where
    r : Rec _ _
    r .[]ʳ       = Q.[ [] ]
    r .∷ʳ x _ y  = ((x ∷_) Q./-map λ _ _ → refl _ BE.∷-cong_) y
    r .is-setʳ   = Q./-is-set
    r .dropʳ x _ = Q.elim-prop λ where
      .Q.[]ʳ xs → Q.[]-respects-relation λ z →
        z BE.∈ x ∷ x ∷ xs      ↝⟨ record { to = [ inj₁ , id ]; from = inj₂ } ⟩□
        z BE.∈ x ∷ xs          □
      .Q.is-propositionʳ _ → Q./-is-set

    r .swapʳ x y _ = Q.elim-prop λ where
      .Q.[]ʳ xs → Q.[]-respects-relation λ z →
        z BE.∈ x ∷ y ∷ xs  ↔⟨ BE.swap-first-two z ⟩□
        z BE.∈ y ∷ x ∷ xs  □
      .Q.is-propositionʳ _ → Q./-is-set

  from : List A / _∼[ set ]_ → Finite-subset-of A
  from {A = A} = Q.rec λ where
    .Q.[]ʳ → L.foldr _∷_ []

    .Q.[]-respects-relationʳ {x = xs} {y = ys} xs∼ys →
      _≃_.from extensionality λ z →
        z ∈ L.foldr _∷_ [] xs  ↔⟨ inverse ∥∈∥≃∈′ ⟩
        ∥ z BE.∈ xs ∥          ↔⟨ Trunc.∥∥-cong-⇔ {k = bijection} (xs∼ys z) ⟩
        ∥ z BE.∈ ys ∥          ↔⟨ ∥∈∥≃∈′ ⟩□
        z ∈ L.foldr _∷_ [] ys  □

    .Q.is-setʳ → is-set

  to∘from : ∀ x → to (from x) ≡ x
  to∘from = Q.elim-prop λ where
      .Q.[]ʳ               → lemma
      .Q.is-propositionʳ _ → Q./-is-set
    where
    lemma : ∀ xs → to (L.foldr _∷_ [] xs) ≡ Q.[ xs ]
    lemma []       = refl _
    lemma (x ∷ xs) =
      to (L.foldr _∷_ [] (x ∷ xs))                         ≡⟨⟩
      ((x ∷_) Q./-map _) (to (L.foldr _∷_ [] xs))          ≡⟨ cong ((x ∷_) Q./-map _) (lemma xs) ⟩
      ((x ∷_) Q./-map λ _ _ → refl _ BE.∷-cong_) Q.[ xs ]  ≡⟨⟩
      Q.[ x ∷ xs ]                                         ∎

  from∘to : ∀ x → from (to x) ≡ x
  from∘to = elim-prop e
    where
    e : Elim-prop _
    e .[]ʳ = refl _

    e .∷ʳ {y = y} x hyp =
      from (to (x ∷ y))                                         ≡⟨⟩
      from (((x ∷_) Q./-map λ _ _ → refl _ BE.∷-cong_) (to y))  ≡⟨ Q.elim-prop
                                                                     {P = λ y → from (((x ∷_) Q./-map λ _ _ → refl _ BE.∷-cong_) y) ≡
                                                                                x ∷ from y}
                                                                     (λ where
                                                                        .Q.[]ʳ _             → refl _
                                                                        .Q.is-propositionʳ _ → is-set)
                                                                     (to y) ⟩
      x ∷ from (to y)                                           ≡⟨ cong (x ∷_) hyp ⟩∎
      x ∷ y                                                     ∎

    e .is-propositionʳ _ = is-set

-- A truncated variant of the proof-relevant membership relation from
-- Bag-equivalence can be expressed in terms of _∈_.

∥∈∥≃∈ : ∥ x BE.∈ ys ∥ ≃ (x ∈ _≃_.from ≃List/∼ Q.[ ys ])
∥∈∥≃∈ = ∥∈∥≃∈′
