------------------------------------------------------------------------
-- Listed finite subsets
------------------------------------------------------------------------

-- Based on Frumin, Geuvers, Gondelman and van der Weide's "Finite
-- Sets in Homotopy Type Theory".

{-# OPTIONS --cubical --safe #-}

open import Equality

module Finite-subset.Listed
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq hiding (elim)

import Equality.Path as P
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (swap)

open import Bag-equivalence eq as BE using (_∼[_]_; set)
open import Bijection eq as Bijection using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (id; _∘_)
open import H-level eq
open import H-level.Closure eq
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; ∣_∣)
import List eq as L
open import Monad eq as M using (Raw-monad; Monad)
open import Quotient eq as Q using (_/_)
open import Surjection eq using (_↠_)
import Univalence-axiom eq as Univ

private
  variable
    a b p         : Level
    A B           : Set a
    P             : A → Set p
    f g           : (x : A) → P x
    H x xs y ys z : A
    m n           : ℕ

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
      ∥ x ≡ y ⊎ x∈z ∥ , Trunc.truncation-is-proposition

    r .dropʳ y z (P , P-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (∥ x ≡ y ⊎ ∥ x ≡ y ⊎ P ∥ ∥  ↔⟨ inverse (Trunc.flatten′
                                                  (λ F → F (x ≡ y ⊎ x ≡ y) ⊎ P) (λ f → ⊎-map f id) [ Trunc.∥∥-map inj₁ , ∣_∣ ∘ inj₂ ]) F.∘
                                       Trunc.∥∥-cong ⊎-assoc F.∘
                                       Trunc.flatten′ (λ F → x ≡ y ⊎ F (x ≡ y ⊎ P)) (λ f → ⊎-map id f) [ ∣_∣ ∘ inj₁ , Trunc.∥∥-map inj₂ ] ⟩
         ∥ ∥ x ≡ y ⊎ x ≡ y ∥ ⊎ P ∥  ↔⟨ Trunc.flatten′ (λ F → F (x ≡ y) ⊎ P) (λ f → ⊎-map f id) [ Trunc.∥∥-map inj₁ , ∣_∣ ∘ inj₂ ] F.∘
                                       Trunc.∥∥-cong (Trunc.idempotent ⊎-cong F.id) ⟩□
         ∥ x ≡ y ⊎ P ∥              □)

    r .swapʳ y z u (P , P-prop) =
      _↔_.to (ignore-propositional-component
                (H-level-propositional ext 1)) $
      Univ.≃⇒≡ univ
        (∥ x ≡ y ⊎ ∥ x ≡ z ⊎ P ∥ ∥  ↔⟨ Trunc.∥∥-cong ⊎-assoc F.∘
                                       Trunc.flatten′ (λ F → x ≡ y ⊎ F (x ≡ z ⊎ P)) (λ f → ⊎-map id f) [ ∣_∣ ∘ inj₁ , Trunc.∥∥-map inj₂ ] ⟩
         ∥ (x ≡ y ⊎ x ≡ z) ⊎ P ∥    ↔⟨ Trunc.∥∥-cong (⊎-comm ⊎-cong F.id) ⟩
         ∥ (x ≡ z ⊎ x ≡ y) ⊎ P ∥    ↔⟨ inverse $
                                       Trunc.∥∥-cong ⊎-assoc F.∘
                                       Trunc.flatten′ (λ F → x ≡ z ⊎ F (x ≡ y ⊎ P)) (λ f → ⊎-map id f) [ ∣_∣ ∘ inj₁ , Trunc.∥∥-map inj₂ ] ⟩□
         ∥ x ≡ z ⊎ ∥ x ≡ y ⊎ P ∥ ∥  □)

    r .is-setʳ = Univ.∃-H-level-H-level-1+ ext univ 1

-- Membership.

infix 4 _∈_

_∈_ : {A : Set a} → A → Finite-subset-of A → Set a
x ∈ y = proj₁ (Membership x y)

-- Membership is propositional.

∈-propositional : ∀ y → Is-proposition (x ∈ y)
∈-propositional y = proj₂ (Membership _ y)

-- Unit tests documenting the computational behaviour of _∈_.

_ : (x ∈ []) ≡ ⊥
_ = refl _

_ : (x ∈ y ∷ z) ≡ ∥ x ≡ y ⊎ x ∈ z ∥
_ = refl _

-- If x is a member of y, then x is a member of y ∪ z.

∈→∈∪ˡ : ∀ y → x ∈ y → x ∈ y ∪ z
∈→∈∪ˡ {x = x} {z = z} = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ ()

  e .∷ʳ {y = y} u hyp =
    Trunc.rec (∈-propositional (u ∷ y ∪ z))
      [ (λ x≡u → ∣ inj₁ x≡u ∣)
      , (λ x∈y → ∣ inj₂ (hyp x∈y) ∣)
      ]

  e .is-propositionʳ y =
    Π-closure ext 1 λ _ →
    ∈-propositional (y ∪ z)

-- If x is a member of z, then x is a member of y ∪ z.

∈→∈∪ʳ : ∀ y → x ∈ z → x ∈ y ∪ z
∈→∈∪ʳ {x = x} {z = z} y =
  x ∈ z      ↝⟨ ∈→∈∪ˡ z ⟩
  x ∈ z ∪ y  ↝⟨ ≡⇒↝ _ (cong (_ ∈_) (comm z)) ⟩□
  x ∈ y ∪ z  □

-- Membership of a union of two subsets can be expressed in terms of
-- membership of the subsets.

∈∪≃∥∈⊎∈∥ : ∀ y → (x ∈ y ∪ z) ≃ ∥ x ∈ y ⊎ x ∈ z ∥
∈∪≃∥∈⊎∈∥ {x = x} {z = z} y =
  _↠_.from
    (Eq.≃↠⇔
       (∈-propositional (y ∪ z))
       Trunc.truncation-is-proposition)
    (record
       { from = Trunc.rec (∈-propositional (y ∪ z))
                  [ ∈→∈∪ˡ y , ∈→∈∪ʳ y ]
       ; to   = elim-prop e y
       })
  where
  e : Elim-prop (λ y → x ∈ y ∪ z → ∥ x ∈ y ⊎ x ∈ z ∥)
  e .[]ʳ = ∣_∣ ∘ inj₂

  e .∷ʳ {y = u} y hyp =
    Trunc.rec Trunc.truncation-is-proposition
      [ (λ x≡y → ∣ inj₁ ∣ inj₁ x≡y ∣ ∣)
      , (x ∈ u ∪ z              ↝⟨ hyp ⟩
         ∥ x ∈ u ⊎ x ∈ z ∥      ↝⟨ Trunc.∥∥-map (⊎-map (∣_∣ ∘ inj₂) id) ⟩□
         ∥ x ∈ y ∷ u ⊎ x ∈ z ∥  □)
      ]

  e .is-propositionʳ _ =
    Π-closure ext 1 λ _ →
    Trunc.truncation-is-proposition

-- If truncated equality is decidable, then membership is also
-- decidable.

member? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec (x ∈ y)
member? equal? x = elim-prop e
  where
  e : Elim-prop _
  e .[]ʳ          = no λ ()
  e .∷ʳ {y = z} y = case equal? x y of
    [ (λ  ∥x≡y∥ _ → yes (Trunc.∥∥-map inj₁ ∥x≡y∥))
    , (λ ¬∥x≡y∥ →
         [ (λ x∈z → yes ∣ inj₂ x∈z ∣)
         , (λ x∉z → no (
              x ∈ y ∷ z          ↔⟨⟩
              ∥ x ≡ y ⊎ x ∈ z ∥  ↝⟨ Trunc.∥∥-map [ ¬∥x≡y∥ ∘ ∣_∣ , x∉z ] ⟩
              ∥ ⊥ ∥              ↔⟨ Trunc.not-inhabited⇒∥∥↔⊥ id ⟩□
              ⊥                  □))
         ])
    ]
  e .is-propositionʳ y =
    Dec-closure-propositional ext (∈-propositional y)

-- Subsets.

_⊆_ : {A : Set a} → Finite-subset-of A → Finite-subset-of A → Set a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- If x is a member of y, then x ∷ y is equal to y.

∈→∷≡ : x ∈ y → x ∷ y ≡ y
∈→∷≡ {x = x} = elim-prop e _
  where
  e : Elim-prop (λ y → x ∈ y → x ∷ y ≡ y)
  e .∷ʳ {y = y} z hyp =
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

-- The subset property can be expressed using _∪_ and _≡_.

⊆≃∪≡ : ∀ x → (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {y = y} x =
  _↠_.from
    (Eq.≃↠⇔
       (Π-closure ext 1 λ _ →
        Π-closure ext 1 λ _ →
        ∈-propositional y)
       is-set)
    (record
       { to   = elim-prop e x
       ; from = λ p z →
           z ∈ x      ↝⟨ ∈→∈∪ˡ x ⟩
           z ∈ x ∪ y  ↝⟨ ≡⇒↝ _ (cong (z ∈_) p) ⟩□
           z ∈ y      □
       })
  where
  e : Elim-prop (λ x → x ⊆ y → x ∪ y ≡ y)
  e .[]ʳ _ =
    [] ∪ y  ≡⟨⟩
    y       ∎

  e .∷ʳ {y = z} x hyp x∷z⊆y =
    x ∷ z ∪ y  ≡⟨ cong (x ∷_) (hyp (λ _ → x∷z⊆y _ ∘ ∣_∣ ∘ inj₂)) ⟩
    x ∷ y      ≡⟨ ∈→∷≡ (x∷z⊆y x ∣ inj₁ (refl _) ∣) ⟩∎
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
          (∈-propositional x)
          (∈-propositional y)))
    (record
       { to   = λ x≡y z → ≡⇒↝ _ (cong (z ∈_) x≡y)
       ; from =
           (∀ z → z ∈ x ⇔ z ∈ y)  ↝⟨ (λ p → _⇔_.to ∘ p , _⇔_.from ∘ p) ⟩
           x ⊆ y × y ⊆ x          ↔⟨ ⊆≃∪≡ x ×-cong ⊆≃∪≡ y ⟩
           x ∪ y ≡ y × y ∪ x ≡ x  ↝⟨ (λ (p , q) → trans (sym q) (trans (comm y) p)) ⟩□
           x ≡ y                  □
       })

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
      ∀ x y Hyp n → Is-proposition (Cons′ x y Hyp n)
    Cons′-propositional x y Hyp zero =
      ⊎-closure-propositional
        (λ _ ())
        (×-closure 1 (∈-propositional y) (proj₂ (Hyp 0)))
        ⊥-propositional
    Cons′-propositional x y Hyp (suc n) =
      ⊎-closure-propositional
        (λ (x∈y , _) (x∉y , _) → x∉y x∈y)
        (×-closure 1 (∈-propositional y) (proj₂ (Hyp (suc n))))
        (×-closure 1 (¬-propositional ext) (proj₂ (Hyp n)))

    Cons :
      A → Finite-subset-of A →
      (ℕ → Proposition a) → (ℕ → Proposition a)
    Cons x y Hyp n =
        Cons′               x y Hyp n
      , Cons′-propositional x y Hyp n

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
        x ∈ x ∷ y          ↔⟨⟩
        ∥ x ≡ x ⊎ x ∈ y ∥  ↝⟨ Trunc.inhabited⇒∥∥↔⊤ ∣ inj₁ (refl _) ∣ ⟩□
        ⊤                  □

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
        inj₁ ( ∣ inj₂ y∈z ∣
             , inj₁
                 ( (                     $⟨ x∈y∷z ⟩
                    x ∈ y ∷ z  ↔⟨⟩
                    ∥ x ≡ y ⊎ x ∈ z ∥    ↝⟨ Trunc.∥∥-map [ (flip (subst (_∈ z)) y∈z ∘ sym) , id ] ⟩
                    ∥ x ∈ z ∥            ↔⟨ Trunc.∥∥↔ (∈-propositional z) ⟩□
                    x ∈ z                □)
                 , p
                 )
             )

      (suc n) (inj₁ (x∈y∷z , inj₂ (y∉z , p))) →
        Trunc.rec (Cons′-propositional y (x ∷ z) (Cons x z H) (suc n))
          [ (λ x≡y →
              inj₁ ( ∣ inj₁ (sym x≡y) ∣
                   , inj₂ ( (x ∈ z  ↝⟨ subst (_∈ z) x≡y ⟩
                             y ∈ z  ↝⟨ y∉z ⟩□
                             ⊥      □)
                          , p
                          )
                   ))
          , (λ x∈z →
               inj₂ ( (y ∈ x ∷ z          ↔⟨⟩
                       ∥ y ≡ x ⊎ y ∈ z ∥  ↝⟨ Trunc.∥∥-map [ flip (subst (_∈ z)) x∈z ∘ sym , id ] ⟩
                       ∥ y ∈ z ∥          ↝⟨ Trunc.∥∥-map y∉z ⟩
                       ∥ ⊥ ∥              ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                       ⊥                  □)
                    , inj₁ (x∈z , p)
                    ))
          ]
          x∈y∷z

      (suc n) (inj₂ (x∉y∷z , inj₁ (y∈z , p))) →
        inj₁ ( ∣ inj₂ y∈z ∣
             , inj₂ ( (x ∈ z      ↝⟨ ∣_∣ ∘ inj₂ ⟩
                       x ∈ y ∷ z  ↝⟨ x∉y∷z ⟩□
                       ⊥          □)
                    , p
                    )
             )

      (suc (suc n)) (inj₂ (x∉y∷z , inj₂ (y∉z , p))) →
        inj₂ ( (y ∈ x ∷ z              ↔⟨⟩
                ∥ y ≡ x ⊎ y ∈ z ∥      ↝⟨ Trunc.∥∥-map (⊎-map (∣_∣ ∘ inj₁ ∘ sym) id) ⟩
                ∥ x ∈ y ∷ z ⊎ y ∈ z ∥  ↝⟨ Trunc.∥∥-map [ x∉y∷z , y∉z ] ⟩
                ∥ ⊥ ∥                  ↔⟨ Trunc.∥∥↔ ⊥-propositional ⟩□
                ⊥                      □)
             , inj₂ ( (x ∈ z      ↝⟨ ∣_∣ ∘ inj₂ ⟩
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
           (Cons′-propositional x (y ∷ z) (Cons y z H) n)
           (Cons′-propositional y (x ∷ z) (Cons x z H) n))
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
  x ≡ y                  ↝⟨ ignore-propositional-component (Π-closure ext 1 (λ _ → ∈-propositional y)) ⟩□
  (x , p) ≡ (y , q)      □

------------------------------------------------------------------------
-- Some definitions related to the definitions in Bag-equivalence

private

  -- A lemma used in the definition of ≃List/∼.

  ∥∈∥≃∈′ : ∥ x BE.∈ ys ∥ ≃ (x ∈ L.foldr _∷_ [] ys)
  ∥∈∥≃∈′ {x = x} {ys = ys} = _↠_.from
    (Eq.≃↠⇔
       Trunc.truncation-is-proposition
       (∈-propositional (L.foldr _∷_ [] ys)))
    (record { to = to _; from = from _ })
    where
    to : ∀ ys → ∥ x BE.∈ ys ∥ → x ∈ L.foldr _∷_ [] ys
    to []       = Trunc.rec (∈-propositional {x = x} []) (λ ())
    to (y ∷ ys) = Trunc.∥∥-map (⊎-map id (to ys ∘ ∣_∣))

    from : ∀ ys → x ∈ L.foldr _∷_ [] ys → ∥ x BE.∈ ys ∥
    from [] ()
    from (y ∷ ys) = Trunc.rec
      Trunc.truncation-is-proposition
      [ ∣_∣ ∘ inj₁ , Trunc.∥∥-map inj₂ ∘ from ys ]

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
    r .dropʳ x _ = Q.elim-Prop _
      (λ xs → Q.[]-respects-relation λ z →
         z BE.∈ x ∷ x ∷ xs      ↝⟨ record { to = [ inj₁ , id ]; from = inj₂ } ⟩□
         z BE.∈ x ∷ xs          □)
      (λ _ → Q./-is-set)

    r .swapʳ x y _ = Q.elim-Prop _
      (λ xs → Q.[]-respects-relation λ z →
         z BE.∈ x ∷ y ∷ xs  ↔⟨ BE.swap-first-two z ⟩□
         z BE.∈ y ∷ x ∷ xs  □)
      (λ _ → Q./-is-set)

  from : List A / _∼[ set ]_ → Finite-subset-of A
  from {A = A} = Q.rec
    (L.foldr _∷_ [])
    (λ {xs ys} xs∼ys → _≃_.from extensionality λ z →
       z ∈ L.foldr _∷_ [] xs  ↔⟨ inverse ∥∈∥≃∈′ ⟩
       ∥ z BE.∈ xs ∥          ↔⟨ Trunc.∥∥-cong-⇔ {k = bijection} (xs∼ys z) ⟩
       ∥ z BE.∈ ys ∥          ↔⟨ ∥∈∥≃∈′ ⟩□
       z ∈ L.foldr _∷_ [] ys  □)
    is-set

  to∘from : ∀ x → to (from x) ≡ x
  to∘from = Q.elim-Prop _ lemma (λ _ → Q./-is-set)
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
      from (((x ∷_) Q./-map λ _ _ → refl _ BE.∷-cong_) (to y))  ≡⟨ Q.elim-Prop (λ y → from (((x ∷_) Q./-map λ _ _ → refl _ BE.∷-cong_) y) ≡
                                                                                      x ∷ from y)
                                                                     (λ _ → refl _)
                                                                     (λ _ → is-set)
                                                                     (to y) ⟩
      x ∷ from (to y)                                           ≡⟨ cong (x ∷_) hyp ⟩∎
      x ∷ y                                                     ∎

    e .is-propositionʳ _ = is-set

-- A truncated variant of the proof-relevant membership relation from
-- Bag-equivalence can be expressed in terms of _∈_.

∥∈∥≃∈ : ∥ x BE.∈ ys ∥ ≃ (x ∈ _≃_.from ≃List/∼ Q.[ ys ])
∥∈∥≃∈ = ∥∈∥≃∈′
