------------------------------------------------------------------------
-- Kuratowski finite subsets
------------------------------------------------------------------------

-- Based on Frumin, Geuvers, Gondelman and van der Weide's "Finite
-- Sets in Homotopy Type Theory".

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Finite-subset.Kuratowski
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq using (_≃_)
import Finite-subset.Listed eq as L
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Truncation.Propositional eq as Trunc
  using (∥_∥; _∥⊎∥_)
open import Monad equality-with-J as M using (Raw-monad; Monad)

private
  variable
    a b p   : Level
    A B     : Set a
    P       : A → Set p
    f g     : (x : A) → P x
    l x y z : A
    m n     : ℕ

------------------------------------------------------------------------
-- Kuratowski finite subsets

-- Kuratowski finite subsets of a given type.

infixr 5 _∪_

data Finite-subset-of (A : Set a) : Set a where
  ∅         : Finite-subset-of A
  singleton : A → Finite-subset-of A
  _∪_       : Finite-subset-of A → Finite-subset-of A →
              Finite-subset-of A
  ∅∪ᴾ       : ∅ ∪ x P.≡ x
  idem-sᴾ   : singleton x ∪ singleton x P.≡ singleton x
  assocᴾ    : x ∪ (y ∪ z) P.≡ (x ∪ y) ∪ z
  commᴾ     : x ∪ y P.≡ y ∪ x
  is-setᴾ   : P.Is-set (Finite-subset-of A)

-- Variants of some of the constructors.

∅∪ : ∅ ∪ x ≡ x
∅∪ = _↔_.from ≡↔≡ ∅∪ᴾ

idem-s : singleton x ∪ singleton x ≡ singleton x
idem-s = _↔_.from ≡↔≡ idem-sᴾ

assoc : x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
assoc = _↔_.from ≡↔≡ assocᴾ

comm : x ∪ y ≡ y ∪ x
comm = _↔_.from ≡↔≡ commᴾ

is-set : Is-set (Finite-subset-of A)
is-set = _↔_.from (H-level↔H-level 2) is-setᴾ

-- ∅ is a right identity for _∪_.

∪∅ : x ∪ ∅ ≡ x
∪∅ {x = x} =
  x ∪ ∅  ≡⟨ comm ⟩
  ∅ ∪ x  ≡⟨ ∅∪ ⟩∎
  x      ∎

------------------------------------------------------------------------
-- Eliminators

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Set a} (P : Finite-subset-of A → Set p) :
             Set (a ⊔ p) where
  field
    ∅ʳ         : P ∅
    singletonʳ : ∀ x → P (singleton x)
    ∪ʳ         : P x → P y → P (x ∪ y)
    ∅∪ʳ        : (p : P x) →
                 P.[ (λ i → P (∅∪ᴾ {x = x} i)) ] ∪ʳ ∅ʳ p ≡ p
    idem-sʳ    : ∀ x →
                 P.[ (λ i → P (idem-sᴾ {x = x} i)) ]
                   ∪ʳ (singletonʳ x) (singletonʳ x) ≡ singletonʳ x
    assocʳ     : (p : P x) (q : P y) (r : P z) →
                 P.[ (λ i → P (assocᴾ {x = x} {y = y} {z = z} i)) ]
                   ∪ʳ p (∪ʳ q r) ≡ ∪ʳ (∪ʳ p q) r
    commʳ      : (p : P x) (q : P y) →
                 P.[ (λ i → P (commᴾ {x = x} {y = y} i)) ]
                   ∪ʳ p q ≡ ∪ʳ q p
    is-setʳ    : ∀ x → P.Is-set (P x)

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : Finite-subset-of A) → P x
elimᴾ {A = A} {P = P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Finite-subset-of A) → P x
  helper ∅                                  = E.∅ʳ
  helper (singleton x)                      = E.singletonʳ x
  helper (x ∪ y)                            = E.∪ʳ (helper x) (helper y)
  helper (∅∪ᴾ {x = x} i)                    = E.∅∪ʳ (helper x) i
  helper (idem-sᴾ i)                        = E.idem-sʳ _ i
  helper (assocᴾ {x = x} {y = y} {z = z} i) = E.assocʳ
                                                (helper x) (helper y)
                                                (helper z) i
  helper (commᴾ {x = x} {y = y} i)          = E.commʳ
                                                (helper x) (helper y) i
  helper (is-setᴾ x y i j)                  =
    P.heterogeneous-UIP E.is-setʳ (is-setᴾ x y)
      (λ i → helper (x i)) (λ i → helper (y i)) i j

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    ∅ʳ         : B
    singletonʳ : A → B
    ∪ʳ         : Finite-subset-of A → Finite-subset-of A → B → B → B
    ∅∪ʳ        : ∀ x p → ∪ʳ ∅ x ∅ʳ p P.≡ p
    idem-sʳ    : ∀ x →
                 ∪ʳ (singleton x) (singleton x)
                    (singletonʳ x) (singletonʳ x) P.≡
                 singletonʳ x
    assocʳ     : ∀ p q r →
                 ∪ʳ x (y ∪ z) p (∪ʳ y z q r) P.≡
                 ∪ʳ (x ∪ y) z (∪ʳ x y p q) r
    commʳ      : ∀ p q → ∪ʳ x y p q P.≡ ∪ʳ y x q p
    is-setʳ    : P.Is-set B

open Recᴾ public

recᴾ : Recᴾ A B → Finite-subset-of A → B
recᴾ r = elimᴾ e
  where
  module R = Recᴾ r

  e : Elimᴾ _
  e .∅ʳ                 = R.∅ʳ
  e .singletonʳ         = R.singletonʳ
  e .∪ʳ {x = x} {y = y} = R.∪ʳ x y
  e .∅∪ʳ {x = x}        = R.∅∪ʳ x
  e .idem-sʳ            = R.idem-sʳ
  e .assocʳ             = R.assocʳ
  e .commʳ              = R.commʳ
  e .is-setʳ _          = R.is-setʳ

-- A dependent eliminator, expressed using equality.

record Elim {A : Set a} (P : Finite-subset-of A → Set p) :
            Set (a ⊔ p) where
  field
    ∅ʳ         : P ∅
    singletonʳ : ∀ x → P (singleton x)
    ∪ʳ         : P x → P y → P (x ∪ y)
    ∅∪ʳ        : (p : P x) → subst P (∅∪ {x = x}) (∪ʳ ∅ʳ p) ≡ p
    idem-sʳ    : ∀ x →
                 subst P (idem-s {x = x})
                         (∪ʳ (singletonʳ x) (singletonʳ x)) ≡
                 singletonʳ x
    assocʳ     : (p : P x) (q : P y) (r : P z) →
                 subst P (assoc {x = x} {y = y} {z = z})
                         (∪ʳ p (∪ʳ q r)) ≡
                 ∪ʳ (∪ʳ p q) r
    commʳ      : (p : P x) (q : P y) →
                 subst P (comm {x = x} {y = y}) (∪ʳ p q) ≡ ∪ʳ q p
    is-setʳ    : ∀ x → Is-set (P x)

open Elim public

elim : Elim P → (x : Finite-subset-of A) → P x
elim e = elimᴾ e′
  where
  module E = Elim e

  e′ : Elimᴾ _
  e′ .∅ʳ           = E.∅ʳ
  e′ .singletonʳ   = E.singletonʳ
  e′ .∪ʳ           = E.∪ʳ
  e′ .∅∪ʳ p        = subst≡→[]≡ (E.∅∪ʳ p)
  e′ .idem-sʳ x    = subst≡→[]≡ (E.idem-sʳ x)
  e′ .assocʳ p q r = subst≡→[]≡ (E.assocʳ p q r)
  e′ .commʳ p q    = subst≡→[]≡ (E.commʳ p q)
  e′ .is-setʳ x    = _↔_.to (H-level↔H-level 2) (E.is-setʳ x)

-- A non-dependent eliminator, expressed using equality.

record Rec (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    ∅ʳ         : B
    singletonʳ : A → B
    ∪ʳ         : Finite-subset-of A → Finite-subset-of A → B → B → B
    ∅∪ʳ        : ∀ x p → ∪ʳ ∅ x ∅ʳ p ≡ p
    idem-sʳ    : ∀ x →
                 ∪ʳ (singleton x) (singleton x)
                    (singletonʳ x) (singletonʳ x) ≡
                 singletonʳ x
    assocʳ     : ∀ p q r →
                 ∪ʳ x (y ∪ z) p (∪ʳ y z q r) ≡
                 ∪ʳ (x ∪ y) z (∪ʳ x y p q) r
    commʳ      : ∀ p q → ∪ʳ x y p q ≡ ∪ʳ y x q p
    is-setʳ    : Is-set B

open Rec public

rec : Rec A B → Finite-subset-of A → B
rec r = recᴾ r′
  where
  module R = Rec r

  r′ : Recᴾ _ _
  r′ .∅ʳ           = R.∅ʳ
  r′ .singletonʳ   = R.singletonʳ
  r′ .∪ʳ           = R.∪ʳ
  r′ .∅∪ʳ x p      = _↔_.to ≡↔≡ (R.∅∪ʳ x p)
  r′ .idem-sʳ x    = _↔_.to ≡↔≡ (R.idem-sʳ x)
  r′ .assocʳ p q r = _↔_.to ≡↔≡ (R.assocʳ p q r)
  r′ .commʳ p q    = _↔_.to ≡↔≡ (R.commʳ p q)
  r′ .is-setʳ      = _↔_.to (H-level↔H-level 2) R.is-setʳ

-- A dependent eliminator for propositions.

record Elim-prop {A : Set a} (P : Finite-subset-of A → Set p) :
                 Set (a ⊔ p) where
  field
    ∅ʳ              : P ∅
    singletonʳ      : ∀ x → P (singleton x)
    ∪ʳ              : P x → P y → P (x ∪ y)
    is-propositionʳ : ∀ x → Is-proposition (P x)

open Elim-prop public

elim-prop : Elim-prop P → (x : Finite-subset-of A) → P x
elim-prop e = elim e′
  where
  module E = Elim-prop e

  e′ : Elim _
  e′ .∅ʳ           = E.∅ʳ
  e′ .singletonʳ   = E.singletonʳ
  e′ .∪ʳ           = E.∪ʳ
  e′ .∅∪ʳ _        = E.is-propositionʳ _ _ _
  e′ .idem-sʳ _    = E.is-propositionʳ _ _ _
  e′ .assocʳ _ _ _ = E.is-propositionʳ _ _ _
  e′ .commʳ _ _    = E.is-propositionʳ _ _ _
  e′ .is-setʳ _    = mono₁ 1 (E.is-propositionʳ _)

-- A non-dependent eliminator for propositions.

record Rec-prop (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    ∅ʳ              : B
    singletonʳ      : A → B
    ∪ʳ              : Finite-subset-of A → Finite-subset-of A →
                      B → B → B
    is-propositionʳ : Is-proposition B

open Rec-prop public

rec-prop : Rec-prop A B → Finite-subset-of A → B
rec-prop r = elim-prop e
  where
  module R = Rec-prop r

  e : Elim-prop _
  e .∅ʳ                 = R.∅ʳ
  e .singletonʳ         = R.singletonʳ
  e .∪ʳ {x = x} {y = y} = R.∪ʳ x y
  e .is-propositionʳ _  = R.is-propositionʳ

------------------------------------------------------------------------
-- Definitions related to listed finite subsets

private

  -- Some definitions used in the implementation of Listed≃Kuratowski
  -- below.

  to : L.Finite-subset-of A → Finite-subset-of A
  to L.[]      = ∅
  to (x L.∷ y) = singleton x ∪ to y

  to (L.dropᴾ {x = x} {y = y} i) =
    (singleton x ∪ (singleton x ∪ to y)  P.≡⟨ assocᴾ ⟩
     (singleton x ∪ singleton x) ∪ to y  P.≡⟨ P.cong (_∪ to y) idem-sᴾ ⟩∎
     singleton x ∪ to y                  ∎) i

  to (L.swapᴾ {x = x} {y = y} {z = z} i) =
    (singleton x ∪ (singleton y ∪ to z)  P.≡⟨ assocᴾ ⟩
     (singleton x ∪ singleton y) ∪ to z  P.≡⟨ P.cong (_∪ to z) commᴾ ⟩
     (singleton y ∪ singleton x) ∪ to z  P.≡⟨ P.sym assocᴾ ⟩∎
     singleton y ∪ (singleton x ∪ to z)  ∎) i

  to (L.is-setᴾ x y i j) =
    is-setᴾ (λ i → to (x i)) (λ i → to (y i)) i j

  to-∪ : (x : L.Finite-subset-of A) → to (x L.∪ y) ≡ to x ∪ to y
  to-∪ {y = y} = L.elim-prop e
    where
    e : L.Elim-prop _
    e .L.is-propositionʳ _ = is-set

    e .L.[]ʳ =
      to y      ≡⟨ sym ∅∪ ⟩∎
      ∅ ∪ to y  ∎

    e .L.∷ʳ {y = z} x hyp =
      singleton x ∪ to (z L.∪ y)   ≡⟨ cong (singleton x ∪_) hyp ⟩
      singleton x ∪ (to z ∪ to y)  ≡⟨ assoc ⟩∎
      (singleton x ∪ to z) ∪ to y  ∎

-- Listed finite subsets are equivalent to Kuratowski finite subsets.

Listed≃Kuratowski : L.Finite-subset-of A ≃ Finite-subset-of A
Listed≃Kuratowski {A = A} = from-bijection (record
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
  from : Finite-subset-of A → L.Finite-subset-of A
  from ∅             = L.[]
  from (singleton x) = x L.∷ L.[]
  from (x ∪ y)       = from x L.∪ from y

  from (∅∪ᴾ {x = x} _) = from x

  from (idem-sᴾ {x = x} i) = L.dropᴾ {x = x} {y = L.[]} i

  from (assocᴾ {x = x} {y = y} {z = z} i) =
    _↔_.to ≡↔≡ (L.assoc {y = from y} {z = from z} (from x)) i

  from (commᴾ {x = x} {y = y} i) =
    _↔_.to ≡↔≡ (L.comm {y = from y} (from x)) i

  from (is-setᴾ x y i j) =
    L.is-setᴾ (λ i → from (x i)) (λ i → from (y i)) i j

  to∘from : ∀ x → to (from x) ≡ x
  to∘from = elim-prop e
    where
    e : Elim-prop _
    e .is-propositionʳ _            = is-set
    e .∅ʳ                           = refl _
    e .singletonʳ _                 = ∪∅
    e .∪ʳ {x = x} {y = y} hyp₁ hyp₂ =
      to (from x L.∪ from y)     ≡⟨ to-∪ (from x) ⟩
      to (from x) ∪ to (from y)  ≡⟨ cong₂ _∪_ hyp₁ hyp₂ ⟩∎
      x ∪ y                      ∎

  from∘to : ∀ x → from (to x) ≡ x
  from∘to = L.elim-prop e
    where
    e : L.Elim-prop _
    e .L.is-propositionʳ _ = L.is-set
    e .L.[]ʳ               = refl _
    e .L.∷ʳ {y = y} x hyp  =
      x L.∷ from (to y)  ≡⟨ cong (x L.∷_) hyp ⟩∎
      x L.∷ y            ∎

-- The forward direction of Listed≃Kuratowski is homomorphic with
-- respect to L._∪_/_∪_.

to-Listed≃Kuratowski-∪ :
  (x : L.Finite-subset-of A) →
  _≃_.to Listed≃Kuratowski (x L.∪ y) ≡
  _≃_.to Listed≃Kuratowski x ∪ _≃_.to Listed≃Kuratowski y
to-Listed≃Kuratowski-∪ = to-∪

-- The other direction of Listed≃Kuratowski is definitionally
-- homomorphic with respect to _∪_/L._∪_.

_ :
  _≃_.from Listed≃Kuratowski (x ∪ y) ≡
  _≃_.from Listed≃Kuratowski x L.∪ _≃_.from Listed≃Kuratowski y
_ = refl _

-- A list-like dependent eliminator for Finite-subset-of, for
-- propositions.

record List-elim-prop
         {A : Set a} (P : Finite-subset-of A → Set p) :
         Set (a ⊔ p) where
  field
    []ʳ             : P ∅
    ∷ʳ              : ∀ x → P y → P (singleton x ∪ y)
    is-propositionʳ : ∀ x → Is-proposition (P x)

open List-elim-prop public

list-elim-prop : List-elim-prop P → (x : Finite-subset-of A) → P x
list-elim-prop {P = P} l x =
  subst P (_≃_.right-inverse-of Listed≃Kuratowski x)
    (L.elim-prop e (_≃_.from Listed≃Kuratowski x))
  where
  module E = List-elim-prop l

  e : L.Elim-prop (P ∘ _≃_.to Listed≃Kuratowski)
  e .L.[]ʳ               = E.[]ʳ
  e .L.∷ʳ x              = E.∷ʳ x
  e .L.is-propositionʳ _ = E.is-propositionʳ _

-- A list-like non-dependent eliminator for Finite-subset-of,
-- expressed using paths.

record List-recᴾ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    []ʳ     : B
    ∷ʳ      : A → Finite-subset-of A → B → B
    dropʳ   : ∀ x y p →
              ∷ʳ x (singleton x ∪ y) (∷ʳ x y p) P.≡ ∷ʳ x y p
    swapʳ   : ∀ x y z p →
              ∷ʳ x (singleton y ∪ z) (∷ʳ y z p) P.≡
              ∷ʳ y (singleton x ∪ z) (∷ʳ x z p)
    is-setʳ : P.Is-set B

open List-recᴾ public

list-recᴾ : List-recᴾ A B → Finite-subset-of A → B
list-recᴾ l = L.recᴾ r ∘ _≃_.from Listed≃Kuratowski
  where
  module E = List-recᴾ l

  r : L.Recᴾ _ _
  r .L.[]ʳ         = E.[]ʳ
  r .L.∷ʳ x y      = E.∷ʳ x (_≃_.to Listed≃Kuratowski y)
  r .L.dropʳ x y   = E.dropʳ x (_≃_.to Listed≃Kuratowski y)
  r .L.swapʳ x y z = E.swapʳ x y (_≃_.to Listed≃Kuratowski z)
  r .L.is-setʳ     = E.is-setʳ

-- Unit tests documenting some of the computational behaviour of
-- list-recᴾ.

_ : list-recᴾ l ∅ ≡ l .[]ʳ
_ = refl _

_ : list-recᴾ l (singleton x) ≡ l .∷ʳ x ∅ (l .[]ʳ)
_ = refl _

_ : let y′ = _≃_.to Listed≃Kuratowski (_≃_.from Listed≃Kuratowski y) in

    list-recᴾ l (singleton x ∪ y) ≡ l .∷ʳ x y′ (list-recᴾ l y)
_ = refl _

-- A list-like non-dependent eliminator for Finite-subset-of,
-- expressed using equality.

record List-rec (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    []ʳ     : B
    ∷ʳ      : A → Finite-subset-of A → B → B
    dropʳ   : ∀ x y p →
              ∷ʳ x (singleton x ∪ y) (∷ʳ x y p) ≡ ∷ʳ x y p
    swapʳ   : ∀ x y z p →
              ∷ʳ x (singleton y ∪ z) (∷ʳ y z p) ≡
              ∷ʳ y (singleton x ∪ z) (∷ʳ x z p)
    is-setʳ : Is-set B

open List-rec public

list-rec : List-rec A B → Finite-subset-of A → B
list-rec l = list-recᴾ l′
  where
  module R = List-rec l

  l′ : List-recᴾ _ _
  l′ .[]ʳ           = R.[]ʳ
  l′ .∷ʳ            = R.∷ʳ
  l′ .dropʳ x y p   = _↔_.to ≡↔≡ (R.dropʳ x y p)
  l′ .swapʳ x y z p = _↔_.to ≡↔≡ (R.swapʳ x y z p)
  l′ .is-setʳ       = _↔_.to (H-level↔H-level 2) R.is-setʳ

-- Unit tests documenting some of the computational behaviour of
-- list-rec.

_ : list-rec l ∅ ≡ l .[]ʳ
_ = refl _

_ : list-rec l (singleton x) ≡ l .∷ʳ x ∅ (l .[]ʳ)
_ = refl _

_ : let y′ = _≃_.to Listed≃Kuratowski (_≃_.from Listed≃Kuratowski y) in

    list-rec l (singleton x ∪ y) ≡ l .∷ʳ x y′ (list-rec l y)
_ = refl _

------------------------------------------------------------------------
-- Membership

-- Membership.

infix 4 _∈_

_∈_ : {A : Set a} → A → Finite-subset-of A → Set a
x ∈ y = x L.∈ _≃_.from Listed≃Kuratowski y

-- Membership is propositional.

∈-propositional : ∀ y → Is-proposition (x ∈ y)
∈-propositional _ = L.∈-propositional

-- A lemma characterising ∅.

∈∅≃ : (x ∈ ∅) ≃ ⊥₀
∈∅≃ = L.∈[]≃

-- A lemma characterising singleton.

∈singleton≃ : (x ∈ singleton y) ≃ ∥ x ≡ y ∥
∈singleton≃ = L.∈singleton≃

-- If x is a member of y, then x is a member of y ∪ z.

∈→∈∪ˡ : ∀ y z → x ∈ y → x ∈ y ∪ z
∈→∈∪ˡ {x = x} y z =
  x ∈ y                                                                ↔⟨⟩
  x L.∈ _≃_.from Listed≃Kuratowski y                                   ↝⟨ L.∈→∈∪ˡ ⟩
  x L.∈ _≃_.from Listed≃Kuratowski y L.∪ _≃_.from Listed≃Kuratowski z  ↔⟨⟩
  x L.∈ _≃_.from Listed≃Kuratowski (y ∪ z)                             ↔⟨⟩
  x ∈ y ∪ z                                                            □

-- If x is a member of z, then x is a member of y ∪ z.

∈→∈∪ʳ : ∀ y z → x ∈ z → x ∈ y ∪ z
∈→∈∪ʳ {x = x} y z =
  x ∈ z                                                                ↔⟨⟩
  x L.∈ _≃_.from Listed≃Kuratowski z                                   ↝⟨ L.∈→∈∪ʳ (_≃_.from Listed≃Kuratowski y) ⟩
  x L.∈ _≃_.from Listed≃Kuratowski y L.∪ _≃_.from Listed≃Kuratowski z  ↔⟨⟩
  x ∈ y ∪ z                                                            □

-- Membership of a union of two subsets can be expressed in terms of
-- membership of the subsets.

∈∪≃ : ∀ y z → (x ∈ y ∪ z) ≃ (x ∈ y ∥⊎∥ x ∈ z)
∈∪≃ {x = x} y z =
  x ∈ y ∪ z                                                            ↔⟨⟩

  x L.∈ _≃_.from Listed≃Kuratowski y L.∪ _≃_.from Listed≃Kuratowski z  ↝⟨ L.∈∪≃ ⟩

  x L.∈ _≃_.from Listed≃Kuratowski y ∥⊎∥
  x L.∈ _≃_.from Listed≃Kuratowski z                                   ↔⟨⟩

  x ∈ y ∥⊎∥ x ∈ z                                                      □

-- If truncated equality is decidable, then membership is also
-- decidable.

member? :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : A) (y : Finite-subset-of A) → Dec (x ∈ y)
member? equal? x = L.member? equal? x ∘ _≃_.from Listed≃Kuratowski

-- Subsets.

_⊆_ : {A : Set a} → Finite-subset-of A → Finite-subset-of A → Set a
x ⊆ y = ∀ z → z ∈ x → z ∈ y

-- The subset property can be expressed using _∪_ and _≡_.

⊆≃∪≡ : (x ⊆ y) ≃ (x ∪ y ≡ y)
⊆≃∪≡ {x = x} {y = y} =
  x ⊆ y                                                              ↝⟨ L.⊆≃∪≡ (_≃_.from Listed≃Kuratowski x) ⟩

  _≃_.from Listed≃Kuratowski x L.∪ _≃_.from Listed≃Kuratowski y ≡
  _≃_.from Listed≃Kuratowski y                                       ↔⟨⟩

  _≃_.from Listed≃Kuratowski (x ∪ y) ≡ _≃_.from Listed≃Kuratowski y  ↝⟨ Eq.≃-≡ (inverse Listed≃Kuratowski) ⟩□

  x ∪ y ≡ y                                                          □

-- Extensionality.

extensionality :
  (x ≡ y) ≃ (∀ z → z ∈ x ⇔ z ∈ y)
extensionality {x = x} {y = y} =
  x ≡ y                                                        ↝⟨ inverse $ Eq.≃-≡ (inverse Listed≃Kuratowski) ⟩
  _≃_.from Listed≃Kuratowski x ≡ _≃_.from Listed≃Kuratowski y  ↝⟨ L.extensionality ⟩□
  (∀ z → z ∈ x ⇔ z ∈ y)                                        □

------------------------------------------------------------------------
-- A law

-- Union is idempotent.

idem : x ∪ x ≡ x
idem {x = x} = _≃_.from extensionality λ y →
  y ∈ x ∪ x        ↔⟨ ∈∪≃ x x ⟩
  y ∈ x ∥⊎∥ y ∈ x  ↔⟨ Trunc.idempotent ⟩
  ∥ y ∈ x ∥        ↔⟨ Trunc.∥∥↔ (∈-propositional x) ⟩□
  y ∈ x            □

------------------------------------------------------------------------
-- Some operations

-- A map function.

map : (A → B) → Finite-subset-of A → Finite-subset-of B
map f = recᴾ r
  where
  r : Recᴾ _ _
  r .∅ʳ           = ∅
  r .singletonʳ x = singleton (f x)
  r .∪ʳ _ _       = _∪_
  r .∅∪ʳ _ _      = ∅∪ᴾ
  r .idem-sʳ _    = idem-sᴾ
  r .assocʳ _ _ _ = assocᴾ
  r .commʳ _ _    = commᴾ
  r .is-setʳ      = is-setᴾ

-- A filter function.

filter : (A → Bool) → Finite-subset-of A → Finite-subset-of A
filter p = rec r
  where
  r : Rec _ _
  r .∅ʳ           = ∅
  r .singletonʳ x = if p x then singleton x else ∅
  r .∪ʳ _ _       = _∪_
  r .∅∪ʳ _ _      = ∅∪
  r .idem-sʳ _    = idem
  r .assocʳ _ _ _ = assoc
  r .commʳ _ _    = comm
  r .is-setʳ      = is-set

-- Join.

join : Finite-subset-of (Finite-subset-of A) → Finite-subset-of A
join = rec r
  where
  r : Rec _ _
  r .∅ʳ           = ∅
  r .singletonʳ   = id
  r .∪ʳ _ _       = _∪_
  r .∅∪ʳ _ _      = ∅∪
  r .idem-sʳ _    = idem
  r .assocʳ _ _ _ = assoc
  r .commʳ _ _    = comm
  r .is-setʳ      = is-set

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ :
  Finite-subset-of A → (A → Finite-subset-of B) → Finite-subset-of B
x >>=′ f = join (map f x)

-- Bind distributes from the right over union.

_ : (x ∪ y) >>=′ f ≡ (x >>=′ f) ∪ (y >>=′ f)
_ = refl _

-- Bind distributes from the left over union.

>>=-left-distributive :
  ∀ x → (x >>=′ λ x → f x ∪ g x) ≡ (x >>=′ f) ∪ (x >>=′ g)
>>=-left-distributive {f = f} {g = g} = elim-prop e
  where
  e : Elim-prop _
  e .∅ʳ                           = ∅      ≡⟨ sym idem ⟩∎
                                    ∅ ∪ ∅  ∎
  e .singletonʳ _                 = refl _
  e .is-propositionʳ _            = is-set
  e .∪ʳ {x = x} {y = y} hyp₁ hyp₂ =
    (x ∪ y) >>=′ (λ x → f x ∪ g x)                         ≡⟨⟩
    (x >>=′ λ x → f x ∪ g x) ∪ (y >>=′ λ x → f x ∪ g x)    ≡⟨ cong₂ _∪_ hyp₁ hyp₂ ⟩
    ((x >>=′ f) ∪ (x >>=′ g)) ∪ ((y >>=′ f) ∪ (y >>=′ g))  ≡⟨ sym assoc ⟩
    (x >>=′ f) ∪ ((x >>=′ g) ∪ ((y >>=′ f) ∪ (y >>=′ g)))  ≡⟨ cong ((x >>=′ f) ∪_) assoc ⟩
    (x >>=′ f) ∪ (((x >>=′ g) ∪ (y >>=′ f)) ∪ (y >>=′ g))  ≡⟨ cong (((x >>=′ f) ∪_) ∘ (_∪ (y >>=′ g))) comm ⟩
    (x >>=′ f) ∪ (((y >>=′ f) ∪ (x >>=′ g)) ∪ (y >>=′ g))  ≡⟨ cong ((x >>=′ f) ∪_) (sym assoc) ⟩
    (x >>=′ f) ∪ ((y >>=′ f) ∪ ((x >>=′ g) ∪ (y >>=′ g)))  ≡⟨ assoc ⟩
    ((x >>=′ f) ∪ (y >>=′ f)) ∪ ((x >>=′ g) ∪ (y >>=′ g))  ≡⟨⟩
    ((x ∪ y) >>=′ f) ∪ ((x ∪ y) >>=′ g)                    ∎

-- Monad laws.

_ : singleton x >>=′ f ≡ f x
_ = refl _

>>=-singleton : x >>=′ singleton ≡ x
>>=-singleton = elim-prop e _
  where
  e : Elim-prop (λ x → x >>=′ singleton ≡ x)
  e .∅ʳ                           = refl _
  e .singletonʳ _                 = refl _
  e .is-propositionʳ _            = is-set
  e .∪ʳ {x = x} {y = y} hyp₁ hyp₂ =
    (x ∪ y) >>=′ singleton                   ≡⟨⟩
    (x >>=′ singleton) ∪ (y >>=′ singleton)  ≡⟨ cong₂ _∪_ hyp₁ hyp₂ ⟩∎
    x ∪ y                                    ∎

>>=-assoc : ∀ x → x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
>>=-assoc {f = f} {g = g} = elim-prop e
  where
  e : Elim-prop _
  e .∅ʳ                           = refl _
  e .singletonʳ _                 = refl _
  e .is-propositionʳ _            = is-set
  e .∪ʳ {x = x} {y = y} hyp₁ hyp₂ =
    (x ∪ y) >>=′ (λ x → f x >>=′ g)                        ≡⟨⟩
    (x >>=′ λ x → f x >>=′ g) ∪ (y >>=′ λ x → f x >>=′ g)  ≡⟨ cong₂ _∪_ hyp₁ hyp₂ ⟩
    (x >>=′ f >>=′ g) ∪ (y >>=′ f >>=′ g)                  ≡⟨⟩
    (x ∪ y) >>=′ f >>=′ g                                  ∎

-- A monad instance.

instance

  raw-monad : Raw-monad {d = a} Finite-subset-of
  raw-monad .M.return = singleton
  raw-monad .M._>>=_  = _>>=′_

  monad : Monad {d = a} Finite-subset-of
  monad .M.Monad.raw-monad           = raw-monad
  monad .M.Monad.left-identity _ _   = refl _
  monad .M.Monad.right-identity _    = >>=-singleton
  monad .M.Monad.associativity x _ _ = >>=-assoc x

------------------------------------------------------------------------
-- Size

-- Size.

infix 4 ∣_∣≡_

∣_∣≡_ : {A : Set a} → Finite-subset-of A → ℕ → Set a
∣ x ∣≡ n = L.∣ _≃_.from Listed≃Kuratowski x ∣≡ n

-- The size predicate is propositional.

∣∣≡-propositional :
  (x : Finite-subset-of A) → Is-proposition (∣ x ∣≡ n)
∣∣≡-propositional = L.∣∣≡-propositional ∘ _≃_.from Listed≃Kuratowski

-- Unit tests documenting some of the computational behaviour of
-- ∣_∣≡_.

_ : (∣ ∅ {A = A} ∣≡ n) ≡ ↑ _ (n ≡ 0)
_ = refl _

_ : ∀ {A : Set a} {x : A} {y} →
    (∣ singleton x ∪ y ∣≡ zero) ≡ (x ∈ y × ∣ y ∣≡ zero ⊎ ⊥)
_ = refl _

_ : (∣ singleton x ∪ y ∣≡ suc n) ≡
    (x ∈ y × ∣ y ∣≡ suc n ⊎ ¬ x ∈ y × ∣ y ∣≡ n)
_ = refl _

-- The size predicate is functional.

∣∣≡-functional :
  (x : Finite-subset-of A) → ∣ x ∣≡ m → ∣ x ∣≡ n → m ≡ n
∣∣≡-functional = L.∣∣≡-functional ∘ _≃_.from Listed≃Kuratowski

-- If truncated equality is decidable, then one can compute the size
-- of a finite subset.

size :
  ((x y : A) → Dec ∥ x ≡ y ∥) →
  (x : Finite-subset-of A) → ∃ λ n → ∣ x ∣≡ n
size equal? = L.size equal? ∘ _≃_.from Listed≃Kuratowski
