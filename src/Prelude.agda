------------------------------------------------------------------------
-- A small prelude
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Note that parts of Agda's standard library make use of the K rule.

module Prelude where

------------------------------------------------------------------------
-- Support for universe polymorphism

-- Universe levels.

open import Agda.Primitive public using (Level; _⊔_; lzero; lsuc)

private
  variable
    a b c ℓ p q r w              : Level
    A A₁ A₂ B B₁ B₂ C D Whatever : Set a
    P Q R                        : A → Set p

-- Lifting.

record ↑ ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open ↑ public

------------------------------------------------------------------------
-- Strings

open import Agda.Builtin.String public using (String)

------------------------------------------------------------------------
-- The unit type

-- A variant of the unit type with η-equality.

open import Agda.Builtin.Unit public using (⊤; tt)

-- A variant without η-equality.

data Unit : Set where
  unit : Unit

-- Block s is used to block unfolding (for performance reasons). The
-- string can be used to indicate what it is that is blocked.

Block : String → Set
Block _ = Unit

pattern ⊠ = unit

-- A function that can be used to locally block something.

block : (Unit → A) → A
block f = f ⊠

-- A function that can be used to unblock something.

unblock : (b : Unit) (P : Unit → Set p) → P ⊠ → P b
unblock ⊠ _ p = p

------------------------------------------------------------------------
-- The empty type

data ⊥ {ℓ} : Set ℓ where

⊥-elim : ⊥ {ℓ = ℓ} → Whatever
⊥-elim ()

-- A version of the empty type that is not universe-polymorphic.

⊥₀ : Set
⊥₀ = ⊥

-- Negation.

infix 3 ¬_

¬_ : Set ℓ → Set ℓ
¬ P = P → ⊥₀

------------------------------------------------------------------------
-- Natural numbers

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ; _-_ to _∸_)

-- Dependent eliminator.

ℕ-rec : P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n
ℕ-rec z s zero    = z
ℕ-rec z s (suc n) = s n (ℕ-rec z s n)

-- Exponentiation.

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
m ^ zero  = 1
m ^ suc n = m * m ^ n

-- Factorial.

infix 9 _!

_! : ℕ → ℕ
zero  ! = 1
suc n ! = suc n * n !

-- Translation from natural numbers to levels.

# : ℕ → Level
# zero    = lzero
# (suc n) = lsuc (# n)

------------------------------------------------------------------------
-- Combinators defined using only abstraction and application

infixr 9 _∘_
infixl 1 _on_
infixr 0 _$_

-- The identity function.

id : A → A
id x = x

-- Composition.

_∘_ : {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- Application.

_$_ : {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

-- Constant functions.

const : A → (B → A)
const x = λ _ → x

{-# DISPLAY const x y = x #-}

-- Flips the first two arguments.

flip : {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ x y → f y x

-- Applies the unary function to each argument and combines the
-- results using the binary function.

_on_ : {C : B → B → Set c} →
       ((x y : B) → C x y) →
       (f : A → B) →
       ((x y : A) → C (f x) (f y))
_*_ on f = λ x y → f x * f y

-- A term's type.

Type-of : {A : Set a} → A → Set a
Type-of {A = A} _ = A

-- Type signatures.

infix 0 type-signature

type-signature : (A : Set a) → A → A
type-signature _ a = a

syntax type-signature A a = a ⦂ A

-- The it function can be used to instantiate an argument by using
-- instance search.

it : ⦃ _ : A ⦄ → A
it ⦃ x ⦄ = x

-- Case expressions (to be used with pattern-matching lambdas).

infix 0 case_return_of_ case_of_

case_return_of_ :
  (x : A) (B : A → Set b) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : A → (A → B) → B
case x of f = case x return _ of f

------------------------------------------------------------------------
-- Σ-types

infixr 4 _,′_
infixr 2 _×_

import Agda.Builtin.Sigma
open Agda.Builtin.Sigma public
  using (Σ; _,_)
  hiding (module Σ)
  renaming (fst to proj₁; snd to proj₂)
module Σ where
  open Agda.Builtin.Sigma.Σ public
    using ()
    renaming (fst to proj₁; snd to proj₂)

-- A variant where the first argument is implicit.

∃ : {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

-- Binary products.

_×_ : (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (const B)

-- A variant of _,_ that is specialised to _×_. Use of this variant
-- can make type-inference easier.

_,′_ : A → B → A × B
_,′_ = _,_

-- A map function.

Σ-map : (f : A → B) → (∀ {x} → P x → Q (f x)) →
        Σ A P → Σ B Q
Σ-map f g = λ p → (f (proj₁ p) , g (proj₂ p))

-- Zip.

Σ-zip : (f : A → B → C) → (∀ {x y} → P x → Q y → R (f x y)) →
        Σ A P → Σ B Q → Σ C R
Σ-zip f g = λ p q → (f (proj₁ p) (proj₁ q) , g (proj₂ p) (proj₂ q))

-- Curry and uncurry.

curry : {B : A → Set b} {C : Σ A B → Set c} →
        ((p : Σ A B) → C p) →
        ((x : A) (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

-- Swaps the two components of the pair.

swap : A × B → B × A
swap (x , y) = y , x

------------------------------------------------------------------------
-- W-types

data W (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  sup : (x : A) (f : B x → W A B) → W A B

-- Projections.

headᵂ : {B : A → Set b} → W A B → A
headᵂ (sup x f) = x

tailᵂ : {B : A → Set b} → (x : W A B) → B (headᵂ x) → W A B
tailᵂ (sup x f) = f

-- If B is always inhabited, then W A B is empty.

abstract

  inhabited⇒W-empty : {B : A → Set b} → (∀ x → B x) → ¬ W A B
  inhabited⇒W-empty b (sup x f) = inhabited⇒W-empty b (f (b x))

------------------------------------------------------------------------
-- Binary sums

infixr 1 _⊎_

data _⊎_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

-- Eliminator for binary sums.

[_,_] : {C : A ⊎ B → Set c} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

-- A generalisation of if-then-else.

infix 5 if_then_else_

if_then_else_ : A ⊎ B → C → C → C
if x then t else f = [ const t , const f ] x

-- A map function.

⊎-map : (A₁ → A₂) → (B₁ → B₂) → A₁ ⊎ B₁ → A₂ ⊎ B₂
⊎-map f g = [ inj₁ ∘ f , inj₂ ∘ g ]

-- The function from-⊎ is a safe analogue of fromJust. For an example
-- of how from-⊎ can be used, see
-- Quotient.equivalence-but-not-strong-equivalence.

From-⊎ : ∀ {ℓ} {A B : Set ℓ} → A ⊎ B → Set ℓ
From-⊎ {A = A} (inj₁ _) = A
From-⊎ {B = B} (inj₂ _) = B

from-⊎ : (x : A ⊎ B) → From-⊎ x
from-⊎ (inj₁ x) = x
from-⊎ (inj₂ y) = y

-- A special case of binary sums: decided predicates.

Dec : Set p → Set p
Dec P = P ⊎ ¬ P

pattern yes p = inj₁ p
pattern no  p = inj₂ p

-- Decidable relations.

Decidable : {A : Set a} {B : Set b} →
            (A → B → Set ℓ) → Set (a ⊔ b ⊔ ℓ)
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

-- Exclusive or.

infixr 1 _Xor_

_Xor_ : Set a → Set b → Set (a ⊔ b)
A Xor B = (A × ¬ B) ⊎ (¬ A × B)

-- Maybe.

Maybe : Set a → Set a
Maybe A = ⊤ ⊎ A

pattern nothing = inj₁ tt
pattern just x  = inj₂ x

-- The truth predicate T is only inhabited when its argument is
-- inj₁ something.

T : A ⊎ B → Set
T b = if b then ⊤ else ⊥

------------------------------------------------------------------------
-- Booleans

-- Booleans.

Bool : Set
Bool = ⊤ ⊎ ⊤

pattern true  = inj₁ tt
pattern false = inj₂ tt

-- Not.

not : Bool → Bool
not b = if b then false else true

-- And.

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
b₁ ∧ b₂ = if b₁ then b₂ else false

-- Or.

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
b₁ ∨ b₂ = if b₁ then true else b₂

------------------------------------------------------------------------
-- Lists

open import Agda.Builtin.List public using (List; []; _∷_)

------------------------------------------------------------------------
-- Finite sets

Fin : ℕ → Set
Fin zero    = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

pattern fzero  = inj₁ tt
pattern fsuc i = inj₂ i

------------------------------------------------------------------------
-- Some relation combinators

-- Combines two relations into a relation on functions.

_→-rel_ : {A : Set a} {C : Set c} →
          (A → C → Set ℓ) → (B → D → Set ℓ) →
          (A → B) → (C → D) → Set (a ⊔ c ⊔ ℓ)
(P →-rel Q) f g = ∀ x y → P x y → Q (f x) (g y)

-- Combines two relations into a relation on products.

_×-rel_ : (A → C → Set ℓ) → (B → D → Set ℓ) → A × B → C × D → Set ℓ
(P ×-rel Q) (x , u) (y , v) = P x y × Q u v

-- Combines two relations into a relation on sums.

_⊎-rel_ : (A → C → Set ℓ) → (B → D → Set ℓ) → A ⊎ B → C ⊎ D → Set ℓ
(P ⊎-rel Q) (inj₁ x) (inj₁ y) = P x y
(P ⊎-rel Q) (inj₁ x) (inj₂ v) = ⊥
(P ⊎-rel Q) (inj₂ u) (inj₁ y) = ⊥
(P ⊎-rel Q) (inj₂ u) (inj₂ v) = Q u v
