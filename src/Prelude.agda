------------------------------------------------------------------------
-- A small prelude
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Note that parts of Agda's standard library make use of the K rule.

module Prelude where

------------------------------------------------------------------------
-- Support for universe polymorphism

-- Universe levels.

open import Agda.Primitive public using (Level; _⊔_; lzero; lsuc)

-- Lifting.

record ↑ {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open ↑ public

------------------------------------------------------------------------
-- The unit type

record ⊤ : Set where
  constructor tt

------------------------------------------------------------------------
-- The empty type

data ⊥ {ℓ} : Set ℓ where

⊥-elim : ∀ {w ℓ} {Whatever : Set w} → ⊥ {ℓ = ℓ} → Whatever
⊥-elim ()

-- A version of the empty type that is not universe-polymorphic.

⊥₀ : Set
⊥₀ = ⊥

-- Negation.

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥₀

------------------------------------------------------------------------
-- Natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

-- Support for natural number literals.

{-# BUILTIN NATURAL ℕ #-}

-- Dependent eliminator.

ℕ-rec : ∀ {p} {P : ℕ → Set p} →
        P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n
ℕ-rec z s zero    = z
ℕ-rec z s (suc n) = s n (ℕ-rec z s n)

-- Addition.

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- Multiplication.

infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

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

-- The usual ordering of the natural numbers.

infix 4 _≤_

data _≤_ (m : ℕ) : ℕ → Set where
  ≤-refl :                       m ≤ m
  ≤-step : ∀ {n} (m≤n : m ≤ n) → m ≤ suc n

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

id : ∀ {a} {A : Set a} → A → A
id x = x

-- Composition.

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- Application.

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

-- Constant functions.

const : ∀ {a b} {A : Set a} {B : Set b} → A → (B → A)
const x = λ _ → x

{-# DISPLAY const x y = x #-}

-- Flips the first two arguments.

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ x y → f y x

-- Applies the unary function to each argument and combines the
-- results using the binary function.

_on_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       (B → B → C) → (A → B) → (A → A → C)
_*_ on f = λ x y → f x * f y

-- A term's type.

Type-of : ∀ {a} {A : Set a} → A → Set a
Type-of {A = A} _ = A

------------------------------------------------------------------------
-- Σ-types

infixr 4 _,_
infixr 2 _×_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- A variant where the first argument is implicit.

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

-- Binary products.

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (const B)

-- A map function.

Σ-map : ∀ {a b p q}
          {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
        (f : A → B) → (∀ {x} → P x → Q (f x)) →
        Σ A P → Σ B Q
Σ-map f g = λ p → (f (proj₁ p) , g (proj₂ p))

-- Zip.

Σ-zip : ∀ {a b c p q r}
          {A : Set a} {B : Set b} {C : Set c}
          {P : A → Set p} {Q : B → Set q} {R : C → Set r} →
        (f : A → B → C) → (∀ {x y} → P x → Q y → R (f x y)) →
        Σ A P → Σ B Q → Σ C R
Σ-zip f g = λ p q → (f (proj₁ p) (proj₁ q) , g (proj₂ p) (proj₂ q))

-- Curry and uncurry.

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
        ((p : Σ A B) → C p) →
        ((x : A) (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

------------------------------------------------------------------------
-- W-types

data W {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  sup : (x : A) (f : B x → W A B) → W A B

-- Projections.

head : ∀ {a b} {A : Set a} {B : A → Set b} →
       W A B → A
head (sup x f) = x

tail : ∀ {a b} {A : Set a} {B : A → Set b} →
       (x : W A B) → B (head x) → W A B
tail (sup x f) = f

-- If B is always inhabited, then W A B is empty.

abstract

  inhabited⇒W-empty : ∀ {a b} {A : Set a} {B : A → Set b} →
                      (∀ x → B x) → ¬ W A B
  inhabited⇒W-empty b (sup x f) = inhabited⇒W-empty b (f (b x))

------------------------------------------------------------------------
-- Support for coinduction

{-# BUILTIN SIZEUNIV Size-universe #-}
{-# BUILTIN SIZE     Size          #-}
{-# BUILTIN SIZELT   Size<_        #-}
{-# BUILTIN SIZESUC  ssuc          #-}
{-# BUILTIN SIZEINF  ∞             #-}

------------------------------------------------------------------------
-- Binary sums

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

-- Eliminator for binary sums.

[_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

-- A map function.

⊎-map : ∀ {a₁ a₂ b₁ b₂}
          {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂} →
        (A₁ → A₂) → (B₁ → B₂) → A₁ ⊎ B₁ → A₂ ⊎ B₂
⊎-map f g = [ inj₁ ∘ f , inj₂ ∘ g ]

-- The function from-⊎ is a safe analogue of fromJust. For an example
-- of how from-⊎ can be used, see
-- Quotient.equivalence-but-not-strong-equivalence.

From-⊎ : ∀ {ℓ} {A B : Set ℓ} → A ⊎ B → Set ℓ
From-⊎ {A = A} (inj₁ _) = A
From-⊎ {B = B} (inj₂ _) = B

from-⊎ : ∀ {ℓ} {A B : Set ℓ} (x : A ⊎ B) → From-⊎ x
from-⊎ (inj₁ x) = x
from-⊎ (inj₂ y) = y

-- A special case of binary sums: decided predicates.

Dec : ∀ {p} → Set p → Set p
Dec P = P ⊎ ¬ P

pattern yes p = inj₁ p
pattern no  p = inj₂ p

-- Decidable relations.

Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} →
            (A → B → Set ℓ) → Set (a ⊔ b ⊔ ℓ)
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

-- Exclusive or.

infixr 1 _Xor_

_Xor_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A Xor B = (A × ¬ B) ⊎ (¬ A × B)

-- Maybe.

Maybe : ∀ {a} → Set a → Set a
Maybe A = ⊤ ⊎ A

pattern nothing = inj₁ tt
pattern just x  = inj₂ x

------------------------------------------------------------------------
-- Booleans

-- Booleans.

Bool : Set
Bool = ⊤ ⊎ ⊤

pattern true  = inj₁ tt
pattern false = inj₂ tt

-- Conditional.

if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

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

-- The truth predicate T is only inhabited when its argument is true.

T : Bool → Set
T b = if b then ⊤ else ⊥

------------------------------------------------------------------------
-- Lists

infixr 5 _∷_

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

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

_→-rel_ : ∀ {a b c d ℓ}
            {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
          (A → C → Set ℓ) → (B → D → Set ℓ) →
          (A → B) → (C → D) → Set (a ⊔ c ⊔ ℓ)
(P →-rel Q) f g = ∀ x y → P x y → Q (f x) (g y)

-- Combines two relations into a relation on products.

_×-rel_ : ∀ {a b c d ℓ}
            {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
          (A → C → Set ℓ) → (B → D → Set ℓ) → A × B → C × D → Set ℓ
(P ×-rel Q) (x , u) (y , v) = P x y × Q u v

-- Combines two relations into a relation on sums.

_⊎-rel_ : ∀ {a b c d ℓ}
            {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
          (A → C → Set ℓ) → (B → D → Set ℓ) → A ⊎ B → C ⊎ D → Set ℓ
(P ⊎-rel Q) (inj₁ x) (inj₁ y) = P x y
(P ⊎-rel Q) (inj₁ x) (inj₂ v) = ⊥
(P ⊎-rel Q) (inj₂ u) (inj₁ y) = ⊥
(P ⊎-rel Q) (inj₂ u) (inj₂ v) = Q u v