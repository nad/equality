------------------------------------------------------------------------
-- A small prelude
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

-- Note that parts of Agda's standard library make use of the K rule.

module Prelude where

------------------------------------------------------------------------
-- Support for universe polymorphism

-- Universe levels.

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

-- Maximum.

infixl 6 _⊔_

_⊔_ : Level → Level → Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}

------------------------------------------------------------------------
-- Some finite types

-- The empty type.

data ⊥ : Set where

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()

-- Negation.

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

-- The unit type.

record ⊤ {ℓ} : Set ℓ where
  constructor tt

-- Booleans.

data Bool : Set where
  true false : Bool

-- Part of the support for reflection (see the module Reflection).

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

-- If-then-else.

if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

-- And.

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

-- The truth predicate T is only inhabited when its argument is true.

T : Bool → Set
T b = if b then ⊤ else ⊥

------------------------------------------------------------------------
-- Natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

-- Support for natural number literals.

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

-- The usual ordering of the natural numbers.

infix 4 _≤_

data _≤_ (m : ℕ) : ℕ → Set where
  ≤-refl :                       m ≤ m
  ≤-step : ∀ {n} (m≤n : m ≤ n) → m ≤ suc n

-- Addition.

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- Some lemmas.

abstract

  zero≤ : ∀ n → zero ≤ n
  zero≤ zero    = ≤-refl
  zero≤ (suc n) = ≤-step (zero≤ n)

  suc≤suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
  suc≤suc ≤-refl       = ≤-refl
  suc≤suc (≤-step m≤n) = ≤-step (suc≤suc m≤n)

  m≤m+n : ∀ m n → m ≤ m + n
  m≤m+n zero    n = zero≤ n
  m≤m+n (suc m) n = suc≤suc (m≤m+n m n)

------------------------------------------------------------------------
-- Simple combinators working solely on and with functions

infixr 9 _∘_
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

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

-- Flips the first two arguments.

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ x y → f y x

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
Σ-map f g (x , y) = (f x , g y)

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

-- A special case of binary sums: decided predicates.

data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

-- Decidable relations.

Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} →
            (A → B → Set ℓ) → Set (a ⊔ b ⊔ ℓ)
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

-- Forgets the proofs.

⌊_⌋ : ∀ {p} {P : Set p} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

------------------------------------------------------------------------
-- Lists

infixr 5 _∷_

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

-- Part of the support for reflection (see the module Reflection).

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}
