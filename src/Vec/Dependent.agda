------------------------------------------------------------------------
-- Vectors for which the element types depend on the position, defined
-- using a recursive function
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec.Dependent
  {c⁺} (eq-J : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq-J

open import Prelude

open import Extensionality eq-J
open import Function-universe eq-J hiding (id; _∘_)

private
  variable
    a p q r : Level
    A       : Type a
    P Q     : A → Type p
    n       : A

------------------------------------------------------------------------
-- The type

-- Vectors.

Vec : (n : ℕ) → (Fin n → Type p) → Type p
Vec zero    P = ↑ _ ⊤
Vec (suc n) P = P fzero × Vec n (P ∘ fsuc)

------------------------------------------------------------------------
-- Some simple functions

-- Finds the element at the given position.

index : Vec n P → (i : Fin n) → P i
index {n = suc _} (x , _)  fzero    = x
index {n = suc _} (_ , xs) (fsuc i) = index xs i

-- Updates the element at the given position.

infix 3 _[_≔_]

_[_≔_] : Vec n P → (i : Fin n) → P i → Vec n P
_[_≔_] {n = zero}  _        ()       _
_[_≔_] {n = suc _} (x , xs) fzero    y = y , xs
_[_≔_] {n = suc _} (x , xs) (fsuc i) y = x , (xs [ i ≔ y ])

-- Applies the function to every element in the vector.

map : (∀ {i} → P i → Q i) → Vec n P → Vec n Q
map {n = zero}  f _        = _
map {n = suc _} f (x , xs) = f x , map f xs

-- Constructs a vector from a function giving the element at each
-- position.

tabulate : ((i : Fin n) → P i) → Vec n P
tabulate {n = zero}  f = _
tabulate {n = suc _} f = f fzero , tabulate (f ∘ fsuc)

-- The head of the vector.

head : Vec (suc n) P → P fzero
head = proj₁

-- The tail of the vector.

tail : Vec (suc n) P → Vec n (P ∘ fsuc)
tail = proj₂

------------------------------------------------------------------------
-- Some properties

-- The map function satisfies the functor laws.

map-id :
  {P : Fin n → Type p} {xs : Vec n P} →
  map id xs ≡ xs
map-id {n = zero}  = refl _
map-id {n = suc n} = cong (_ ,_) map-id

map-∘ :
  {P : Fin n → Type p} {Q : Fin n → Type q} {R : Fin n → Type r}
  {f : ∀ {i} → Q i → R i} {g : ∀ {i} → P i → Q i} {xs : Vec n P} →
  map (f ∘ g) xs ≡ map f (map g xs)
map-∘ {n = zero}  = refl _
map-∘ {n = suc n} = cong (_ ,_) map-∘

-- If f and g are pointwise equal, then map f xs and map g xs are
-- equal.

map-cong :
  {P : Fin n → Type p} {Q : Fin n → Type q}
  {f g : ∀ {i} → P i → Q i} {xs : Vec n P} →
  (∀ {i} (x : P i) → f x ≡ g x) → map f xs ≡ map g xs
map-cong {n = zero}  _   = refl _
map-cong {n = suc _} hyp = cong₂ _,_ (hyp _) (map-cong hyp)

-- A fusion lemma for map and tabulate.

map-tabulate :
  {P : Fin n → Type p} {Q : Fin n → Type q}
  {f : ∀ {i} → P i → Q i} {g : (i : Fin n) → P i} →
  map f (tabulate g) ≡ tabulate (f ∘ g)
map-tabulate {n = zero}  = refl _
map-tabulate {n = suc n} = cong (_ ,_) map-tabulate

-- The function tabulate is a left inverse of index.

tabulate-index :
  ∀ n {P : Fin n → Type a} {xs : Vec n P} →
  tabulate (index xs) ≡ xs
tabulate-index zero    = refl _
tabulate-index (suc n) = cong (_ ,_) (tabulate-index n)

-- The function tabulate is a right inverse of index (pointwise).

index-tabulate :
  ∀ n {P : Fin n → Type a} {f : (i : Fin n) → P i} i →
  index (tabulate f) i ≡ f i
index-tabulate (suc n) fzero    = refl _
index-tabulate (suc n) (fsuc _) = index-tabulate n _

-- There is an equivalence between Vec n P and (x : Fin n) → P x
-- (assuming extensionality).

Vec≃Π :
  {P : Fin n → Type p} →
  Vec n P ↝[ lzero ∣ p ] ((x : Fin n) → P x)
Vec≃Π =
  generalise-ext?
    (record { to = index; from = tabulate })
    (λ ext →
         (λ _ → apply-ext ext $ index-tabulate _)
       , (λ _ → tabulate-index _))
