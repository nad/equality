------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module List
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Monad eq hiding (map)

------------------------------------------------------------------------
-- Some functions

-- Right fold.

foldr : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → B) → B → List A → B
foldr _⊕_ ε []       = ε
foldr _⊕_ ε (x ∷ xs) = x ⊕ foldr _⊕_ ε xs

-- Left fold.

foldl : ∀ {a b} {A : Set a} {B : Set b} →
        (B → A → B) → B → List A → B
foldl _⊕_ ε []       = ε
foldl _⊕_ ε (x ∷ xs) = foldl _⊕_ (ε ⊕ x) xs

-- The length of a list.

length : ∀ {a} {A : Set a} → List A → ℕ
length = foldr (const suc) 0

-- Appends two lists.

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
xs ++ ys = foldr _∷_ ys xs

-- Maps a function over a list.

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f = foldr (λ x ys → f x ∷ ys) []

-- Concatenates a list of lists.

concat : ∀ {a} {A : Set a} → List (List A) → List A
concat = foldr _++_ []

-- Reverses a list.

reverse : ∀ {a} {A : Set a} → List A → List A
reverse = foldl (λ xs x → x ∷ xs) []

-- Replicates the given value the given number of times.

replicate : ∀ {a} {A : Set a} → ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

-- A filter function.

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter p = foldr (λ x xs → if p x then x ∷ xs else xs) []

-- Finds the element at the given position.

index : ∀ {a} {A : Set a} (xs : List A) → Fin (length xs) → A
index []       ()
index (x ∷ xs) fzero    = x
index (x ∷ xs) (fsuc i) = index xs i

-- A lookup function.

lookup : ∀ {a b} {A : Set a} {B : Set b} →
         (A → A → Bool) → A → List (A × B) → Maybe B
lookup _≟_ x []             = nothing
lookup _≟_ x ((y , z) ∷ ps) =
  if x ≟ y then just z else lookup _≟_ x ps

-- The list nats-< consists of the first n natural numbers in
-- strictly descending order.

nats-< : ℕ → List ℕ
nats-< zero    = []
nats-< (suc n) = n ∷ nats-< n

------------------------------------------------------------------------
-- Some properties

-- The function foldr _∷_ [] is pointwise equal to the identity
-- function.

foldr-∷-[] : ∀ {a} {A : Set a} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷-[] []       = refl _
foldr-∷-[] (x ∷ xs) = cong (x ∷_) (foldr-∷-[] xs)

-- The empty list is a right identity for the append function.

++-right-identity :
  ∀ {a} {A : Set a} (xs : List A) → xs ++ [] ≡ xs
++-right-identity []       = refl _
++-right-identity (x ∷ xs) = cong (x ∷_) (++-right-identity xs)

-- The append function is associative.

++-associative : ∀ {a} {A : Set a} (xs ys zs : List A) →
                 xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-associative []       ys zs = refl _
++-associative (x ∷ xs) ys zs = cong (x ∷_) (++-associative xs ys zs)

-- The map function commutes with _++_.

map-++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) →
         map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl _
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

-- The concat function commutes with _++_.

concat-++ : ∀ {a} {A : Set a} (xss yss : List (List A)) →
            concat (xss ++ yss) ≡ concat xss ++ concat yss
concat-++ []         yss = refl _
concat-++ (xs ∷ xss) yss =
  concat ((xs ∷ xss) ++ yss)        ≡⟨⟩
  xs ++ concat (xss ++ yss)         ≡⟨ cong (xs ++_) (concat-++ xss yss) ⟩
  xs ++ (concat xss ++ concat yss)  ≡⟨ ++-associative xs _ _ ⟩
  (xs ++ concat xss) ++ concat yss  ≡⟨ refl _ ⟩∎
  concat (xs ∷ xss) ++ concat yss   ∎

-- A fusion lemma for foldr and map.

foldr∘map :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  (_⊕_ : B → C → C) (ε : C) (f : A → B) (xs : List A) →
  (foldr _⊕_ ε ∘ map f) xs ≡ foldr (_⊕_ ∘ f) ε xs
foldr∘map _⊕_ ε f []       = ε ∎
foldr∘map _⊕_ ε f (x ∷ xs) = cong (f x ⊕_) (foldr∘map _⊕_ ε f xs)

-- A fusion lemma for length and map.

length∘map :
  ∀ {a b} {A : Set a} {B : Set b} →
  (f : A → B) (xs : List A) →
  (length ∘ map f) xs ≡ length xs
length∘map = foldr∘map _ _

-- The length function is homomorphic with respect to _++_/_+_.

length-++ :
  ∀ {a} {A : Set a} xs {ys : List A} →
  length (xs ++ ys) ≡ length xs + length ys
length-++ []       = refl _
length-++ (_ ∷ xs) = cong suc (length-++ xs)

-- The functions filter and map commute (kind of).

filter∘map :
  ∀ {a b} {A : Set a} {B : Set b}
  (p : B → Bool) (f : A → B) (xs : List A) →
  (filter p ∘ map f) xs ≡ (map f ∘ filter (p ∘ f)) xs
filter∘map p f []       = refl _
filter∘map p f (x ∷ xs) with p (f x)
... | true  = cong (_ ∷_) (filter∘map p f xs)
... | false = filter∘map p f xs

-- The length of nats-< n is n.

length∘nats-< : ∀ n → length (nats-< n) ≡ n
length∘nats-< zero    = 0 ∎
length∘nats-< (suc n) = cong suc (length∘nats-< n)

-- If xs ++ ys is equal to [], then both lists are.

++≡[]→≡[]×≡[] :
  ∀ {a} {A : Set a} (xs {ys} : List A) →
  xs ++ ys ≡ [] → xs ≡ [] × ys ≡ []
++≡[]→≡[]×≡[] []      {[]}    _    = refl _ , refl _
++≡[]→≡[]×≡[] []      {_ ∷ _} ∷≡[] = ⊥-elim (List.[]≢∷ (sym ∷≡[]))
++≡[]→≡[]×≡[] (_ ∷ _)         ∷≡[] = ⊥-elim (List.[]≢∷ (sym ∷≡[]))

------------------------------------------------------------------------
-- The list monad

instance

  -- The list monad.

  raw-monad : ∀ {ℓ} → Raw-monad (List {a = ℓ})
  Raw-monad.return raw-monad x    = x ∷ []
  Raw-monad._>>=_  raw-monad xs f = concat (map f xs)

  monad : ∀ {ℓ} → Monad (List {a = ℓ})
  Monad.raw-monad      monad     = raw-monad
  Monad.left-identity  monad x f = foldr-∷-[] (f x)
  Monad.right-identity monad xs  = lemma xs
    where
    lemma : ∀ xs → concat (map (_∷ []) xs) ≡ xs
    lemma []       = refl _
    lemma (x ∷ xs) =
      concat (map (_∷ []) (x ∷ xs))  ≡⟨⟩
      x ∷ concat (map (_∷ []) xs)    ≡⟨ cong (x ∷_) (lemma xs) ⟩∎
      x ∷ xs                         ∎
  Monad.associativity monad xs f g = lemma xs
    where
    lemma : ∀ xs → concat (map (concat ∘ map g ∘ f) xs) ≡
                   concat (map g (concat (map f xs)))
    lemma []       = refl _
    lemma (x ∷ xs) =
      concat (map (concat ∘ map g ∘ f) (x ∷ xs))                    ≡⟨⟩
      concat (map g (f x)) ++ concat (map (concat ∘ map g ∘ f) xs)  ≡⟨ cong (concat (map g (f x)) ++_) (lemma xs) ⟩
      concat (map g (f x)) ++ concat (map g (concat (map f xs)))    ≡⟨ sym $ concat-++ (map g (f x)) _ ⟩
      concat (map g (f x) ++ map g (concat (map f xs)))             ≡⟨ cong concat (sym $ map-++ g (f x) _) ⟩
      concat (map g (f x ++ concat (map f xs)))                     ≡⟨ refl _ ⟩∎
      concat (map g (concat (map f (x ∷ xs))))                      ∎
