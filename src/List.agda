------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module List
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open Derived-definitions-and-properties eq
open import Monad eq hiding (map)

-- Right fold.

foldr : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → B) → B → List A → B
foldr _⊕_ ε []       = ε
foldr _⊕_ ε (x ∷ xs) = x ⊕ foldr _⊕_ ε xs

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

-- A filter function.

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter p = foldr (λ x xs → if p x then x ∷ xs else xs) []

-- A lookup function.

lookup : ∀ {a} {A : Set a} (xs : List A) → Fin (length xs) → A
lookup []       ()
lookup (x ∷ xs) fzero    = x
lookup (x ∷ xs) (fsuc i) = lookup xs i

-- The function foldr _∷_ [] is pointwise equal to the identity
-- function.

foldr-∷-[] : ∀ {a} {A : Set a} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷-[] []       = refl _
foldr-∷-[] (x ∷ xs) = cong (x ∷_) (foldr-∷-[] xs)

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

instance

  -- The list monad.

  monad : ∀ {ℓ} → Monad (List {a = ℓ})
  Raw-monad.return (Monad.raw-monad monad) x    = x ∷ []
  Raw-monad._>>=_  (Monad.raw-monad monad) xs f = concat (map f xs)
  Monad.left-identity  monad x f                = foldr-∷-[] (f x)
  Monad.right-identity monad xs                 = lemma xs
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
