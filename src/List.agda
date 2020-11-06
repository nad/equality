------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module List
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open import Bijection eq as Bijection using (_↔_)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equality.Groupoid eq
import Equivalence eq as Eq
open import Function-universe eq hiding (_∘_)
open import H-level eq as H-level
open import H-level.Closure eq
open import Monad eq hiding (map)
open import Nat eq
open import Nat.Solver eq

private
  variable
    a ℓ      : Level
    A B C    : Type a
    x y      : A
    f        : A → B
    n        : ℕ
    xs ys zs : List A
    ns       : List ℕ

------------------------------------------------------------------------
-- Some functions

-- The tail of a list. Returns [] if the list is empty.

tail : List A → List A
tail []       = []
tail (_ ∷ xs) = xs

-- The function take n returns the first n elements of a list (or the
-- entire list, if the list does not contain n elements).

take : ℕ → List A → List A
take zero    xs       = []
take (suc n) (x ∷ xs) = x ∷ take n xs
take (suc n) xs@[]    = xs

-- The function drop n removes the first n elements from a list (or
-- all elements, if the list does not contain n elements).

drop : ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) (x ∷ xs) = drop n xs
drop (suc n) xs@[]    = xs

-- Right fold.

foldr : (A → B → B) → B → List A → B
foldr _⊕_ ε []       = ε
foldr _⊕_ ε (x ∷ xs) = x ⊕ foldr _⊕_ ε xs

-- Left fold.

foldl : (B → A → B) → B → List A → B
foldl _⊕_ ε []       = ε
foldl _⊕_ ε (x ∷ xs) = foldl _⊕_ (ε ⊕ x) xs

-- The length of a list.

length : List A → ℕ
length = foldr (const suc) 0

-- The sum of all the elements in a list of natural numbers.

sum : List ℕ → ℕ
sum = foldr _+_ 0

-- Appends two lists.

infixr 5 _++_

_++_ : List A → List A → List A
xs ++ ys = foldr _∷_ ys xs

-- Maps a function over a list.

map : (A → B) → List A → List B
map f = foldr (λ x ys → f x ∷ ys) []

-- Concatenates a list of lists.

concat : List (List A) → List A
concat = foldr _++_ []

-- "Zips" two lists, using the given function to combine elementsw.

zip-with : (A → B → C) → List A → List B → List C
zip-with f []       _        = []
zip-with f _        []       = []
zip-with f (x ∷ xs) (y ∷ ys) = f x y ∷ zip-with f xs ys

-- "Zips" two lists.

zip : List A → List B → List (A × B)
zip = zip-with _,_

-- Reverses a list.

reverse : List A → List A
reverse = foldl (λ xs x → x ∷ xs) []

-- Replicates the given value the given number of times.

replicate : ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

-- A filter function.

filter : (A → Bool) → List A → List A
filter p = foldr (λ x xs → if p x then x ∷ xs else xs) []

-- Finds the element at the given position.

index : (xs : List A) → Fin (length xs) → A
index []       ()
index (x ∷ xs) fzero    = x
index (x ∷ xs) (fsuc i) = index xs i

-- A lookup function.

lookup : (A → A → Bool) → A → List (A × B) → Maybe B
lookup _≟_ x []             = nothing
lookup _≟_ x ((y , z) ∷ ps) =
  if x ≟ y then just z else lookup _≟_ x ps

-- The list nats-< consists of the first n natural numbers in
-- strictly descending order.

nats-< : ℕ → List ℕ
nats-< zero    = []
nats-< (suc n) = n ∷ nats-< n

-- A list that includes every tail of the given list (including the
-- list itself) exactly once. Longer tails precede shorter ones.

tails : List A → List (List A)
tails []           = [] ∷ []
tails xxs@(_ ∷ xs) = xxs ∷ tails xs

------------------------------------------------------------------------
-- Some properties

-- If you take the first n elements from xs and append what you get if
-- you drop the first n elements from xs, then you get xs (even if n
-- is larger than the length of xs).

take++drop : ∀ n → take n xs ++ drop n xs ≡ xs
take++drop               zero    = refl _
take++drop {xs = []}     (suc n) = refl _
take++drop {xs = x ∷ xs} (suc n) = cong (x ∷_) (take++drop n)

-- The map function commutes with take n.

map-take : map f (take n xs) ≡ take n (map f xs)
map-take {n = zero}                = refl _
map-take {n = suc n} {xs = []}     = refl _
map-take {n = suc n} {xs = x ∷ xs} = cong (_ ∷_) map-take

-- The map function commutes with drop n.

map-drop : ∀ n → map f (drop n xs) ≡ drop n (map f xs)
map-drop               zero    = refl _
map-drop {xs = []}     (suc n) = refl _
map-drop {xs = x ∷ xs} (suc n) = map-drop n

-- The function foldr _∷_ [] is pointwise equal to the identity
-- function.

foldr-∷-[] : (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷-[] []       = refl _
foldr-∷-[] (x ∷ xs) = cong (x ∷_) (foldr-∷-[] xs)

-- The empty list is a right identity for the append function.

++-right-identity : (xs : List A) → xs ++ [] ≡ xs
++-right-identity []       = refl _
++-right-identity (x ∷ xs) = cong (x ∷_) (++-right-identity xs)

-- The append function is associative.

++-associative : (xs ys zs : List A) →
                 xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-associative []       ys zs = refl _
++-associative (x ∷ xs) ys zs = cong (x ∷_) (++-associative xs ys zs)

-- The map function commutes with _++_.

map-++ : (f : A → B) (xs ys : List A) →
         map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl _
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

-- The concat function commutes with _++_.

concat-++ : (xss yss : List (List A)) →
            concat (xss ++ yss) ≡ concat xss ++ concat yss
concat-++ []         yss = refl _
concat-++ (xs ∷ xss) yss =
  concat ((xs ∷ xss) ++ yss)        ≡⟨⟩
  xs ++ concat (xss ++ yss)         ≡⟨ cong (xs ++_) (concat-++ xss yss) ⟩
  xs ++ (concat xss ++ concat yss)  ≡⟨ ++-associative xs _ _ ⟩
  (xs ++ concat xss) ++ concat yss  ≡⟨ refl _ ⟩∎
  concat (xs ∷ xss) ++ concat yss   ∎

-- A lemma relating foldr and _++_.

foldr-++ :
  {c : A → B → B} {n : B} →
  ∀ xs → foldr c n (xs ++ ys) ≡ foldr c (foldr c n ys) xs
foldr-++                           []       = refl _
foldr-++ {ys = ys} {c = c} {n = n} (x ∷ xs) =
  foldr c n (x ∷ xs ++ ys)         ≡⟨⟩
  c x (foldr c n (xs ++ ys))       ≡⟨ cong (c x) (foldr-++ xs) ⟩
  c x (foldr c (foldr c n ys) xs)  ≡⟨⟩
  foldr c (foldr c n ys) (x ∷ xs)  ∎

-- A fusion lemma for foldr and map.

foldr∘map :
  (_⊕_ : B → C → C) (ε : C) (f : A → B) (xs : List A) →
  (foldr _⊕_ ε ∘ map f) xs ≡ foldr (_⊕_ ∘ f) ε xs
foldr∘map _⊕_ ε f []       = ε ∎
foldr∘map _⊕_ ε f (x ∷ xs) = cong (f x ⊕_) (foldr∘map _⊕_ ε f xs)

-- A fusion lemma for length and map.

length∘map :
  (f : A → B) (xs : List A) →
  (length ∘ map f) xs ≡ length xs
length∘map = foldr∘map _ _

-- A lemma relating index, map and length∘map.

index∘map :
  ∀ xs {i} →
  index (map f xs) i ≡
  f (index xs (subst Fin (length∘map f xs) i))
index∘map {f = f} (x ∷ xs) {i} =
  index (f x ∷ map f xs) i                                  ≡⟨ lemma i ⟩
  f (index (x ∷ xs) (subst (λ n → ⊤ ⊎ Fin n) p i))          ≡⟨⟩
  f (index (x ∷ xs) (subst (Fin ∘ suc) p i))                ≡⟨ cong (f ∘ index _) (subst-∘ Fin suc p) ⟩
  f (index (x ∷ xs) (subst Fin (cong suc p) i))             ≡⟨⟩
  f (index (x ∷ xs) (subst Fin (length∘map f (x ∷ xs)) i))  ∎
  where
  p = length∘map f xs

  lemma :
    ∀ i →
    index (f x ∷ map f xs) i ≡
    f (index (x ∷ xs) (subst (λ n → ⊤ ⊎ Fin n) p i))
  lemma fzero =
    index (f x ∷ map f xs) fzero                          ≡⟨⟩
    f x                                                   ≡⟨⟩
    f (index (x ∷ xs) fzero)                              ≡⟨⟩
    f (index (x ∷ xs) (inj₁ (subst (λ _ → ⊤) p tt)))      ≡⟨ cong (f ∘ index _) $ sym $ push-subst-inj₁ {y≡z = p} _ _ ⟩∎
    f (index (x ∷ xs) (subst (λ n → ⊤ ⊎ Fin n) p fzero))  ∎
  lemma (fsuc i) =
    index (f x ∷ map f xs) (fsuc i)                          ≡⟨⟩
    index (map f xs) i                                       ≡⟨ index∘map xs ⟩
    f (index xs (subst Fin p i))                             ≡⟨⟩
    f (index (x ∷ xs) (fsuc (subst Fin p i)))                ≡⟨ cong (f ∘ index _) $ sym $ push-subst-inj₂ {y≡z = p} _ _ ⟩∎
    f (index (x ∷ xs) (subst (λ n → ⊤ ⊎ Fin n) p (fsuc i)))  ∎

-- The length function is homomorphic with respect to _++_/_+_.

length-++ : ∀ xs → length (xs ++ ys) ≡ length xs + length ys
length-++ []       = refl _
length-++ (_ ∷ xs) = cong suc (length-++ xs)

-- The sum function is homomorphic with respect to _++_/_+_.

sum-++ : ∀ ms → sum (ms ++ ns) ≡ sum ms + sum ns
sum-++           []       = refl _
sum-++ {ns = ns} (m ∷ ms) =
  sum (m ∷ ms ++ ns)     ≡⟨⟩
  m + sum (ms ++ ns)     ≡⟨ cong (m +_) $ sum-++ ms ⟩
  m + (sum ms + sum ns)  ≡⟨ +-assoc m ⟩
  (m + sum ms) + sum ns  ≡⟨⟩
  sum (m ∷ ms) + sum ns  ∎

-- Some lemmas related to reverse.

++-reverse : ∀ xs → reverse xs ++ ys ≡ foldl (flip _∷_) ys xs
++-reverse xs = lemma xs
  where
  lemma :
    ∀ xs →
    foldl (flip _∷_) ys xs ++ zs ≡
    foldl (flip _∷_) (ys ++ zs) xs
  lemma                     []       = refl _
  lemma {ys = ys} {zs = zs} (x ∷ xs) =
    foldl (flip _∷_) ys (x ∷ xs) ++ zs    ≡⟨⟩
    foldl (flip _∷_) (x ∷ ys) xs ++ zs    ≡⟨ lemma xs ⟩
    foldl (flip _∷_) (x ∷ ys ++ zs) xs    ≡⟨⟩
    foldl (flip _∷_) (ys ++ zs) (x ∷ xs)  ∎

reverse-∷ : ∀ xs → reverse (x ∷ xs) ≡ reverse xs ++ x ∷ []
reverse-∷ {x = x} xs =
  reverse (x ∷ xs)              ≡⟨⟩
  foldl (flip _∷_) (x ∷ []) xs  ≡⟨ sym $ ++-reverse xs ⟩∎
  reverse xs ++ x ∷ []          ∎

reverse-++ : ∀ xs → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ {ys = ys} [] =
  reverse ys        ≡⟨ sym $ ++-right-identity _ ⟩∎
  reverse ys ++ []  ∎
reverse-++ {ys = ys} (x ∷ xs) =
  reverse (x ∷ xs ++ ys)                ≡⟨ reverse-∷ (xs ++ _) ⟩
  reverse (xs ++ ys) ++ x ∷ []          ≡⟨ cong (_++ _) $ reverse-++ xs ⟩
  (reverse ys ++ reverse xs) ++ x ∷ []  ≡⟨ sym $ ++-associative (reverse ys) _ _ ⟩
  reverse ys ++ (reverse xs ++ x ∷ [])  ≡⟨ cong (reverse ys ++_) $ sym $ reverse-∷ xs ⟩∎
  reverse ys ++ reverse (x ∷ xs)        ∎

reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse []       = refl _
reverse-reverse (x ∷ xs) =
  reverse (reverse (x ∷ xs))                ≡⟨ cong reverse (reverse-∷ xs) ⟩
  reverse (reverse xs ++ x ∷ [])            ≡⟨ reverse-++ (reverse xs) ⟩
  reverse (x ∷ []) ++ reverse (reverse xs)  ≡⟨⟩
  x ∷ reverse (reverse xs)                  ≡⟨ cong (x ∷_) (reverse-reverse xs) ⟩∎
  x ∷ xs                                    ∎

map-reverse : ∀ xs → map f (reverse xs) ≡ reverse (map f xs)
map-reverse         []       = refl _
map-reverse {f = f} (x ∷ xs) =
  map f (reverse (x ∷ xs))        ≡⟨ cong (map f) $ reverse-∷ xs ⟩
  map f (reverse xs ++ x ∷ [])    ≡⟨ map-++ _ (reverse xs) _ ⟩
  map f (reverse xs) ++ f x ∷ []  ≡⟨ cong (_++ _) $ map-reverse xs ⟩
  reverse (map f xs) ++ f x ∷ []  ≡⟨ sym $ reverse-∷ (map f xs) ⟩
  reverse (f x ∷ map f xs)        ≡⟨⟩
  reverse (map f (x ∷ xs))        ∎

foldr-reverse :
  {c : A → B → B} {n : B} →
  ∀ xs → foldr c n (reverse xs) ≡ foldl (flip c) n xs
foldr-reverse                 []       = refl _
foldr-reverse {c = c} {n = n} (x ∷ xs) =
  foldr c n (reverse (x ∷ xs))      ≡⟨ cong (foldr c n) (reverse-++ {ys = xs} (x ∷ [])) ⟩
  foldr c n (reverse xs ++ x ∷ [])  ≡⟨ foldr-++ (reverse xs) ⟩
  foldr c (c x n) (reverse xs)      ≡⟨ foldr-reverse xs ⟩
  foldl (flip c) (c x n) xs         ≡⟨⟩
  foldl (flip c) n (x ∷ xs)         ∎

foldl-reverse :
  {c : B → A → B} {n : B} →
  ∀ xs → foldl c n (reverse xs) ≡ foldr (flip c) n xs
foldl-reverse {c = c} {n = n} xs =
  foldl c n (reverse xs)                   ≡⟨ sym (foldr-reverse (reverse xs)) ⟩
  foldr (flip c) n (reverse (reverse xs))  ≡⟨ cong (foldr (flip c) n) (reverse-reverse xs) ⟩∎
  foldr (flip c) n xs                      ∎

length-reverse : (xs : List A) → length (reverse xs) ≡ length xs
length-reverse []       = refl _
length-reverse (x ∷ xs) =
  length (reverse (x ∷ xs))      ≡⟨ cong length (reverse-∷ xs) ⟩
  length (reverse xs ++ x ∷ [])  ≡⟨ length-++ (reverse xs) ⟩
  length (reverse xs) + 1        ≡⟨ cong (_+ 1) (length-reverse xs) ⟩
  length xs + 1                  ≡⟨ +-comm (length xs) ⟩∎
  length (x ∷ xs)                ∎

sum-reverse : ∀ ns → sum (reverse ns) ≡ sum ns
sum-reverse []       = refl _
sum-reverse (n ∷ ns) =
  sum (reverse (n ∷ ns))           ≡⟨ cong sum (reverse-∷ ns) ⟩
  sum (reverse ns ++ n ∷ [])       ≡⟨ sum-++ (reverse ns) ⟩
  sum (reverse ns) + sum (n ∷ [])  ≡⟨ cong₂ _+_ (sum-reverse ns) +-right-identity ⟩
  sum ns + n                       ≡⟨ +-comm (sum ns) ⟩∎
  sum (n ∷ ns)                     ∎

-- The functions filter and map commute (kind of).

filter∘map :
  (p : B → Bool) (f : A → B) (xs : List A) →
  (filter p ∘ map f) xs ≡ (map f ∘ filter (p ∘ f)) xs
filter∘map p f []       = refl _
filter∘map p f (x ∷ xs) with p (f x)
... | true  = cong (_ ∷_) (filter∘map p f xs)
... | false = filter∘map p f xs

-- The length of replicate n x is n.

length-replicate : ∀ n → length (replicate n x) ≡ n
length-replicate         zero    = refl _
length-replicate {x = x} (suc n) =
  length (replicate (suc n) x)  ≡⟨⟩
  suc (length (replicate n x))  ≡⟨ cong suc $ length-replicate n ⟩∎
  suc n                         ∎

-- The sum of replicate m n is m * n.

sum-replicate : ∀ m → sum (replicate m n) ≡ m * n
sum-replicate         zero    = refl _
sum-replicate {n = n} (suc m) =
  sum (replicate (suc m) n)  ≡⟨⟩
  n + sum (replicate m n)    ≡⟨ cong (n +_) $ sum-replicate m ⟩
  n + m * n                  ≡⟨⟩
  suc m * n                  ∎

-- The length of nats-< n is n.

length∘nats-< : ∀ n → length (nats-< n) ≡ n
length∘nats-< zero    = 0 ∎
length∘nats-< (suc n) = cong suc (length∘nats-< n)

-- The sum of nats-< n can be expressed without referring to lists.

sum-nats-< : ∀ n → sum (nats-< n) ≡ ⌊ n * pred n /2⌋
sum-nats-< zero          = refl _
sum-nats-< (suc zero)    = refl _
sum-nats-< (suc (suc n)) =
  sum (suc n ∷ nats-< (suc n))       ≡⟨⟩
  suc n + sum (nats-< (suc n))       ≡⟨ cong (suc n +_) (sum-nats-< (suc n)) ⟩
  suc n + ⌊ suc n * n /2⌋            ≡⟨ sym $ ⌊2*+/2⌋≡ (suc n) ⟩
  ⌊ 2 * suc n + suc n * n /2⌋        ≡⟨ cong ⌊_/2⌋ (solve 1 (λ n → con 2 :* (con 1 :+ n) :+ (con 1 :+ n) :* n :=
                                                                   con 1 :+ n :+ (con 1 :+ n :+ n :* (con 1 :+ n)))
                                                          (refl _) n) ⟩
  ⌊ suc n + (suc n + n * suc n) /2⌋  ≡⟨⟩
  ⌊ suc (suc n) * suc n /2⌋          ∎

-- If xs ++ ys is equal to [], then both lists are.

++≡[]→≡[]×≡[] : ∀ xs → xs ++ ys ≡ [] → xs ≡ [] × ys ≡ []
++≡[]→≡[]×≡[] {ys = []}    []      _    = refl _ , refl _
++≡[]→≡[]×≡[] {ys = _ ∷ _} []      ∷≡[] = ⊥-elim (List.[]≢∷ (sym ∷≡[]))
++≡[]→≡[]×≡[]              (_ ∷ _) ∷≡[] = ⊥-elim (List.[]≢∷ (sym ∷≡[]))

-- Empty lists are not equal to non-empty lists.

[]≢++∷ : ∀ xs → [] ≢ xs ++ y ∷ ys
[]≢++∷ {y = y} {ys = ys} xs =
  [] ≡ xs ++ y ∷ ys  ↝⟨ sym ∘ proj₂ ∘ ++≡[]→≡[]×≡[] xs ∘ sym ⟩
  [] ≡ y ∷ ys        ↝⟨ List.[]≢∷ ⟩□
  ⊥                  □

------------------------------------------------------------------------
-- The list monad

instance

  -- The list monad.

  raw-monad : Raw-monad (List {a = ℓ})
  Raw-monad.return raw-monad x    = x ∷ []
  Raw-monad._>>=_  raw-monad xs f = concat (map f xs)

  monad : Monad (List {a = ℓ})
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

------------------------------------------------------------------------
-- Some isomorphisms

-- An unfolding lemma for List.

List↔Maybe[×List] : List A ↔ Maybe (A × List A)
List↔Maybe[×List] = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { [] → inj₁ tt; (x ∷ xs) → inj₂ (x , xs) }
      ; from = [ (λ _ → []) , uncurry _∷_ ]
      }
    ; right-inverse-of = [ (λ _ → refl _) , (λ _ → refl _) ]
    }
  ; left-inverse-of = λ { [] → refl _; (_ ∷ _) → refl _ }
  }

-- Some isomorphisms related to list equality.

[]≡[]↔⊤ : [] ≡ ([] ⦂ List A) ↔ ⊤
[]≡[]↔⊤ =
  [] ≡ []            ↔⟨ inverse $ Eq.≃-≡ (Eq.↔⇒≃ List↔Maybe[×List]) ⟩
  nothing ≡ nothing  ↝⟨ inverse Bijection.≡↔inj₁≡inj₁ ⟩
  tt ≡ tt            ↝⟨ tt≡tt↔⊤ ⟩□
  ⊤                  □

[]≡∷↔⊥ : [] ≡ x ∷ xs ↔ ⊥ {ℓ = ℓ}
[]≡∷↔⊥ {x = x} {xs = xs} =
  [] ≡ x ∷ xs              ↔⟨ inverse $ Eq.≃-≡ (Eq.↔⇒≃ List↔Maybe[×List]) ⟩
  nothing ≡ just (x , xs)  ↝⟨ Bijection.≡↔⊎ ⟩
  ⊥                        ↝⟨ ⊥↔⊥ ⟩□
  ⊥                        □

∷≡[]↔⊥ : x ∷ xs ≡ [] ↔ ⊥ {ℓ = ℓ}
∷≡[]↔⊥ {x = x} {xs = xs} =
  x ∷ xs ≡ []  ↝⟨ ≡-comm ⟩
  [] ≡ x ∷ xs  ↝⟨ []≡∷↔⊥ ⟩□
  ⊥            □

∷≡∷↔≡×≡ : x ∷ xs ≡ y ∷ ys ↔ x ≡ y × xs ≡ ys
∷≡∷↔≡×≡ {x = x} {xs = xs} {y = y} {ys = ys} =
  x ∷ xs ≡ y ∷ ys                ↔⟨ inverse $ Eq.≃-≡ (Eq.↔⇒≃ List↔Maybe[×List]) ⟩
  just (x , xs) ≡ just (y , ys)  ↝⟨ inverse Bijection.≡↔inj₂≡inj₂ ⟩
  (x , xs) ≡ (y , ys)            ↝⟨ inverse ≡×≡↔≡ ⟩□
  x ≡ y × xs ≡ ys                □

------------------------------------------------------------------------
-- H-levels

-- If A is inhabited, then List A is not a proposition.

¬-List-propositional : A → ¬ Is-proposition (List A)
¬-List-propositional x h = List.[]≢∷ $ h [] (x ∷ [])

-- H-levels greater than or equal to two are closed under List.

H-level-List : ∀ n → H-level (2 + n) A → H-level (2 + n) (List A)
H-level-List n _ {[]} {[]} =
                             $⟨ ⊤-contractible ⟩
  Contractible ⊤             ↝⟨ H-level-cong _ 0 (inverse []≡[]↔⊤) ⟩
  Contractible ([] ≡ [])     ↝⟨ H-level.mono (zero≤ (1 + n)) ⟩□
  H-level (1 + n) ([] ≡ [])  □

H-level-List n h {[]} {y ∷ ys} =
                                 $⟨ ⊥-propositional ⟩
  Is-proposition ⊥₀              ↝⟨ H-level-cong _ 1 (inverse []≡∷↔⊥) ⟩
  Is-proposition ([] ≡ y ∷ ys)   ↝⟨ H-level.mono (suc≤suc (zero≤ n)) ⟩□
  H-level (1 + n) ([] ≡ y ∷ ys)  □

H-level-List n h {x ∷ xs} {[]} =
                                 $⟨ ⊥-propositional ⟩
  Is-proposition ⊥₀              ↝⟨ H-level-cong _ 1 (inverse ∷≡[]↔⊥) ⟩
  Is-proposition (x ∷ xs ≡ [])   ↝⟨ H-level.mono (suc≤suc (zero≤ n)) ⟩□
  H-level (1 + n) (x ∷ xs ≡ [])  □

H-level-List n h {x ∷ xs} {y ∷ ys} =
  H-level-cong _ (1 + n) (inverse ∷≡∷↔≡×≡)
    (×-closure (1 + n) h (H-level-List n h))
