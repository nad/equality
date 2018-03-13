------------------------------------------------------------------------
-- Colists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Colist where

open import Conat using (Conat; zero; suc; force; infinity)
open import Equality.Propositional
open import Prelude

------------------------------------------------------------------------
-- The type

-- Colists.

mutual

  infixr 5 _∷_

  data Colist {a} (A : Set a) (i : Size) : Set a where
    []  : Colist A i
    _∷_ : A → Colist′ A i → Colist A i

  record Colist′ {a} (A : Set a) (i : Size) : Set a where
    coinductive
    field
      force : {j : Size< i} → Colist A j

open Colist′ public

------------------------------------------------------------------------
-- Some operations

-- A variant of cons.

infixr 5 _∷′_

_∷′_ : ∀ {i a} {A : Set a} → A → Colist A i → Colist A i
x ∷′ xs = x ∷ λ { .force → xs }

-- The colist's tail, if any.

tail : ∀ {a} {A : Set a} {i} → Colist A i → Colist′ A i
tail xs@[]    = λ { .force → xs }
tail (x ∷ xs) = xs

-- A map function.

map : ∀ {a b i} {A : Set a} {B : Set b} →
      (A → B) → Colist A i → Colist B i
map f []       = []
map f (x ∷ xs) = f x ∷ λ { .force → map f (force xs) }

-- The colist replicate n x contains exactly n copies of x (and
-- nothing else).

replicate : ∀ {a i} {A : Set a} → Conat i → A → Colist A i
replicate zero    x = []
replicate (suc n) x = x ∷ λ { .force → replicate (force n) x }

-- Repeats the given element indefinitely.

repeat : ∀ {a i} {A : Set a} → A → Colist A i
repeat = replicate infinity

-- Appends one colist to another.

infixr 5 _++_

_++_ : ∀ {a i} {A : Set a} → Colist A i → Colist A i → Colist A i
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ λ { .force → force xs ++ ys }

------------------------------------------------------------------------
-- Bisimilarity

-- [ ∞ ] xs ∼ ys means that xs and ys are "equal".

mutual

  infix 4 [_]_∼_ [_]_∼′_

  data [_]_∼_ {a} {A : Set a} (i : Size) :
              Colist A ∞ → Colist A ∞ → Set a where
    []  : [ i ] [] ∼ []
    _∷_ : ∀ {x y xs ys} →
          x ≡ y → [ i ] force xs ∼′ force ys → [ i ] x ∷ xs ∼ y ∷ ys

  record [_]_∼′_ {a} {A : Set a} (i : Size)
                 (xs ys : Colist A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → [ j ] xs ∼ ys

open [_]_∼′_ public

-- Bisimilarity is an equivalence relation.

reflexive-∼ : ∀ {i a} {A : Set a}
              (xs : Colist A ∞) → [ i ] xs ∼ xs
reflexive-∼ []       = []
reflexive-∼ (x ∷ xs) = refl ∷ λ { .force → reflexive-∼ (force xs) }

symmetric-∼ : ∀ {i a} {A : Set a} {xs ys : Colist A ∞} →
              [ i ] xs ∼ ys → [ i ] ys ∼ xs
symmetric-∼ []        = []
symmetric-∼ (p₁ ∷ p₂) = sym p₁ ∷ λ { .force → symmetric-∼ (force p₂) }

transitive-∼ : ∀ {i a} {A : Set a} {xs ys zs : Colist A ∞} →
               [ i ] xs ∼ ys → [ i ] ys ∼ zs → [ i ] xs ∼ zs
transitive-∼ []        []        = []
transitive-∼ (p₁ ∷ p₂) (q₁ ∷ q₂) =
  trans p₁ q₁ ∷ λ { .force → transitive-∼ (force p₂) (force q₂) }

-- A property relating Colist._∷_ and _∷′_.

∷∼∷′ : ∀ {i a} {A : Set a} {x : A} {xs} →
       [ i ] x ∷ xs ∼ x ∷′ force xs
∷∼∷′ = refl ∷ λ { .force → reflexive-∼ _ }

------------------------------------------------------------------------
-- The ◇ predicate

-- ◇ ∞ P xs means that P holds for some element in xs.

data ◇ {a p} {A : Set a}
       (P : A → Set p) : Colist A ∞ → Set (a ⊔ p) where
  here  : ∀ {x xs} → P x → ◇ P (x ∷ xs)
  there : ∀ {x xs} → ◇ P (force xs) → ◇ P (x ∷ xs)

-- ◇ respects bisimilarity.

◇-∼ :
  ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
  [ ∞ ] xs ∼ ys → ◇ P xs → ◇ P ys
◇-∼ (refl ∷ _) (here p)  = here p
◇-∼ (_    ∷ b) (there p) = there (◇-∼ (force b) p)

-- A map function for ◇.

◇-map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} →
        (∀ {x} → P x → Q x) →
        (∀ {xs} → ◇ P xs → ◇ Q xs)
◇-map f (here p)  = here (f p)
◇-map f (there p) = there (◇-map f p)

-- If a predicate holds for some element in a colist, then it holds
-- for some value.

◇-witness : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
            ◇ P xs → ∃ P
◇-witness (here p)  = _ , p
◇-witness (there p) = ◇-witness p

-- If const P holds for some element, then P holds.

◇-const : ∀ {a p} {A : Set a} {P : Set p} {xs : Colist A ∞} →
          ◇ (const P) xs → P
◇-const = proj₂ ∘ ◇-witness

------------------------------------------------------------------------
-- The □ predicate

-- □ ∞ P xs means that P holds for every element in xs.

mutual

  data □ {a p} {A : Set a} (i : Size)
         (P : A → Set p) : Colist A ∞ → Set (a ⊔ p) where
    []  : □ i P []
    _∷_ : ∀ {x xs} → P x → □′ i P (force xs) → □ i P (x ∷ xs)

  record □′ {a p} {A : Set a} (i : Size)
            (P : A → Set p) (xs : Colist A ∞) : Set (a ⊔ p) where
    coinductive
    field
      force : {j : Size< i} → □ j P xs

open □′ public

-- Some projections.

□-head : ∀ {a p i} {A : Set a} {P : A → Set p} {x xs} →
         □ i P (x ∷ xs) → P x
□-head (p ∷ _) = p

□-tail : ∀ {a p i} {j : Size< i} {A : Set a} {P : A → Set p} {x xs} →
         □ i P (x ∷ xs) → □ j P (force xs)
□-tail (_ ∷ ps) = force ps

-- □ respects bisimilarity.

□-∼ :
  ∀ {i a p} {A : Set a} {P : A → Set p} {xs ys} →
  [ i ] xs ∼ ys → □ i P xs → □ i P ys
□-∼ []         _        = []
□-∼ (refl ∷ b) (p ∷ ps) = p ∷ λ { .force → □-∼ (force b) (force ps) }

-- If P is universally true, then □ i P is also universally true.

□-replicate : ∀ {a p i} {A : Set a} {P : A → Set p} →
              (∀ x → P x) →
              (∀ xs → □ i P xs)
□-replicate f []       = []
□-replicate f (x ∷ xs) = f x ∷ λ { .force → □-replicate f (force xs) }

-- Something resembling applicative functor application for □.

infixl 4 _□-⊛_

_□-⊛_ : ∀ {i a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs} →
        □ i (λ x → P x → Q x) xs → □ i P xs → □ i Q xs
[]       □-⊛ _        = []
(f ∷ fs) □-⊛ (p ∷ ps) = f p ∷ λ { .force → force fs □-⊛ force ps }

-- A map function for □.

□-map : ∀ {a p q i} {A : Set a} {P : A → Set p} {Q : A → Set q} →
        (∀ {x} → P x → Q x) →
        (∀ {xs} → □ i P xs → □ i Q xs)
□-map f ps = □-replicate (λ _ → f) _ □-⊛ ps

-- Something resembling applicative functor application for □ and ◇.

infixl 4 _□◇-⊛_

_□◇-⊛_ : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs} →
         □ ∞ (λ x → P x → Q x) xs → ◇ P xs → ◇ Q xs
(f ∷ _)  □◇-⊛ (here p)  = here (f p)
(_ ∷ fs) □◇-⊛ (there p) = there (force fs □◇-⊛ p)

-- A combination of some of the combinators above.

□◇-witness :
  ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs} →
  □ ∞ P xs → ◇ Q xs → ∃ λ x → P x × Q x
□◇-witness p q = ◇-witness (□-map _,_ p □◇-⊛ q)
