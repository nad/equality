------------------------------------------------------------------------
-- Colists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Colist where

open import Conat using (Conat; zero; suc; force; infinity)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

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

data ◇ {a p} {A : Set a} (i : Size)
       (P : A → Set p) : Colist A ∞ → Set (a ⊔ p) where
  here  : ∀ {x xs} → P x → ◇ i P (x ∷ xs)
  there : ∀ {x xs} {j : Size< i} → ◇ j P (force xs) → ◇ i P (x ∷ xs)

-- ◇ respects bisimilarity.

◇-∼ :
  ∀ {a p i} {A : Set a} {P : A → Set p} {xs ys} →
  [ ∞ ] xs ∼ ys → ◇ i P xs → ◇ i P ys
◇-∼ (refl ∷ _) (here p)  = here p
◇-∼ (_    ∷ b) (there p) = there (◇-∼ (force b) p)

-- A map function for ◇.

◇-map : ∀ {a p q i} {A : Set a} {P : A → Set p} {Q : A → Set q} →
        (∀ {x} → P x → Q x) →
        (∀ {xs} → ◇ i P xs → ◇ i Q xs)
◇-map f (here p)  = here (f p)
◇-map f (there p) = there (◇-map f p)

-- A variant of ◇-map.

◇-map′ : ∀ {a b p q i}
           {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
           {f : A → B} →
         (∀ {x} → P x → Q (f x)) →
         (∀ {xs} → ◇ i P xs → ◇ i Q (map f xs))
◇-map′ g (here p)  = here (g p)
◇-map′ g (there p) = there (◇-map′ g p)

-- If a predicate holds for some element in a colist, then it holds
-- for some value.

◇-witness : ∀ {a p i} {A : Set a} {P : A → Set p} {xs} →
            ◇ i P xs → ∃ P
◇-witness (here p)  = _ , p
◇-witness (there p) = ◇-witness p

-- If const P holds for some element, then P holds.

◇-const : ∀ {a p i} {A : Set a} {P : Set p} {xs : Colist A ∞} →
          ◇ i (const P) xs → P
◇-const = proj₂ ∘ ◇-witness

-- Colist membership.

infix 4 [_]_∈_

[_]_∈_ : ∀ {a} {A : Set a} → Size → A → Colist A ∞ → Set a
[ i ] x ∈ xs = ◇ i (x ≡_) xs

-- A generalisation of "◇ ∞ P xs holds iff P holds for some element in
-- xs".

◇⇔∈× : ∀ {a p i} {A : Set a} {P : A → Set p} {xs} →
       ◇ i P xs ⇔ ∃ λ x → [ i ] x ∈ xs × P x
◇⇔∈× {P = P} = record { to = to; from = from }
  where
  to : ∀ {i xs} → ◇ i P xs → ∃ λ x → [ i ] x ∈ xs × P x
  to (here p)  = _ , here refl , p
  to (there p) = Σ-map id (Σ-map there id) (to p)

  from : ∀ {i xs} → (∃ λ x → [ i ] x ∈ xs × P x) → ◇ i P xs
  from (x , here refl  , p) = here p
  from (x , there x∈xs , p) = there (from (x , x∈xs , p))

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

-- A generalisation of "□ ∞ P xs holds iff P is true for every element
-- in xs".

□⇔∈→ : ∀ {a p i} {A : Set a} {P : A → Set p} {xs} →
       □ i P xs ⇔ (∀ x → [ i ] x ∈ xs → P x)
□⇔∈→ {P = P} = record { to = to; from = from _ }
  where
  to : ∀ {i xs} → □ i P xs → (∀ x → [ i ] x ∈ xs → P x)
  to (p ∷ ps) x (here refl)  = p
  to (p ∷ ps) x (there x∈xs) = to (force ps) x x∈xs

  from : ∀ {i} xs → (∀ x → [ i ] x ∈ xs → P x) → □ i P xs
  from []       f = []
  from (x ∷ xs) f =
    f x (here refl) ∷ λ { .force → from (force xs) (λ x → f x ∘ there) }

-- If P is universally true, then □ i P is also universally true.

□-replicate : ∀ {a p i} {A : Set a} {P : A → Set p} →
              (∀ x → P x) →
              (∀ xs → □ i P xs)
□-replicate f _ = _⇔_.from □⇔∈→ (λ x _ → f x)

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

-- A variant of □-map.

□-map′ : ∀ {a b p q i}
           {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
           {f : A → B} →
         (∀ {x} → P x → Q (f x)) →
         (∀ {xs} → □ i P xs → □ i Q (map f xs))
□-map′ g []       = []
□-map′ g (p ∷ ps) = g p ∷ λ { .force → □-map′ g (force ps) }

-- Something resembling applicative functor application for □ and ◇.

infixl 4 _□◇-⊛_

_□◇-⊛_ : ∀ {a p q i} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs} →
         □ i (λ x → P x → Q x) xs → ◇ i P xs → ◇ i Q xs
(f ∷ _)  □◇-⊛ (here p)  = here (f p)
(_ ∷ fs) □◇-⊛ (there p) = there (force fs □◇-⊛ p)

-- A combination of some of the combinators above.

□◇-witness :
  ∀ {a p q i} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs} →
  □ i P xs → ◇ i Q xs → ∃ λ x → P x × Q x
□◇-witness p q = ◇-witness (□-map _,_ p □◇-⊛ q)

------------------------------------------------------------------------
-- A variant of ◇ with a sized predicate

-- ◇ˢ ∞ P xs means that (some instance of) P holds for some element in
-- xs.

data ◇ˢ {a p} {A : Set a} (i : Size)
        (P : Size → A → Set p) : Colist A ∞ → Set (a ⊔ p) where
  here  : ∀ {x xs} → P i x → ◇ˢ i P (x ∷ xs)
  there : ∀ {x xs} {j : Size< i} → ◇ˢ j P (force xs) → ◇ˢ i P (x ∷ xs)

-- ◇ˢ respects bisimilarity.

◇ˢ-∼ :
  ∀ {a p i} {A : Set a} {P : Size → A → Set p} {xs ys} →
  [ ∞ ] xs ∼ ys → ◇ˢ i P xs → ◇ˢ i P ys
◇ˢ-∼ (refl ∷ _) (here p)  = here p
◇ˢ-∼ (_    ∷ b) (there p) = there (◇ˢ-∼ (force b) p)

-- If P is upwards closed, then flip ◇ˢ P is upwards closed.

◇ˢ-upwards-closed :
  ∀ {a p} {A : Set a} {P : Size → A → Set p} →
  (∀ {i} {j : Size< i} {x} → P j x → P i x) →
  (∀ {i} {j : Size< i} {xs} → ◇ˢ j P xs → ◇ˢ i P xs)
◇ˢ-upwards-closed P-closed (here p)  = here (P-closed p)
◇ˢ-upwards-closed P-closed (there p) =
  there (◇ˢ-upwards-closed P-closed p)

-- A variant of the previous lemma.

◇ˢ-upwards-closed-∞ :
  ∀ {a p} {A : Set a} {P : Size → A → Set p} →
  (∀ {i x} → P i x → P ∞ x) →
  (∀ {i xs} → ◇ˢ i P xs → ◇ˢ ∞ P xs)
◇ˢ-upwards-closed-∞ P-closed-∞ (here p)  = here (P-closed-∞ p)
◇ˢ-upwards-closed-∞ P-closed-∞ (there p) =
  there (◇ˢ-upwards-closed-∞ P-closed-∞ p)

-- A map function for ◇ˢ.

◇ˢ-map : ∀ {a p q i}
           {A : Set a} {P : Size → A → Set p} {Q : Size → A → Set q} →
         (∀ {i x} → P i x → Q i x) →
         (∀ {xs} → ◇ˢ i P xs → ◇ˢ i Q xs)
◇ˢ-map f (here p)  = here (f p)
◇ˢ-map f (there p) = there (◇ˢ-map f p)

-- A variant of ◇ˢ-map.

◇ˢ-map′ : ∀ {a b p q i} {A : Set a} {B : Set b}
            {P : Size → A → Set p} {Q : Size → B → Set q} {f : A → B} →
          (∀ {i x} → P i x → Q i (f x)) →
          (∀ {xs} → ◇ˢ i P xs → ◇ˢ i Q (map f xs))
◇ˢ-map′ g (here p)  = here (g p)
◇ˢ-map′ g (there p) = there (◇ˢ-map′ g p)

-- If a predicate holds for some element in a colist, then it holds
-- for some value (assuming that P is upwards closed).

◇ˢ-witness : ∀ {a p i} {A : Set a} {P : Size → A → Set p} {xs} →
             (∀ {i} {j : Size< i} {x} → P j x → P i x) →
             ◇ˢ i P xs → ∃ (P i)
◇ˢ-witness closed (here p)  = _ , p
◇ˢ-witness closed (there p) = Σ-map id closed (◇ˢ-witness closed p)

-- If P ∞ holds for some element in xs, then ◇ˢ ∞ P xs holds.

∈×∞→◇ˢ : ∀ {a p} {A : Set a} {P : Size → A → Set p} {x xs} →
         [ ∞ ] x ∈ xs → P ∞ x → ◇ˢ ∞ P xs
∈×∞→◇ˢ (here refl)  p = here p
∈×∞→◇ˢ (there x∈xs) p = there (∈×∞→◇ˢ x∈xs p)

-- If P i x implies P ∞ x for any i and x, then ◇ˢ ∞ P xs holds iff
-- P ∞ holds for some element in xs.

◇ˢ⇔∈× : ∀ {a p} {A : Set a} {P : Size → A → Set p} {xs} →
        (∀ {i x} → P i x → P ∞ x) →
        ◇ˢ ∞ P xs ⇔ (∃ λ x → [ ∞ ] x ∈ xs × P ∞ x)
◇ˢ⇔∈× {P = P} →∞ = record
  { to   = to
  ; from = λ { (_ , x∈xs , p) → ∈×∞→◇ˢ x∈xs p }
  }
  where
  to : ∀ {i xs} → ◇ˢ i P xs → ∃ λ x → [ ∞ ] x ∈ xs × P ∞ x
  to (here p)  = _ , here refl , →∞ p
  to (there p) = Σ-map id (Σ-map there id) (to p)

-- Sized variants of the previous lemma.

◇ˢ→∈× : ∀ {a p} {A : Set a} {P : Size → A → Set p} →
        (∀ {i} {j : Size< i} {x} → P j x → P i x) →
        ∀ {i xs} → ◇ˢ i P xs → ∃ λ x → [ i ] x ∈ xs × P i x
◇ˢ→∈× closed (here p)  = _ , here refl , p
◇ˢ→∈× closed (there p) = Σ-map id (Σ-map there closed) (◇ˢ→∈× closed p)

∈×→◇ˢ : ∀ {a p} {A : Set a} {P : Size → A → Set p} →
        (∀ {i} {j : Size< i} {x} → P i x → P j x) →
        ∀ {i x xs} → [ i ] x ∈ xs → P i x → ◇ˢ i P xs
∈×→◇ˢ closed (here refl)  p = here p
∈×→◇ˢ closed (there x∈xs) p = there (∈×→◇ˢ closed x∈xs (closed p))

-- ◇ ∞ (P ∞) is "contained in" ◇ˢ ∞ P.

◇∞→◇ˢ∞ : ∀ {a p} {A : Set a} {P : Size → A → Set p} {xs} →
         ◇ ∞ (P ∞) xs → ◇ˢ ∞ P xs
◇∞→◇ˢ∞ {P = P} {xs} =
  ◇ ∞ (P ∞) xs                    ↝⟨ _⇔_.to ◇⇔∈× ⟩
  (∃ λ x → [ ∞ ] x ∈ xs × P ∞ x)  ↝⟨ (λ { (_ , x∈xs , p) → ∈×∞→◇ˢ x∈xs p }) ⟩□
  ◇ˢ ∞ P xs                       □

-- If P i x implies P ∞ x for any i and x, then ◇ˢ ∞ P is pointwise
-- logically equivalent to ◇ ∞ (P ∞).

◇ˢ∞⇔◇∞ : ∀ {a p} {A : Set a} {P : Size → A → Set p} {xs} →
         (∀ {i x} → P i x → P ∞ x) →
         ◇ˢ ∞ P xs ⇔ ◇ ∞ (P ∞) xs
◇ˢ∞⇔◇∞ {P = P} {xs} →∞ =
  ◇ˢ ∞ P xs                       ↝⟨ ◇ˢ⇔∈× →∞ ⟩
  (∃ λ x → [ ∞ ] x ∈ xs × P ∞ x)  ↝⟨ inverse ◇⇔∈× ⟩□
  ◇ ∞ (P ∞) xs                    □

-- ◇ˢ i (const P) is pointwise logically equivalent to ◇ i P.

◇ˢ⇔◇ : ∀ {a p i} {A : Set a} {P : A → Set p} {xs} →
       ◇ˢ i (const P) xs ⇔ ◇ i P xs
◇ˢ⇔◇ {P = P} {xs} = record { to = to; from = from }
  where
  to : ∀ {i xs} → ◇ˢ i (const P) xs → ◇ i P xs
  to (here p)  = here p
  to (there p) = there (to p)

  from : ∀ {i xs} → ◇ i P xs → ◇ˢ i (const P) xs
  from (here p)  = here p
  from (there p) = there (from p)

------------------------------------------------------------------------
-- A variant of □ with a sized predicate

-- □ˢ ∞ P xs means that (some instance of) P holds for every element
-- in xs.

mutual

  data □ˢ {a p} {A : Set a} (i : Size)
          (P : Size → A → Set p) : Colist A ∞ → Set (a ⊔ p) where
    []  : □ˢ i P []
    _∷_ : ∀ {x xs} → P i x → □ˢ′ i P (force xs) → □ˢ i P (x ∷ xs)

  record □ˢ′ {a p} {A : Set a} (i : Size)
             (P : Size → A → Set p) (xs : Colist A ∞) : Set (a ⊔ p) where
    coinductive
    field
      force : {j : Size< i} → □ˢ j P xs

open □ˢ′ public

-- Some projections.

□ˢ-head : ∀ {a p i} {A : Set a} {P : Size → A → Set p} {x xs} →
          □ˢ i P (x ∷ xs) → P i x
□ˢ-head (p ∷ _) = p

□ˢ-tail : ∀ {a p i} {j : Size< i}
            {A : Set a} {P : Size → A → Set p} {x xs} →
          □ˢ i P (x ∷ xs) → □ˢ j P (force xs)
□ˢ-tail (_ ∷ ps) = force ps

-- □ˢ respects bisimilarity.

□ˢ-∼ :
  ∀ {i a p} {A : Set a} {P : Size → A → Set p} {xs ys} →
  [ i ] xs ∼ ys → □ˢ i P xs → □ˢ i P ys
□ˢ-∼ []         _        = []
□ˢ-∼ (refl ∷ b) (p ∷ ps) = p ∷ λ { .force → □ˢ-∼ (force b) (force ps) }

-- If P is downwards closed, then flip □ˢ P is downwards closed.

□ˢ-downwards-closed :
  ∀ {a p} {A : Set a} {P : Size → A → Set p} →
  (∀ {i} {j : Size< i} {x} → P i x → P j x) →
  (∀ {i} {j : Size< i} {xs} → □ˢ i P xs → □ˢ j P xs)
□ˢ-downwards-closed P-closed []       = []
□ˢ-downwards-closed P-closed (p ∷ ps) =
  P-closed p ∷ λ { .force → □ˢ-downwards-closed P-closed (force ps) }

-- A variant of the previous lemma.

□ˢ-downwards-closed-∞ :
  ∀ {a p} {A : Set a} {P : Size → A → Set p} →
  (∀ {i x} → P ∞ x → P i x) →
  (∀ {i xs} → □ˢ ∞ P xs → □ˢ i P xs)
□ˢ-downwards-closed-∞ P-closed-∞ []       = []
□ˢ-downwards-closed-∞ P-closed-∞ (p ∷ ps) =
  P-closed-∞ p ∷ λ { .force →
  □ˢ-downwards-closed-∞ P-closed-∞ (force ps) }

-- If □ˢ ∞ P xs holds, then P ∞ holds for every element in xs.

□ˢ∞∈→ : ∀ {a p} {A : Set a} {P : Size → A → Set p} {xs x} →
        □ˢ ∞ P xs → [ ∞ ] x ∈ xs → P ∞ x
□ˢ∞∈→ (p ∷ ps) (here refl)  = p
□ˢ∞∈→ (p ∷ ps) (there x∈xs) = □ˢ∞∈→ (force ps) x∈xs

-- If P ∞ x implies P i x for any i and x, then □ˢ ∞ P xs holds iff P ∞
-- holds for every element in xs.

□ˢ⇔∈→ : ∀ {a p} {A : Set a} {P : Size → A → Set p} {xs} →
        (∀ {i x} → P ∞ x → P i x) →
        □ˢ ∞ P xs ⇔ (∀ x → [ ∞ ] x ∈ xs → P ∞ x)
□ˢ⇔∈→ {P = P} ∞→ = record { to = λ p _ → □ˢ∞∈→ p; from = from _ }
  where
  from : ∀ {i} xs → (∀ x → [ ∞ ] x ∈ xs → P ∞ x) → □ˢ i P xs
  from []       f = []
  from (x ∷ xs) f =
    ∞→ (f x (here refl)) ∷ λ { .force →
    from (force xs) (λ x → f x ∘ there) }

-- Sized variants of the previous lemma.

□ˢ∈→ : ∀ {a p} {A : Set a} {P : Size → A → Set p} →
       (∀ {i} {j : Size< i} {x} → P j x → P i x) →
       ∀ {i x xs} → □ˢ i P xs → [ i ] x ∈ xs → P i x
□ˢ∈→ closed (p ∷ ps) (here refl)  = p
□ˢ∈→ closed (p ∷ ps) (there x∈xs) = closed (□ˢ∈→ closed (force ps) x∈xs)

∈→→□ˢ : ∀ {a p} {A : Set a} {P : Size → A → Set p} →
        (∀ {i} {j : Size< i} {x} → P i x → P j x) →
        ∀ {i} xs → (∀ x → [ i ] x ∈ xs → P i x) → □ˢ i P xs
∈→→□ˢ closed []       f = []
∈→→□ˢ closed (x ∷ xs) f =
  f x (here refl) ∷ λ { .force →
  ∈→→□ˢ closed (force xs) (λ x → closed ∘ f x ∘ there) }

-- □ˢ ∞ P is "contained in" □ ∞ (P ∞).

□ˢ∞→□∞ : ∀ {a p} {A : Set a} {P : Size → A → Set p} {xs} →
         □ˢ ∞ P xs → □ ∞ (P ∞) xs
□ˢ∞→□∞ {P = P} {xs} =
  □ˢ ∞ P xs                     ↝⟨ (λ p _ → □ˢ∞∈→ p) ⟩
  (∀ x → [ ∞ ] x ∈ xs → P ∞ x)  ↝⟨ _⇔_.from □⇔∈→ ⟩□
  □ ∞ (P ∞) xs                  □

-- If P ∞ x implies P i x for any i and x, then □ˢ ∞ P is pointwise
-- logically equivalent to □ ∞ (P ∞).

□ˢ∞⇔□∞ : ∀ {a p} {A : Set a} {P : Size → A → Set p} {xs} →
         (∀ {i x} → P ∞ x → P i x) →
         □ˢ ∞ P xs ⇔ □ ∞ (P ∞) xs
□ˢ∞⇔□∞ {P = P} {xs} ∞→ =
  □ˢ ∞ P xs                     ↝⟨ □ˢ⇔∈→ ∞→ ⟩
  (∀ x → [ ∞ ] x ∈ xs → P ∞ x)  ↝⟨ inverse □⇔∈→ ⟩□
  □ ∞ (P ∞) xs                  □

-- □ˢ i (const P) is pointwise logically equivalent to □ i P.

□ˢ⇔□ : ∀ {a p i} {A : Set a} {P : A → Set p} {xs} →
       □ˢ i (const P) xs ⇔ □ i P xs
□ˢ⇔□ {P = P} {xs} = record { to = to; from = from }
  where
  to : ∀ {i xs} → □ˢ i (const P) xs → □ i P xs
  to []       = []
  to (p ∷ ps) = p ∷ λ { .force → to (force ps) }

  from : ∀ {i xs} → □ i P xs → □ˢ i (const P) xs
  from []       = []
  from (p ∷ ps) = p ∷ λ { .force → from (force ps) }

-- If P is universally true, then □ˢ i P is also universally true.

□ˢ-replicate : ∀ {a p i} {A : Set a} {P : Size → A → Set p} →
               (∀ {i} x → P i x) →
               (∀ xs → □ˢ i P xs)
□ˢ-replicate f []       = []
□ˢ-replicate f (x ∷ xs) = f x ∷ λ { .force → □ˢ-replicate f (force xs) }

-- Something resembling applicative functor application for □ˢ.

infixl 4 _□ˢ-⊛_

_□ˢ-⊛_ : ∀ {i a p q} {A : Set a}
           {P : Size → A → Set p} {Q : Size → A → Set q} {xs} →
         □ˢ i (λ j x → P j x → Q j x) xs → □ˢ i P xs → □ˢ i Q xs
[]       □ˢ-⊛ _        = []
(f ∷ fs) □ˢ-⊛ (p ∷ ps) = f p ∷ λ { .force → force fs □ˢ-⊛ force ps }

-- A map function for □ˢ.

□ˢ-map : ∀ {a p q i}
           {A : Set a} {P : Size → A → Set p} {Q : Size → A → Set q} →
         (∀ {i x} → P i x → Q i x) →
         (∀ {xs} → □ˢ i P xs → □ˢ i Q xs)
□ˢ-map f ps = □ˢ-replicate (λ _ → f) _ □ˢ-⊛ ps

-- A variant of □ˢ-map.

□ˢ-map′ : ∀ {a b p q i} {A : Set a} {B : Set b}
            {P : Size → A → Set p} {Q : Size → B → Set q} {f : A → B} →
          (∀ {i x} → P i x → Q i (f x)) →
          (∀ {xs} → □ˢ i P xs → □ˢ i Q (map f xs))
□ˢ-map′ g []       = []
□ˢ-map′ g (p ∷ ps) = g p ∷ λ { .force → □ˢ-map′ g (force ps) }

-- Something resembling applicative functor application for □ˢ and ◇ˢ.

infixl 4 _□ˢ◇ˢ-⊛_

_□ˢ◇ˢ-⊛_ : ∀ {a p q i} {A : Set a}
             {P : Size → A → Set p} {Q : Size → A → Set q} {xs} →
           □ˢ i (λ j x → P j x → Q j x) xs → ◇ˢ i P xs → ◇ˢ i Q xs
(f ∷ _)  □ˢ◇ˢ-⊛ (here p)  = here (f p)
(_ ∷ fs) □ˢ◇ˢ-⊛ (there p) = there (force fs □ˢ◇ˢ-⊛ p)

-- A combination of some of the combinators above.

□ˢ◇ˢ-witness :
  ∀ {a p q i}
    {A : Set a} {P : Size → A → Set p} {Q : Size → A → Set q} {xs} →
  (∀ {i} {j : Size< i} {x} → P j x → P i x) →
  (∀ {i} {j : Size< i} {x} → Q j x → Q i x) →
  □ˢ i P xs → ◇ˢ i Q xs → ∃ λ x → P i x × Q i x
□ˢ◇ˢ-witness P-closed Q-closed p q =
  ◇ˢ-witness (λ { {_} {_} → Σ-map P-closed Q-closed })
             (□ˢ-map _,_ p □ˢ◇ˢ-⊛ q)
