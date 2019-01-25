------------------------------------------------------------------------
-- Colists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Colist where

open import Conat using (Conat; zero; suc; force; infinity)
open import Equality.Propositional as E using (_≡_; refl)
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Size

open import Function-universe E.equality-with-J hiding (id; _∘_)
import Nat E.equality-with-J as Nat

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

-- The length of a colist.

length : ∀ {a i} {A : Set a} → Colist A i → Conat i
length []       = zero
length (n ∷ ns) = suc λ { .force → length (force ns) }

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

-- The colist cycle x xs is an endless cycle of repetitions of the
-- colist x ∷ xs.

cycle : ∀ {a i} {A : Set a} → A → Colist′ A i → Colist A i
cycle x xs = x ∷ λ { .force → force xs ++ cycle x xs }

-- "Scan left".

scanl : ∀ {a b i} {A : Set a} {B : Set b} →
        (A → B → A) → A → Colist B i → Colist A i
scanl c n []       = n ∷ λ { .force → [] }
scanl c n (x ∷ xs) = n ∷ λ { .force → scanl c (c n x) (force xs) }

-- The natural numbers in strictly increasing order.

nats : ∀ {i} → Colist ℕ i
nats = 0 ∷ λ { .force → map suc nats }

-- The colist nats-from n is the natural numbers greater than or equal
-- to n, in strictly increasing order.

nats-from : ∀ {i} → ℕ → Colist ℕ i
nats-from n = n ∷ λ { .force → nats-from (suc n) }

-- The list take n xs is the longest possible prefix of xs that
-- contains at most n elements.

take : ∀ {a} {A : Set a} → ℕ → Colist A ∞ → List A
take zero    _        = []
take _       []       = []
take (suc n) (x ∷ xs) = x ∷ take n (force xs)

------------------------------------------------------------------------
-- Bisimilarity

module _ {a} {A : Set a} where

  -- [ ∞ ] xs ∼ ys means that xs and ys are "equal".

  mutual

    infix 4 [_]_∼_ [_]_∼′_

    data [_]_∼_ (i : Size) : Colist A ∞ → Colist A ∞ → Set a where
      []  : [ i ] [] ∼ []
      _∷_ : ∀ {x y xs ys} →
            x ≡ y → [ i ] force xs ∼′ force ys → [ i ] x ∷ xs ∼ y ∷ ys

    record [_]_∼′_ (i : Size) (xs ys : Colist A ∞) : Set a where
      coinductive
      field
        force : {j : Size< i} → [ j ] xs ∼ ys

  open [_]_∼′_ public

  -- Bisimilarity is an equivalence relation.

  reflexive-∼ : ∀ {i} xs → [ i ] xs ∼ xs
  reflexive-∼ []       = []
  reflexive-∼ (x ∷ xs) = refl ∷ λ { .force → reflexive-∼ (force xs) }

  symmetric-∼ : ∀ {i xs ys} →
                [ i ] xs ∼ ys → [ i ] ys ∼ xs
  symmetric-∼ []        = []
  symmetric-∼ (p₁ ∷ p₂) =
    E.sym p₁ ∷ λ { .force → symmetric-∼ (force p₂) }

  transitive-∼ : ∀ {i xs ys zs} →
                 [ i ] xs ∼ ys → [ i ] ys ∼ zs → [ i ] xs ∼ zs
  transitive-∼ []        []        = []
  transitive-∼ (p₁ ∷ p₂) (q₁ ∷ q₂) =
    E.trans p₁ q₁ ∷ λ { .force → transitive-∼ (force p₂) (force q₂) }

  -- Equational reasoning combinators.

  infix  -1 _∎
  infixr -2 step-∼ step-≡ _∼⟨⟩_

  _∎ : ∀ {i} xs → [ i ] xs ∼ xs
  _∎ = reflexive-∼

  step-∼ : ∀ {i} xs {ys zs} →
           [ i ] ys ∼ zs → [ i ] xs ∼ ys → [ i ] xs ∼ zs
  step-∼ _ ys∼zs xs∼ys = transitive-∼ xs∼ys ys∼zs

  syntax step-∼ xs ys∼zs xs∼ys = xs ∼⟨ xs∼ys ⟩ ys∼zs

  step-≡ : ∀ {i} xs {ys zs} → [ i ] ys ∼ zs → xs ≡ ys → [ i ] xs ∼ zs
  step-≡ _ ys∼zs refl = ys∼zs

  syntax step-≡ xs ys∼zs xs≡ys = xs ≡⟨ xs≡ys ⟩ ys∼zs

  _∼⟨⟩_ : ∀ {i} xs {ys} → [ i ] xs ∼ ys → [ i ] xs ∼ ys
  _ ∼⟨⟩ xs∼ys = xs∼ys

  -- A property relating Colist._∷_ and _∷′_.

  ∷∼∷′ : ∀ {i} {x : A} {xs} →
         [ i ] x ∷ xs ∼ x ∷′ force xs
  ∷∼∷′ = refl ∷ λ { .force → reflexive-∼ _ }

-- Functor laws.

map-id :
  ∀ {a i} {A : Set a} (xs : Colist A ∞) →
  [ i ] map id xs ∼ xs
map-id []       = []
map-id (_ ∷ xs) = refl ∷ λ { .force → map-id (force xs) }

map-∘ :
  ∀ {a b c i} {A : Set a} {B : Set b} {C : Set c}
    {f : B → C} {g : A → B}
  (xs : Colist A ∞) →
  [ i ] map (f ∘ g) xs ∼ map f (map g xs)
map-∘ []       = []
map-∘ (_ ∷ xs) = refl ∷ λ { .force → map-∘ (force xs) }

-- If two non-empty colists are bisimilar, then their heads are
-- bisimilar.

head-cong : ∀ {a i} {A : Set a} {x y : A} {xs ys} →
            [ i ] x ∷ xs ∼ y ∷ ys → x ≡ y
head-cong (p ∷ _) = p

-- Some preservation lemmas.

tail-cong :
  ∀ {a i} {A : Set a} {xs ys : Colist A ∞} →
  [ i ] xs ∼ ys → [ i ] force (tail xs) ∼′ force (tail ys)
tail-cong []       = λ { .force → [] }
tail-cong (_ ∷ ps) = ps

map-cong :
  ∀ {a b i} {A : Set a} {B : Set b} {f g : A → B} {xs ys} →
  (∀ x → f x ≡ g x) → [ i ] xs ∼ ys → [ i ] map f xs ∼ map g ys
map-cong f≡g []          = []
map-cong f≡g (refl ∷ ps) =
  f≡g _ ∷ λ { .force → map-cong f≡g (force ps) }

length-cong :
  ∀ {a i} {A : Set a} {xs ys : Colist A ∞} →
  [ i ] xs ∼ ys → Conat.[ i ] length xs ∼ length ys
length-cong []       = zero
length-cong (_ ∷ ps) = suc λ { .force → length-cong (force ps) }

replicate-cong :
  ∀ {a i} {A : Set a} {m n} {x : A} →
  Conat.[ i ] m ∼ n → [ i ] replicate m x ∼ replicate n x
replicate-cong zero    = []
replicate-cong (suc p) = refl ∷ λ { .force → replicate-cong (force p) }

infixr 5 _++-cong_

_++-cong_ :
  ∀ {a i} {A : Set a} {xs₁ xs₂ ys₁ ys₂ : Colist A ∞} →
  [ i ] xs₁ ∼ ys₁ → [ i ] xs₂ ∼ ys₂ → [ i ] xs₁ ++ xs₂ ∼ ys₁ ++ ys₂
[]       ++-cong qs = qs
(p ∷ ps) ++-cong qs = p ∷ λ { .force → force ps ++-cong qs }

cycle-cong :
  ∀ {a i} {A : Set a} {x : A} {xs ys} →
  [ i ] force xs ∼′ force ys → [ i ] cycle x xs ∼ cycle x ys
cycle-cong p = refl ∷ λ { .force → force p ++-cong cycle-cong p }

scanl-cong :
  ∀ {a b i} {A : Set a} {B : Set b} {c : A → B → A} {n : A} {xs ys} →
  [ i ] xs ∼ ys → [ i ] scanl c n xs ∼ scanl c n ys
scanl-cong []          = refl ∷ λ { .force → [] }
scanl-cong (refl ∷ ps) = refl ∷ λ { .force → scanl-cong (force ps) }

take-cong :
  ∀ {a} {A : Set a} n {xs ys : Colist A ∞} →
  [ ∞ ] xs ∼ ys → take n xs ≡ take n ys
take-cong n       []       = refl
take-cong zero    (p ∷ ps) = refl
take-cong (suc n) (p ∷ ps) = E.cong₂ _∷_ p (take-cong n (force ps))

-- The length of replicate n x is bisimilar to n.

length-replicate :
  ∀ {a i} {A : Set a} {x : A} n →
  Conat.[ i ] length (replicate n x) ∼ n
length-replicate zero    = zero
length-replicate (suc n) =
  suc λ { .force → length-replicate (force n) }

-- A lemma relating nats and nats-from n.

map-+-nats∼nats-from :
  ∀ {i} n → [ i ] map (n +_) nats ∼ nats-from n
map-+-nats∼nats-from n = Nat.+-right-identity ∷ λ { .force →
  map (n +_) (map suc nats)  ∼⟨ symmetric-∼ (map-∘ _) ⟩
  map ((n +_) ∘ suc) nats    ∼⟨ map-cong (λ _ → E.sym (Nat.suc+≡+suc _)) (_ ∎) ⟩
  map (suc n +_) nats        ∼⟨ map-+-nats∼nats-from (suc n) ⟩
  nats-from (suc n)          ∎ }

-- The colist nats is bisimilar to nats-from 0.

nats∼nats-from-0 : ∀ {i} → [ i ] nats ∼ nats-from 0
nats∼nats-from-0 =
  nats             ∼⟨ symmetric-∼ (map-id _) ⟩
  map id nats      ∼⟨⟩
  map (0 +_) nats  ∼⟨ map-+-nats∼nats-from _ ⟩
  nats-from 0      ∎

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

◇-map′ : ∀ {a b c p q i} {A : Set a} {B : Set b} {C : Set c}
           {P : B → Set p} {Q : C → Set q}
           {f : A → B} {g : A → C} →
         (∀ {x} → P (f x) → Q (g x)) →
         (∀ {xs} → ◇ i P (map f xs) → ◇ i Q (map g xs))
◇-map′ g {_ ∷ _} (here p)  = here (g p)
◇-map′ g {_ ∷ _} (there p) = there (◇-map′ g p)
◇-map′ g {[]}    ()

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

-- If P holds for some element in replicate (suc n) x, then it also
-- holds for x, and vice versa.

◇-replicate-suc⇔ :
  ∀ {a p i} {A : Set a} {P : A → Set p} {x : A} {n} →
  ◇ i P (replicate (suc n) x) ⇔ P x
◇-replicate-suc⇔ {P = P} {x} = record
  { to   = to _
  ; from = here
  }
  where
  to : ∀ {i} n → ◇ i P (replicate n x) → P x
  to zero    ()
  to (suc n) (here p)  = p
  to (suc n) (there p) = to (force n) p

-- If P holds for some element in cycle x xs, then it also holds for
-- some element in x ∷ xs, and vice versa.

◇-cycle⇔ :
  ∀ {a p i} {A : Set a} {P : A → Set p} {x : A} {xs} →
  ◇ i P (cycle x xs) ⇔ ◇ i P (x ∷ xs)
◇-cycle⇔ {i = i} {P = P} {x} {xs} = record
  { to   = ◇ i P (cycle x xs)               ↝⟨ ◇-∼ (transitive-∼ ∷∼∷′ (symmetric-∼ ∷∼∷′)) ⟩
           ◇ i P ((x ∷ xs) ++ cycle x xs)   ↝⟨ to _ ⟩
           ◇ i P (x ∷ xs) ⊎ ◇ i P (x ∷ xs)  ↝⟨ [ id , id ] ⟩□
           ◇ i P (x ∷ xs)                   □
  ; from = ◇ i P (x ∷ xs)                  ↝⟨ from ⟩
           ◇ i P ((x ∷ xs) ++ cycle x xs)  ↝⟨ ◇-∼ (transitive-∼ ∷∼∷′ (symmetric-∼ ∷∼∷′)) ⟩□
           ◇ i P (cycle x xs)              □
  }
  where
  to : ∀ {i} ys → ◇ i P (ys ++ cycle x xs) → ◇ i P ys ⊎ ◇ i P (x ∷ xs)
  to []       (here p)  = inj₂ (here p)
  to []       (there p) = case to (force xs) p of
                            [ inj₂ ∘ there , inj₂ ]
  to (y ∷ ys) (here p)  = inj₁ (here p)
  to (y ∷ ys) (there p) = ⊎-map there id (to (force ys) p)

  from : ∀ {i ys} → ◇ i P ys → ◇ i P (ys ++ cycle x xs)
  from (here p)   = here p
  from (there ps) = there (from ps)

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

□-map′ : ∀ {a b c p q i} {A : Set a} {B : Set b} {C : Set c}
           {P : B → Set p} {Q : C → Set q}
           {f : A → B} {g : A → C} →
         (∀ {x} → P (f x) → Q (g x)) →
         (∀ {xs} → □ i P (map f xs) → □ i Q (map g xs))
□-map′ g {[]}    []       = []
□-map′ g {_ ∷ _} (p ∷ ps) = g p ∷ λ { .force → □-map′ g (force ps) }

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

-- If P holds for every element in replicate (suc n) x, then it also holds
-- for x, and vice versa.

□-replicate-suc⇔ :
  ∀ {a p i} {A : Set a} {P : A → Set p} {x : A} {n} →
  □ i P (replicate (suc n) x) ⇔ P x
□-replicate-suc⇔ {P = P} {x} = record
  { to   = □-head
  ; from = from _
  }
  where
  from : ∀ {i} n → P x → □ i P (replicate n x)
  from zero    p = []
  from (suc n) p = p ∷ λ { .force → from (force n) p }

-- If P holds for every element in cycle x xs, then it also holds for
-- every element in x ∷ xs, and vice versa.

□-cycle⇔ :
  ∀ {a p i} {A : Set a} {P : A → Set p} {x : A} {xs} →
  □ i P (cycle x xs) ⇔ □ i P (x ∷ xs)
□-cycle⇔ {i = i} {P = P} {x} {xs} = record
  { to   = □ i P (cycle x xs)              ↝⟨ (λ { (p ∷ ps) → p ∷ ps }) ⟩
           □ i P ((x ∷ xs) ++ cycle x xs)  ↝⟨ to _ ⟩□
           □ i P (x ∷ xs)                  □
  ; from = □ i P (x ∷ xs)                  ↝⟨ (λ hyp → from hyp hyp) ⟩
           □ i P ((x ∷ xs) ++ cycle x xs)  ↝⟨ (λ { (p ∷ ps) → p ∷ ps }) ⟩□
           □ i P (cycle x xs)              □
  }
  where
  to : ∀ {i} ys → □ i P (ys ++ cycle x xs) → □ i P ys
  to []       _        = []
  to (y ∷ ys) (p ∷ ps) = p ∷ λ { .force → to (force ys) (force ps) }

  from : ∀ {i ys} →
         □ i P (x ∷ xs) → □ i P ys → □ i P (ys ++ cycle x xs)
  from ps       (q ∷ qs) = q ∷ λ { .force → from ps (force qs) }
  from (p ∷ ps) []       = p ∷ λ { .force → from (p ∷ ps) (force ps) }

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

◇ˢ-map′ : ∀ {a b c p q i} {A : Set a} {B : Set b} {C : Set c}
            {P : Size → B → Set p} {Q : Size → C → Set q}
            {f : A → B} {g : A → C} →
          (∀ {i x} → P i (f x) → Q i (g x)) →
          (∀ {xs} → ◇ˢ i P (map f xs) → ◇ˢ i Q (map g xs))
◇ˢ-map′ g {_ ∷ _} (here p)  = here (g p)
◇ˢ-map′ g {_ ∷ _} (there p) = there (◇ˢ-map′ g p)
◇ˢ-map′ g {[]}    ()

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

-- If ◇ˢ i P (x ∷ xs) holds, then ◇ˢ i P (cycle x xs) also holds.

◇ˢ-cycle← :
  ∀ {a p i} {A : Set a} {P : Size → A → Set p} {x : A} {xs} →
  ◇ˢ i P (x ∷ xs) → ◇ˢ i P (cycle x xs)
◇ˢ-cycle← {i = i} {P = P} {x} {xs} =
  ◇ˢ i P (x ∷ xs)                  ↝⟨ from ⟩
  ◇ˢ i P ((x ∷ xs) ++ cycle x xs)  ↝⟨ ◇ˢ-∼ (transitive-∼ ∷∼∷′ (symmetric-∼ ∷∼∷′)) ⟩□
  ◇ˢ i P (cycle x xs)              □
  where
  from : ∀ {i ys} → ◇ˢ i P ys → ◇ˢ i P (ys ++ cycle x xs)
  from (here p)   = here p
  from (there ps) = there (from ps)

-- If P i x implies P ∞ x for any i and x, then ◇ˢ ∞ P (cycle x xs) is
-- logically equivalent to ◇ˢ ∞ P (x ∷ xs).

◇ˢ-cycle⇔ :
  ∀ {a p} {A : Set a} {P : Size → A → Set p} {x : A} {xs} →
  (∀ {i x} → P i x → P ∞ x) →
  ◇ˢ ∞ P (cycle x xs) ⇔ ◇ˢ ∞ P (x ∷ xs)
◇ˢ-cycle⇔ {P = P} {x} {xs} →∞ = record
  { to   = ◇ˢ ∞ P (cycle x xs)                ↝⟨ ◇ˢ-∼ (transitive-∼ ∷∼∷′ (symmetric-∼ ∷∼∷′)) ⟩
           ◇ˢ ∞ P ((x ∷ xs) ++ cycle x xs)    ↝⟨ to _ ⟩
           ◇ˢ ∞ P (x ∷ xs) ⊎ ◇ˢ ∞ P (x ∷ xs)  ↝⟨ [ id , id ] ⟩□
           ◇ˢ ∞ P (x ∷ xs)                    □
  ; from = ◇ˢ-cycle←
  }
  where
  to :
    ∀ {i} ys → ◇ˢ i P (ys ++ cycle x xs) → ◇ˢ ∞ P ys ⊎ ◇ˢ ∞ P (x ∷ xs)
  to []       (here p)  = inj₂ (here (→∞ p))
  to []       (there p) = case to (force xs) p of
                            [ inj₂ ∘ there , inj₂ ]
  to (y ∷ ys) (here p)  = inj₁ (here (→∞ p))
  to (y ∷ ys) (there p) = ⊎-map there id (to (force ys) p)

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

□ˢ-map′ : ∀ {a b c p q i} {A : Set a} {B : Set b} {C : Set c}
            {P : Size → B → Set p} {Q : Size → C → Set q}
            {f : A → B} {g : A → C} →
          (∀ {i x} → P i (f x) → Q i (g x)) →
          (∀ {xs} → □ˢ i P (map f xs) → □ˢ i Q (map g xs))
□ˢ-map′ g {[]}    []       = []
□ˢ-map′ g {_ ∷ _} (p ∷ ps) = g p ∷ λ { .force → □ˢ-map′ g (force ps) }

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

-- If □ˢ i P (cycle x xs) holds, then □ˢ i P (x ∷ xs) also holds.

□ˢ-cycle→ :
  ∀ {a p i} {A : Set a} {P : Size → A → Set p} {x : A} {xs} →
  □ˢ i P (cycle x xs) → □ˢ i P (x ∷ xs)
□ˢ-cycle→ {i = i} {P = P} {x} {xs} =
  □ˢ i P (cycle x xs)              ↝⟨ (λ { (p ∷ ps) → p ∷ ps }) ⟩
  □ˢ i P ((x ∷ xs) ++ cycle x xs)  ↝⟨ to _ ⟩□
  □ˢ i P (x ∷ xs)                  □
  where
  to : ∀ {i} ys → □ˢ i P (ys ++ cycle x xs) → □ˢ i P ys
  to []       _        = []
  to (y ∷ ys) (p ∷ ps) = p ∷ λ { .force → to (force ys) (force ps) }

-- If P ∞ x implies P i x for any i and x, then □ˢ ∞ P (cycle x xs) is
-- logically equivalent to □ˢ ∞ P (x ∷ xs).

□ˢ-cycle⇔ :
  ∀ {a p} {A : Set a} {P : Size → A → Set p} {x : A} {xs} →
  (∀ {i x} → P ∞ x → P i x) →
  □ˢ ∞ P (cycle x xs) ⇔ □ˢ ∞ P (x ∷ xs)
□ˢ-cycle⇔ {P = P} {x} {xs} ∞→ = record
  { to   = □ˢ-cycle→
  ; from = □ˢ ∞ P (x ∷ xs)                  ↝⟨ (λ hyp → from hyp hyp) ⟩
           □ˢ ∞ P ((x ∷ xs) ++ cycle x xs)  ↝⟨ (λ { (p ∷ ps) → p ∷ ps }) ⟩□
           □ˢ ∞ P (cycle x xs)              □
  }
  where
  from : ∀ {i ys} →
         □ˢ ∞ P (x ∷ xs) → □ˢ i P ys → □ˢ i P (ys ++ cycle x xs)
  from ps       (q ∷ qs) = q ∷ λ { .force → from ps (force qs) }
  from (p ∷ ps) []       = ∞→ p ∷ λ { .force →
                           from (p ∷ ps) (force ps) }
