------------------------------------------------------------------------
-- Colists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

open import Equality

module Colist {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

private
  open module E = Derived-definitions-and-properties eq using (_≡_)

open import Logical-equivalence using (_⇔_)
open import Prelude
open import Prelude.Size

open import Conat eq as Conat using (Conat; zero; suc; force; infinity)
open import Function-universe eq hiding (id; _∘_)
import Nat eq as Nat

private variable
  a p q                                    : Level
  A B                                      : Type a
  P Q                                      : A → Type p
  Pˢ Qˢ                                    : Size → A → Type p
  i                                        : Size
  c m ms n ns x xs xs₁ xs₂ y ys ys₁ ys₂ zs : A
  f g                                      : (x : A) → P x

------------------------------------------------------------------------
-- The type

-- Colists.

mutual

  infixr 5 _∷_

  data Colist (A : Type a) (i : Size) : Type a where
    []  : Colist A i
    _∷_ : A → Colist′ A i → Colist A i

  record Colist′ (A : Type a) (i : Size) : Type a where
    coinductive
    field
      force : {j : Size< i} → Colist A j

open Colist′ public

------------------------------------------------------------------------
-- Some operations

-- A variant of cons.

infixr 5 _∷′_

_∷′_ : A → Colist A i → Colist A i
x ∷′ xs = x ∷ λ { .force → xs }

-- The colist's tail, if any.

tail : Colist A i → Colist′ A i
tail xs@[]    = λ { .force → xs }
tail (x ∷ xs) = xs

-- A map function.

map : (A → B) → Colist A i → Colist B i
map f []       = []
map f (x ∷ xs) = f x ∷ λ { .force → map f (force xs) }

-- The length of a colist.

length : Colist A i → Conat i
length []       = zero
length (n ∷ ns) = suc λ { .force → length (force ns) }

-- The colist replicate n x contains exactly n copies of x (and
-- nothing else).

replicate : Conat i → A → Colist A i
replicate zero    x = []
replicate (suc n) x = x ∷ λ { .force → replicate (force n) x }

-- Repeats the given element indefinitely.

repeat : A → Colist A i
repeat = replicate infinity

-- Appends one colist to another.

infixr 5 _++_

_++_ : Colist A i → Colist A i → Colist A i
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ λ { .force → force xs ++ ys }

-- The colist cycle x xs is an endless cycle of repetitions of the
-- colist x ∷ xs.

cycle : A → Colist′ A i → Colist A i
cycle x xs = x ∷ λ { .force → force xs ++ cycle x xs }

-- "Scan left".

scanl : (A → B → A) → A → Colist B i → Colist A i
scanl c n []       = n ∷ λ { .force → [] }
scanl c n (x ∷ xs) = n ∷ λ { .force → scanl c (c n x) (force xs) }

-- The natural numbers in strictly increasing order.

nats : Colist ℕ i
nats = 0 ∷ λ { .force → map suc nats }

-- The colist nats-from n is the natural numbers greater than or equal
-- to n, in strictly increasing order.

nats-from : ℕ → Colist ℕ i
nats-from n = n ∷ λ { .force → nats-from (suc n) }

-- The list take n xs is the longest possible prefix of xs that
-- contains at most n elements.

take : ℕ → Colist A ∞ → List A
take zero    _        = []
take _       []       = []
take (suc n) (x ∷ xs) = x ∷ take n (force xs)

-- The sum of the successor of every element in the list.

sum-of-successors : Colist (Conat ∞) i → Conat i
sum-of-successors []       = zero
sum-of-successors (n ∷ ns) = suc λ { .force →
  n Conat.+ sum-of-successors (ns .force) }

------------------------------------------------------------------------
-- Bisimilarity

-- [ ∞ ] xs ∼ ys means that xs and ys are "equal".

mutual

  infix 4 [_]_∼_ [_]_∼′_

  data [_]_∼_ {A : Type a} (i : Size) :
         Colist A ∞ → Colist A ∞ → Type a where
    []  : [ i ] [] ∼ []
    _∷_ : x ≡ y → [ i ] force xs ∼′ force ys → [ i ] x ∷ xs ∼ y ∷ ys

  record [_]_∼′_ {A : Type a} (i : Size) (xs ys : Colist A ∞) :
           Type a where
    coinductive
    field
      force : {j : Size< i} → [ j ] xs ∼ ys

open [_]_∼′_ public

-- Bisimilarity is an equivalence relation.

reflexive-∼ : (xs : Colist A ∞) → [ i ] xs ∼ xs
reflexive-∼ []       = []
reflexive-∼ (x ∷ xs) =
  E.refl _ ∷ λ { .force → reflexive-∼ (force xs) }

symmetric-∼ : [ i ] xs ∼ ys → [ i ] ys ∼ xs
symmetric-∼ []        = []
symmetric-∼ (p₁ ∷ p₂) =
  E.sym p₁ ∷ λ { .force → symmetric-∼ (force p₂) }

transitive-∼ : [ i ] xs ∼ ys → [ i ] ys ∼ zs → [ i ] xs ∼ zs
transitive-∼ []        []        = []
transitive-∼ (p₁ ∷ p₂) (q₁ ∷ q₂) =
  E.trans p₁ q₁ ∷ λ { .force → transitive-∼ (force p₂) (force q₂) }

-- Equational reasoning combinators.

infix  -1 _∎
infixr -2 step-∼ step-≡ _∼⟨⟩_

_∎ : (xs : Colist A ∞) → [ i ] xs ∼ xs
_∎ = reflexive-∼

step-∼ : ∀ xs → [ i ] ys ∼ zs → [ i ] xs ∼ ys → [ i ] xs ∼ zs
step-∼ _ ys∼zs xs∼ys = transitive-∼ xs∼ys ys∼zs

syntax step-∼ xs ys∼zs xs∼ys = xs ∼⟨ xs∼ys ⟩ ys∼zs

step-≡ : ∀ xs → [ i ] ys ∼ zs → xs ≡ ys → [ i ] xs ∼ zs
step-≡ {i = i} _ ys∼zs xs≡ys = E.subst ([ i ]_∼ _) (E.sym xs≡ys) ys∼zs

syntax step-≡ xs ys∼zs xs≡ys = xs ≡⟨ xs≡ys ⟩ ys∼zs

_∼⟨⟩_ : ∀ xs → [ i ] xs ∼ ys → [ i ] xs ∼ ys
_ ∼⟨⟩ xs∼ys = xs∼ys

-- A property relating Colist._∷_ and _∷′_.

∷∼∷′ : [ i ] x ∷ xs ∼ x ∷′ force xs
∷∼∷′ = E.refl _ ∷ λ { .force → reflexive-∼ _ }

-- Functor laws.

map-id : (xs : Colist A ∞) → [ i ] map id xs ∼ xs
map-id []       = []
map-id (_ ∷ xs) = E.refl _ ∷ λ { .force → map-id (force xs) }

map-∘ :
  (xs : Colist A ∞) →
  [ i ] map (f ∘ g) xs ∼ map f (map g xs)
map-∘ []       = []
map-∘ (_ ∷ xs) = E.refl _ ∷ λ { .force → map-∘ (force xs) }

-- If two non-empty colists are bisimilar, then their heads are
-- bisimilar.

head-cong : [ i ] x ∷ xs ∼ y ∷ ys → x ≡ y
head-cong (p ∷ _) = p

-- Some preservation lemmas.

tail-cong : [ i ] xs ∼ ys → [ i ] force (tail xs) ∼′ force (tail ys)
tail-cong []       = λ { .force → [] }
tail-cong (_ ∷ ps) = ps

map-cong :
  (∀ x → f x ≡ g x) →
  [ i ] xs ∼ ys → [ i ] map f xs ∼ map g ys
map-cong                 f≡g []                           = []
map-cong {f = f} {g = g} f≡g (_∷_ {x = x} {y = y} x≡y ps) =
  (f x  E.≡⟨ E.cong f x≡y ⟩
   f y  E.≡⟨ f≡g y ⟩∎
   g y  ∎) ∷ λ { .force →
  map-cong f≡g (force ps) }

length-cong : [ i ] xs ∼ ys → Conat.[ i ] length xs ∼ length ys
length-cong []       = zero
length-cong (_ ∷ ps) = suc λ { .force → length-cong (force ps) }

replicate-cong : Conat.[ i ] m ∼ n → [ i ] replicate m x ∼ replicate n x
replicate-cong zero    = []
replicate-cong (suc p) =
  E.refl _ ∷ λ { .force → replicate-cong (force p) }

infixr 5 _++-cong_

_++-cong_ :
  [ i ] xs₁ ∼ ys₁ → [ i ] xs₂ ∼ ys₂ → [ i ] xs₁ ++ xs₂ ∼ ys₁ ++ ys₂
[]       ++-cong qs = qs
(p ∷ ps) ++-cong qs = p ∷ λ { .force → force ps ++-cong qs }

cycle-cong : [ i ] force xs ∼′ force ys → [ i ] cycle x xs ∼ cycle x ys
cycle-cong p = E.refl _ ∷ λ { .force → force p ++-cong cycle-cong p }

scanl-cong : [ i ] xs ∼ ys → [ i ] scanl c n xs ∼ scanl c n ys
scanl-cong [] = E.refl _ ∷ λ { .force → [] }

scanl-cong {c = c} {n = n}
           (_∷_ {x = x} {y = y} {xs = xs} {ys = ys} x≡y ps) =
  E.refl n ∷ λ { .force →
    scanl c (c n x) (force xs)  ≡⟨ E.cong (λ x → scanl _ (c _ x) _) x≡y ⟩
    scanl c (c n y) (force xs)  ∼⟨ scanl-cong (force ps) ⟩
    scanl c (c n y) (force ys)  ∎ }

take-cong : ∀ n → [ ∞ ] xs ∼ ys → take n xs ≡ take n ys
take-cong n       []       = E.refl _
take-cong zero    (p ∷ ps) = E.refl _
take-cong (suc n) (p ∷ ps) = E.cong₂ _∷_ p (take-cong n (force ps))

sum-of-successors-cong :
  [ i ] ms ∼ ns →
  Conat.[ i ] sum-of-successors ms ∼ sum-of-successors ns
sum-of-successors-cong []       = zero
sum-of-successors-cong (p ∷ ps) = suc λ { .force →
  E.subst (Conat.[ _ ] _ ∼_) p (Conat.reflexive-∼ _)
    Conat.+-cong
  sum-of-successors-cong (ps .force) }

-- The length of replicate n x is bisimilar to n.

length-replicate : ∀ n → Conat.[ i ] length (replicate n x) ∼ n
length-replicate zero    = zero
length-replicate (suc n) =
  suc λ { .force → length-replicate (force n) }

-- A lemma relating nats and nats-from n.

map-+-nats∼nats-from :
  ∀ n → [ i ] map (n +_) nats ∼ nats-from n
map-+-nats∼nats-from n = Nat.+-right-identity ∷ λ { .force →
  map (n +_) (map suc nats)  ∼⟨ symmetric-∼ (map-∘ _) ⟩
  map ((n +_) ∘ suc) nats    ∼⟨ map-cong (λ _ → E.sym (Nat.suc+≡+suc _)) (_ ∎) ⟩
  map (suc n +_) nats        ∼⟨ map-+-nats∼nats-from (suc n) ⟩
  nats-from (suc n)          ∎ }

-- The colist nats is bisimilar to nats-from 0.

nats∼nats-from-0 : [ i ] nats ∼ nats-from 0
nats∼nats-from-0 =
  nats             ∼⟨ symmetric-∼ (map-id _) ⟩
  map id nats      ∼⟨⟩
  map (0 +_) nats  ∼⟨ map-+-nats∼nats-from _ ⟩
  nats-from 0      ∎

------------------------------------------------------------------------
-- The ◇ predicate

-- ◇ ∞ P xs means that P holds for some element in xs.

data ◇ {A : Type a} (i : Size)
       (P : A → Type p) : Colist A ∞ → Type (a ⊔ p) where
  here  : P x → ◇ i P (x ∷ xs)
  there : {j : Size< i} → ◇ j P (force xs) → ◇ i P (x ∷ xs)

-- ◇ respects bisimilarity.

◇-∼ : [ ∞ ] xs ∼ ys → ◇ i P xs → ◇ i P ys
◇-∼ (x≡y ∷ _) (here p)  = here (E.subst _ x≡y p)
◇-∼ (_   ∷ b) (there p) = there (◇-∼ (force b) p)

-- A map function for ◇.

◇-map :
  (∀ {x} → P x → Q x) →
  (∀ {xs} → ◇ i P xs → ◇ i Q xs)
◇-map f (here p)  = here (f p)
◇-map f (there p) = there (◇-map f p)

-- A variant of ◇-map.

◇-map′ :
  (∀ {x} → P (f x) → Q (g x)) →
  (∀ {xs} → ◇ i P (map f xs) → ◇ i Q (map g xs))
◇-map′ g {xs = _ ∷ _} (here p)  = here (g p)
◇-map′ g {xs = _ ∷ _} (there p) = there (◇-map′ g p)
◇-map′ g {xs = []}    ()

-- If a predicate holds for some element in a colist, then it holds
-- for some value.

◇-witness : ◇ i P xs → ∃ P
◇-witness (here p)  = _ , p
◇-witness (there p) = ◇-witness p

-- If const A holds for some element, then A holds.

◇-const : ◇ i (const A) xs → A
◇-const = proj₂ ∘ ◇-witness

-- Colist membership.

infix 4 [_]_∈_

[_]_∈_ : {A : Type a} → Size → A → Colist A ∞ → Type a
[ i ] x ∈ xs = ◇ i (x ≡_) xs

-- A generalisation of "◇ ∞ P xs holds iff P holds for some element in
-- xs".

◇⇔∈× : ◇ i P xs ⇔ ∃ λ x → [ i ] x ∈ xs × P x
◇⇔∈× {P = P} = record { to = to; from = from }
  where
  to : ◇ i P xs → ∃ λ x → [ i ] x ∈ xs × P x
  to (here p)  = _ , here (E.refl _) , p
  to (there p) = Σ-map id (Σ-map there id) (to p)

  from : (∃ λ x → [ i ] x ∈ xs × P x) → ◇ i P xs
  from (x , here eq   , p) = here (E.subst P eq p)
  from (x , there x∈xs , p) = there (from (x , x∈xs , p))

-- If P holds for some element in replicate (suc n) x, then it also
-- holds for x, and vice versa.

◇-replicate-suc⇔ : ◇ i P (replicate (suc n) x) ⇔ P x
◇-replicate-suc⇔ {P = P} {x = x} = record
  { to   = to _
  ; from = here
  }
  where
  to : ∀ n → ◇ i P (replicate n x) → P x
  to zero    ()
  to (suc n) (here p)  = p
  to (suc n) (there p) = to (force n) p

-- If P holds for some element in cycle x xs, then it also holds for
-- some element in x ∷ xs, and vice versa.

◇-cycle⇔ : ◇ i P (cycle x xs) ⇔ ◇ i P (x ∷ xs)
◇-cycle⇔ {i = i} {P = P} {x = x} {xs = xs} = record
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

  from : ∀ {i} → ◇ i P ys → ◇ i P (ys ++ cycle x xs)
  from (here p)   = here p
  from (there ps) = there (from ps)

------------------------------------------------------------------------
-- The □ predicate

-- □ ∞ P xs means that P holds for every element in xs.

mutual

  data □ {A : Type a} (i : Size)
         (P : A → Type p) : Colist A ∞ → Type (a ⊔ p) where
    []  : □ i P []
    _∷_ : P x → □′ i P (force xs) → □ i P (x ∷ xs)

  record □′ {A : Type a} (i : Size)
            (P : A → Type p) (xs : Colist A ∞) : Type (a ⊔ p) where
    coinductive
    field
      force : {j : Size< i} → □ j P xs

open □′ public

-- Some projections.

□-head : □ i P (x ∷ xs) → P x
□-head (p ∷ _) = p

□-tail : {j : Size< i} → □ i P (x ∷ xs) → □ j P (force xs)
□-tail (_ ∷ ps) = force ps

-- □ respects bisimilarity.

□-∼ : [ i ] xs ∼ ys → □ i P xs → □ i P ys
□-∼ []       _        = []
□-∼ (eq ∷ b) (p ∷ ps) =
  E.subst _ eq p ∷ λ { .force →
  □-∼ (force b) (force ps) }

-- A generalisation of "□ ∞ P xs holds iff P is true for every element
-- in xs".

□⇔∈→ : □ i P xs ⇔ (∀ x → [ i ] x ∈ xs → P x)
□⇔∈→ {P = P} = record { to = to; from = from _ }
  where
  to : □ i P xs → (∀ x → [ i ] x ∈ xs → P x)
  to (p ∷ ps) x (here eq)    = E.subst P (E.sym eq) p
  to (p ∷ ps) x (there x∈xs) = to (force ps) x x∈xs

  from : ∀ xs → (∀ x → [ i ] x ∈ xs → P x) → □ i P xs
  from []       f = []
  from (x ∷ xs) f =
    f x (here (E.refl _)) ∷ λ { .force →
    from (force xs) (λ x → f x ∘ there) }

-- If P is universally true, then □ i P is also universally true.

□-replicate : (∀ x → P x) → (∀ xs → □ i P xs)
□-replicate f _ = _⇔_.from □⇔∈→ (λ x _ → f x)

-- Something resembling applicative functor application for □.

infixl 4 _□-⊛_

_□-⊛_ : □ i (λ x → P x → Q x) xs → □ i P xs → □ i Q xs
[]       □-⊛ _        = []
(f ∷ fs) □-⊛ (p ∷ ps) = f p ∷ λ { .force → force fs □-⊛ force ps }

-- A map function for □.

□-map :
  (∀ {x} → P x → Q x) →
  (∀ {xs} → □ i P xs → □ i Q xs)
□-map f ps = □-replicate (λ _ → f) _ □-⊛ ps

-- A variant of □-map.

□-map′ :
  (∀ {x} → P (f x) → Q (g x)) →
  (∀ {xs} → □ i P (map f xs) → □ i Q (map g xs))
□-map′ g {xs = []}    []       = []
□-map′ g {xs = _ ∷ _} (p ∷ ps) =
  g p ∷ λ { .force → □-map′ g (force ps) }

-- Something resembling applicative functor application for □ and ◇.

infixl 4 _□◇-⊛_

_□◇-⊛_ : □ i (λ x → P x → Q x) xs → ◇ i P xs → ◇ i Q xs
(f ∷ _)  □◇-⊛ (here p)  = here (f p)
(_ ∷ fs) □◇-⊛ (there p) = there (force fs □◇-⊛ p)

-- A combination of some of the combinators above.

□◇-witness : □ i P xs → ◇ i Q xs → ∃ λ x → P x × Q x
□◇-witness p q = ◇-witness (□-map _,_ p □◇-⊛ q)

-- If P holds for every element in replicate (suc n) x, then it also holds
-- for x, and vice versa.

□-replicate-suc⇔ : □ i P (replicate (suc n) x) ⇔ P x
□-replicate-suc⇔ {P = P} {x = x} = record
  { to   = □-head
  ; from = from _
  }
  where
  from : ∀ n → P x → □ i P (replicate n x)
  from zero    p = []
  from (suc n) p = p ∷ λ { .force → from (force n) p }

-- If P holds for every element in cycle x xs, then it also holds for
-- every element in x ∷ xs, and vice versa.

□-cycle⇔ : □ i P (cycle x xs) ⇔ □ i P (x ∷ xs)
□-cycle⇔ {i = i} {P = P} {x = x} {xs = xs} = record
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

  from : ∀ {i} → □ i P (x ∷ xs) → □ i P ys → □ i P (ys ++ cycle x xs)
  from ps       (q ∷ qs) = q ∷ λ { .force → from ps (force qs) }
  from (p ∷ ps) []       = p ∷ λ { .force → from (p ∷ ps) (force ps) }

------------------------------------------------------------------------
-- A variant of ◇ with a sized predicate

-- ◇ˢ ∞ Pˢ xs means that (some instance of) Pˢ holds for some element
-- in xs.

data ◇ˢ {A : Type a} (i : Size)
        (Pˢ : Size → A → Type p) : Colist A ∞ → Type (a ⊔ p) where
  here  : Pˢ i x → ◇ˢ i Pˢ (x ∷ xs)
  there : {j : Size< i} → ◇ˢ j Pˢ (force xs) → ◇ˢ i Pˢ (x ∷ xs)

-- ◇ˢ respects bisimilarity.

◇ˢ-∼ : [ ∞ ] xs ∼ ys → ◇ˢ i Pˢ xs → ◇ˢ i Pˢ ys
◇ˢ-∼ (eq ∷ _) (here p)  = here (E.subst _ eq p)
◇ˢ-∼ (_  ∷ b) (there p) = there (◇ˢ-∼ (force b) p)

-- If Pˢ is upwards closed, then flip ◇ˢ Pˢ is upwards closed.

◇ˢ-upwards-closed :
  (∀ {i} {j : Size< i} {x} → Pˢ j x → Pˢ i x) →
  (∀ {i} {j : Size< i} {xs} → ◇ˢ j Pˢ xs → ◇ˢ i Pˢ xs)
◇ˢ-upwards-closed Pˢ-closed (here p)  = here (Pˢ-closed p)
◇ˢ-upwards-closed Pˢ-closed (there p) =
  there (◇ˢ-upwards-closed Pˢ-closed p)

-- A variant of the previous lemma.

◇ˢ-upwards-closed-∞ :
  (∀ {i x} → Pˢ i x → Pˢ ∞ x) →
  (∀ {i xs} → ◇ˢ i Pˢ xs → ◇ˢ ∞ Pˢ xs)
◇ˢ-upwards-closed-∞ Pˢ-closed-∞ (here p)  = here (Pˢ-closed-∞ p)
◇ˢ-upwards-closed-∞ Pˢ-closed-∞ (there p) =
  there (◇ˢ-upwards-closed-∞ Pˢ-closed-∞ p)

-- A map function for ◇ˢ.

◇ˢ-map :
  (∀ {i x} → Pˢ i x → Qˢ i x) →
  (∀ {xs} → ◇ˢ i Pˢ xs → ◇ˢ i Qˢ xs)
◇ˢ-map f (here p)  = here (f p)
◇ˢ-map f (there p) = there (◇ˢ-map f p)

-- A variant of ◇ˢ-map.

◇ˢ-map′ :
  (∀ {i x} → Pˢ i (f x) → Qˢ i (g x)) →
  (∀ {xs} → ◇ˢ i Pˢ (map f xs) → ◇ˢ i Qˢ (map g xs))
◇ˢ-map′ g {xs = _ ∷ _} (here p)  = here (g p)
◇ˢ-map′ g {xs = _ ∷ _} (there p) = there (◇ˢ-map′ g p)
◇ˢ-map′ g {xs = []}    ()

-- If a predicate holds for some element in a colist, then it holds
-- for some value (assuming that Pˢ is upwards closed).

◇ˢ-witness :
  (∀ {i} {j : Size< i} {x} → Pˢ j x → Pˢ i x) →
  ◇ˢ i Pˢ xs → ∃ (Pˢ i)
◇ˢ-witness closed (here p)  = _ , p
◇ˢ-witness closed (there p) = Σ-map id closed (◇ˢ-witness closed p)

-- If Pˢ ∞ holds for some element in xs, then ◇ˢ ∞ Pˢ xs holds.

∈×∞→◇ˢ : [ ∞ ] x ∈ xs → Pˢ ∞ x → ◇ˢ ∞ Pˢ xs
∈×∞→◇ˢ (here eq)    p = here (E.subst _ eq p)
∈×∞→◇ˢ (there x∈xs) p = there (∈×∞→◇ˢ x∈xs p)

-- If Pˢ i x implies Pˢ ∞ x for any i and x, then ◇ˢ ∞ Pˢ xs holds iff
-- Pˢ ∞ holds for some element in xs.

◇ˢ⇔∈× :
  (∀ {i x} → Pˢ i x → Pˢ ∞ x) →
  ◇ˢ ∞ Pˢ xs ⇔ (∃ λ x → [ ∞ ] x ∈ xs × Pˢ ∞ x)
◇ˢ⇔∈× {Pˢ = Pˢ} →∞ = record
  { to   = to
  ; from = λ { (_ , x∈xs , p) → ∈×∞→◇ˢ x∈xs p }
  }
  where
  to : ◇ˢ i Pˢ xs → ∃ λ x → [ ∞ ] x ∈ xs × Pˢ ∞ x
  to (here p)  = _ , here (E.refl _) , →∞ p
  to (there p) = Σ-map id (Σ-map there id) (to p)

-- Sized variants of the previous lemma.

◇ˢ→∈× :
  (∀ {i} {j : Size< i} {x} → Pˢ j x → Pˢ i x) →
  ◇ˢ i Pˢ xs → ∃ λ x → [ i ] x ∈ xs × Pˢ i x
◇ˢ→∈× closed (here p)  = _ , here (E.refl _) , p
◇ˢ→∈× closed (there p) = Σ-map id (Σ-map there closed) (◇ˢ→∈× closed p)

∈×→◇ˢ :
  (∀ {i} {j : Size< i} {x} → Pˢ i x → Pˢ j x) →
  [ i ] x ∈ xs → Pˢ i x → ◇ˢ i Pˢ xs
∈×→◇ˢ closed (here eq)    p = here (E.subst _ eq p)
∈×→◇ˢ closed (there x∈xs) p = there (∈×→◇ˢ closed x∈xs (closed p))

-- ◇ ∞ (Pˢ ∞) is "contained in" ◇ˢ ∞ Pˢ.

◇∞→◇ˢ∞ : ◇ ∞ (Pˢ ∞) xs → ◇ˢ ∞ Pˢ xs
◇∞→◇ˢ∞ {Pˢ = Pˢ} {xs = xs} =
  ◇ ∞ (Pˢ ∞) xs                    ↝⟨ _⇔_.to ◇⇔∈× ⟩
  (∃ λ x → [ ∞ ] x ∈ xs × Pˢ ∞ x)  ↝⟨ (λ { (_ , x∈xs , p) → ∈×∞→◇ˢ x∈xs p }) ⟩□
  ◇ˢ ∞ Pˢ xs                       □

-- If Pˢ i x implies Pˢ ∞ x for any i and x, then ◇ˢ ∞ Pˢ is pointwise
-- logically equivalent to ◇ ∞ (Pˢ ∞).

◇ˢ∞⇔◇∞ :
  (∀ {i x} → Pˢ i x → Pˢ ∞ x) →
  ◇ˢ ∞ Pˢ xs ⇔ ◇ ∞ (Pˢ ∞) xs
◇ˢ∞⇔◇∞ {Pˢ = Pˢ} {xs = xs} →∞ =
  ◇ˢ ∞ Pˢ xs                       ↝⟨ ◇ˢ⇔∈× →∞ ⟩
  (∃ λ x → [ ∞ ] x ∈ xs × Pˢ ∞ x)  ↝⟨ inverse ◇⇔∈× ⟩□
  ◇ ∞ (Pˢ ∞) xs                    □

-- ◇ˢ i (const P) is pointwise logically equivalent to ◇ i P.

◇ˢ⇔◇ : ◇ˢ i (λ _ → P) xs ⇔ ◇ i P xs
◇ˢ⇔◇ {P = P} = record { to = to; from = from }
  where
  to : ◇ˢ i (λ _ → P) xs → ◇ i P xs
  to (here p)  = here p
  to (there p) = there (to p)

  from : ◇ i P xs → ◇ˢ i (λ _ → P) xs
  from (here p)  = here p
  from (there p) = there (from p)

-- If ◇ˢ i Pˢ (x ∷ xs) holds, then ◇ˢ i Pˢ (cycle x xs) also holds.

◇ˢ-cycle← : ◇ˢ i Pˢ (x ∷ xs) → ◇ˢ i Pˢ (cycle x xs)
◇ˢ-cycle← {i = i} {Pˢ = Pˢ} {x = x} {xs = xs} =
  ◇ˢ i Pˢ (x ∷ xs)                  ↝⟨ from ⟩
  ◇ˢ i Pˢ ((x ∷ xs) ++ cycle x xs)  ↝⟨ ◇ˢ-∼ (transitive-∼ ∷∼∷′ (symmetric-∼ ∷∼∷′)) ⟩□
  ◇ˢ i Pˢ (cycle x xs)              □
  where
  from : ∀ {i} → ◇ˢ i Pˢ ys → ◇ˢ i Pˢ (ys ++ cycle x xs)
  from (here p)   = here p
  from (there ps) = there (from ps)

-- If Pˢ i x implies Pˢ ∞ x for any i and x, then ◇ˢ ∞ Pˢ (cycle x xs)
-- is logically equivalent to ◇ˢ ∞ Pˢ (x ∷ xs).

◇ˢ-cycle⇔ :
  (∀ {i x} → Pˢ i x → Pˢ ∞ x) →
  ◇ˢ ∞ Pˢ (cycle x xs) ⇔ ◇ˢ ∞ Pˢ (x ∷ xs)
◇ˢ-cycle⇔ {Pˢ = Pˢ} {x = x} {xs = xs} →∞ = record
  { to   = ◇ˢ ∞ Pˢ (cycle x xs)                 ↝⟨ ◇ˢ-∼ (transitive-∼ ∷∼∷′ (symmetric-∼ ∷∼∷′)) ⟩
           ◇ˢ ∞ Pˢ ((x ∷ xs) ++ cycle x xs)     ↝⟨ to _ ⟩
           ◇ˢ ∞ Pˢ (x ∷ xs) ⊎ ◇ˢ ∞ Pˢ (x ∷ xs)  ↝⟨ [ id , id ] ⟩□
           ◇ˢ ∞ Pˢ (x ∷ xs)                     □
  ; from = ◇ˢ-cycle←
  }
  where
  to : ∀ ys → ◇ˢ i Pˢ (ys ++ cycle x xs) → ◇ˢ ∞ Pˢ ys ⊎ ◇ˢ ∞ Pˢ (x ∷ xs)
  to []       (here p)  = inj₂ (here (→∞ p))
  to []       (there p) = case to (force xs) p of
                            [ inj₂ ∘ there , inj₂ ]
  to (y ∷ ys) (here p)  = inj₁ (here (→∞ p))
  to (y ∷ ys) (there p) = ⊎-map there id (to (force ys) p)

------------------------------------------------------------------------
-- A variant of □ with a sized predicate

-- □ˢ ∞ Pˢ xs means that (some instance of) Pˢ holds for every element
-- in xs.

mutual

  data □ˢ {A : Type a} (i : Size)
          (Pˢ : Size → A → Type p) : Colist A ∞ → Type (a ⊔ p) where
    []  : □ˢ i Pˢ []
    _∷_ : Pˢ i x → □ˢ′ i Pˢ (force xs) → □ˢ i Pˢ (x ∷ xs)

  record □ˢ′ {A : Type a} (i : Size)
             (Pˢ : Size → A → Type p) (xs : Colist A ∞) :
             Type (a ⊔ p) where
    coinductive
    field
      force : {j : Size< i} → □ˢ j Pˢ xs

open □ˢ′ public

-- Some projections.

□ˢ-head : □ˢ i Pˢ (x ∷ xs) → Pˢ i x
□ˢ-head (p ∷ _) = p

□ˢ-tail :
  {j : Size< i} →
  □ˢ i Pˢ (x ∷ xs) → □ˢ j Pˢ (force xs)
□ˢ-tail (_ ∷ ps) = force ps

-- □ˢ respects bisimilarity.

□ˢ-∼ : [ i ] xs ∼ ys → □ˢ i Pˢ xs → □ˢ i Pˢ ys
□ˢ-∼ []       _        = []
□ˢ-∼ (eq ∷ b) (p ∷ ps) =
  E.subst _ eq p ∷ λ { .force →
  □ˢ-∼ (force b) (force ps) }

-- If Pˢ is downwards closed, then flip □ˢ Pˢ is downwards closed.

□ˢ-downwards-closed :
  (∀ {i} {j : Size< i} {x} → Pˢ i x → Pˢ j x) →
  (∀ {i} {j : Size< i} {xs} → □ˢ i Pˢ xs → □ˢ j Pˢ xs)
□ˢ-downwards-closed Pˢ-closed []       = []
□ˢ-downwards-closed Pˢ-closed (p ∷ ps) =
  Pˢ-closed p ∷ λ { .force → □ˢ-downwards-closed Pˢ-closed (force ps) }

-- A variant of the previous lemma.

□ˢ-downwards-closed-∞ :
  (∀ {i x} → Pˢ ∞ x → Pˢ i x) →
  (∀ {i xs} → □ˢ ∞ Pˢ xs → □ˢ i Pˢ xs)
□ˢ-downwards-closed-∞ Pˢ-closed-∞ []       = []
□ˢ-downwards-closed-∞ Pˢ-closed-∞ (p ∷ ps) =
  Pˢ-closed-∞ p ∷ λ { .force →
  □ˢ-downwards-closed-∞ Pˢ-closed-∞ (force ps) }

-- If □ˢ ∞ Pˢ xs holds, then Pˢ ∞ holds for every element in xs.

□ˢ∞∈→ : □ˢ ∞ Pˢ xs → [ ∞ ] x ∈ xs → Pˢ ∞ x
□ˢ∞∈→ (p ∷ ps) (here eq)    = E.subst _ (E.sym eq) p
□ˢ∞∈→ (p ∷ ps) (there x∈xs) = □ˢ∞∈→ (force ps) x∈xs

-- If Pˢ ∞ x implies Pˢ i x for any i and x, then □ˢ ∞ Pˢ xs holds iff
-- Pˢ ∞ holds for every element in xs.

□ˢ⇔∈→ :
  (∀ {i x} → Pˢ ∞ x → Pˢ i x) →
  □ˢ ∞ Pˢ xs ⇔ (∀ x → [ ∞ ] x ∈ xs → Pˢ ∞ x)
□ˢ⇔∈→ {Pˢ = Pˢ} ∞→ = record { to = λ p _ → □ˢ∞∈→ p; from = from _ }
  where
  from : ∀ xs → (∀ x → [ ∞ ] x ∈ xs → Pˢ ∞ x) → □ˢ i Pˢ xs
  from []       f = []
  from (x ∷ xs) f =
    ∞→ (f x (here (E.refl _))) ∷ λ { .force →
    from (force xs) (λ x → f x ∘ there) }

-- Sized variants of the previous lemma.

□ˢ∈→ :
  (∀ {i} {j : Size< i} {x} → Pˢ j x → Pˢ i x) →
  ∀ {i x xs} → □ˢ i Pˢ xs → [ i ] x ∈ xs → Pˢ i x
□ˢ∈→ closed (p ∷ ps) (here eq)    = E.subst _ (E.sym eq) p
□ˢ∈→ closed (p ∷ ps) (there x∈xs) = closed (□ˢ∈→ closed (force ps) x∈xs)

∈→→□ˢ :
  (∀ {i} {j : Size< i} {x} → Pˢ i x → Pˢ j x) →
  ∀ {i} xs → (∀ x → [ i ] x ∈ xs → Pˢ i x) → □ˢ i Pˢ xs
∈→→□ˢ closed []       f = []
∈→→□ˢ closed (x ∷ xs) f =
  f x (here (E.refl _)) ∷ λ { .force →
  ∈→→□ˢ closed (force xs) (λ x → closed ∘ f x ∘ there) }

-- □ˢ ∞ Pˢ is "contained in" □ ∞ (Pˢ ∞).

□ˢ∞→□∞ : □ˢ ∞ Pˢ xs → □ ∞ (Pˢ ∞) xs
□ˢ∞→□∞ {Pˢ = Pˢ} {xs = xs} =
  □ˢ ∞ Pˢ xs                     ↝⟨ (λ p _ → □ˢ∞∈→ p) ⟩
  (∀ x → [ ∞ ] x ∈ xs → Pˢ ∞ x)  ↝⟨ _⇔_.from □⇔∈→ ⟩□
  □ ∞ (Pˢ ∞) xs                  □

-- If Pˢ ∞ x implies Pˢ i x for any i and x, then □ˢ ∞ Pˢ is pointwise
-- logically equivalent to □ ∞ (Pˢ ∞).

□ˢ∞⇔□∞ :
  (∀ {i x} → Pˢ ∞ x → Pˢ i x) →
  □ˢ ∞ Pˢ xs ⇔ □ ∞ (Pˢ ∞) xs
□ˢ∞⇔□∞ {Pˢ = Pˢ} {xs = xs} ∞→ =
  □ˢ ∞ Pˢ xs                     ↝⟨ □ˢ⇔∈→ ∞→ ⟩
  (∀ x → [ ∞ ] x ∈ xs → Pˢ ∞ x)  ↝⟨ inverse □⇔∈→ ⟩□
  □ ∞ (Pˢ ∞) xs                  □

-- □ˢ i (const P) is pointwise logically equivalent to □ i P.

□ˢ⇔□ : □ˢ i (λ _ → P) xs ⇔ □ i P xs
□ˢ⇔□ {P = P} = record { to = to; from = from }
  where
  to : □ˢ i (λ _ → P) xs → □ i P xs
  to []       = []
  to (p ∷ ps) = p ∷ λ { .force → to (force ps) }

  from : □ i P xs → □ˢ i (λ _ → P) xs
  from []       = []
  from (p ∷ ps) = p ∷ λ { .force → from (force ps) }

-- If Pˢ is universally true, then □ˢ i Pˢ is also universally true.

□ˢ-replicate : (∀ {i} x → Pˢ i x) → (∀ xs → □ˢ i Pˢ xs)
□ˢ-replicate f []       = []
□ˢ-replicate f (x ∷ xs) = f x ∷ λ { .force → □ˢ-replicate f (force xs) }

-- Something resembling applicative functor application for □ˢ.

infixl 4 _□ˢ-⊛_

_□ˢ-⊛_ : □ˢ i (λ j x → Pˢ j x → Qˢ j x) xs → □ˢ i Pˢ xs → □ˢ i Qˢ xs
[]       □ˢ-⊛ _        = []
(f ∷ fs) □ˢ-⊛ (p ∷ ps) = f p ∷ λ { .force → force fs □ˢ-⊛ force ps }

-- A map function for □ˢ.

□ˢ-map :
  (∀ {i x} → Pˢ i x → Qˢ i x) →
  (∀ {xs} → □ˢ i Pˢ xs → □ˢ i Qˢ xs)
□ˢ-map f ps = □ˢ-replicate (λ _ → f) _ □ˢ-⊛ ps

-- A variant of □ˢ-map.

□ˢ-map′ :
  (∀ {i x} → Pˢ i (f x) → Qˢ i (g x)) →
  (∀ {xs} → □ˢ i Pˢ (map f xs) → □ˢ i Qˢ (map g xs))
□ˢ-map′ g {([])}  []       = []
□ˢ-map′ g {_ ∷ _} (p ∷ ps) = g p ∷ λ { .force → □ˢ-map′ g (force ps) }

-- Something resembling applicative functor application for □ˢ and ◇ˢ.

infixl 4 _□ˢ◇ˢ-⊛_

_□ˢ◇ˢ-⊛_ : □ˢ i (λ j x → Pˢ j x → Qˢ j x) xs → ◇ˢ i Pˢ xs → ◇ˢ i Qˢ xs
(f ∷ _)  □ˢ◇ˢ-⊛ (here p)  = here (f p)
(_ ∷ fs) □ˢ◇ˢ-⊛ (there p) = there (force fs □ˢ◇ˢ-⊛ p)

-- A combination of some of the combinators above.

□ˢ◇ˢ-witness :
  (∀ {i} {j : Size< i} {x} → Pˢ j x → Pˢ i x) →
  (∀ {i} {j : Size< i} {x} → Qˢ j x → Qˢ i x) →
  □ˢ i Pˢ xs → ◇ˢ i Qˢ xs → ∃ λ x → Pˢ i x × Qˢ i x
□ˢ◇ˢ-witness Pˢ-closed Qˢ-closed p q =
  ◇ˢ-witness (λ { {_} {_} → Σ-map Pˢ-closed Qˢ-closed })
             (□ˢ-map _,_ p □ˢ◇ˢ-⊛ q)

-- If □ˢ i Pˢ (cycle x xs) holds, then □ˢ i Pˢ (x ∷ xs) also holds.

□ˢ-cycle→ : □ˢ i Pˢ (cycle x xs) → □ˢ i Pˢ (x ∷ xs)
□ˢ-cycle→ {i = i} {Pˢ = Pˢ} {x = x} {xs = xs} =
  □ˢ i Pˢ (cycle x xs)              ↝⟨ (λ { (p ∷ ps) → p ∷ ps }) ⟩
  □ˢ i Pˢ ((x ∷ xs) ++ cycle x xs)  ↝⟨ to _ ⟩□
  □ˢ i Pˢ (x ∷ xs)                  □
  where
  to : ∀ {i} ys → □ˢ i Pˢ (ys ++ cycle x xs) → □ˢ i Pˢ ys
  to []       _        = []
  to (y ∷ ys) (p ∷ ps) = p ∷ λ { .force → to (force ys) (force ps) }

-- If Pˢ ∞ x implies Pˢ i x for any i and x, then □ˢ ∞ Pˢ (cycle x xs)
-- is logically equivalent to □ˢ ∞ Pˢ (x ∷ xs).

□ˢ-cycle⇔ :
  (∀ {i x} → Pˢ ∞ x → Pˢ i x) →
  □ˢ ∞ Pˢ (cycle x xs) ⇔ □ˢ ∞ Pˢ (x ∷ xs)
□ˢ-cycle⇔ {Pˢ = Pˢ} {x = x} {xs = xs} ∞→ = record
  { to   = □ˢ-cycle→
  ; from = □ˢ ∞ Pˢ (x ∷ xs)                  ↝⟨ (λ hyp → from hyp hyp) ⟩
           □ˢ ∞ Pˢ ((x ∷ xs) ++ cycle x xs)  ↝⟨ (λ { (p ∷ ps) → p ∷ ps }) ⟩□
           □ˢ ∞ Pˢ (cycle x xs)              □
  }
  where
  from : □ˢ ∞ Pˢ (x ∷ xs) → □ˢ i Pˢ ys → □ˢ i Pˢ (ys ++ cycle x xs)
  from ps       (q ∷ qs) = q ∷ λ { .force → from ps (force qs) }
  from (p ∷ ps) []       = ∞→ p ∷ λ { .force →
                           from (p ∷ ps) (force ps) }
