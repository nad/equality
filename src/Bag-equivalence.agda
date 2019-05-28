------------------------------------------------------------------------
-- Bag equivalence for lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Bag-equivalence
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq hiding (trans)

open import Logical-equivalence hiding (id; _∘_; inverse)
open import Prelude as P hiding (id; swap)

open import Bijection eq using (_↔_; module _↔_; Σ-≡,≡↔≡)
open import Equality.Decision-procedures eq
open import Fin eq as Finite
open import Function-universe eq as Function-universe
  hiding (_∘_; Kind; module Kind; bijection)
open import H-level eq
open import H-level.Closure eq
open import Injection eq using (_↣_)
open import List eq
open import Monad eq hiding (map)
open import Nat eq hiding (_≟_)

private
  variable
    a ℓ p q                  : Level
    A B                      : Set a
    P Q                      : A → Set p
    x y z                    : A
    xs xs₁ xs₂ ys ys₁ ys₂ zs : List A
    xss yss                  : List (List A)
    k                        : Function-universe.Kind
    m n                      : ℕ

------------------------------------------------------------------------
-- Any

-- Any.

Any : (A → Set p) → List A → Set p
Any P []       = ⊥
Any P (x ∷ xs) = P x ⊎ Any P xs

-- Alternative definition of Any.

data Any′ {A : Set a} (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} → P x       → Any′ P (x ∷ xs)
  there : ∀ {x xs} → Any′ P xs → Any′ P (x ∷ xs)

-- The two definitions of Any are isomorphic.

Any′-[] : Any′ P [] ↔ ⊥ {ℓ = ℓ}
Any′-[] = record
  { surjection = record
    { logical-equivalence = record
      { from = λ ()
      ; to   = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ ()
  }

Any′-∷ : Any′ P (x ∷ xs) ↔ P x ⊎ Any′ P xs
Any′-∷ = record
  { surjection = record
    { logical-equivalence = record
      { from = [ here , there ]
      ; to   = λ where
                 (here p)  → inj₁ p
                 (there p) → inj₂ p
        }
    ; right-inverse-of = [ (λ _ → refl _) , (λ _ → refl _) ]
    }
  ; left-inverse-of = λ where
      (here _)  → refl _
      (there _) → refl _
  }

Any↔Any′ : Any P xs ↔ Any′ P xs
Any↔Any′ {P = P} {xs = []} =
  ⊥          ↔⟨ inverse Any′-[] ⟩
  Any′ P []  □
Any↔Any′ {P = P} {xs = x ∷ xs} =
  P x ⊎ Any P xs   ↔⟨ id ⊎-cong Any↔Any′ {P = P} ⟩
  P x ⊎ Any′ P xs  ↔⟨ inverse Any′-∷ ⟩
  Any′ P (x ∷ xs)  □

------------------------------------------------------------------------
-- Lemmas relating Any to some basic list functions

Any-++ : (P : A → Set p) (xs ys : List A) →
         Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P [] ys =
  Any P ys      ↔⟨ inverse ⊎-left-identity ⟩
  ⊥ ⊎ Any P ys  □
Any-++ P (x ∷ xs) ys =
  P x ⊎ Any P (xs ++ ys)       ↔⟨ id ⊎-cong Any-++ P xs ys ⟩
  P x ⊎ (Any P xs ⊎ Any P ys)  ↔⟨ ⊎-assoc ⟩
  (P x ⊎ Any P xs) ⊎ Any P ys  □

Any-concat : (P : A → Set p) (xss : List (List A)) →
             Any P (concat xss) ↔ Any (Any P) xss
Any-concat P []         = id
Any-concat P (xs ∷ xss) =
  Any P (xs ++ concat xss)       ↔⟨ Any-++ P xs (concat xss) ⟩
  Any P xs ⊎ Any P (concat xss)  ↔⟨ id ⊎-cong Any-concat P xss ⟩
  Any P xs ⊎ Any (Any P) xss     □

Any-map : (P : B → Set p) (f : A → B) (xs : List A) →
          Any P (map f xs) ↔ Any (P ∘ f) xs
Any-map P f []       = id
Any-map P f (x ∷ xs) =
  P (f x)   ⊎ Any P (map f xs)  ↔⟨ id ⊎-cong Any-map P f xs ⟩
  (P ∘ f) x ⊎ Any (P ∘ f) xs    □

Any->>= : {A B : Set ℓ}
          (P : B → Set p) (xs : List A) (f : A → List B) →
          Any P (xs >>= f) ↔ Any (Any P ∘ f) xs
Any->>= P xs f =
  Any P (concat (map f xs))  ↔⟨ Any-concat P (map f xs) ⟩
  Any (Any P) (map f xs)     ↔⟨ Any-map (Any P) f xs ⟩
  Any (Any P ∘ f) xs         □

Any-filter : (P : A → Set p) (p : A → Bool) (xs : List A) →
             Any P (filter p xs) ↔ Any (λ x → P x × T (p x)) xs
Any-filter P p []       = ⊥ □
Any-filter P p (x ∷ xs) with p x
... | true  =
   P x      ⊎ Any P (filter p xs)           ↔⟨ inverse ×-right-identity ⊎-cong Any-filter P p xs ⟩
  (P x × ⊤) ⊎ Any (λ x → P x × T (p x)) xs  □
... | false =
  Any P (filter p xs)                       ↔⟨ Any-filter P p xs ⟩
              Any (λ x → P x × T (p x)) xs  ↔⟨ inverse ⊎-left-identity ⟩
  ⊥₀        ⊎ Any (λ x → P x × T (p x)) xs  ↔⟨ inverse ×-right-zero ⊎-cong (_ □) ⟩
  (P x × ⊥) ⊎ Any (λ x → P x × T (p x)) xs  □

------------------------------------------------------------------------
-- List membership

infix 4 _∈_

_∈_ : A → List A → Set _
x ∈ xs = Any (λ y → x ≡ y) xs

-- Any can be expressed using _∈_.

Any-∈ : (P : A → Set p) (xs : List A) →
        Any P xs ↔ ∃ λ x → P x × x ∈ xs
Any-∈ P [] =
  ⊥                  ↔⟨ inverse ×-right-zero ⟩
  (∃ λ x → ⊥₀)       ↔⟨ ∃-cong (λ x → inverse ×-right-zero) ⟩
  (∃ λ x → P x × ⊥)  □
Any-∈ P (x ∷ xs) =
  P x                   ⊎ Any P xs                ↔⟨ ∃-intro P x ⊎-cong Any-∈ P xs ⟩
  (∃ λ y → P y × y ≡ x) ⊎ (∃ λ y → P y × y ∈ xs)  ↔⟨ inverse ∃-⊎-distrib-left ⟩
  (∃ λ y → P y × y ≡ x ⊎ P y × y ∈ xs)            ↔⟨ ∃-cong (λ y → inverse ×-⊎-distrib-left) ⟩
  (∃ λ y → P y × (y ≡ x ⊎ y ∈ xs))                □

-- Using this property we can prove that Any and _⊎_ commute.

Any-⊎ : (P : A → Set p) (Q : A → Set q) (xs : List A) →
        Any (λ x → P x ⊎ Q x) xs ↔ Any P xs ⊎ Any Q xs
Any-⊎ P Q xs =
  Any (λ x → P x ⊎ Q x) xs                         ↔⟨ Any-∈ (λ x → P x ⊎ Q x) xs ⟩
  (∃ λ x → (P x ⊎ Q x) × x ∈ xs)                   ↔⟨ ∃-cong (λ x → ×-⊎-distrib-right) ⟩
  (∃ λ x → P x × x ∈ xs ⊎ Q x × x ∈ xs)            ↔⟨ ∃-⊎-distrib-left ⟩
  (∃ λ x → P x × x ∈ xs) ⊎ (∃ λ x → Q x × x ∈ xs)  ↔⟨ inverse $ Any-∈ P xs ⊎-cong Any-∈ Q xs ⟩
  Any P xs ⊎ Any Q xs                              □

------------------------------------------------------------------------
-- Some lemmas related to list membership

-- If f and g are pointwise equal for elements in xs, then map f xs
-- and map g xs are equal.

map-cong-∈ :
  (f g : A → B) (xs : List A) →
  (∀ {x} → x ∈ xs → f x ≡ g x) →
  map f xs ≡ map g xs
map-cong-∈ p q []       p≡q = refl _
map-cong-∈ p q (x ∷ xs) p≡q =
  cong₂ _∷_ (p≡q (inj₁ (refl _))) (map-cong-∈ p q xs (p≡q ∘ inj₂))

-- If p and q are pointwise equal for elements in xs, then filter p xs
-- and filter q xs are equal.

filter-cong-∈ :
  (p q : A → Bool) (xs : List A) →
  (∀ {x} → x ∈ xs → p x ≡ q x) →
  filter p xs ≡ filter q xs
filter-cong-∈ p q []       p≡q = refl _
filter-cong-∈ p q (x ∷ xs) p≡q
  with p x | q x | p≡q (inj₁ (refl _))
     | filter-cong-∈ p q xs (p≡q ∘ inj₂)
... | true  | true  | _   | ih = cong (x ∷_) ih
... | false | false | _   | ih = ih
... | true  | false | t≡f | _  = ⊥-elim $ Bool.true≢false t≡f
... | false | true  | f≡t | _  = ⊥-elim $ Bool.true≢false $ sym f≡t

-- The ordering of natural numbers can be related to list membership
-- and nats-<.

<-↔-∈-nats-< : m < n ↔ m ∈ nats-< n
<-↔-∈-nats-< {m = m} {n = zero} =
  m < zero         ↝⟨ <zero↔ ⟩
  ⊥                ↔⟨⟩
  m ∈ nats-< zero  □
<-↔-∈-nats-< {m = m} {n = suc n} =
  m < suc n             ↔⟨⟩
  suc m ≤ suc n         ↝⟨ suc≤suc↔ ⟩
  m ≤ n                 ↝⟨ ≤↔<⊎≡ ⟩
  m < n ⊎ m ≡ n         ↝⟨ ⊎-comm ⟩
  m ≡ n ⊎ m < n         ↝⟨ Function-universe.id ⊎-cong <-↔-∈-nats-< ⟩
  m ≡ n ⊎ m ∈ nats-< n  ↔⟨⟩
  m ∈ nats-< (suc n)    □

------------------------------------------------------------------------
-- Bag and set equivalence and the subset and subbag orders

-- Various kinds of relatedness.
--
-- NOTE: Perhaps it would be better to define the subbag property in
-- terms of embeddings, rather than injections. The HoTT book (first
-- edition) claims that injectivity "is an ill-behaved notion for
-- non-sets".

open Function-universe public using (Kind) hiding (module Kind)

module Kind where

  open Function-universe public
    using ()
    renaming ( implication         to subset
             ; logical-equivalence to set
             ; injection           to subbag
             ; bijection           to bag
             ; equivalence         to bag-with-equivalence
             )

open Kind public

-- A general definition of "relatedness" for lists.

infix 4 _∼[_]_

_∼[_]_ : {A : Set a} → List A → Kind → List A → Set a
xs ∼[ k ] ys = ∀ z → z ∈ xs ↝[ k ] z ∈ ys

-- Bag equivalence.

infix 4 _≈-bag_

_≈-bag_ : {A : Set a} → List A → List A → Set a
xs ≈-bag ys = xs ∼[ bag ] ys

-- Alternative definition of bag equivalence.

infix 4 _≈-bag′_

record _≈-bag′_ {A : Set a} (xs ys : List A) : Set a where
  field
    bijection : Fin (length xs) ↔ Fin (length ys)
    related   : xs And ys Are-related-by bijection

-- Yet another definition of bag equivalence. This definition is taken
-- from Coq's standard library.

infixr 5 _∷_
infix  4 _≈-bag″_

data _≈-bag″_ {A : Set a} : List A → List A → Set a where
  []    : [] ≈-bag″ []
  _∷_   : ∀ x {xs ys} (xs≈ys : xs ≈-bag″ ys) → x ∷ xs ≈-bag″ x ∷ ys
  swap  : ∀ {x y xs} → x ∷ y ∷ xs ≈-bag″ y ∷ x ∷ xs
  trans : ∀ {xs ys zs}
          (xs≈ys : xs ≈-bag″ ys) (ys≈zs : ys ≈-bag″ zs) → xs ≈-bag″ zs

------------------------------------------------------------------------
-- Some congruence lemmas

Any-cong : (∀ x → P x ↝[ k ] Q x) → xs ∼[ k ] ys →
           Any P xs ↝[ k ] Any Q ys
Any-cong {P = P} {Q = Q} {xs = xs} {ys = ys} P↔Q xs≈ys =
  Any P xs                ↔⟨ Any-∈ P xs ⟩
  (∃ λ z → P z × z ∈ xs)  ↝⟨ ∃-cong (λ z → P↔Q z ×-cong xs≈ys z) ⟩
  (∃ λ z → Q z × z ∈ ys)  ↔⟨ inverse (Any-∈ Q ys) ⟩
  Any Q ys                □

++-cong : xs₁ ∼[ k ] ys₁ → xs₂ ∼[ k ] ys₂ →
          xs₁ ++ xs₂ ∼[ k ] ys₁ ++ ys₂
++-cong {xs₁ = xs₁} {ys₁ = ys₁} {xs₂ = xs₂} {ys₂ = ys₂}
        xs₁∼ys₁ xs₂∼ys₂ = λ z →
  z ∈ xs₁ ++ xs₂     ↔⟨ Any-++ _ xs₁ xs₂ ⟩
  z ∈ xs₁ ⊎ z ∈ xs₂  ↝⟨ xs₁∼ys₁ z ⊎-cong xs₂∼ys₂ z ⟩
  z ∈ ys₁ ⊎ z ∈ ys₂  ↔⟨ inverse (Any-++ _ ys₁ ys₂) ⟩
  z ∈ ys₁ ++ ys₂     □

map-cong : (f : A → B) → xs ∼[ k ] ys → map f xs ∼[ k ] map f ys
map-cong {xs = xs} {ys = ys} f xs∼ys = λ z →
  z ∈ map f xs            ↔⟨ Any-map _ f xs ⟩
  Any (λ x → z ≡ f x) xs  ↝⟨ Any-cong (λ x → z ≡ f x □) xs∼ys ⟩
  Any (λ x → z ≡ f x) ys  ↔⟨ inverse (Any-map _ f ys) ⟩
  z ∈ map f ys            □

concat-cong : xss ∼[ k ] yss → concat xss ∼[ k ] concat yss
concat-cong {xss = xss} {yss = yss} xss∼yss = λ z →
  z ∈ concat xss           ↔⟨ Any-concat _ xss ⟩
  Any (λ zs → z ∈ zs) xss  ↝⟨ Any-cong (λ zs → z ∈ zs □) xss∼yss ⟩
  Any (λ zs → z ∈ zs) yss  ↔⟨ inverse (Any-concat _ yss) ⟩
  z ∈ concat yss           □

>>=-cong : {A B : Set ℓ} {xs ys : List A} {f g : A → List B} →
           xs ∼[ k ] ys → (∀ x → f x ∼[ k ] g x) →
           (xs >>= f) ∼[ k ] (ys >>= g)
>>=-cong {xs = xs} {ys = ys} {f = f} {g = g} xs∼ys f∼g = λ z →
  z ∈ xs >>= f            ↔⟨ Any->>= _ xs f ⟩
  Any (λ x → z ∈ f x) xs  ↝⟨ Any-cong (λ x → f∼g x z) xs∼ys ⟩
  Any (λ x → z ∈ g x) ys  ↔⟨ inverse (Any->>= _ ys g) ⟩
  z ∈ ys >>= g            □

filter-cong : (p : A → Bool) (xs ys : List A) →
              xs ∼[ k ] ys → filter p xs ∼[ k ] filter p ys
filter-cong p xs ys xs∼ys = λ z →
  z ∈ filter p xs                 ↔⟨ Any-filter _ p xs ⟩
  Any (λ x → z ≡ x × T (p x)) xs  ↝⟨ Any-cong (λ _ → _ □) xs∼ys ⟩
  Any (λ x → z ≡ x × T (p x)) ys  ↔⟨ inverse (Any-filter _ p ys) ⟩
  z ∈ filter p ys                 □

------------------------------------------------------------------------
-- More properties

-- Any preserves decidability of equality.

module Dec (dec : ∀ {x} → Decidable-equality (P x)) where

  infix 4 _≟_

  _≟_ : Decidable-equality (Any P xs)
  _≟_ {xs = _ ∷ _} = ⊎.Dec._≟_ dec _≟_

-- If the type of x is a set, then equality is decidable for x ∈ xs.

module Dec-∈ (A-set : Is-set A) where

  infix 4 _≟_

  _≟_ : ∀ {x xs} → Decidable-equality (x ∈ xs)
  _≟_ = Dec._≟_ λ _ _ → yes (A-set _ _)

-- Bind distributes from the left over append.

>>=-left-distributive :
  {A B : Set ℓ} (xs : List A) (f g : A → List B) →
  xs >>= (λ x → f x ++ g x) ≈-bag (xs >>= f) ++ (xs >>= g)
>>=-left-distributive xs f g = λ z →
  z ∈ xs >>= (λ x → f x ++ g x)                    ↔⟨ Any->>= (_≡_ z) xs (λ x → f x ++ g x) ⟩
  Any (λ x → z ∈ f x ++ g x) xs                    ↔⟨ Any-cong (λ x → Any-++ (_≡_ z) (f x) (g x)) (λ _ → id) ⟩
  Any (λ x → z ∈ f x ⊎ z ∈ g x) xs                 ↔⟨ Any-⊎ (λ x → z ∈ f x) (λ x → z ∈ g x) xs ⟩
  Any (λ x → z ∈ f x) xs ⊎ Any (λ x → z ∈ g x) xs  ↔⟨ inverse (Any->>= (_≡_ z) xs f ⊎-cong Any->>= (_≡_ z) xs g) ⟩
  z ∈ xs >>= f ⊎ z ∈ xs >>= g                      ↔⟨ inverse (Any-++ (_≡_ z) (xs >>= f) (xs >>= g)) ⟩
  z ∈ (xs >>= f) ++ (xs >>= g)                     □

-- This property does not hold for ordinary list equality.

¬->>=-left-distributive :
  ¬ ({A B : Set} (xs : List A) (f g : A → List B) →
     xs >>= (λ x → f x ++ g x) ≡ (xs >>= f) ++ (xs >>= g))
¬->>=-left-distributive distrib = Bool.true≢false true≡false
  where
  tf = true ∷ false ∷ []
  f  = λ x → x ∷ []
  g  = f

  ttff≡tftf : true ∷ true ∷ false ∷ false ∷ [] ≡
              true ∷ false ∷ true ∷ false ∷ []
  ttff≡tftf = distrib tf f g

  true≡false : true ≡ false
  true≡false = List.cancel-∷-head (List.cancel-∷-tail ttff≡tftf)

-- _++_ is commutative.

++-comm : (xs ys : List A) → xs ++ ys ≈-bag ys ++ xs
++-comm xs ys = λ z →
  z ∈ xs ++ ys     ↔⟨ Any-++ (_≡_ z) xs ys ⟩
  z ∈ xs ⊎ z ∈ ys  ↔⟨ ⊎-comm ⟩
  z ∈ ys ⊎ z ∈ xs  ↔⟨ inverse (Any-++ (_≡_ z) ys xs) ⟩
  z ∈ ys ++ xs     □

-- _++_ is idempotent (when set equivalence is used).

++-idempotent : (xs : List A) → xs ++ xs ∼[ set ] xs
++-idempotent xs = λ z →
  z ∈ xs ++ xs     ↔⟨ Any-++ (_≡_ z) xs xs ⟩
  z ∈ xs ⊎ z ∈ xs  ↝⟨ ⊎-idempotent ⟩
  z ∈ xs           □

-- The so-called "range splitting" property (see, for instance,
-- Hoogendijks "(Relational) Programming Laws in the Boom Hierarchy of
-- Types").

range-splitting : (p : A → Bool) (xs : List A) →
                  filter p xs ++ filter (not ∘ p) xs ≈-bag xs
range-splitting p xs = λ z →
  z ∈ filter p xs ++ filter (not ∘ p) xs                  ↔⟨ Any-++ _ _ (filter (not ∘ p) xs) ⟩
  z ∈ filter p xs ⊎ z ∈ filter (not ∘ p) xs               ↔⟨ Any-filter _ p xs ⊎-cong Any-filter _ (not ∘ p) xs ⟩
  Any (λ x → z ≡ x × T (p x)) xs ⊎
    Any (λ x → z ≡ x × T (not (p x))) xs                  ↔⟨ inverse $ Any-⊎ _ _ xs ⟩
  Any (λ x → z ≡ x × T (p x) ⊎ z ≡ x × T (not (p x))) xs  ↔⟨ Any-cong (λ x → lemma (z ≡ x) (p x)) (λ x → x ∈ xs □) ⟩
  z ∈ xs                                                  □
  where
  lemma : ∀ {a} (A : Set a) (b : Bool) → A × T b ⊎ A × T (not b) ↔ A
  lemma A b =
    A × T b ⊎ A × T (not b)  ↔⟨ ×-comm ⊎-cong ×-comm ⟩
    T b × A ⊎ T (not b) × A  ↔⟨ if-lemma (λ _ → A) id id b ⟩
    A                        □

-- The so-called "range disjunction" property, strengthened to use the
-- subbag preorder instead of set equivalence.

range-disjunction :
  (p q : A → Bool) (xs : List A) →
  filter (λ x → p x ∨ q x) xs ∼[ subbag ]
  filter p xs ++ filter q xs
range-disjunction p q xs = λ z →
  z ∈ filter (λ x → p x ∨ q x) xs                                  ↔⟨ Any-filter _ (λ x → p x ∨ q x) _ ⟩
  Any (λ x → z ≡ x × T (p x ∨ q x)) xs                             ↝⟨ Any-cong (λ x → lemma (z ≡ x) (p x) (q x)) (λ x → x ∈ xs □) ⟩
  Any (λ x → z ≡ x × T (p x) ⊎ z ≡ x × T (q x)) xs                 ↔⟨ Any-⊎ _ _ _ ⟩
  Any (λ x → z ≡ x × T (p x)) xs ⊎ Any (λ x → z ≡ x × T (q x)) xs  ↔⟨ inverse (Any-filter _ p _ ⊎-cong Any-filter _ q _) ⟩
  z ∈ filter p xs ⊎ z ∈ filter q xs                                ↔⟨ inverse $ Any-++ _ _ _ ⟩
  z ∈ filter p xs ++ filter q xs                                   □
  where
  inj : (b₁ b₂ : Bool) → T (b₁ ∨ b₂) ↣ T b₁ ⊎ T b₂
  inj true  true  = record { to = inj₁; injective = λ _ → refl _  }
  inj true  false = record { to = inj₁; injective = ⊎.cancel-inj₁ }
  inj false true  = record { to = inj₂; injective = ⊎.cancel-inj₂ }
  inj false false = record { to = λ (); injective = λ {}          }

  lemma : ∀ {a} (A : Set a) (b₁ b₂ : Bool) →
          A × T (b₁ ∨ b₂) ↣ A × T b₁ ⊎ A × T b₂
  lemma A b₁ b₂ =
    A × T (b₁ ∨ b₂)      ↝⟨ id ×-cong inj b₁ b₂ ⟩
    A × (T b₁ ⊎ T b₂)    ↔⟨ ×-⊎-distrib-left ⟩
    A × T b₁ ⊎ A × T b₂  □

------------------------------------------------------------------------
-- The first two definitions of bag equivalence above are logically
-- equivalent

-- One direction follows from the following lemma, which states that
-- list membership can be expressed as "there is an index which points
-- to the element".
--
-- As an aside, note that the right-hand side is almost
-- index xs ⁻¹ z.

∈-index : (xs : List A) → z ∈ xs ↔ ∃ λ i → z ≡ index xs i
∈-index {z = z} [] =
  ⊥                               ↔⟨ inverse $ ∃-Fin-zero _ ⟩
  (∃ λ (i : ⊥) → z ≡ index [] i)  □
∈-index {z = z} (x ∷ xs) =
  z ≡ x ⊎ z ∈ xs                    ↔⟨ id ⊎-cong ∈-index xs ⟩
  z ≡ x ⊎ (∃ λ i → z ≡ index xs i)  ↔⟨ inverse $ ∃-Fin-suc _ ⟩
  (∃ λ i → z ≡ index (x ∷ xs) i)    □

-- The index which points to the element.

index-of : z ∈ xs → Fin (length xs)
index-of = proj₁ ∘ _↔_.to (∈-index _)

-- For the other direction a sequence of lemmas is used.

-- The first lemma states that ∃ λ z → z ∈ xs is isomorphic to Fin n,
-- where n is the length of xs. Thierry Coquand pointed out that this
-- is a generalisation of singleton-contractible.

Fin-length : (xs : List A) → (∃ λ z → z ∈ xs) ↔ Fin (length xs)
Fin-length xs =
  (∃ λ z → z ∈ xs)                  ↔⟨ ∃-cong (λ _ → ∈-index xs) ⟩
  (∃ λ z → ∃ λ i → z ≡ index xs i)  ↔⟨ ∃-comm ⟩
  (∃ λ i → ∃ λ z → z ≡ index xs i)  ↔⟨⟩
  (∃ λ i → Singleton (index xs i))  ↔⟨ ∃-cong (λ _ → _⇔_.to contractible⇔↔⊤ (singleton-contractible _)) ⟩
  Fin (length xs) × ⊤               ↔⟨ ×-right-identity ⟩
  Fin (length xs)                   □

-- From this lemma we get that lists which are bag equivalent have
-- related lengths.

Fin-length-cong : xs ≈-bag ys → Fin (length xs) ↔ Fin (length ys)
Fin-length-cong {xs = xs} {ys = ys} xs≈ys =
  Fin (length xs)   ↔⟨ inverse $ Fin-length xs ⟩
  ∃ (λ z → z ∈ xs)  ↔⟨ ∃-cong xs≈ys ⟩
  ∃ (λ z → z ∈ ys)  ↔⟨ Fin-length ys ⟩
  Fin (length ys)   □

abstract

  -- In fact, they have equal lengths.

  length-cong : xs ≈-bag ys → length xs ≡ length ys
  length-cong = _⇔_.to Finite.isomorphic-same-size ∘ Fin-length-cong

  -- All that remains (except for some bookkeeping) is to show that
  -- the isomorphism which Fin-length-cong returns relates the two
  -- lists.

  Fin-length-cong-relates :
    {xs ys : List A} (xs≈ys : xs ≈-bag ys) →
    xs And ys Are-related-by Fin-length-cong xs≈ys
  Fin-length-cong-relates {xs = xs} {ys = ys} xs≈ys i =
    index xs i                                ≡⟨ proj₂ $ to (∈-index _) $ to (xs≈ys _) (from (∈-index _) (i , refl _)) ⟩
    index ys (proj₁ $ to (∈-index _) $
              to (xs≈ys _) $
              from (∈-index _) (i , refl _))  ≡⟨⟩
    index ys (to (Fin-length-cong xs≈ys) i)   ∎
    where open _↔_

-- We get that the two definitions of bag equivalence are logically
-- equivalent.

≈⇔≈′ : xs ≈-bag ys ⇔ xs ≈-bag′ ys
≈⇔≈′ = record
  { to   = λ xs≈ys → record
             { bijection = Fin-length-cong xs≈ys
             ; related   = Fin-length-cong-relates xs≈ys
             }
  ; from = from
  }
  where
  equality-lemma : y ≡ z → (x ≡ y) ↔ (x ≡ z)
  equality-lemma = flip-trans-isomorphism

  from : xs ≈-bag′ ys → xs ≈-bag ys
  from {xs = xs} {ys = ys} xs≈ys z =
    z ∈ xs                    ↔⟨ ∈-index xs ⟩
    ∃ (λ i → z ≡ index xs i)  ↔⟨ Σ-cong (_≈-bag′_.bijection xs≈ys)
                                        (λ i → equality-lemma $
                                                 _≈-bag′_.related xs≈ys i) ⟩
    ∃ (λ i → z ≡ index ys i)  ↔⟨ inverse (∈-index ys) ⟩
    z ∈ ys                    □

------------------------------------------------------------------------
-- Left cancellation

-- We have basically already showed that cons is left cancellative for
-- the (first) alternative definition of bag equivalence.

∷-left-cancellative′ : ∀ xs ys → x ∷ xs ≈-bag′ x ∷ ys → xs ≈-bag′ ys
∷-left-cancellative′ {x = x} xs ys x∷xs≈x∷ys = record
  { bijection = Finite.cancel-suc (_≈-bag′_.bijection x∷xs≈x∷ys)
  ; related   = Finite.cancel-suc-preserves-relatedness x xs ys
                  (_≈-bag′_.bijection x∷xs≈x∷ys)
                  (_≈-bag′_.related x∷xs≈x∷ys)
  }

-- By the equivalence above we get the result also for the first
-- definition of bag equivalence, but we can show this directly, with
-- the help of some lemmas.

abstract

  -- The index-of function commutes with applications of certain
  -- inverses. Note that the last three equational reasoning steps do
  -- not need to be written out; I included them in an attempt to make
  -- it easier to understand why the lemma holds.

  index-of-commutes :
    {xs ys : List A} (xs≈ys : xs ≈-bag ys) (p : z ∈ xs) →
    index-of (_↔_.to (xs≈ys z) p) ≡
    _↔_.to (Fin-length-cong xs≈ys) (index-of p)
  index-of-commutes {z = z} {xs = xs} {ys = ys} xs≈ys p =
    index-of $ to (xs≈ys z) p                                     ≡⟨⟩

    index-of $ proj₂ $ Σ-map P.id (λ {x} → to (xs≈ys x)) (z , p)  ≡⟨ cong (index-of ∘ proj₂ ∘ Σ-map P.id (to (xs≈ys _))) $ sym $
                                                                     left-inverse-of (Fin-length xs) (z , p) ⟩
    index-of $ proj₂ $ Σ-map P.id (λ {x} → to (xs≈ys x)) $
    from (Fin-length xs) $ to (Fin-length xs) (z , p)             ≡⟨⟩

    to (Fin-length ys) $ Σ-map P.id (λ {x} → to (xs≈ys x)) $
    from (Fin-length xs) $ index-of p                             ≡⟨⟩

    to (Fin-length-cong xs≈ys) $ index-of p                       ∎
    where
    open _↔_

  -- Bag equivalence isomorphisms preserve index equality. Note that
  -- this means that, even if the underlying equality is proof
  -- relevant, a bag equivalence isomorphism cannot map two distinct
  -- proofs, that point to the same position, to different positions.

  index-equality-preserved :
    {xs ys : List A} {p q : z ∈ xs}
    (xs≈ys : xs ≈-bag ys) →
    index-of p ≡ index-of q →
    index-of (_↔_.to (xs≈ys z) p) ≡ index-of (_↔_.to (xs≈ys z) q)
  index-equality-preserved {z = z} {p = p} {q = q} xs≈ys eq =
    index-of (_↔_.to (xs≈ys z) p)                ≡⟨ index-of-commutes xs≈ys p ⟩
    _↔_.to (Fin-length-cong xs≈ys) (index-of p)  ≡⟨ cong (_↔_.to (Fin-length-cong xs≈ys)) eq ⟩
    _↔_.to (Fin-length-cong xs≈ys) (index-of q)  ≡⟨ sym $ index-of-commutes xs≈ys q ⟩∎
    index-of (_↔_.to (xs≈ys z) q)                ∎

-- If x ∷ xs is bag equivalent to x ∷ ys, then xs and ys are bag
-- equivalent.

∷-left-cancellative : x ∷ xs ≈-bag x ∷ ys → xs ≈-bag ys
∷-left-cancellative {x = x} x∷xs≈x∷ys z =
  ⊎-left-cancellative
    (x∷xs≈x∷ys z)
    (lemma x∷xs≈x∷ys)
    (lemma (inverse ∘ x∷xs≈x∷ys))
  where
  abstract

    -- If the equality type is proof irrelevant (so that p and q are
    -- equal), then this lemma can be proved without the help of
    -- index-equality-preserved.

    lemma : (inv : x ∷ xs ≈-bag x ∷ ys) →
            Well-behaved (_↔_.to (inv z))
    lemma {xs = xs} inv {b = z∈xs} {a = p} {a′ = q} hyp₁ hyp₂ =
      ⊎.inj₁≢inj₂ (
        fzero                                   ≡⟨⟩
        index-of {xs = x ∷ xs} (inj₁ p)         ≡⟨ cong index-of $ sym $ to-from hyp₂ ⟩
        index-of {xs = x ∷ xs} (from (inj₁ q))  ≡⟨ index-equality-preserved (inverse ∘ inv) (refl _) ⟩
        index-of {xs = x ∷ xs} (from (inj₁ p))  ≡⟨ cong index-of $ to-from hyp₁ ⟩
        index-of {xs = x ∷ xs} (inj₂ z∈xs)      ≡⟨⟩
        fsuc (index-of {xs = xs} z∈xs)          ∎)
      where open _↔_ (inv z)

-- Cons is not left cancellative for set equivalence.

∷-not-left-cancellative :
  ¬ (∀ {A : Set} {x : A} {xs ys} →
     x ∷ xs ∼[ set ] x ∷ ys → xs ∼[ set ] ys)
∷-not-left-cancellative cancel =
  _⇔_.to (cancel (++-idempotent (tt ∷ [])) tt) (inj₁ (refl _))

-- _++_ is left and right cancellative (for bag equivalence).

++-left-cancellative :
  ∀ xs → xs ++ ys ≈-bag xs ++ zs → ys ≈-bag zs
++-left-cancellative []       eq = eq
++-left-cancellative (x ∷ xs) eq =
  ++-left-cancellative xs (∷-left-cancellative eq)

++-right-cancellative : xs ++ zs ≈-bag ys ++ zs → xs ≈-bag ys
++-right-cancellative {xs = xs} {zs = zs} {ys = ys} eq =
  ++-left-cancellative zs (λ z →
    z ∈ zs ++ xs  ↔⟨ ++-comm zs xs z ⟩
    z ∈ xs ++ zs  ↔⟨ eq z ⟩
    z ∈ ys ++ zs  ↔⟨ ++-comm ys zs z ⟩
    z ∈ zs ++ ys  □)

------------------------------------------------------------------------
-- The third definition of bag equivalence is sound with respect to
-- the other two

-- _∷_ preserves bag equivalence.

infixr 5 _∷-cong_

_∷-cong_ : x ≡ y → xs ≈-bag ys → x ∷ xs ≈-bag y ∷ ys
_∷-cong_ {x = x} {y = y} {xs = xs} {ys = ys} x≡y xs≈ys = λ z →
  z ≡ x ⊎ z ∈ xs  ↔⟨ flip-trans-isomorphism x≡y ⊎-cong xs≈ys z ⟩
  z ≡ y ⊎ z ∈ ys  □

-- We can swap the first two elements of a list.

swap-first-two : x ∷ y ∷ xs ≈-bag y ∷ x ∷ xs
swap-first-two {x = x} {y = y} {xs = xs} = λ z →
   z ≡ x ⊎ z ≡ y  ⊎ z ∈ xs  ↔⟨ ⊎-assoc ⟩
  (z ≡ x ⊎ z ≡ y) ⊎ z ∈ xs  ↔⟨ ⊎-comm ⊎-cong id ⟩
  (z ≡ y ⊎ z ≡ x) ⊎ z ∈ xs  ↔⟨ inverse ⊎-assoc ⟩
   z ≡ y ⊎ z ≡ x  ⊎ z ∈ xs  □

-- The third definition of bag equivalence is sound with respect to
-- the first one.

≈″⇒≈ : xs ≈-bag″ ys → xs ≈-bag ys
≈″⇒≈ []                  = λ _ → id
≈″⇒≈ (x ∷ xs≈ys)         = refl _ ∷-cong ≈″⇒≈ xs≈ys
≈″⇒≈ swap                = swap-first-two
≈″⇒≈ (trans xs≈ys ys≈zs) = λ z → _ ↔⟨ ≈″⇒≈ xs≈ys z ⟩ ≈″⇒≈ ys≈zs z

-- The other direction should also be provable, but I expect that this
-- requires some work.
