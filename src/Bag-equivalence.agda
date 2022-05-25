------------------------------------------------------------------------
-- Bag equivalence for lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Bag-equivalence
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

private
  open module D = Derived-definitions-and-properties eq
    hiding (trans)

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; swap)

open import Bijection eq using (_↔_; module _↔_; Σ-≡,≡↔≡)
open import Embedding eq as Emb using (Embedding)
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Fin eq as Finite
open import Function-universe eq as Function-universe
  hiding (_∘_; Kind; equivalence)
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (_↣_)
open import List eq
open import Monad eq hiding (map)
open import Nat eq using (_≤_; _<_)
open import Surjection eq using (_↠_)

private
  module F = Function-universe

  variable
    a ℓ p q                  : Level
    A B                      : Type a
    P Q                      : A → Type p
    x y z                    : A
    xs xs₁ xs₂ ys ys₁ ys₂ zs : List A
    xss yss                  : List (List A)
    k                        : F.Kind
    m n                      : ℕ

------------------------------------------------------------------------
-- Any

-- Any.

Any : (A → Type p) → List A → Type p
Any P []       = ⊥
Any P (x ∷ xs) = P x ⊎ Any P xs

-- Alternative definition of Any.

data Any′ {A : Type a} (P : A → Type p) : List A → Type (a ⊔ p) where
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

Any-++ : (P : A → Type p) (xs ys : List A) →
         Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P [] ys =
  Any P ys      ↔⟨ inverse ⊎-left-identity ⟩
  ⊥ ⊎ Any P ys  □
Any-++ P (x ∷ xs) ys =
  P x ⊎ Any P (xs ++ ys)       ↔⟨ id ⊎-cong Any-++ P xs ys ⟩
  P x ⊎ (Any P xs ⊎ Any P ys)  ↔⟨ ⊎-assoc ⟩
  (P x ⊎ Any P xs) ⊎ Any P ys  □

Any-concat : (P : A → Type p) (xss : List (List A)) →
             Any P (concat xss) ↔ Any (Any P) xss
Any-concat P []         = id
Any-concat P (xs ∷ xss) =
  Any P (xs ++ concat xss)       ↔⟨ Any-++ P xs (concat xss) ⟩
  Any P xs ⊎ Any P (concat xss)  ↔⟨ id ⊎-cong Any-concat P xss ⟩
  Any P xs ⊎ Any (Any P) xss     □

Any-map : (P : B → Type p) (f : A → B) (xs : List A) →
          Any P (map f xs) ↔ Any (P ∘ f) xs
Any-map P f []       = id
Any-map P f (x ∷ xs) =
  P (f x)   ⊎ Any P (map f xs)  ↔⟨ id ⊎-cong Any-map P f xs ⟩
  (P ∘ f) x ⊎ Any (P ∘ f) xs    □

Any->>= : {A B : Type ℓ}
          (P : B → Type p) (xs : List A) (f : A → List B) →
          Any P (xs >>= f) ↔ Any (Any P ∘ f) xs
Any->>= P xs f =
  Any P (concat (map f xs))  ↔⟨ Any-concat P (map f xs) ⟩
  Any (Any P) (map f xs)     ↔⟨ Any-map (Any P) f xs ⟩
  Any (Any P ∘ f) xs         □

Any-filter : (P : A → Type p) (p : A → Bool) (xs : List A) →
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

_∈_ : A → List A → Type _
x ∈ xs = Any (λ y → x ≡ y) xs

-- Any can be expressed using _∈_.

Any-∈ : (P : A → Type p) (xs : List A) →
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

Any-⊎ : (P : A → Type p) (Q : A → Type q) (xs : List A) →
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
  m ≡ n ⊎ m < n         ↝⟨ F.id ⊎-cong <-↔-∈-nats-< ⟩
  m ≡ n ⊎ m ∈ nats-< n  ↔⟨⟩
  m ∈ nats-< (suc n)    □

------------------------------------------------------------------------
-- Bag and set equivalence and the subset and subbag orders

-- Various kinds of relatedness.

open Function-universe public using (Kind) hiding (module Kind)

module Kind where

  open Function-universe public
    using ()
    renaming ( implication         to subset
             ; logical-equivalence to set
             ; embedding           to subbag
             ; bijection           to bag-with-bijection
             ; equivalence         to bag
             ; equivalenceᴱ        to bag-with-equivalenceᴱ
             )

open Kind public

-- A general definition of "relatedness" for lists.

infix 4 _∼[_]_

_∼[_]_ : {A : Type a} → List A → Kind → List A → Type a
xs ∼[ k ] ys = ∀ z → z ∈ xs ↝[ k ] z ∈ ys

-- Bag equivalence.

infix 4 _≈-bag_

_≈-bag_ : {A : Type a} → List A → List A → Type a
xs ≈-bag ys = xs ∼[ bag ] ys

-- Alternative definition of bag equivalence.

infix 4 _≈-bag′_

record _≈-bag′_ {A : Type a} (xs ys : List A) : Type a where
  field
    equivalence : Fin (length xs) ≃ Fin (length ys)
    related     : xs And ys Are-related-by from-equivalence equivalence

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

>>=-cong : {A B : Type ℓ} {xs ys : List A} {f g : A → List B} →
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
  {A B : Type ℓ} (xs : List A) (f g : A → List B) →
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
  ¬ ({A B : Type} (xs : List A) (f g : A → List B) →
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
  lemma : ∀ {a} (A : Type a) (b : Bool) → A × T b ⊎ A × T (not b) ↔ A
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

  lemma : ∀ {a} (A : Type a) (b₁ b₂ : Bool) →
          Embedding (A × T (b₁ ∨ b₂)) (A × T b₁ ⊎ A × T b₂)
  lemma A b₁ b₂ =
    A × T (b₁ ∨ b₂)      ↝⟨ id
                              ×-cong
                            _⇔_.to
                              (Emb.↣⇔Embedding
                                 (H-level.mono₁ 1 (T-propositional (b₁ ∨ b₂)))
                                 (⊎-closure 0
                                    (H-level.mono₁ 1 (T-propositional b₁))
                                    (H-level.mono₁ 1 (T-propositional b₂))))
                              (inj b₁ b₂) ⟩
    A × (T b₁ ⊎ T b₂)    ↔⟨ ×-⊎-distrib-left ⟩□
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
    index xs i                                    ≡⟨ proj₂ $ _↔_.to (∈-index _) $ _≃_.to (xs≈ys _) (_↔_.from (∈-index _) (i , refl _)) ⟩

    index ys (proj₁ $ _↔_.to (∈-index _) $
              _≃_.to (xs≈ys _) $
              _↔_.from (∈-index _) (i , refl _))  ≡⟨⟩

    index ys (_↔_.to (Fin-length-cong xs≈ys) i)   ∎

-- We get that the two definitions of bag equivalence are logically
-- equivalent.
--
-- The result can be strengthened, see Container.List.≈≃≈′.

≈⇔≈′ : xs ≈-bag ys ⇔ xs ≈-bag′ ys
≈⇔≈′ = record
  { to   = λ xs≈ys → record
             { equivalence = from-bijection $ Fin-length-cong xs≈ys
             ; related     = Fin-length-cong-relates xs≈ys
             }
  ; from = from
  }
  where
  equality-lemma : y ≡ z → (x ≡ y) ↔ (x ≡ z)
  equality-lemma = flip-trans-isomorphism

  from : xs ≈-bag′ ys → xs ≈-bag ys
  from {xs = xs} {ys = ys} xs≈ys z =
    z ∈ xs                    ↔⟨ ∈-index xs ⟩
    ∃ (λ i → z ≡ index xs i)  ↔⟨ Σ-cong (_≈-bag′_.equivalence xs≈ys)
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
  { equivalence =
      from-bijection $ Finite.cancel-suc $ from-equivalence $
      _≈-bag′_.equivalence x∷xs≈x∷ys
  ; related =
      Finite.cancel-suc-preserves-relatedness x xs ys
        (from-equivalence $ _≈-bag′_.equivalence x∷xs≈x∷ys)
        (_≈-bag′_.related x∷xs≈x∷ys)
  }

-- By the logical equivalence above we get the result also for the
-- first definition of bag equivalence, but we can show this directly,
-- with the help of some lemmas.

abstract

  -- The index-of function commutes with applications of certain
  -- inverses. Note that the last three equational reasoning steps do
  -- not need to be written out; I included them in an attempt to make
  -- it easier to understand why the lemma holds.

  index-of-commutes :
    {xs ys : List A} (xs≈ys : xs ≈-bag ys) (p : z ∈ xs) →
    index-of (_≃_.to (xs≈ys z) p) ≡
    _↔_.to (Fin-length-cong xs≈ys) (index-of p)
  index-of-commutes {z = z} {xs = xs} {ys = ys} xs≈ys p =
    index-of $ _≃_.to (xs≈ys z) p                                     ≡⟨⟩

    index-of $ proj₂ $ Σ-map P.id (λ {x} → _≃_.to (xs≈ys x)) (z , p)  ≡⟨ cong (index-of ∘ proj₂ ∘ Σ-map P.id (_≃_.to (xs≈ys _))) $ sym $
                                                                         _↔_.left-inverse-of (Fin-length xs) (z , p) ⟩
    index-of $ proj₂ $ Σ-map P.id (λ {x} → _≃_.to (xs≈ys x)) $
    _↔_.from (Fin-length xs) $ _↔_.to (Fin-length xs) (z , p)         ≡⟨⟩

    _↔_.to (Fin-length ys) $ Σ-map P.id (λ {x} → _≃_.to (xs≈ys x)) $
    _↔_.from (Fin-length xs) $ index-of p                             ≡⟨⟩

    _↔_.to (Fin-length-cong xs≈ys) $ index-of p                       ∎

  -- Bag equivalence isomorphisms preserve index equality. Note that
  -- this means that, even if the underlying equality is proof
  -- relevant, a bag equivalence isomorphism cannot map two distinct
  -- proofs, that point to the same position, to different positions.

  index-equality-preserved :
    {xs ys : List A} {p q : z ∈ xs}
    (xs≈ys : xs ≈-bag ys) →
    index-of p ≡ index-of q →
    index-of (_≃_.to (xs≈ys z) p) ≡ index-of (_≃_.to (xs≈ys z) q)
  index-equality-preserved {z = z} {p = p} {q = q} xs≈ys eq =
    index-of (_≃_.to (xs≈ys z) p)                ≡⟨ index-of-commutes xs≈ys p ⟩
    _↔_.to (Fin-length-cong xs≈ys) (index-of p)  ≡⟨ cong (_↔_.to (Fin-length-cong xs≈ys)) eq ⟩
    _↔_.to (Fin-length-cong xs≈ys) (index-of q)  ≡⟨ sym $ index-of-commutes xs≈ys q ⟩∎
    index-of (_≃_.to (xs≈ys z) q)                ∎

-- If x ∷ xs is bag equivalent to x ∷ ys, then xs and ys are bag
-- equivalent.

∷-left-cancellative : x ∷ xs ≈-bag x ∷ ys → xs ≈-bag ys
∷-left-cancellative {x = x} {xs = xs} {ys = ys} x∷xs≈x∷ys z =
  z ∈ xs  ↔⟨ ⊎-left-cancellative
               (from-equivalence $ x∷xs≈x∷ys z)
               (lemma x∷xs≈x∷ys)
               (lemma (inverse ∘ x∷xs≈x∷ys)) ⟩□
  z ∈ ys  □
  where
  abstract

    -- If the equality type is proof irrelevant (so that p and q are
    -- equal), then this lemma can be proved without the help of
    -- index-equality-preserved.

    lemma :
      ∀ {xs ys} (inv : x ∷ xs ≈-bag x ∷ ys) →
      Well-behaved (_≃_.to (inv z))
    lemma {xs = xs} inv {b = z∈xs} {a = p} {a′ = q} hyp₁ hyp₂ =
      ⊎.inj₁≢inj₂ (
        fzero                                   ≡⟨⟩
        index-of {xs = x ∷ xs} (inj₁ p)         ≡⟨ cong index-of $ sym $ to-from hyp₂ ⟩
        index-of {xs = x ∷ xs} (from (inj₁ q))  ≡⟨ index-equality-preserved (inverse ∘ inv) (refl _) ⟩
        index-of {xs = x ∷ xs} (from (inj₁ p))  ≡⟨ cong index-of $ to-from hyp₁ ⟩
        index-of {xs = x ∷ xs} (inj₂ z∈xs)      ≡⟨⟩
        fsuc (index-of {xs = xs} z∈xs)          ∎)
      where
      open _≃_ (inv z)

-- Cons is not left cancellative for set equivalence.

∷-not-left-cancellative :
  ¬ (∀ {A : Type} {x : A} {xs ys} →
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
-- The delete function

-- If an element is a member of a list, then one can remove the
-- element from the list.

delete : {ys : List A} → x ∈ ys → List A
delete {ys = _ ∷ ys} (inj₁ _) = ys
delete {ys = y ∷ _}  (inj₂ p) = y ∷ delete p

-- If p has type y ∈ ys, then x ∈ ys is equivalent to
-- x ∈ y ∷ delete p.

∈≃≡⊎∈delete :
  {ys : List A} (p : y ∈ ys) →
  (x ∈ ys) ≃ (x ∈ y ∷ delete p)
∈≃≡⊎∈delete {y = y} {x = x} {ys = z ∷ ys} (inj₁ y≡z) =
  x ≡ z ⊎ x ∈ ys  ↝⟨ ≡⇒↝ _ (cong (_ ≡_) (sym y≡z)) ⊎-cong id ⟩□
  x ≡ y ⊎ x ∈ ys  □
∈≃≡⊎∈delete {y = y} {x = x} {ys = z ∷ ys} (inj₂ p) =
  x ≡ z ⊎ x ∈ ys                  ↝⟨ id ⊎-cong ∈≃≡⊎∈delete p ⟩
  x ≡ z ⊎ (x ≡ y ⊎ x ∈ delete p)  ↔⟨ inverse ⊎-assoc F.∘ (⊎-comm ⊎-cong id) F.∘ ⊎-assoc ⟩□
  x ≡ y ⊎ (x ≡ z ⊎ x ∈ delete p)  □

-- A simplification lemma for ∈≃≡⊎∈delete.

from-∈≃≡⊎∈delete-inj₁ :
  {xs : List A} (p : x ∈ xs) →
  _≃_.from (∈≃≡⊎∈delete p) (inj₁ (refl x)) ≡ p
from-∈≃≡⊎∈delete-inj₁ {x = x} {xs = _ ∷ _} (inj₁ p) =
  _≃_.from (∈≃≡⊎∈delete (inj₁ p)) (inj₁ (refl x))         ≡⟨⟩
  inj₁ (_≃_.from (≡⇒↝ _ (cong (_ ≡_) (sym p))) (refl x))  ≡⟨ cong inj₁ $
                                                             D.trans (sym $ subst-in-terms-of-inverse∘≡⇒↝ F.equivalence _ (_ ≡_) _) $
                                                             D.trans (sym trans-subst) $
                                                             D.trans (trans-reflˡ _) $
                                                             sym-sym _ ⟩∎
  inj₁ p                                                  ∎
from-∈≃≡⊎∈delete-inj₁ {x = x} {xs = _ ∷ _} (inj₂ p) =
  _≃_.from (∈≃≡⊎∈delete (inj₂ p)) (inj₁ (refl x))  ≡⟨⟩
  inj₂ (_≃_.from (∈≃≡⊎∈delete p) (inj₁ (refl x)))  ≡⟨ cong inj₂ $ from-∈≃≡⊎∈delete-inj₁ p ⟩∎
  inj₂ p                                           ∎

-- The fact that two membership proofs (for the same list) have
-- different indices can be expressed in a certain way using
-- ∈≃≡⊎∈delete.

index-of≢index-of≃ :
  {zs : List A} (p : x ∈ zs) (q : y ∈ zs) →
  Distinct (index-of p) (index-of q) ≃
  Distinct fzero (index-of (_≃_.to (∈≃≡⊎∈delete p) q))
index-of≢index-of≃ {zs = _ ∷ _} (inj₁ _) (inj₁ _) = ⊥  □
index-of≢index-of≃ {zs = _ ∷ _} (inj₂ _) (inj₁ _) = ⊤  □
index-of≢index-of≃ {zs = _ ∷ _} (inj₁ _) (inj₂ _) = ⊤  □
index-of≢index-of≃ {zs = _ ∷ _} (inj₂ p) (inj₂ q) =
  Distinct (fsuc (index-of p)) (fsuc (index-of q))                    ↔⟨⟩

  Distinct (index-of p) (index-of q)                                  ↝⟨ index-of≢index-of≃ p q ⟩

  Distinct fzero (index-of (_≃_.to (∈≃≡⊎∈delete p) q))                ↔⟨ lemma (_≃_.to (∈≃≡⊎∈delete p) q) ⟩

  Distinct fzero
    (index-of $
     _↔_.to
       (inverse ⊎-assoc F.∘ (⊎-comm ⊎-cong id) F.∘ ⊎-assoc)
       (inj₂ (_≃_.to (∈≃≡⊎∈delete p) q)))                             ↔⟨⟩

  Distinct fzero (index-of (_≃_.to (∈≃≡⊎∈delete (inj₂ p)) (inj₂ q)))  □
  where
  lemma :
    (p : x ∈ y ∷ zs) →
    Distinct fzero (index-of p) ≃
    Distinct fzero
      (index-of {xs = y ∷ z ∷ zs} $
       _↔_.to (inverse ⊎-assoc F.∘ (⊎-comm ⊎-cong id) F.∘ ⊎-assoc)
         (inj₂ p))
  lemma (inj₁ _) = id
  lemma (inj₂ _) = id

-- Insertion x xs ys means that ys is the result of inserting x
-- somewhere in xs. This definition is based on one due to the Zulip
-- user glyph
-- (https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/Counting.20elements.20in.20a.20.28family.20of.29.20type.28s.29/near/283317566).

data Insertion {A : Type a} : A → List A → List A → Type a where
  here  : x ∷ xs ≡ ys → Insertion x xs ys
  there : x ≡ y → Insertion z xs ys → Insertion z (x ∷ xs) (y ∷ ys)

-- One can express Insertion using _∈_ and delete.

Insertion≃ :
  {xs ys : List A} →
  Insertion x xs ys ≃ ∃ λ (p : x ∈ ys) → xs ≡ delete p
Insertion≃ {x = x} = Eq.↔→≃ to from to-from from-to
  where
  to : Insertion x xs ys → ∃ λ (p : x ∈ ys) → xs ≡ delete p
  to {ys = []}    (here p) = ⊥-elim (List.[]≢∷ (sym p))
  to {ys = _ ∷ _} (here p) =
    let p₁ , p₂ = _↔_.to ∷≡∷↔≡×≡ p in
    inj₁ p₁ , p₂
  to (there p q) = Σ-map inj₂ (cong₂ _∷_ p) (to q)

  from : (∃ λ (p : x ∈ ys) → xs ≡ delete p) → Insertion x xs ys
  from {ys = _ ∷ _}              (inj₁ p , q) = here (cong₂ _∷_ p q)
  from {ys = _ ∷ _} {xs = []}    (inj₂ p , q) = ⊥-elim (List.[]≢∷ q)
  from {ys = _ ∷ _} {xs = _ ∷ _} (inj₂ p , q) =
    let q₁ , q₂ = _↔_.to ∷≡∷↔≡×≡ q in
    there q₁ (from (p , q₂))

  to-from : (p : ∃ λ (p : x ∈ ys) → xs ≡ delete p) → to (from p) ≡ p
  to-from {ys = _ ∷ _} (inj₁ p , q) =
    let p′ , q′ = _↔_.to ∷≡∷↔≡×≡ (cong₂ _∷_ p q) in

    inj₁ p′ , q′  ≡⟨ cong (λ (p , q) → inj₁ p , q) $ _↔_.right-inverse-of ∷≡∷↔≡×≡ _ ⟩∎
    inj₁ p , q    ∎
  to-from {ys = _ ∷ _} {xs = []} (inj₂ p , q) =
    ⊥-elim (List.[]≢∷ q)
  to-from {ys = _ ∷ _} {xs = _ ∷ _} (inj₂ p , q) =
    Σ-map inj₂
      (cong₂ _∷_ (proj₁ (_↔_.to ∷≡∷↔≡×≡ q)))
      (to (from (p , proj₂ (_↔_.to ∷≡∷↔≡×≡ q))))     ≡⟨ cong (Σ-map inj₂ (cong₂ _∷_ (proj₁ (_↔_.to ∷≡∷↔≡×≡ q)))) $ to-from _ ⟩

    Σ-map inj₂
      (cong₂ _∷_ (proj₁ (_↔_.to ∷≡∷↔≡×≡ q)))
      (p , proj₂ (_↔_.to ∷≡∷↔≡×≡ q))                 ≡⟨⟩

    inj₂ p , uncurry (cong₂ _∷_) (_↔_.to ∷≡∷↔≡×≡ q)  ≡⟨ cong (inj₂ p ,_) $ _↔_.left-inverse-of ∷≡∷↔≡×≡ _ ⟩∎

    inj₂ p , q                                       ∎

  from-to : (p : Insertion x xs ys) → from (to p) ≡ p
  from-to {ys = []}    (here p) = ⊥-elim (List.[]≢∷ (sym p))
  from-to {ys = _ ∷ _} (here p) =
    here (uncurry (cong₂ _∷_) (_↔_.to ∷≡∷↔≡×≡ p))  ≡⟨ cong here $ _↔_.left-inverse-of ∷≡∷↔≡×≡ _ ⟩∎
    here p                                         ∎
  from-to (there p q) =
    let to-q₁ , to-q₂ = _↔_.to ∷≡∷↔≡×≡ (cong₂ _∷_ p (proj₂ (to q))) in

    there to-q₁ (from (proj₁ (to q) , to-q₂))  ≡⟨ cong (λ (to-q₁ , to-q₂) → there to-q₁ (from (proj₁ (to q) , to-q₂))) $
                                                  _↔_.right-inverse-of ∷≡∷↔≡×≡ _ ⟩
    there p (from (to q))                      ≡⟨ cong (there p) (from-to q) ⟩∎
    there p q                                  ∎

------------------------------------------------------------------------
-- Two more definitions of bag equivalence

-- A definition of bag equivalence based on one due to the Zulip user
-- glyph
-- (https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/Counting.20elements.20in.20a.20.28family.20of.29.20type.28s.29/near/283317566).

infix 4 _≈-bag″_

data _≈-bag″_ {A : Type a} : List A → List A → Type a where
  []   : [] ≈-bag″ []
  cons : Insertion x ys zs → xs ≈-bag″ ys → x ∷ xs ≈-bag″ zs

-- The type [] ≈-bag″ xs is a proposition.

[]≈″-propositional : Is-proposition ([] ≈-bag″ xs)
[]≈″-propositional {xs = []}    [] [] = refl _
[]≈″-propositional {xs = _ ∷ _} _  ()

-- A variant of _≈-bag″_.

infix 4 _≈-bag‴_

_≈-bag‴_ : {A : Type a} → List A → List A → Type a
[]     ≈-bag‴ ys = [] ≡ ys
x ∷ xs ≈-bag‴ ys = ∃ λ (p : x ∈ ys) → xs ≈-bag‴ delete p

-- The type ×s ≈-bag″ ys is equivalent to xs ≈-bag‴ ys.

≈″≃≈‴ : (xs ≈-bag″ ys) ≃ (xs ≈-bag‴ ys)
≈″≃≈‴ {xs = xs} = Eq.↔→≃ to (from xs) (to-from xs) from-to
  where
  to : ∀ {xs} → xs ≈-bag″ ys → xs ≈-bag‴ ys
  to []                   = refl _
  to (cons {xs = xs} p q) =
    let x∈ , eq = _≃_.to Insertion≃ p in
    x∈ , subst (xs ≈-bag‴_) eq (to q)

  from : ∀ xs → xs ≈-bag‴ ys → xs ≈-bag″ ys
  from []       p       = subst ([] ≈-bag″_) p []
  from (_ ∷ xs) (p , q) =
    cons (_≃_.from Insertion≃ (p , refl _)) (from xs q)

  to-from : ∀ xs (p : xs ≈-bag‴ ys) → to (from xs p) ≡ p
  to-from [] p =
    to (subst ([] ≈-bag″_) p [])  ≡⟨ elim¹
                                       (λ p → to (subst ([] ≈-bag″_) p []) ≡ p)
                                       (cong to $ subst-refl _ _)
                                       _ ⟩∎
    p                             ∎
  to-from (_ ∷ xs) (p , q) =
    proj₁ lemma₁ , subst (xs ≈-bag‴_) (proj₂ lemma₁) (to (from xs q))  ≡⟨ Σ-≡,≡→≡
                                                                            (cong proj₁ lemma₂)
                                                                            (
      subst ((xs ≈-bag‴_) ∘ delete)
        (cong proj₁ lemma₂)
        (subst (xs ≈-bag‴_) (proj₂ lemma₁) (to (from xs q)))                 ≡⟨ elim₁
                                                                                  (λ {lemma₁} lemma₂ →
                                                                                     subst ((xs ≈-bag‴_) ∘ delete)
                                                                                       (cong proj₁ lemma₂)
                                                                                       (subst (xs ≈-bag‴_) (proj₂ lemma₁) (to (from xs q))) ≡
                                                                                     q)
                                                                                  (
        subst ((xs ≈-bag‴_) ∘ delete)
          (cong proj₁ (refl _))
          (subst (xs ≈-bag‴_) (refl _) (to (from xs q)))                           ≡⟨ D.trans (sym $ subst-∘ _ _ _) $
                                                                                      subst-refl _ _ ⟩

        subst (xs ≈-bag‴_) (refl _) (to (from xs q))                               ≡⟨ subst-refl _ _ ⟩

        to (from xs q)                                                             ≡⟨ to-from xs q ⟩∎

        q                                                                          ∎)
                                                                                  lemma₂ ⟩∎
      q                                                                      ∎) ⟩∎

    p , q                                                              ∎
    where
    lemma₁ =
      _≃_.to Insertion≃ (_≃_.from Insertion≃ (p , refl (delete p)))

    lemma₂ : lemma₁ ≡ (p , refl (delete p))
    lemma₂ = _≃_.right-inverse-of Insertion≃ (p , refl _)

  from-to : ∀ {xs} (p : xs ≈-bag″ ys) → from xs (to p) ≡ p
  from-to [] =
    subst ([] ≈-bag″_) (refl _) []  ≡⟨ subst-refl _ _ ⟩∎
    []                              ∎
  from-to (cons {xs = xs} p q) =
    let x∈ , eq = _≃_.to Insertion≃ p in

    cons (_≃_.from Insertion≃ (x∈ , refl _))
      (from xs (subst (xs ≈-bag‴_) eq (to q)))          ≡⟨ elim₁
                                                             (λ {ys} eq →
                                                                (q : _ ≈-bag″ ys) →
                                                                cons (_≃_.from Insertion≃ (x∈ , refl _))
                                                                  (from xs (subst (xs ≈-bag‴_) eq (to q))) ≡
                                                                cons (_≃_.from Insertion≃ (x∈ , eq)) (from xs (to q)))
                                                             (λ q →
      cons (_≃_.from Insertion≃ (x∈ , refl _))
        (from xs (subst (xs ≈-bag‴_) (refl _) (to q)))          ≡⟨ cong (cons _ ∘ from xs) $ subst-refl _ _ ⟩∎

      cons (_≃_.from Insertion≃ (x∈ , refl _))
        (from xs (to q))                                        ∎)
                                                             eq q ⟩

    cons (_≃_.from Insertion≃ (x∈ , eq))
      (from xs (to q))                                  ≡⟨ cong (flip cons (from xs (to q))) $
                                                           _≃_.left-inverse-of Insertion≃ _ ⟩

    cons p (from xs (to q))                             ≡⟨ cong (cons _) $ from-to q ⟩∎

    cons p q                                            ∎

-- If two membership proofs, one for x and one for y, point to the
-- same position in a list, then x is equal to y.

index-of≡index-of→≡ :
  {zs : List A} (p : x ∈ zs) (q : y ∈ zs) →
  index-of p ≡ index-of q →
  x ≡ y
index-of≡index-of→≡ {x = x} {y = y} {zs = z ∷ _} (inj₁ p) (inj₁ q) _ =
  x  ≡⟨ p ⟩
  z  ≡⟨ sym q ⟩∎
  y  ∎
index-of≡index-of→≡ {zs = _ ∷ _} (inj₂ p) (inj₂ q) r =
  index-of≡index-of→≡ p q (⊎.cancel-inj₂ r)
index-of≡index-of→≡ {zs = _ ∷ _} (inj₁ p) (inj₂ q) r =
  ⊥-elim $ ⊎.inj₁≢inj₂ r
index-of≡index-of→≡ {zs = _ ∷ _} (inj₂ p) (inj₁ q) r =
  ⊥-elim $ ⊎.inj₁≢inj₂ (sym r)

-- A "computation rule" for index-of≡index-of→≡.

index-of≡index-of→≡-refl :
  {zs : List A} (p : x ∈ zs) →
  index-of≡index-of→≡ p p (refl (index-of p)) ≡ refl x
index-of≡index-of→≡-refl {x = x} {zs = z ∷ _} (inj₁ p) =
  D.trans p (sym p)  ≡⟨ trans-symʳ _ ⟩∎
  refl x             ∎
index-of≡index-of→≡-refl {x = x} {zs = _ ∷ _} (inj₂ p) =
  index-of≡index-of→≡ p p (⊎.cancel-inj₂ (refl (inj₂ (index-of p))))  ≡⟨ cong (index-of≡index-of→≡ p p) $ cong-refl _ ⟩
  index-of≡index-of→≡ p p (refl (index-of p))                         ≡⟨ index-of≡index-of→≡-refl p ⟩∎
  refl x                                                              ∎

-- The type ×s ≈-bag ys is equivalent to xs ≈-bag‴ ys (assuming
-- extensionality).

≈≃≈‴ :
  {A : Type a} (xs {ys} : List A) →
  xs ≈-bag ys ↝[ a ∣ a ] xs ≈-bag‴ ys
≈≃≈‴ {a = a} [] {ys = ys} ext =
  (∀ z → ⊥ ≃ (z ∈ ys))  ↝⟨ (∀-cong ext λ _ → ≃⊥≃¬ ext F.∘ ≃-comm ext) ⟩
  (∀ z → ¬ z ∈ ys)      ↝⟨ generalise-ext?
                             (record { to = to ys; from = from })
                             (λ ext → to-from ys , from-to ext)
                             ext ⟩□
  [] ≡ ys               □
  where
  to : ∀ ys → (∀ z → ¬ z ∈ ys) → [] ≡ ys
  to []      _ = refl _
  to (y ∷ _) p = ⊥-elim $ p y (inj₁ (refl _))

  from : ∀ {ys} → [] ≡ ys → ∀ z → ¬ z ∈ ys
  from eq z p = ⊥-elim $ subst (z ∈_) (sym eq) p

  to-from : ∀ ys p → to ys (from p) ≡ p
  to-from [] p =
    refl []  ≡⟨ H-level.mono₁ 0 (_⇔_.from contractible⇔↔⊤ []≡[]↔⊤) _ _ ⟩∎
    p        ∎
  to-from (_ ∷ _) p = ⊥-elim $ List.[]≢∷ p

  from-to :
    Extensionality a a →
    ∀ p → from (to ys p) ≡ p
  from-to ext _ =
    (Π-closure ext 1 λ _ →
     ¬-propositional
       (lower-extensionality lzero _ ext))
      _ _

≈≃≈‴ {a = a} (x ∷ xs) {ys = ys} ext =
  (∀ z → (z ∈ x ∷ xs) ≃ (z ∈ ys))                               ↝⟨ generalise-ext?
                                                                     (record { to = to; from = from })
                                                                     (λ ext → to-from ext , from-to ext)
                                                                     ext ⟩
  (∃ λ (p : x ∈ ys) →
   ∀ z →
   (z ∈ xs) ≃
   (∃ λ (q : z ∈ ys) → Distinct (index-of p) (index-of q)))     ↝⟨ (∃-cong λ p → ∀-cong ext λ _ → ≃-cong ext id $ ∃-cong λ _ →
                                                                    index-of≢index-of≃ p _) ⟩
  (∃ λ (p : x ∈ ys) →
   ∀ z →
   (z ∈ xs) ≃
   (∃ λ (q : z ∈ ys) →
    Distinct fzero (index-of (_≃_.to (∈≃≡⊎∈delete p) q))))      ↝⟨ (∃-cong λ p → ∀-cong ext λ _ → ≃-cong ext id $
                                                                    Σ-cong (∈≃≡⊎∈delete p) λ _ → id) ⟩
  (∃ λ (p : x ∈ ys) →
   ∀ z →
   (z ∈ xs) ≃
   (∃ λ (q : z ∈ x ∷ delete p) → Distinct fzero (index-of q)))  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ≃-cong ext id ∃-Distinct-fzero≃) ⟩

  (∃ λ (p : x ∈ ys) → ∀ z → (z ∈ xs) ≃ (z ∈ delete p))          ↝⟨ (∃-cong λ _ → ≈≃≈‴ xs ext) ⟩□

  (∃ λ (p : x ∈ ys) → xs ≈-bag‴ delete p)                       □
  where
  ∃-Distinct-fzero≃ :
    ∀ {x y} {ys : List A} →
    (∃ λ (p : x ∈ y ∷ ys) → Distinct fzero (index-of p)) ≃ (x ∈ ys)
  ∃-Distinct-fzero≃ = Eq.↔→≃
    (λ { (inj₂ x , _) → x })
    (λ x → inj₂ x , _)
    refl
    (λ { (inj₂ _ , _) → refl _ })

  to :
    (∀ z → (z ∈ x ∷ xs) ≃ (z ∈ ys)) →
    ∃ λ (p : x ∈ ys) →
    ∀ z →
    (z ∈ xs) ≃
    (∃ λ (q : z ∈ ys) → Distinct (index-of p) (index-of q))
  to p =
      _≃_.to (p x) (inj₁ (refl _))
    , λ z →
        z ∈ xs                                                ↝⟨ inverse ∃-Distinct-fzero≃ ⟩

        (∃ λ (q : z ∈ x ∷ xs) → Distinct fzero (index-of q))  ↝⟨ (Σ-cong (p z) λ q → ≡⇒↝ _ $ cong (Distinct fzero ∘ index-of) $ sym $
                                                                  _≃_.left-inverse-of (p z) q) ⟩
        (∃ λ (q : z ∈ ys) →
         Distinct fzero (index-of (_≃_.from (p z) q)))        ↝⟨ ∃-cong lemma ⟩□

        (∃ λ (q : z ∈ ys) →
         Distinct (index-of (_≃_.to (p x) (inj₁ (refl _))))
           (index-of q))                                      □
    where abstract
    lemma :
      ∀ q →
      Distinct fzero (index-of (_≃_.from (p z) q)) ≃
      Distinct (index-of (_≃_.to (p x) (inj₁ (refl x)))) (index-of q)
    lemma {z = z} q =
      _↠_.from
        (Eq.≃↠⇔
           (Finite.Distinct-propositional
              fzero {j = index-of (_≃_.from (p z) q)})
           (Finite.Distinct-propositional
              (index-of (_≃_.to (p x) (inj₁ (refl x))))))
        (Distinct fzero (index-of (_≃_.from (p z) q))          ↝⟨ Finite.Distinct↔≢ _ ⟩

         fzero ≢ index-of (_≃_.from (p z) q)                   ↝⟨ →-cong₁ _ ≡-comm ⟩

         index-of (_≃_.from (p z) q) ≢ fzero                   ↝⟨ ≡⇒↝ _ $ cong (_≢ _) $ index-of-commutes (inverse ∘ p) _ ⟩

         _↔_.from (Fin-length-cong p) (index-of q) ≢ fzero     ↝⟨ →-cong₁ _ $ from≡↔≡to (Eq.↔⇒≃ $ Fin-length-cong p) ⟩

         index-of q ≢ _↔_.to (Fin-length-cong p) fzero         ↝⟨ ≡⇒↝ _ $ cong (_ ≢_) $ sym $ index-of-commutes p _ ⟩

         index-of q ≢ index-of (_≃_.to (p x) (inj₁ (refl x)))  ↝⟨ →-cong₁ _ ≡-comm ⟩

         index-of (_≃_.to (p x) (inj₁ (refl x))) ≢ index-of q  ↝⟨ inverse $ Finite.Distinct↔≢ _ ⟩□

         Distinct (index-of (_≃_.to (p x) (inj₁ (refl x))))
           (index-of q)                                        □)

  from :
    (∃ λ (p : x ∈ ys) →
     ∀ z →
     (z ∈ xs) ≃
     (∃ λ (q : z ∈ ys) → Distinct (index-of p) (index-of q))) →
    ∀ z → (z ∈ x ∷ xs) ≃ (z ∈ ys)
  from (p , q) z =
    Eq.↔→≃
      to′
      (λ r → from′ r (index-of r Fin.≟ index-of p))
      (λ r → to′-from′ r (index-of r Fin.≟ index-of p))
      (λ r → from′-to′ r _)
    where
    to′ : z ∈ x ∷ xs → z ∈ ys
    to′ =
      [ flip (subst (_∈ ys)) p ∘ sym
      , (λ r → proj₁ $ _≃_.to (q z) r)
      ]

    from′ :
      (r : z ∈ ys) →
      Dec (index-of r ≡ index-of p) →
      z ∈ x ∷ xs
    from′ r (yes r≡p) =
      inj₁
        (z  ≡⟨ index-of≡index-of→≡ r p r≡p ⟩∎
         x  ∎)
    from′ r (no r≢p) =
      inj₂ (_≃_.from (q z)
              (r , _⇔_.from (Finite.Distinct↔≢ _) (r≢p ∘ sym)))

    abstract

      to′-from′ :
        (r : z ∈ ys) (s : Dec (index-of r ≡ index-of p)) →
        to′ (from′ r s) ≡ r
      to′-from′ r (no r≢p) =
        proj₁ (_≃_.to (q z) (_≃_.from (q z) (r , _)))  ≡⟨ cong proj₁ $ _≃_.right-inverse-of (q z) _ ⟩∎
        r                                              ∎
      to′-from′ r (yes r≡p) = lemma _ _ _ _
        where
        lemma :
          ∀ ys (p : x ∈ ys) (r : z ∈ ys)
          (r≡p : index-of r ≡ index-of p) →
          subst (_∈ ys) (sym (index-of≡index-of→≡ r p r≡p)) p ≡ r
        lemma (y ∷ ys) (inj₁ p) (inj₁ r) r≡p =
          subst (_∈ y ∷ ys) (sym (D.trans r (sym p))) (inj₁ p)  ≡⟨ push-subst-inj₁ _ _ ⟩
          inj₁ (subst (_≡ y) (sym (D.trans r (sym p))) p)       ≡⟨ cong inj₁ $ subst-trans _ ⟩
          inj₁ (D.trans (D.trans r (sym p)) p)                  ≡⟨ cong inj₁ $ trans-[trans-sym]- _ _ ⟩∎
          inj₁ r                                                ∎
        lemma (y ∷ ys) (inj₂ p) (inj₂ r) r≡p =
          subst (_∈ y ∷ ys)
            (sym (index-of≡index-of→≡ r p (⊎.cancel-inj₂ r≡p)))
            (inj₂ p)                                                ≡⟨ push-subst-inj₂ _ _ ⟩

          inj₂
            (subst (_∈ ys)
               (sym (index-of≡index-of→≡ r p (⊎.cancel-inj₂ r≡p)))
               p)                                                   ≡⟨ cong inj₂ $ lemma _ _ _ _ ⟩∎

          inj₂ r                                                    ∎
        lemma (_ ∷ _) (inj₁ _) (inj₂ _) r≡p =
          ⊥-elim $ ⊎.inj₁≢inj₂ (sym r≡p)
        lemma (_ ∷ _) (inj₂ _) (inj₁ _) r≡p =
          ⊥-elim $ ⊎.inj₁≢inj₂ r≡p

      from′-to′ :
        (r : z ∈ x ∷ xs) (s : Dec (index-of (to′ r) ≡ index-of p)) →
        from′ (to′ r) s ≡ r
      from′-to′ (inj₁ r) (yes to′r≡p) =
        inj₁ (index-of≡index-of→≡ (subst (_∈ ys) (sym r) p) p to′r≡p)  ≡⟨ cong inj₁ $
                                                                          elim¹
                                                                            (λ r →
                                                                               ∀ p to′r≡p →
                                                                               index-of≡index-of→≡ (subst (_∈ ys) (sym r) p) p to′r≡p ≡ r)
                                                                            (λ p to′r≡p →
          index-of≡index-of→≡ (subst (_∈ ys) (sym (refl _)) p) p
            to′r≡p                                                             ≡⟨ cong (index-of≡index-of→≡ _ p) $
                                                                                  Fin-set _ _ _ ⟩
          index-of≡index-of→≡ (subst (_∈ ys) (sym (refl _)) p) p
            (cong index-of
               (D.trans (cong (flip (subst (_∈ ys)) p) sym-refl) $
                subst-refl _ _))                                               ≡⟨ elim₁
                                                                                    (λ {p′} (eq : p′ ≡ p) →
                                                                                       index-of≡index-of→≡ p′ p (cong index-of eq) ≡
                                                                                       index-of≡index-of→≡ p p (refl _))
                                                                                    (cong (index-of≡index-of→≡ _ p) $ cong-refl _)
                                                                                    _ ⟩

          index-of≡index-of→≡ p p (refl _)                                     ≡⟨ index-of≡index-of→≡-refl p ⟩∎

          refl _                                                               ∎)
                                                                            _ _ _ ⟩∎
        inj₁ r                                                         ∎
      from′-to′ (inj₂ r) (yes to′r≡p) =
        ⊥-elim $ _⇔_.to (Finite.Distinct↔≢ _) (proj₂ (_≃_.to (q z) r))
          (index-of p                         ≡⟨ sym to′r≡p ⟩
           index-of (to′ (inj₂ r))            ≡⟨⟩
           index-of (proj₁ (_≃_.to (q z) r))  ∎)
      from′-to′ (inj₂ r) (no _) =
        inj₂ (_≃_.from (q z) (proj₁ (_≃_.to (q z) r) , _))  ≡⟨ cong inj₂ $ cong (_≃_.from (q z)) $ cong (_ ,_) $
                                                               Finite.Distinct-propositional (index-of p) _ _ ⟩
        inj₂ (_≃_.from (q z) (_≃_.to (q z) r))              ≡⟨ cong inj₂ $ _≃_.left-inverse-of (q z) _ ⟩∎
        inj₂ r                                              ∎
      from′-to′ (inj₁ r) (no to′r≢p) =                   $⟨ to′r≢p ⟩
        index-of (subst (_∈ ys) (sym r) p) ≢ index-of p  →⟨ _∘ D.trans
                                                                 (elim¹
                                                                    (λ r → ∀ p → index-of (subst (_∈ ys) (sym r) p) ≡ index-of p)
                                                                    (λ _ → cong index-of $
                                                                           D.trans (cong (flip (subst (_∈ ys)) _) sym-refl) $
                                                                           subst-refl _ _)
                                                                    r p) ⟩
        index-of p ≢ index-of p                          →⟨ _$ refl _ ⟩
        ⊥                                                →⟨ ⊥-elim ⟩□
        _                                                □

  abstract

    to-from :
      Extensionality a a →
      (p : ∃ λ (p : x ∈ ys) →
           ∀ z →
           (z ∈ xs) ≃
           (∃ λ (q : z ∈ ys) → Distinct (index-of p) (index-of q))) →
      to (from p) ≡ p
    to-from ext (p , q) =
      Σ-≡,≡→≡
        (subst (_∈ ys) (sym (refl x)) p  ≡⟨ D.trans (cong (flip (subst (_∈ ys)) _) sym-refl) $
                                            subst-refl _ _ ⟩∎
         p                               ∎)
        (apply-ext ext λ z →
         Eq.lift-equality ext $
         apply-ext ext λ r →
         Σ-≡,≡→≡
           (proj₁ $
            _≃_.to
              (subst
                 (λ p →
                    ∀ z →
                    (z ∈ xs) ≃
                    (∃ λ (q : z ∈ ys) →
                     Distinct (index-of p) (index-of q)))
                 _ _ z)
              r                                            ≡⟨ cong (λ eq → proj₁ $ _≃_.to eq r) $ sym $
                                                              push-subst-application _ _ ⟩
            proj₁ $
            _≃_.to
              (subst
                 (λ p →
                    (z ∈ xs) ≃
                    (∃ λ (q : z ∈ ys) →
                     Distinct (index-of p) (index-of q)))
                 _ _)
              r                                            ≡⟨ cong proj₁ $ cong (_$ r)
                                                              Eq.to-subst ⟩
            proj₁ $
            subst
              (λ p →
                 z ∈ xs →
                 ∃ λ (q : z ∈ ys) →
                 Distinct (index-of p) (index-of q))
              _ _ r                                        ≡⟨ cong proj₁ $ sym $
                                                              push-subst-application _ _ ⟩
            proj₁ $
            subst
              (λ p →
                 ∃ λ (q : z ∈ ys) →
                 Distinct (index-of p) (index-of q))
              _ _                                          ≡⟨ cong proj₁ $ push-subst-pair _ _ ⟩

            subst (λ _ → z ∈ ys) _
              (proj₁ (_≃_.to (q z) r))                     ≡⟨ subst-const _ ⟩∎

            proj₁ (_≃_.to (q z) r)                         ∎)
           (Finite.Distinct-propositional (index-of p) _ _))

    from-to :
      Extensionality a a →
      (p : ∀ z → (z ∈ x ∷ xs) ≃ (z ∈ ys)) →
      from (to p) ≡ p
    from-to ext p =
      apply-ext ext λ z →
      Eq.lift-equality ext $
      apply-ext ext λ where
        (inj₂ q) → _≃_.to (p z) (inj₂ q)  ∎
        (inj₁ q) →
          subst (_∈ ys) (sym q) (_≃_.to (p x) (inj₁ (refl _)))  ≡⟨ elim₁
                                                                     (λ {z} q →
                                                                        subst (_∈ ys) (sym q) (_≃_.to (p x) (inj₁ (refl _))) ≡
                                                                        _≃_.to (p z) (inj₁ q))
                                                                     (D.trans (cong (flip (subst (_∈ ys)) _) sym-refl) $
                                                                      subst-refl _ _)
                                                                     _ ⟩∎
          _≃_.to (p z) (inj₁ q)                                 ∎

-- The type ×s ≈-bag ys is equivalent to xs ≈-bag″ ys (assuming
-- extensionality).

≈≃≈″ :
  {A : Type a} {xs ys : List A} →
  (xs ≈-bag ys) ↝[ a ∣ a ] (xs ≈-bag″ ys)
≈≃≈″ {xs = xs} {ys = ys} ext =
  xs ≈-bag ys   ↝⟨ ≈≃≈‴ xs ext ⟩
  xs ≈-bag‴ ys  ↔⟨ inverse ≈″≃≈‴ ⟩□
  xs ≈-bag″ ys  □

------------------------------------------------------------------------
-- Yet another definition of bag equivalence

-- A definition of bag equivalence that is taken from Coq's standard
-- library.

infixr 5 _∷_
infix  4 _≈-bag⁗_

data _≈-bag⁗_ {A : Type a} : List A → List A → Type a where
  []    : [] ≈-bag⁗ []
  _∷_   : ∀ x {xs ys} (xs≈ys : xs ≈-bag⁗ ys) → x ∷ xs ≈-bag⁗ x ∷ ys
  swap  : ∀ {x y xs} → x ∷ y ∷ xs ≈-bag⁗ y ∷ x ∷ xs
  trans : ∀ {xs ys zs}
          (xs≈ys : xs ≈-bag⁗ ys) (ys≈zs : ys ≈-bag⁗ zs) → xs ≈-bag⁗ zs

-- _∷_ preserves _∼[ k ]_.

infixr 5 _∷-cong_

_∷-cong_ : x ≡ y → xs ∼[ k ] ys → x ∷ xs ∼[ k ] y ∷ ys
_∷-cong_ {x = x} {y = y} {xs = xs} {ys = ys} x≡y xs≈ys = λ z →
  z ≡ x ⊎ z ∈ xs  ↝⟨ from-bijection (flip-trans-isomorphism x≡y) ⊎-cong xs≈ys z ⟩□
  z ≡ y ⊎ z ∈ ys  □

-- We can swap the first two elements of a list.

swap-first-two : x ∷ y ∷ xs ≈-bag y ∷ x ∷ xs
swap-first-two {x = x} {y = y} {xs = xs} = λ z →
   z ≡ x ⊎ z ≡ y  ⊎ z ∈ xs  ↔⟨ ⊎-assoc ⟩
  (z ≡ x ⊎ z ≡ y) ⊎ z ∈ xs  ↔⟨ ⊎-comm ⊎-cong id ⟩
  (z ≡ y ⊎ z ≡ x) ⊎ z ∈ xs  ↔⟨ inverse ⊎-assoc ⟩
   z ≡ y ⊎ z ≡ x  ⊎ z ∈ xs  □

-- The type ×s ≈-bag ys is logically equivalent to xs ≈-bag″ ys.

≈⇔≈⁗ : xs ≈-bag ys ⇔ xs ≈-bag⁗ ys
≈⇔≈⁗ {xs = xs} {ys = ys} = record
  { from = from
  ; to   =
      xs ≈-bag  ys  →⟨ ≈≃≈‴ _ _ ⟩
      xs ≈-bag‴ ys  →⟨ to ⟩□
      xs ≈-bag⁗ ys  □
  }
  where
  from : {xs ys : List A} → xs ≈-bag⁗ ys → xs ≈-bag ys
  from []                  = λ _ → id
  from (x ∷ xs≈ys)         = refl _ ∷-cong from xs≈ys
  from swap                = swap-first-two
  from (trans xs≈ys ys≈zs) = λ z → _ ↔⟨ from xs≈ys z ⟩ from ys≈zs z

  refl-≈ : (xs : List A) → xs ≈-bag⁗ xs
  refl-≈ []       = []
  refl-≈ (x ∷ xs) = x ∷ refl-≈ xs

  ≈-∷-delete :
    {xs : List A} (p : x ∈ xs) →
    x ∷ delete p ≈-bag⁗ xs
  ≈-∷-delete {xs = _ ∷ _} (inj₁ p) =
    subst (λ x → _ ≈-bag⁗ x ∷ _) p (refl-≈ _)
  ≈-∷-delete {xs = _ ∷ _} (inj₂ p) =
    trans swap (_ ∷ ≈-∷-delete p)

  cons′ :
    {xs ys : List A} (p : x ∈ ys) →
    xs ≈-bag⁗ delete p → x ∷ xs ≈-bag⁗ ys
  cons′ {ys = _ ∷ _} (inj₁ p) q =
    subst (λ x → _ ≈-bag⁗ x ∷ _) p (_ ∷ q)
  cons′ {ys = _ ∷ _} (inj₂ p) q =
    trans (_ ∷ q) $
    trans swap $
    _ ∷ ≈-∷-delete p

  to : {xs ys : List A} → xs ≈-bag‴ ys → xs ≈-bag⁗ ys
  to {xs = []}    p       = subst ([] ≈-bag⁗_) p []
  to {xs = _ ∷ _} (p , q) = cons′ p (to q)

-- However, it is not the case that, for all lists xs and ys of type
-- List A, there is a split surjection from xs ≈-bag″ ys to
-- xs ≈-bag⁗ ys.

¬≈″↠≈⁗ : ¬ ({xs ys : List A} → xs ≈-bag″ ys ↠ xs ≈-bag⁗ ys)
¬≈″↠≈⁗ {A = A} =
  ({xs ys : List A} → xs ≈-bag″ ys ↠ xs ≈-bag⁗ ys)  →⟨ (λ hyp → hyp) ⟩

  ([] ≈-bag″ [] ↠ [] ≈-bag⁗ ([] ⦂ List A))          →⟨ (λ hyp → H-level.respects-surjection hyp 1 []≈″-propositional) ⟩

  Is-proposition ([] ≈-bag⁗ [])                     →⟨ (λ hyp → p₁≢p₂ (hyp _ _)) ⟩□

  ⊥                                                 □
  where
  p₁ p₂ : [] ≈-bag⁗ ([] ⦂ List A)
  p₁ = []
  p₂ = trans [] []

  p₁≢p₂ : p₁ ≢ p₂
  p₁≢p₂ p₁≡p₂ = subst id (cong is-[] p₁≡p₂) _
    where
    is-[] : [] ≈-bag⁗ ([] ⦂ List A) → Type
    is-[] []          = ⊤
    is-[] (trans _ _) = ⊥
