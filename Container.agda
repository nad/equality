------------------------------------------------------------------------
-- Containers, including a definition of bag equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container where

open import Bag-equality using (Kind; bag)
open import Equivalence hiding (id; _∘_; inverse)
open import Equality.Propositional
open import Prelude hiding (List; map; lookup)

import Bijection
open Bijection equality-with-J using (_↔_; module _↔_)
import Function-universe
open Function-universe equality-with-J
  hiding (id; Kind) renaming (_∘_ to _⟨∘⟩_)

------------------------------------------------------------------------
-- Containers

record Container : Set₁ where
  constructor _▷_
  field
    Shape    : Set
    Position : Shape → Set

open Container

-- Interpretation of containers.

⟦_⟧ : Container → Set → Set
⟦ S ▷ P ⟧ A = ∃ λ (s : S) → (P s → A)

-- Some examples.

module Examples where

  -- Lists.

  List : Container
  List = ℕ ▷ Fin

  -- Streams.

  Stream : Container
  Stream = ⊤ ▷ const ℕ

  -- Finite binary trees with information in the internal nodes.

  data S : Set where
    leaf  : S
    node  : S → S → S

  P : S → Set
  P leaf       = ⊥
  P (node l r) = P l ⊎ ⊤ ⊎ P r

  Tree : Container
  Tree = S ▷ P

------------------------------------------------------------------------
-- Some projections

-- The shape of something.

shape : ∀ {C A} → ⟦ C ⟧ A → Shape C
shape = proj₁

-- A lookup function.

lookup : ∀ {C A} (xs : ⟦ C ⟧ A) → Position C (shape xs) → A
lookup = proj₂

------------------------------------------------------------------------
-- Map

-- Containers are functors.

map : ∀ {C X Y} → (X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Σ-map id (λ g → f ∘ g)

module Map where

  identity : ∀ {C X} (xs : ⟦ C ⟧ X) → map id xs ≡ xs
  identity xs = refl

  composition : ∀ {C X Y Z} (f : Y → Z) (g : X → Y) (xs : ⟦ C ⟧ X) →
                map f (map g xs) ≡ map (f ∘ g) xs
  composition f g xs = refl

------------------------------------------------------------------------
-- Any, _∈_, bag equality and similar relations

-- Definition of Any for containers.

Any :  {C : Container} {A : Set} →
       (A → Set) → (⟦ C ⟧ A → Set)
Any {S ▷ P} Q (s , f) = ∃ λ (p : P s) → Q (f p)

-- Membership predicate.

infix 4 _∈_

_∈_ : {C : Container} {A : Set} → A → ⟦ C ⟧ A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

-- Bag equality etc. Note that the containers can be different as long
-- as the elements they contain have equal types.

infix 4 _∼[_]_

_∼[_]_ : ∀ {C₁ C₂ A} → ⟦ C₁ ⟧ A → Kind → ⟦ C₂ ⟧ A → Set
xs ∼[ k ] ys = ∀ z → z ∈ xs ↝[ k ] z ∈ ys

-- Bag equality.

infix 4 _≈-bag_

_≈-bag_ : {C₁ C₂ : Container} {A : Set} → ⟦ C₁ ⟧ A → ⟦ C₂ ⟧ A → Set
xs ≈-bag ys = xs ∼[ bag ] ys

------------------------------------------------------------------------
-- Various properties related to Any, _∈_ and _∼[_]_

-- Lemma relating Any to map.

Any-map : ∀ {C A B} (P : B → Set) (f : A → B) (xs : ⟦ C ⟧ A) →
          Any P (map f xs) ↔ Any (P ∘ f) xs
Any-map P f xs = Any P (map f xs) □

-- Any can be expressed using _∈_.

Any-∈ : ∀ {C A} (P : A → Set) (xs : ⟦ C ⟧ A) →
        Any P xs ↔ ∃ λ x → P x × x ∈ xs
Any-∈ P (s , f) =
  (∃ λ p → P (f p))                ↔⟨ ∃-cong (λ p → ∃-intro P (f p)) ⟩
  (∃ λ p → ∃ λ x → P x × x ≡ f p)  ↔⟨ ∃-comm ⟩
  (∃ λ x → ∃ λ p → P x × x ≡ f p)  ↔⟨ ∃-cong (λ _ → ∃-comm) ⟩
  (∃ λ x → P x × ∃ λ p → x ≡ f p)  □

-- Using this property we can prove that Any and _⊎_ commute.

Any-⊎ : ∀ {C A} (P Q : A → Set) (xs : ⟦ C ⟧ A) →
        Any (λ x → P x ⊎ Q x) xs ↔ Any P xs ⊎ Any Q xs
Any-⊎ P Q xs =
  Any (λ x → P x ⊎ Q x) xs                         ↔⟨ Any-∈ (λ x → P x ⊎ Q x) xs ⟩
  (∃ λ x → (P x ⊎ Q x) × x ∈ xs)                   ↔⟨ ∃-cong (λ x → ×-⊎-distrib-right) ⟩
  (∃ λ x → P x × x ∈ xs ⊎ Q x × x ∈ xs)            ↔⟨ ∃-⊎-distrib-left ⟩
  (∃ λ x → P x × x ∈ xs) ⊎ (∃ λ x → Q x × x ∈ xs)  ↔⟨ inverse $ Any-∈ P xs ⊎-cong Any-∈ Q xs ⟩
  Any P xs ⊎ Any Q xs                              □

-- Any preserves functions of various kinds and respects bag equality
-- and similar relations.

Any-cong : ∀ {k C D A} {P Q : A → Set}
           (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
           (∀ x → P x ↝[ k ] Q x) → xs ∼[ k ] ys →
           Any P xs ↝[ k ] Any Q ys
Any-cong {P = P} {Q} xs ys P↔Q xs∼ys =
  Any P xs                ↔⟨ Any-∈ P xs ⟩
  (∃ λ z → P z × z ∈ xs)  ↝⟨ ∃-cong (λ z → P↔Q z ×-cong xs∼ys z) ⟩
  (∃ λ z → Q z × z ∈ ys)  ↔⟨ inverse (Any-∈ Q ys) ⟩
  Any Q ys                □

-- Map preserves the relations.

map-cong : ∀ {k C D} {A B : Set} (f : A → B)
           (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
           xs ∼[ k ] ys → map f xs ∼[ k ] map f ys
map-cong f xs ys xs∼ys = λ z →
  z ∈ map f xs            ↔⟨ Any-map (_≡_ z) f xs ⟩
  Any (λ x → z ≡ f x) xs  ↝⟨ Any-cong xs ys (λ x → z ≡ f x □) xs∼ys ⟩
  Any (λ x → z ≡ f x) ys  ↔⟨ inverse (Any-map (_≡_ z) f ys) ⟩
  z ∈ map f ys            □
