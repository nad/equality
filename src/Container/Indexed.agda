------------------------------------------------------------------------
-- Indexed containers
------------------------------------------------------------------------

-- Partly based on "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris, and partly based on "Non-wellfounded trees in
-- Homotopy Type Theory" by Ahrens, Capriotti and Spadotti.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Container.Indexed
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

import Bijection eq as B
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)

private
  variable
    a ℓ p p₁ p₂ q s : Level
    A I O           : Type a
    P Q R           : A → Type p
    ext f i k o     : A

------------------------------------------------------------------------
-- _⇾_

-- A kind of function space for indexed types.

infix 4 _⇾_

_⇾_ :
  {A : Type a} →
  (A → Type p) → (A → Type q) → Type (a ⊔ p ⊔ q)
P ⇾ Q = ∀ x → P x → Q x

-- An identity function.

id⇾ : P ⇾ P
id⇾ _ = id

-- Composition for _⇾_.

infixr 9 _∘⇾_

_∘⇾_ : Q ⇾ R → P ⇾ Q → P ⇾ R
f ∘⇾ g = λ i → f i ∘ g i

------------------------------------------------------------------------
-- Containers

-- Doubly indexed containers.

record Container₂ (I : Type i) (O : Type o) s p :
                  Type (i ⊔ o ⊔ lsuc (s ⊔ p)) where
  field
    Shape    : O → Type s
    Position : ∀ {o} → Shape o → Type p
    index    : ∀ {o} {s : Shape o} → Position s → I

open Container₂ public

-- Singly indexed containers.

Container : Type i → ∀ s p → Type (i ⊔ lsuc (s ⊔ p))
Container I = Container₂ I I

private
  variable
    C : Container₂ I O s p

-- Container₂ can be expressed as a nested Σ-type.

Container≃Σ :
  Container₂ I O s p ≃
  (∃ λ (S : O → Type s) →
   ∃ λ (P : ∀ {o} → S o → Type p) →
     ∀ {o} {s : S o} → P s → I)
Container≃Σ = Eq.↔→≃
  (λ C → C .Shape , C .Position , C .index)
  (λ (S , P , i) → record { Shape = S; Position = P; index = i })
  refl
  refl

------------------------------------------------------------------------
-- Polynomial functors

-- The polynomial functor associated to a container.

⟦_⟧ :
  {I : Type i} {O : Type o} →
  Container₂ I O s p → (I → Type ℓ) → O → Type (ℓ ⊔ s ⊔ p)
⟦ C ⟧ P i = ∃ λ (s : Shape C i) → (p : Position C s) → P (index C p)

-- A map function.

map : (C : Container₂ I O s p) → P ⇾ Q → ⟦ C ⟧ P ⇾ ⟦ C ⟧ Q
map C f _ (s , g) = s , f _ ∘ g

-- Functor laws.

map-id : map C (id⇾ {P = P}) ≡ id⇾
map-id = refl _

map-∘ :
  (f : Q ⇾ R) (g : P ⇾ Q) →
  map C (f ∘⇾ g) ≡ map C f ∘⇾ map C g
map-∘ _ _ = refl _

-- A preservation lemma.

⟦⟧-cong :
  {I : Type i} {P₁ : I → Type p₁} {P₂ : I → Type p₂} →
  Extensionality? k p (p₁ ⊔ p₂) →
  (C : Container₂ I O s p) →
  (∀ i → P₁ i ↝[ k ] P₂ i) →
  (∀ o → ⟦ C ⟧ P₁ o ↝[ k ] ⟦ C ⟧ P₂ o)
⟦⟧-cong {P₁ = P₁} {P₂ = P₂} ext C P₁↝P₂ o =
  (∃ λ (s : Shape C o) → (p : Position C s) → P₁ (index C p))  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → P₁↝P₂ _) ⟩□
  (∃ λ (s : Shape C o) → (p : Position C s) → P₂ (index C p))  □

-- The forward direction of ⟦⟧-cong is an instance of map (at least
-- when k is equivalence).

_ : _≃_.to (⟦⟧-cong ext C f o) ≡ map C (_≃_.to ∘ f) o
_ = refl _

-- The shapes of a container are pointwise equivalent to the
-- polynomial functor of the container applied to the constant
-- function yielding the unit type.
--
-- (This lemma was suggested to me by an anonymous reviewer of a
-- paper.)

Shape≃⟦⟧⊤ :
  (C : Container₂ I O s p) →
  Shape C o ≃ ⟦ C ⟧ (λ _ → ⊤) o
Shape≃⟦⟧⊤ {o = o} C =
  Shape C o                                 ↔⟨ inverse $ drop-⊤-right (λ _ → →-right-zero) ⟩□
  (∃ λ (s : Shape C o) → Position C s → ⊤)  □

------------------------------------------------------------------------
-- Lifting the position type family

-- One can lift the position type family so that it is in a universe
-- that is at least as large as that containing the input indices.

lift-positions :
  {I : Type i} →
  Container₂ I O s p → Container₂ I O s (i ⊔ p)
lift-positions {i = i} C = λ where
  .Shape          → C .Shape
  .Position s     → ↑ i (C .Position s)
  .index (lift p) → C .index p

-- The result of ⟦_⟧ is not affected by lift-positions (up to
-- pointwise equivalence).

⟦⟧≃⟦lift-positions⟧ :
  {I : Type i}
  (C : Container₂ I O s p) (P : I → Type ℓ) →
  ⟦ C ⟧ P o ≃ ⟦ lift-positions C ⟧ P o
⟦⟧≃⟦lift-positions⟧ {o = o} C P =
  ∃-cong λ s →

  ((      p  :      Position C s)  → P (index C p))  ↝⟨ Eq.↔→≃ (_∘ lower) (_∘ lift) refl refl ⟩□
  (((lift p) : ↑ _ (Position C s)) → P (index C p))  □
