------------------------------------------------------------------------
-- Some definitions related to and properties of finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Note that this module is not parametrised by a definition of
-- equality; it uses ordinary propositional equality.

module Fin where

open import Equality.Propositional as P
open import Equivalence hiding (id; _∘_)
open import Prelude

private
  module Bijection where
    import Bijection; open Bijection P.equality-with-J public
open Bijection hiding (id; _∘_)
import Equality.Decision-procedures as ED; open ED P.equality-with-J

------------------------------------------------------------------------
-- Some bijections related to Fin

∃-Fin-zero : (P : Fin zero → Set) → ∃ P ↔ ⊥
∃-Fin-zero P = record
  { surjection = record
    { equivalence = record
      { to   = absurd ∘ proj₁
      ; from = ⊥-elim
      }
    ; right-inverse-of = λ x → ⊥-elim x
    }
  ; left-inverse-of = absurd ∘ proj₁
  }
  where
  absurd : {A : Set} → Fin 0 → A
  absurd ()

∃-Fin-suc : ∀ {n} (P : Fin (suc n) → Set) →
            ∃ P ↔ P zero ⊎ ∃ (P ∘ suc)
∃-Fin-suc P = record
  { surjection = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = [ (λ _ → refl) , (λ _ → refl) ]
    }
  ; left-inverse-of = from∘to
  }
  where
  to : ∃ P → P zero ⊎ ∃ (P ∘ suc)
  to (zero  , p) = inj₁ p
  to (suc i , p) = inj₂ (i , p)

  from = [ _,_ zero , Σ-map suc id ]

  from∘to : ∀ p → from (to p) ≡ p
  from∘to (zero  , p) = refl
  from∘to (suc i , p) = refl

------------------------------------------------------------------------
-- A lookup function

lookup′ : ∀ {A : Set} {n} (xs : List A) → Fin n → length xs ≡ n → A
lookup′ []       ()      refl
lookup′ (x ∷ xs) zero    _    = x
lookup′ (x ∷ xs) (suc i) eq   = lookup′ xs i (ℕ.cancel-suc eq)

lookup : {A : Set} (xs : List A) → Fin (length xs) → A
lookup xs i = lookup′ xs i refl

-- xs And ys Are-related-by f is inhabited if the indices of xs and ys
-- which are related by f point to equal elements.

infix 4 _And_Are-related-by_

_And_Are-related-by_ :
  {A : Set} (xs ys : List A) → Fin (length xs) ↔ Fin (length ys) → Set
xs And ys Are-related-by f =
  ∀ i → lookup xs i ≡ lookup ys (_↔_.to f i)

------------------------------------------------------------------------
-- If two nonempty finite sets are isomorphic, then we can remove one
-- element from each and get new isomorphic finite sets

cancel-suc : ∀ {m n} → Fin (1 + m) ↔ Fin (1 + n) → Fin m ↔ Fin n
cancel-suc = λ f → record
  { surjection = record
    { equivalence = record
      { to   = to                     f
      ; from = to $ Bijection.inverse f
      }
    ; right-inverse-of = to∘to $ Bijection.inverse f
    }
  ; left-inverse-of    = to∘to                     f
  }
  where
  to : ∀ {m n} → Fin (1 + m) ↔ Fin (1 + n) → Fin m → Fin n
  to f i with _↔_.to f (suc i) | sym (_↔_.left-inverse-of f (suc i))
  ... | suc j | _     = j
  ... | zero  | left⁺ with _↔_.to f zero | sym (_↔_.left-inverse-of f zero)
  ...   | suc j | _     = j
  ...   | zero  | left⁰ = ⊥-elim (Fin.0≢+ 0≡+)
    where
    0≡+ = zero             ≡⟨ left⁰ ⟩
          _↔_.from f zero  ≡⟨ sym left⁺ ⟩∎
          suc i            ∎

  abstract

    to∘to : ∀ {m n} (f : Fin (1 + m) ↔ Fin (1 + n)) (i : Fin m) →
            to (Bijection.inverse f) (to f i) ≡ i
    to∘to f i with _↔_.to f (suc i) | sym (_↔_.left-inverse-of f (suc i))
    to∘to f i | suc j | left⁺ with _↔_.from f (suc j) | sym (_↔_.right-inverse-of f (suc j))
    to∘to f i | suc j | refl  | .(suc i) | right⁺ = refl
    to∘to f i | zero  | left⁺ with _↔_.to f zero | sym (_↔_.left-inverse-of f zero)
    to∘to f i | zero  | left⁺ | suc j | left⁰ with _↔_.from f (suc j) | sym (_↔_.right-inverse-of f (suc j))
    to∘to f i | zero  | left⁺ | suc j | refl  | .zero | right⁺ with _↔_.from f zero | sym (_↔_.right-inverse-of f zero)
    to∘to f i | zero  | refl  | suc j | refl  | .zero | right⁺ | .(suc i) | right⁰ = refl
    to∘to f i | zero  | left⁺ | zero  | left⁰ = ⊥-elim (Fin.0≢+ 0≡+)
      where
      0≡+ = zero             ≡⟨ left⁰ ⟩
            _↔_.from f zero  ≡⟨ sym left⁺ ⟩∎
            suc i            ∎

abstract

  -- In fact, we can do it in such a way that, if the input bijection
  -- relates elements of two lists with equal heads, then the output
  -- bijection relates elements of the tails of the lists.

  cancel-suc-preserves-relatedness :
    ∀ {A : Set} (x : A) xs ys
    (f : Fin (length (x ∷ xs)) ↔ Fin (length (x ∷ ys))) →
    x ∷ xs And x ∷ ys Are-related-by f →
    xs And ys Are-related-by cancel-suc f
  cancel-suc-preserves-relatedness x xs ys =
    related′ refl refl
    where
    related′ : ∀ {m n} (eq₁ : length xs ≡ m) (eq₂ : length ys ≡ n)
               (f : Fin (1 + m) ↔ Fin (1 + n)) →
               (∀ i → lookup′ (x ∷ xs) i (cong suc eq₁) ≡
                      lookup′ (x ∷ ys) (_↔_.to f i) (cong suc eq₂)) →
               ∀ i → lookup′ xs i eq₁ ≡
                     lookup′ ys (_↔_.to (cancel-suc f) i) eq₂
    related′ eq₁ eq₂ f related i
      with _↔_.to f (suc i)
         | sym (_↔_.left-inverse-of f (suc i))
         | related (suc i)
    related′ eq₁ eq₂ f related i | suc k | _ | hyp₁
      with eq₁ | eq₂
    ... | refl | refl = hyp₁
    related′ eq₁ eq₂ f related i | zero | _ | hyp₁
      with _↔_.to f zero
         | sym (_↔_.left-inverse-of f zero)
         | related zero
    related′ eq₁ eq₂ f related i | zero | _ | hyp₁ | suc j | _ | hyp₂
      with eq₁ | eq₂
    ... | refl | refl =
      lookup xs i  ≡⟨ hyp₁ ⟩
      x            ≡⟨ hyp₂ ⟩∎
      lookup ys j  ∎
    related′ eq₁ eq₂ f related i
      | zero | left⁺ | hyp₁ | zero  | left⁰ | hyp₂ = ⊥-elim (Fin.0≢+ 0≡+)
      where
      0≡+ = zero             ≡⟨ left⁰ ⟩
            _↔_.from f zero  ≡⟨ sym left⁺ ⟩∎
            suc i            ∎

-- By using cancel-suc we can show that finite sets are isomorphic iff
-- they have equal size.

isomorphic-same-size : ∀ {m n} → (Fin m ↔ Fin n) ⇔ m ≡ n
isomorphic-same-size {m} {n} = record
  { to   = to m n
  ; from = λ m≡n → subst (λ n → Fin m ↔ Fin n) m≡n Bijection.id
  }
  where
  abstract
    to : ∀ m n → (Fin m ↔ Fin n) → m ≡ n
    to zero    zero    _       = refl
    to (suc m) (suc n) 1+m↔1+n = cong suc $ to m n $ cancel-suc 1+m↔1+n
    to zero    (suc n)   0↔1+n with _↔_.from 0↔1+n zero
    ... | ()
    to (suc m) zero    1+m↔0   with _↔_.to 1+m↔0 zero
    ... | ()
