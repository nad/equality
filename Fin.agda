------------------------------------------------------------------------
-- Some definitions related to and properties of finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Note that this module is not parametrised by a definition of
-- equality; it uses ordinary propositional equality.

module Fin where

open import Equality.Propositional as P
open import Equivalence hiding (id; _∘_; inverse)
open import Prelude hiding (id)

import Bijection
open Bijection P.equality-with-J using (_↔_; module _↔_)
import Equality.Decision-procedures as ED; open ED P.equality-with-J
import Function-universe as FU; open FU P.equality-with-J hiding (_∘_)

------------------------------------------------------------------------
-- Some bijections relating Fin and ∃

∃-Fin-zero : (P : Fin zero → Set) → ∃ P ↔ ⊥
∃-Fin-zero P = Σ-left-zero

∃-Fin-suc : ∀ {n} (P : Fin (suc n) → Set) →
            ∃ P ↔ P (inj₁ tt) ⊎ ∃ (P ∘ inj₂)
∃-Fin-suc P =
  ∃ P                          ↔⟨ ∃-⊎-distrib-right ⟩
  ∃ (P ∘ inj₁) ⊎ ∃ (P ∘ inj₂)  ↔⟨ Σ-left-identity ⊎-cong id ⟩∎
  P (inj₁ tt) ⊎ ∃ (P ∘ inj₂)   ∎

------------------------------------------------------------------------
-- If two nonempty finite sets are isomorphic, then we can remove one
-- element from each and get new isomorphic finite sets

cancel-suc : ∀ {m n} → Fin (1 + m) ↔ Fin (1 + n) → Fin m ↔ Fin n
cancel-suc = λ f → record
  { surjection = record
    { equivalence = record
      { to   = to           f
      ; from = to $ inverse f
      }
    ; right-inverse-of = to∘to $ inverse f
    }
  ; left-inverse-of    = to∘to           f
  }
  where
  to : ∀ {m n} → Fin (1 + m) ↔ Fin (1 + n) → Fin m → Fin n
  to f i with _↔_.to f (inj₂ i) | sym (_↔_.left-inverse-of f (inj₂ i))
  ... | inj₂ j | _     = j
  ... | inj₁ _ | left⁺ with _↔_.to f (inj₁ _) | sym (_↔_.left-inverse-of f (inj₁ _))
  ...   | inj₂ j | _     = j
  ...   | inj₁ _ | left⁰ = ⊥-elim (⊎.inj₁≢inj₂ 0≡+)
    where
    0≡+ = inj₁ _               ≡⟨ left⁰ ⟩
          _↔_.from f (inj₁ _)  ≡⟨ sym left⁺ ⟩∎
          inj₂ i               ∎

  abstract

    to∘to : ∀ {m n} (f : Fin (1 + m) ↔ Fin (1 + n)) (i : Fin m) →
            to (inverse f) (to f i) ≡ i
    to∘to f i with _↔_.to f (inj₂ i) | sym (_↔_.left-inverse-of f (inj₂ i))
    to∘to f i | inj₂ j  | left⁺ with _↔_.from f (inj₂ j) | sym (_↔_.right-inverse-of f (inj₂ j))
    to∘to f i | inj₂ j  | refl  | .(inj₂ i) | right⁺ = refl
    to∘to f i | inj₁ tt | left⁺ with _↔_.to f (inj₁ tt) | sym (_↔_.left-inverse-of f (inj₁ tt))
    to∘to f i | inj₁ tt | left⁺ | inj₂ j  | left⁰ with _↔_.from f (inj₂ j) | sym (_↔_.right-inverse-of f (inj₂ j))
    to∘to f i | inj₁ tt | left⁺ | inj₂ j  | refl  | .(inj₁ tt) | right⁺ with _↔_.from f (inj₁ tt) | sym (_↔_.right-inverse-of f (inj₁ tt))
    to∘to f i | inj₁ tt | refl  | inj₂ j  | refl  | .(inj₁ tt) | right⁺ | .(inj₂ i) | right⁰ = refl
    to∘to f i | inj₁ tt | left⁺ | inj₁ tt | left⁰ = ⊥-elim (⊎.inj₁≢inj₂ 0≡+)
      where
      0≡+ = inj₁ tt               ≡⟨ left⁰ ⟩
            _↔_.from f (inj₁ tt)  ≡⟨ sym left⁺ ⟩∎
            inj₂ i                ∎

-- In fact, we can do it in such a way that, if the input bijection
-- relates elements of two lists with equal heads, then the output
-- bijection relates elements of the tails of the lists.
--
-- xs And ys Are-related-by f is inhabited if the indices of xs and ys
-- which are related by f point to equal elements.

infix 4 _And_Are-related-by_

_And_Are-related-by_ :
  {A : Set} (xs ys : List A) → Fin (length xs) ↔ Fin (length ys) → Set
xs And ys Are-related-by f =
  ∀ i → lookup xs i ≡ lookup ys (_↔_.to f i)

abstract

  -- The tails are related.

  cancel-suc-preserves-relatedness :
    ∀ {A : Set} (x : A) xs ys
    (f : Fin (length (x ∷ xs)) ↔ Fin (length (x ∷ ys))) →
    x ∷ xs And x ∷ ys Are-related-by f →
    xs And ys Are-related-by cancel-suc f
  cancel-suc-preserves-relatedness x xs ys f related i
    with _↔_.to f (inj₂ i)
       | sym (_↔_.left-inverse-of f (inj₂ i))
       | related (inj₂ i)
  cancel-suc-preserves-relatedness x xs ys f related i | inj₂ k  | _ | hyp₁ = hyp₁
  cancel-suc-preserves-relatedness x xs ys f related i | inj₁ tt | _ | hyp₁
    with _↔_.to f (inj₁ tt)
       | sym (_↔_.left-inverse-of f (inj₁ tt))
       | related (inj₁ tt)
  cancel-suc-preserves-relatedness x xs ys f related i
    | inj₁ tt | _ | hyp₁ | inj₂ j | _ | hyp₂ =
    lookup xs i  ≡⟨ hyp₁ ⟩
    x            ≡⟨ hyp₂ ⟩∎
    lookup ys j  ∎
  cancel-suc-preserves-relatedness x xs ys f related i
    | inj₁ tt | left⁺ | hyp₁ | inj₁ tt | left⁰ | hyp₂ =
    ⊥-elim (⊎.inj₁≢inj₂ 0≡+)
    where
    0≡+ = inj₁ tt               ≡⟨ left⁰ ⟩
          _↔_.from f (inj₁ tt)  ≡⟨ sym left⁺ ⟩∎
          inj₂ i                ∎

-- By using cancel-suc we can show that finite sets are isomorphic iff
-- they have equal size.

isomorphic-same-size : ∀ {m n} → (Fin m ↔ Fin n) ⇔ m ≡ n
isomorphic-same-size {m} {n} = record
  { to   = to m n
  ; from = λ m≡n → subst (λ n → Fin m ↔ Fin n) m≡n id
  }
  where
  abstract
    to : ∀ m n → (Fin m ↔ Fin n) → m ≡ n
    to zero    zero    _       = refl
    to (suc m) (suc n) 1+m↔1+n = cong suc $ to m n $ cancel-suc 1+m↔1+n
    to zero    (suc n)   0↔1+n = ⊥-elim $ _↔_.from 0↔1+n (inj₁ tt)
    to (suc m) zero    1+m↔0   = ⊥-elim $ _↔_.to 1+m↔0 (inj₁ tt)
