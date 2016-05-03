------------------------------------------------------------------------
-- Some definitions related to and properties of finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Fin
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence hiding (id; _∘_; inverse)
open import Prelude hiding (id)

open import Bijection eq using (_↔_; module _↔_)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq hiding (_∘_)
open import H-level eq
open import H-level.Closure eq
open import List eq
open import Univalence-axiom eq

------------------------------------------------------------------------
-- Some bijections relating Fin and ∃

∃-Fin-zero : ∀ {p ℓ} (P : Fin zero → Set p) → ∃ P ↔ ⊥ {ℓ = ℓ}
∃-Fin-zero P = Σ-left-zero

∃-Fin-suc : ∀ {p n} (P : Fin (suc n) → Set p) →
            ∃ P ↔ P fzero ⊎ ∃ (P ∘ fsuc)
∃-Fin-suc P =
  ∃ P                          ↔⟨ ∃-⊎-distrib-right ⟩
  ∃ (P ∘ inj₁) ⊎ ∃ (P ∘ inj₂)  ↔⟨ Σ-left-identity ⊎-cong id ⟩□
  P (inj₁ tt) ⊎ ∃ (P ∘ inj₂)   □

------------------------------------------------------------------------
-- Fin n is a set

abstract

  Fin-set : ∀ n → Is-set (Fin n)
  Fin-set zero    = mono₁ 1 ⊥-propositional
  Fin-set (suc n) = ⊎-closure 0 (mono 0≤2 ⊤-contractible) (Fin-set n)
    where
    0≤2 : 0 ≤ 2
    0≤2 = ≤-step (≤-step ≤-refl)

------------------------------------------------------------------------
-- If two nonempty finite sets are isomorphic, then we can remove one
-- element from each and get new isomorphic finite sets

private

  well-behaved : ∀ {m n} (f : Fin (1 + m) ↔ Fin (1 + n)) →
                 Well-behaved (_↔_.to f)
  well-behaved f {b = i} eq₁ eq₂ = ⊎.inj₁≢inj₂ (
    fzero         ≡⟨ sym $ to-from f eq₂ ⟩
    from f fzero  ≡⟨ to-from f eq₁ ⟩∎
    fsuc i        ∎)
    where open _↔_

cancel-suc : ∀ {m n} → Fin (1 + m) ↔ Fin (1 + n) → Fin m ↔ Fin n
cancel-suc f =
  ⊎-left-cancellative f (well-behaved f) (well-behaved $ inverse f)

-- In fact, we can do it in such a way that, if the input bijection
-- relates elements of two lists with equal heads, then the output
-- bijection relates elements of the tails of the lists.
--
-- xs And ys Are-related-by f is inhabited if the indices of xs and ys
-- which are related by f point to equal elements.

infix 4 _And_Are-related-by_

_And_Are-related-by_ :
  ∀ {a} {A : Set a}
  (xs ys : List A) → Fin (length xs) ↔ Fin (length ys) → Set a
xs And ys Are-related-by f =
  ∀ i → lookup xs i ≡ lookup ys (_↔_.to f i)

abstract

  -- The tails are related.

  cancel-suc-preserves-relatedness :
    ∀ {a} {A : Set a} (x : A) xs ys
    (f : Fin (length (x ∷ xs)) ↔ Fin (length (x ∷ ys))) →
    x ∷ xs And x ∷ ys Are-related-by f →
    xs And ys Are-related-by cancel-suc f
  cancel-suc-preserves-relatedness x xs ys f related = helper
    where
    open _↔_ f

    helper : xs And ys Are-related-by cancel-suc f
    helper i with inspect (to (fsuc i)) | related (fsuc i)
    helper i | fsuc k , eq₁ | hyp₁ =
      lookup xs i                    ≡⟨ hyp₁ ⟩
      lookup (x ∷ ys) (to (fsuc i))  ≡⟨ cong (lookup (x ∷ ys)) eq₁ ⟩
      lookup (x ∷ ys) (fsuc k)       ≡⟨ refl _ ⟩∎
      lookup ys k                    ∎
    helper i | fzero , eq₁ | hyp₁
      with inspect (to (fzero)) | related (fzero)
    helper i | fzero , eq₁ | hyp₁ | fsuc j , eq₂ | hyp₂ =
      lookup xs i                    ≡⟨ hyp₁ ⟩
      lookup (x ∷ ys) (to (fsuc i))  ≡⟨ cong (lookup (x ∷ ys)) eq₁ ⟩
      lookup (x ∷ ys) (fzero)        ≡⟨ refl _ ⟩
      x                              ≡⟨ hyp₂ ⟩
      lookup (x ∷ ys) (to (fzero))   ≡⟨ cong (lookup (x ∷ ys)) eq₂ ⟩
      lookup (x ∷ ys) (fsuc j)       ≡⟨ refl _ ⟩∎
      lookup ys j                    ∎
    helper i | fzero , eq₁ | hyp₁ | fzero , eq₂ | hyp₂ =
      ⊥-elim $ well-behaved f eq₁ eq₂

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
    to zero    zero    _       = refl _
    to (suc m) (suc n) 1+m↔1+n = cong suc $ to m n $ cancel-suc 1+m↔1+n
    to zero    (suc n)   0↔1+n = ⊥-elim $ _↔_.from 0↔1+n fzero
    to (suc m) zero    1+m↔0   = ⊥-elim $ _↔_.to 1+m↔0 fzero

------------------------------------------------------------------------
-- "Type arithmetic" using Fin

-- Taking the disjoint union of two finite sets amounts to the same
-- thing as adding the sizes.

Fin⊎Fin↔Fin+ : ∀ m n → Fin m ⊎ Fin n ↔ Fin (m + n)
Fin⊎Fin↔Fin+ zero n =
  Fin 0 ⊎ Fin n  ↝⟨ id ⟩
  ⊥ ⊎ Fin n      ↝⟨ ⊎-left-identity ⟩
  Fin n          ↝⟨ id ⟩□
  Fin (0 + n)    □
Fin⊎Fin↔Fin+ (suc m) n =
  Fin (suc m) ⊎ Fin n  ↝⟨ id ⟩
  (⊤ ⊎ Fin m) ⊎ Fin n  ↝⟨ inverse ⊎-assoc ⟩
  ⊤ ⊎ (Fin m ⊎ Fin n)  ↝⟨ id ⊎-cong Fin⊎Fin↔Fin+ m n ⟩
  ⊤ ⊎ Fin (m + n)      ↝⟨ id ⟩
  Fin (suc (m + n))    ↝⟨ id ⟩□
  Fin (suc m + n)      □

-- Taking the product of two finite sets amounts to the same thing as
-- multiplying the sizes.

Fin×Fin↔Fin* : ∀ m n → Fin m × Fin n ↔ Fin (m * n)
Fin×Fin↔Fin* zero n =
  Fin 0 × Fin n  ↝⟨ id ⟩
  ⊥ × Fin n      ↝⟨ ×-left-zero ⟩
  ⊥              ↝⟨ id ⟩□
  Fin 0          □
Fin×Fin↔Fin* (suc m) n =
  Fin (suc m) × Fin n        ↝⟨ id ⟩
  (⊤ ⊎ Fin m) × Fin n        ↝⟨ ∃-⊎-distrib-right ⟩
  ⊤ × Fin n ⊎ Fin m × Fin n  ↝⟨ ×-left-identity ⊎-cong Fin×Fin↔Fin* m n ⟩
  Fin n ⊎ Fin (m * n)        ↝⟨ Fin⊎Fin↔Fin+ _ _ ⟩
  Fin (n + m * n)            ↝⟨ id ⟩□
  Fin (suc m * n)            □

-- Forming the function space between two finite sets amounts to the
-- same thing as raising one size to the power of the other (assuming
-- extensionality).

[Fin→Fin]↔Fin^ :
  Extensionality (# 0) (# 0) →
  ∀ m n → (Fin m → Fin n) ↔ Fin (n ^ m)
[Fin→Fin]↔Fin^ ext zero n =
  (Fin 0 → Fin n)  ↝⟨ id ⟩
  (⊥ → Fin n)      ↝⟨ Π⊥↔⊤ ext ⟩
  ⊤                ↝⟨ inverse ⊎-right-identity ⟩□
  Fin 1            □
[Fin→Fin]↔Fin^ ext (suc m) n =
  (Fin (suc m) → Fin n)          ↝⟨ id ⟩
  (⊤ ⊎ Fin m → Fin n)            ↝⟨ Π⊎↔Π×Π ext ⟩
  (⊤ → Fin n) × (Fin m → Fin n)  ↝⟨ Π-left-identity ×-cong [Fin→Fin]↔Fin^ ext m n ⟩
  Fin n × Fin (n ^ m)            ↝⟨ Fin×Fin↔Fin* _ _ ⟩
  Fin (n * n ^ m)                ↝⟨ id ⟩□
  Fin (n ^ suc m)                □

-- Automorphisms on Fin n are isomorphic to Fin (n !) (assuming
-- extensionality).

[Fin↔Fin]↔Fin! :
  Extensionality (# 0) (# 0) →
  ∀ n → (Fin n ↔ Fin n) ↔ Fin (n !)
[Fin↔Fin]↔Fin! ext zero =
  Fin 0 ↔ Fin 0  ↝⟨ Eq.↔↔≃ ext (Fin-set 0) ⟩
  Fin 0 ≃ Fin 0  ↝⟨ id ⟩
  ⊥ ≃ ⊥          ↔⟨ ≃⊥≃¬ ext ⟩
  ¬ ⊥            ↝⟨ ¬⊥↔⊤ ext ⟩
  ⊤              ↝⟨ inverse ⊎-right-identity ⟩
  ⊤ ⊎ ⊥          ↝⟨ id ⟩□
  Fin 1          □
[Fin↔Fin]↔Fin! ext (suc n) =
  Fin (suc n) ↔ Fin (suc n)      ↝⟨ [⊤⊎↔⊤⊎]↔[⊤⊎×↔] ext Fin._≟_ ⟩
  Fin (suc n) × (Fin n ↔ Fin n)  ↝⟨ id ×-cong [Fin↔Fin]↔Fin! ext n ⟩
  Fin (suc n) × Fin (n !)        ↝⟨ Fin×Fin↔Fin* _ _ ⟩□
  Fin (suc n !)                  □

-- A variant of the previous property.

[Fin≡Fin]↔Fin! :
  Extensionality (# 0) (# 0) →
  Univalence (# 0) →
  ∀ n → (Fin n ≡ Fin n) ↔ Fin (n !)
[Fin≡Fin]↔Fin! ext univ n =
  Fin n ≡ Fin n  ↔⟨ ≡≃≃ univ ⟩
  Fin n ≃ Fin n  ↝⟨ inverse $ Eq.↔↔≃ ext (Fin-set n) ⟩
  Fin n ↔ Fin n  ↝⟨ [Fin↔Fin]↔Fin! ext n ⟩□
  Fin (n !)      □