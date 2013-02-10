------------------------------------------------------------------------
-- Some definitions related to and properties of finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Note that this module is not parametrised by a definition of
-- equality; it uses ordinary propositional equality.

module Fin where

open import Equality.Propositional as P
open import Logical-equivalence hiding (id; _∘_; inverse)
open import Prelude hiding (id)

open import Bijection P.equality-with-J using (_↔_; module _↔_)
open import Equality.Decision-procedures P.equality-with-J
open import Function-universe P.equality-with-J hiding (_∘_)
open import H-level P.equality-with-J
open import H-level.Closure P.equality-with-J

------------------------------------------------------------------------
-- Some bijections relating Fin and ∃

∃-Fin-zero : ∀ {p ℓ} (P : Fin zero → Set p) → ∃ P ↔ ⊥ {ℓ = ℓ}
∃-Fin-zero P = Σ-left-zero

∃-Fin-suc : ∀ {p n} (P : Fin (suc n) → Set p) →
            ∃ P ↔ P (inj₁ tt) ⊎ ∃ (P ∘ inj₂)
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
  well-behaved f {b = i} eq₁ eq₂ =  ⊎.inj₁≢inj₂ (
    inj₁ tt           ≡⟨ sym $ to-from f eq₂ ⟩
    from f (inj₁ tt)  ≡⟨ to-from f eq₁ ⟩∎
    inj₂ i            ∎)
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
    helper i with inspect (to (inj₂ i)) | related (inj₂ i)
    helper i | inj₂ k with-≡ eq₁ | hyp₁ =
      lookup xs i                    ≡⟨ hyp₁ ⟩
      lookup (x ∷ ys) (to (inj₂ i))  ≡⟨ cong (lookup (x ∷ ys)) eq₁ ⟩
      lookup (x ∷ ys) (inj₂ k)       ≡⟨ refl ⟩∎
      lookup ys k                    ∎
    helper i | inj₁ tt with-≡ eq₁ | hyp₁
      with inspect (to (inj₁ tt)) | related (inj₁ tt)
    helper i | inj₁ tt with-≡ eq₁ | hyp₁ | inj₂ j with-≡ eq₂ | hyp₂ =
      lookup xs i                     ≡⟨ hyp₁ ⟩
      lookup (x ∷ ys) (to (inj₂ i))   ≡⟨ cong (lookup (x ∷ ys)) eq₁ ⟩
      lookup (x ∷ ys) (inj₁ tt)       ≡⟨ refl ⟩
      x                               ≡⟨ hyp₂ ⟩
      lookup (x ∷ ys) (to (inj₁ tt))  ≡⟨ cong (lookup (x ∷ ys)) eq₂ ⟩
      lookup (x ∷ ys) (inj₂ j)        ≡⟨ refl ⟩∎
      lookup ys j                     ∎
    helper i | inj₁ tt with-≡ eq₁ | hyp₁ | inj₁ tt with-≡ eq₂ | hyp₂ =
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
    to zero    zero    _       = refl
    to (suc m) (suc n) 1+m↔1+n = cong suc $ to m n $ cancel-suc 1+m↔1+n
    to zero    (suc n)   0↔1+n = ⊥-elim $ _↔_.from 0↔1+n (inj₁ tt)
    to (suc m) zero    1+m↔0   = ⊥-elim $ _↔_.to 1+m↔0 (inj₁ tt)
