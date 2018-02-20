------------------------------------------------------------------------
-- Some definitions related to and properties of finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Fin
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence hiding (id; _∘_; inverse)
open import Prelude hiding (id)

open import Bijection eq as Bijection using (_↔_; module _↔_)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq hiding (_∘_)
open import H-level eq
open import H-level.Closure eq
open import List eq
open import Nat eq as Nat using (_≤_; ≤-refl; ≤-step; _<_)
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
  ∀ i → index xs i ≡ index ys (_↔_.to f i)

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
      index xs i                    ≡⟨ hyp₁ ⟩
      index (x ∷ ys) (to (fsuc i))  ≡⟨ cong (index (x ∷ ys)) eq₁ ⟩
      index (x ∷ ys) (fsuc k)       ≡⟨ refl _ ⟩∎
      index ys k                    ∎
    helper i | fzero , eq₁ | hyp₁
      with inspect (to (fzero)) | related (fzero)
    helper i | fzero , eq₁ | hyp₁ | fsuc j , eq₂ | hyp₂ =
      index xs i                    ≡⟨ hyp₁ ⟩
      index (x ∷ ys) (to (fsuc i))  ≡⟨ cong (index (x ∷ ys)) eq₁ ⟩
      index (x ∷ ys) (fzero)        ≡⟨ refl _ ⟩
      x                             ≡⟨ hyp₂ ⟩
      index (x ∷ ys) (to (fzero))   ≡⟨ cong (index (x ∷ ys)) eq₂ ⟩
      index (x ∷ ys) (fsuc j)       ≡⟨ refl _ ⟩∎
      index ys j                    ∎
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
-- The natural number corresponding to a value in Fin n

-- The underlying natural number.

⌞_⌟ : ∀ {n} → Fin n → ℕ
⌞_⌟ {n = zero}  ()
⌞_⌟ {n = suc _} fzero    = zero
⌞_⌟ {n = suc _} (fsuc i) = suc ⌞ i ⌟

-- Use of subst Fin does not change the underlying natural number.

⌞subst⌟ : ∀ {m n} (p : m ≡ n) (i : Fin m) → ⌞ subst Fin p i ⌟ ≡ ⌞ i ⌟
⌞subst⌟ {m} p i =
  ⌞ subst Fin p i ⌟         ≡⟨ cong (uncurry λ n p → ⌞ subst Fin {y = n} p i ⌟) (Σ-≡,≡→≡ (sym p) (

      trans p (sym p)            ≡⟨ trans-symʳ p ⟩∎
      refl m                     ∎)) ⟩

  ⌞ subst Fin (refl m) i ⌟  ≡⟨ cong ⌞_⌟ (subst-refl _ _) ⟩∎
  ⌞ i ⌟                     ∎

-- If the underlying natural numbers are equal, then the values in
-- Fin n are equal.

cancel-⌞⌟ : ∀ {n} {i j : Fin n} → ⌞ i ⌟ ≡ ⌞ j ⌟ → i ≡ j
cancel-⌞⌟ {zero}  {}
cancel-⌞⌟ {suc _} {fzero}  {fzero}  _   = refl _
cancel-⌞⌟ {suc _} {fzero}  {fsuc _} 0≡+ = ⊥-elim (Nat.0≢+ 0≡+)
cancel-⌞⌟ {suc _} {fsuc _} {fzero}  +≡0 = ⊥-elim (Nat.0≢+ (sym +≡0))
cancel-⌞⌟ {suc _} {fsuc _} {fsuc _} +≡+ =
  cong fsuc (cancel-⌞⌟ (Nat.cancel-suc +≡+))

-- Values of type Fin n can be seen as natural numbers smaller than n.

Fin↔< : ∀ n → Fin n ↔ ∃ λ m → m < n
Fin↔< zero =
  ⊥                   ↝⟨ inverse ×-right-zero ⟩
  ℕ × ⊥               ↔⟨ ∃-cong (λ _ → inverse <zero↔) ⟩□
  (∃ λ m → m < zero)  □
Fin↔< (suc n) =
  ⊤ ⊎ Fin n                          ↝⟨ inverse (_⇔_.to contractible⇔↔⊤ (singleton-contractible n)) ⊎-cong Fin↔< n ⟩
  (∃ λ m → m ≡ n) ⊎ (∃ λ m → m < n)  ↝⟨ inverse ∃-⊎-distrib-left ⟩
  (∃ λ m → m ≡ n ⊎ m < n)            ↝⟨ ∃-cong (λ _ → ⊎-comm) ⟩
  (∃ λ m → m < n ⊎ m ≡ n)            ↝⟨ ∃-cong (λ _ → inverse ≤↔<⊎≡) ⟩
  (∃ λ m → m ≤ n)                    ↝⟨ ∃-cong (λ _ → inverse suc≤suc↔) ⟩
  (∃ λ m → suc m ≤ suc n)            ↔⟨⟩
  (∃ λ m → m < suc n)                □

-- The forward direction of Fin↔< gives the "mirror image" of the
-- underlying natural number.

Fin↔<≡∸⌞⌟ :
  ∀ {n} (i : Fin n) → proj₁ (_↔_.to (Fin↔< n) i) ≡ Nat.pred (n ∸ ⌞ i ⌟)
Fin↔<≡∸⌞⌟ {n = zero}  ()
Fin↔<≡∸⌞⌟ {n = suc _} fzero    = refl _
Fin↔<≡∸⌞⌟ {n = suc _} (fsuc i) = Fin↔<≡∸⌞⌟ i

------------------------------------------------------------------------
-- Weakening

-- Single-step weakening.

weaken₁ : ∀ {n} → Fin n → Fin (suc n)
weaken₁ {zero}  ()
weaken₁ {suc _} fzero    = fzero
weaken₁ {suc _} (fsuc i) = fsuc (weaken₁ i)

weaken₁-correct : ∀ {n} (i : Fin n) → ⌞ weaken₁ i ⌟ ≡ ⌞ i ⌟
weaken₁-correct {zero}  ()
weaken₁-correct {suc _} fzero    = refl _
weaken₁-correct {suc _} (fsuc i) = cong suc (weaken₁-correct i)

-- Multiple-step weakening.

weaken : ∀ {m n} → m ≤ n → Fin m → Fin n
weaken (Nat.≤-refl′ m≡n)       = subst Fin m≡n
weaken (Nat.≤-step′ m≤k 1+k≡n) = subst Fin 1+k≡n ∘ weaken₁ ∘ weaken m≤k

weaken-correct : ∀ {m n} (m≤n : m ≤ n) (i : Fin m) →
                 ⌞ weaken m≤n i ⌟ ≡ ⌞ i ⌟
weaken-correct (Nat.≤-refl′ m≡n) i =
  ⌞ subst Fin m≡n i ⌟  ≡⟨ ⌞subst⌟ _ _ ⟩∎
  ⌞ i ⌟                ∎
weaken-correct (Nat.≤-step′ m≤k 1+k≡n) i =
  ⌞ subst Fin 1+k≡n (weaken₁ (weaken m≤k i)) ⌟  ≡⟨ ⌞subst⌟ _ _ ⟩
  ⌞ weaken₁ (weaken m≤k i) ⌟                    ≡⟨ weaken₁-correct _ ⟩
  ⌞ weaken m≤k i ⌟                              ≡⟨ weaken-correct m≤k _ ⟩∎
  ⌞ i ⌟                                         ∎

------------------------------------------------------------------------
-- Arithmetic

-- Addition.

_+ᶠ_ : ∀ {m n} → Fin m → Fin n → Fin (m + n)
_+ᶠ_ {m = zero}  ()
_+ᶠ_ {m = suc m} fzero    j = weaken (Nat.m≤n+m _ (suc m)) j
_+ᶠ_ {m = suc _} (fsuc i) j = fsuc (i +ᶠ j)

+ᶠ-correct :
  ∀ {m n} (i : Fin m) (j : Fin n) → ⌞ i +ᶠ j ⌟ ≡ ⌞ i ⌟ + ⌞ j ⌟
+ᶠ-correct {m = zero}  ()
+ᶠ-correct {m = suc m} fzero    j = weaken-correct
                                      (Nat.m≤n+m _ (suc m)) _
+ᶠ-correct {m = suc _} (fsuc i) j = cong suc (+ᶠ-correct i j)

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

------------------------------------------------------------------------
-- Inequality and a related isomorphism

-- Inequality.

Distinct : ∀ {n} → Fin n → Fin n → Set
Distinct {zero}  ()
Distinct {suc _} fzero    fzero    = ⊥
Distinct {suc _} fzero    (fsuc j) = ⊤
Distinct {suc _} (fsuc i) fzero    = ⊤
Distinct {suc _} (fsuc i) (fsuc j) = Distinct i j

-- This definition of inequality is pointwise logically equivalent to
-- _≢_, and in the presence of extensionality the two definitions are
-- pointwise isomorphic.

Distinct↔≢ :
  ∀ {k n} {i j : Fin n} →
  Extensionality? ⌊ k ⌋-sym lzero lzero →
  Distinct i j ↝[ ⌊ k ⌋-sym ] i ≢ j
Distinct↔≢ {n = zero}  {}
Distinct↔≢ {n = suc _} {fzero} {fzero} ext =
  ⊥              ↔⟨ inverse Π-left-identity ⟩
  ¬ ⊤            ↝⟨ →-cong ext (from-bijection $ inverse tt≡tt↔⊤) id ⟩
  tt ≢ tt        ↝⟨ →-cong ext (from-bijection Bijection.≡↔inj₁≡inj₁) id ⟩□
  fzero ≢ fzero  □

Distinct↔≢ {n = suc _} {fzero} {fsuc j} ext =
  ⊤               ↝⟨ inverse $ ¬⊥↔⊤ ext ⟩
  ¬ ⊥             ↝⟨ →-cong ext (from-bijection $ inverse Bijection.≡↔⊎) id ⟩□
  fzero ≢ fsuc j  □

Distinct↔≢ {n = suc _} {fsuc i} {fzero} ext =
  ⊤               ↝⟨ inverse $ ¬⊥↔⊤ ext ⟩
  ¬ ⊥             ↝⟨ →-cong ext (from-bijection $ inverse Bijection.≡↔⊎) id ⟩□
  fsuc i ≢ fzero  □

Distinct↔≢ {n = suc _} {fsuc i} {fsuc j} ext =
  Distinct i j     ↝⟨ Distinct↔≢ ext ⟩
  i ≢ j            ↝⟨ →-cong ext (from-bijection Bijection.≡↔inj₂≡inj₂) id ⟩□
  fsuc i ≢ fsuc j  □

-- For every i : Fin (suc n) there is a bijection between Fin n and
-- numbers in Fin (suc n) distinct from i.
--
-- The forward direction of this bijection corresponds to the function
-- "thin" from McBride's "First-order unification by structural
-- recursion", with an added inequality proof, and the other direction
-- is a total variant of "thick".

Fin↔Fin+≢ :
  ∀ {n} (i : Fin (suc n)) →
  Fin n ↔ ∃ λ (j : Fin (suc n)) → Distinct j i
Fin↔Fin+≢ {n} fzero =
  Fin n                                       ↝⟨ inverse ⊎-left-identity ⟩
  ⊥ ⊎ Fin n                                   ↝⟨ inverse $ id ⊎-cong ×-right-identity ⟩
  ⊥ ⊎ Fin n × ⊤                               ↝⟨ inverse $ ∃-Fin-suc _ ⟩□
  (∃ λ (j : Fin (suc n)) → Distinct j fzero)  □

Fin↔Fin+≢ {zero}  (fsuc ())
Fin↔Fin+≢ {suc n} (fsuc i)  =
  Fin (1 + n)                                    ↔⟨⟩
  ⊤ ⊎ Fin n                                      ↝⟨ id ⊎-cong Fin↔Fin+≢ i ⟩
  ⊤ ⊎ (∃ λ (j : Fin (1 + n)) → Distinct j i)     ↔⟨ inverse $ ∃-Fin-suc _ ⟩□
  (∃ λ (j : Fin (2 + n)) → Distinct j (fsuc i))  □
