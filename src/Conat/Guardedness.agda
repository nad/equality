------------------------------------------------------------------------
-- Conatural numbers defined using --guardedness rather than
-- --sized-types
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical=no-glue --guardedness #-}

import Equality.Path as P

module Conat.Guardedness
  {c⁺} (eq : ∀ {a p} → P.Equality-with-paths a p c⁺) where

open P.Derived-definitions-and-properties eq

open import Dec
open import Erased.Basics
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Bool equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Erased.Stability equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
import Nat equality-with-J as Nat

private variable
  A B     : Type _
  x       : A
  f p     : A → B
  n n₁ n₂ : ℕ

------------------------------------------------------------------------
-- The type

mutual

  -- "Conatural numbers": a coinductive variant of the natural
  -- numbers.

  data Conat : Type where
    zero : Conat
    suc  : Conat′ → Conat

  record Conat′ : Type where
    coinductive
    field
      force : Conat

open Conat′ public

private variable
  m m₁ m₂ m₃ : Conat

------------------------------------------------------------------------
-- Some operations

-- Conversion from Conat to Conat′.

conv : Conat → Conat′
conv m .force = m

-- The largest conatural number.

∞ : Conat
∞ = suc λ { .force → ∞ }

-- Turns natural numbers into conatural numbers.

⌜_⌝ : ℕ → Conat
⌜ zero  ⌝ = zero
⌜ suc m ⌝ = suc (conv ⌜ m ⌝)

------------------------------------------------------------------------
-- Bisimilarity

mutual

  -- Bisimilarity.

  infix 4 _∼_ _∼′_

  data _∼_ : Conat → Conat → Type where
    zero : zero ∼ zero
    suc  : ∀ {m₁ m₂} → m₁ ∼′ m₂ → suc m₁ ∼ suc m₂

  record _∼′_ (m₁ m₂ : Conat′) : Type where
    coinductive
    field
      force : m₁ .force ∼ m₂ .force

open _∼′_ public

opaque

  -- Bisimilarity is reflexive.

  reflexive-∼ : m ∼ m
  reflexive-∼ {m = zero}  = zero
  reflexive-∼ {m = suc _} = suc λ { .force → reflexive-∼ }

opaque

  -- Bisimilarity is symmetric.

  symmetric-∼ : m₁ ∼ m₂ → m₂ ∼ m₁
  symmetric-∼ zero    = zero
  symmetric-∼ (suc p) = suc λ { .force → symmetric-∼ (force p) }

opaque

  -- Bisimilarity is transitive.

  transitive-∼ : m₁ ∼ m₂ → m₂ ∼ m₃ → m₁ ∼ m₃
  transitive-∼ zero    zero    = zero
  transitive-∼ (suc p) (suc q) =
    suc λ { .force → transitive-∼ (force p) (force q) }

opaque

  -- Extensionality for bisimilarity.

  extensionality : m₁ ∼ m₂ → m₁ ≡ m₂
  extensionality = λ m₁∼m₂ → _↔_.from ≡↔≡ (ext m₁∼m₂)
    where
    mutual
      ext : m₁ ∼ m₂ → m₁ P.≡ m₂
      ext zero        _ = zero
      ext (suc m₁∼m₂) i = suc (ext′ m₁∼m₂ i)

      ext′ : ∀ {m₁ m₂} → m₁ ∼′ m₂ → m₁ P.≡ m₂
      ext′ m₁∼m₂ i .force = ext (m₁∼m₂ .force) i

------------------------------------------------------------------------
-- Ordering

-- Strict ordering.

infix 4 _<_

data _<_ : Conat → Conat → Type where
  zero : ∀ {m} → zero < suc m
  suc  : ∀ {m₁ m₂} → m₁ .force < m₂ .force → suc m₁ < suc m₂

opaque

  -- Everything in the image of ⌜_⌝ is strictly smaller than ∞.

  ⌜⌝<∞ : ⌜ n ⌝ < ∞
  ⌜⌝<∞ {n = zero}  = zero
  ⌜⌝<∞ {n = suc _} = suc ⌜⌝<∞

opaque

  -- It is not the case that ∞ is strictly smaller than something.

  ∞≮ : ¬ ∞ < m
  ∞≮ (suc ∞<) = ∞≮ ∞<

opaque

  -- The inequality ⌜ n ⌝ < ⌜ suc n ⌝ holds.

  <-suc : ⌜ n ⌝ < ⌜ suc n ⌝
  <-suc {n = zero}  = zero
  <-suc {n = suc _} = suc <-suc

opaque

  -- If ⌜ n₁ ⌝ < ⌜ n₂ ⌝, then ⌜ n₁ ⌝ < ⌜ suc n₂ ⌝.

  <-step : ⌜ n₁ ⌝ < ⌜ n₂ ⌝ → ⌜ n₁ ⌝ < ⌜ suc n₂ ⌝
  <-step = lemma _ _
    where
    lemma : ∀ n₁ n₂ → ⌜ n₁ ⌝ < ⌜ n₂ ⌝ → ⌜ n₁ ⌝ < ⌜ suc n₂ ⌝
    lemma _        zero     ()
    lemma zero     (suc n₂) zero        = zero
    lemma (suc n₁) (suc n₂) (suc n₁<n₂) = suc (<-step n₁<n₂)

opaque

  -- The inequality ⌜ n₁ ⌝ < ⌜ n₂ ⌝ holds if and only if n₁ Nat.< n₂
  -- holds.

  ⌜⌝<⌜⌝⇔< : ⌜ n₁ ⌝ < ⌜ n₂ ⌝ ⇔ n₁ Nat.< n₂
  ⌜⌝<⌜⌝⇔< = record { to = to _ _; from = from }
    where
    to : ∀ n₁ n₂ → ⌜ n₁ ⌝ < ⌜ n₂ ⌝ → n₁ Nat.< n₂
    to _        zero     ()
    to zero     (suc n₂) zero        = Nat.suc≤suc (Nat.zero≤ _)
    to (suc n₁) (suc n₂) (suc n₁<n₂) = Nat.suc≤suc (to _ _ n₁<n₂)

    from : n₁ Nat.< n₂ → ⌜ n₁ ⌝ < ⌜ n₂ ⌝
    from (Nat.≤-refl′ eq) =
      subst (_<_ _) (cong ⌜_⌝ eq) <-suc
    from (Nat.≤-step′ n₁<n₂ eq) =
      subst (_<_ _) (cong ⌜_⌝ eq) (<-step (from n₁<n₂))

------------------------------------------------------------------------
-- One can decide whether a function from Conat to Bool is true for
-- some input

-- This section is based on Escardó's "Infinite sets that Satisfy the
-- Principle of Omniscience in any Variety of Constructive
-- Mathematics" (doi:10.2178/jsl.7803040).

opaque

  -- If m is not bisimilar to any number in the image of ⌜_⌝, then m
  -- is bisimilar to ∞.

  ≁⌜⌝→∼∞ : @0 (∀ n → ¬ m ∼ ⌜ n ⌝) → m ∼ ∞
  ≁⌜⌝→∼∞ {m = zero}  hyp = ⊥-elim₀ (hyp zero reflexive-∼)
  ≁⌜⌝→∼∞ {m = suc _} hyp =
    suc λ where
      .force → ≁⌜⌝→∼∞ λ n eq → hyp (suc n) (suc λ { .force → eq })

opaque

  -- It is not the case that m is not bisimilar to ∞ and also not
  -- bisimilar to every number in the image of ⌜_⌝.

  ¬≁∞×≁⌜⌝ : ¬ (¬ m ∼ ∞ × (∀ n → ¬ m ∼ ⌜ n ⌝))
  ¬≁∞×≁⌜⌝ (≇∞ , ≇⌜⌝) = ≇∞ (≁⌜⌝→∼∞ ≇⌜⌝)

opaque

  -- If a function f from Conat to a type with decidable equality is
  -- constant on the image of ⌜_⌝ combined with ∞ (with a given fixed
  -- value x), then f is constant (with the same fixed value x).

  constant-if-constant-for-⌜⌝-∞ :
    ((x y : A) → Dec (x ≡ y)) →
    (f : Conat → A) →
    @0 (∀ n → f ⌜ n ⌝ ≡ x) →
    @0 f ∞ ≡ x →
    f m ≡ x
  constant-if-constant-for-⌜⌝-∞ {x} {m} _≟_ f hyp₁ hyp₂ =
    decided-stable (f m ≟ x) λ neq →
    ¬≁∞×≁⌜⌝
      ( (λ ∼∞ →
           neq
             (f m  ≡⟨ cong f (extensionality ∼∞) ⟩
              f ∞  ≡⟨ hyp₂ ⟩∎
              x    ∎))
      , (λ n ∼⌜n⌝ →
           neq
             (f m      ≡⟨ cong f (extensionality ∼⌜n⌝) ⟩
              f ⌜ n ⌝  ≡⟨ hyp₁ n ⟩∎
              x        ∎))
      )

private

  -- A function used in the implementation of search.

  next : (Conat → Bool) → (Conat → Bool)
  next f m = f (suc (conv m))

mutual

  -- A search procedure that returns the smallest number for which the
  -- predicate is true, if any.

  search : (Conat → Bool) → Conat
  search f = search′ f (f zero)

  private

    -- A function used in the implementation of search.

    search′ : (Conat → Bool) → Bool → Conat
    search′ f true  = zero
    search′ f false = suc λ { .force → search (next f) }

opaque

  -- The function search returns a number ⌜ n ⌝ if and only if the
  -- predicate is true for this number and false for all numbers that
  -- are, in a certain sense, smaller.

  ∼⌜⌝⇔ :
    search f ∼ ⌜ n ⌝ ⇔
    (f ⌜ n ⌝ ≡ true × ∀ {m} → m Nat.< n → f ⌜ m ⌝ ≡ false)
  ∼⌜⌝⇔ = record { to = to _ _; from = from _ _ }
    where
    to :
      ∀ f n → search f ∼ ⌜ n ⌝ →
      f ⌜ n ⌝ ≡ true × ∀ {m} → m Nat.< n → f ⌜ m ⌝ ≡ false
    to f zero hyp with f zero
    … | true  = refl _ , λ m<0 → ⊥-elim (Nat.≮0 _ m<0)
    … | false = case hyp of λ ()
    to f (suc n) hyp = lemma _ (refl _) hyp
      where
      lemma :
        ∀ b → f zero ≡ b → search′ f b ∼ ⌜ suc n ⌝ →
        f ⌜ suc n ⌝ ≡ true × ∀ {m} → m Nat.< suc n → f ⌜ m ⌝ ≡ false
      lemma true  _  ()
      lemma false eq (suc hyp) =
        Σ-map id
          (λ where
             _   {m = zero}  → λ _ → eq
             eqs {m = suc m} → eqs {m = m} ∘ Nat.suc≤suc⁻¹)
          (to (next f) n (hyp .force))

    from :
      ∀ f n → f ⌜ n ⌝ ≡ true × (∀ {m} → m Nat.< n → f ⌜ m ⌝ ≡ false) →
      search f ∼ ⌜ n ⌝
    from f zero (hyp , _) with f zero
    … | true  = zero
    … | false = ⊥-elim (Bool.true≢false (sym hyp))
    from f (suc n) (hyp₁ , hyp₂) = lemma _ (refl _)
      where
      lemma : ∀ b → f zero ≡ b → search′ f b ∼ ⌜ suc n ⌝
      lemma true eq =
        ⊥-elim $
        Bool.true≢false
          (true    ≡⟨ sym eq ⟩
           f zero  ≡⟨ hyp₂ (Nat.suc≤suc (Nat.zero≤ _)) ⟩∎
           false   ∎)
      lemma false _ =
        suc λ { .force → from (next f) n (hyp₁ , hyp₂ ∘ Nat.suc≤suc) }

opaque

  -- The function search returns ∞ if and only if the predicate is
  -- false for numbers in the image of ⌜_⌝.

  ∼∞⇔ : search f ∼ ∞ ⇔ (∀ n → f ⌜ n ⌝ ≡ false)
  ∼∞⇔ = record { to = to _; from = from _ }
    where
    to : ∀ f → search f ∼ ∞ → ∀ n → f ⌜ n ⌝ ≡ false
    to f hyp zero with f zero
    … | false = refl _
    … | true  = case hyp of λ ()
    to f hyp (suc n) = lemma _ hyp
      where
      lemma : ∀ b → search′ f b ∼ ∞ → f ⌜ suc n ⌝ ≡ false
      lemma true  ()
      lemma false (suc hyp) = to (next f) (hyp .force) n

    from : ∀ f → (∀ n → f ⌜ n ⌝ ≡ false) → search f ∼ ∞
    from f hyp = lemma _ (refl _)
      where
      lemma : ∀ b → f zero ≡ b → search′ f b ∼ ∞
      lemma false _  = suc λ { .force → from (next f) (hyp ∘ suc) }
      lemma true  eq =
        ⊥-elim $
        Bool.true≢false
          (true    ≡⟨ sym eq ⟩
           f zero  ≡⟨ hyp zero ⟩∎
           false   ∎)

opaque

  -- If p (search p) is false, then p m is false for every m.

  search-correct₁ :
    (p : Conat → Bool) →
    @0 p (search p) ≡ false →
    p m ≡ false
  search-correct₁ p hyp =
    constant-if-constant-for-⌜⌝-∞ Bool._≟_ p (∼∞⇔ ._⇔_.to ∼∞) ≡false
    where
    @0 ∼∞ : search p ∼ ∞
    ∼∞ =
      ≁⌜⌝→∼∞ λ n eq →
      Bool.true≢false
        (true          ≡⟨ sym (∼⌜⌝⇔ ._⇔_.to eq .proj₁) ⟩
         p ⌜ n ⌝       ≡⟨ sym (cong p (extensionality eq)) ⟩
         p (search p)  ≡⟨ hyp ⟩∎
         false         ∎)

    @0 ≡false : p ∞ ≡ false
    ≡false =
      p ∞           ≡⟨ sym (cong p (extensionality ∼∞)) ⟩
      p (search p)  ≡⟨ hyp ⟩∎
      false         ∎

opaque

  -- If p (search p) is true, then p m is false for all m strictly
  -- smaller than search p.

  search-correct₂ :
    @0 p (search p) ≡ true →
    @0 m < search p →
    p m ≡ false
  search-correct₂ hyp m< =
    Dec→Stable (_ Bool.≟ _)
      [ lemma _ hyp _ reflexive-∼ (refl _) m< ]
    where
    @0 lemma :
      ∀ p →
      p m₂ ≡ true →
      ∀ b →
      m₂ ∼ search′ p b →
      p zero ≡ b →
      m₁ < m₂ →
      p m₁ ≡ false
    lemma _ _   true  ()        _  zero
    lemma _ _   false _         eq zero                  = eq
    lemma _ _   true  ()        _  (suc _)
    lemma p hyp false (suc m₂∼) eq (suc {m₁} {m₂} m₁<m₂) =
      let eq =
            next p (m₂ .force)  ≡⟨ cong p (extensionality (suc (λ { .force → reflexive-∼ }))) ⟩
            p (suc m₂)          ≡⟨ hyp ⟩∎
            true                ∎
      in
      p (suc m₁)          ≡⟨ cong p (extensionality (suc (λ { .force → reflexive-∼ }))) ⟩
      next p (m₁ .force)  ≡⟨ lemma (next p) eq _ (m₂∼ .force) (refl _) m₁<m₂ ⟩∎
      false               ∎

-- Is the predicate true for some number?

exists : (Conat → Bool) → Bool
exists p = p (search p)

opaque

  -- The function exists is correct.

  exists-correct :
    (p : Conat → Bool) →
    if exists p then (∃ λ m → p m ≡ true) else (∀ m → p m ≡ false)
  exists-correct p = lemma _ (refl _)
    where
    lemma :
      ∀ b → exists p ≡ b →
      if b then (∃ λ m → p m ≡ true) else (∀ m → p m ≡ false)
    lemma true  eq = _ , eq
    lemma false eq = λ _ → search-correct₁ p eq

-- Is the predicate true for all numbers?
--
-- This kind of construction can be found in Escardó's "Seemingly
-- impossible functional programs"
-- (https://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/).

forevery : (Conat → Bool) → Bool
forevery p = not (exists (not ∘ p))

opaque

  -- The function forevery is correct.

  forevery-correct :
    (p : Conat → Bool) →
    if forevery p then (∀ m → p m ≡ true) else (∃ λ m → p m ≡ false)
  forevery-correct p =                                              $⟨ exists-correct (not ∘ p) ⟩
    if exists (not ∘ p)
    then (∃ λ m → not (p m) ≡ true) else (∀ m → not (p m) ≡ false)  ↔⟨ if-encoding (exists (not ∘ p)) ⟩

    T (exists (not ∘ p)) × (∃ λ m → not (p m) ≡ true) ⊎
    T (not (exists (not ∘ p))) × (∀ m → not (p m) ≡ false)          →⟨ subst T (sym (not-involutive (exists (not ∘ p))))
                                                                         ×-cong
                                                                       (∃-cong λ _ → _↔_.to not≡↔≡not)
                                                                         ⊎-cong
                                                                       F.id
                                                                         ×-cong
                                                                       (∀-cong _ λ _ → _↔_.to not≡↔≡not) ⟩
    T (not (not (exists (not ∘ p)))) × (∃ λ m → p m ≡ false) ⊎
    T (not (exists (not ∘ p))) × (∀ m → p m ≡ true)                 ↔⟨ ⊎-comm ⟩

    T (not (exists (not ∘ p))) × (∀ m → p m ≡ true) ⊎
    T (not (not (exists (not ∘ p)))) × (∃ λ m → p m ≡ false)        ↔⟨ inverse (if-encoding (not (exists (not ∘ p)))) ⟩□

    if not (exists (not ∘ p))
    then (∀ m → p m ≡ true) else (∃ λ m → p m ≡ false)              □
