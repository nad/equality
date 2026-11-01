------------------------------------------------------------------------
-- Normal forms used by Nat.Solver
------------------------------------------------------------------------

-- The code is based on "Proving Equalities in a Commutative Ring Done
-- Right in Coq" by Grégoire and Mahboubi, but specialised to natural
-- numbers.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Nat.Solver.Normal
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Bool eq
open import Equality.Decision-procedures eq
open import Function-universe eq as F hiding (id; _∘_)
open import List eq
open import Nat eq as N hiding (_≟_)

private variable
  k k₁ k₂ m m₁ m₂ n n₁ n₂ n₃ n₄ x : ℕ
  ρ                               : List ℕ

------------------------------------------------------------------------
-- Normal forms of polynomials

-- Sparse Horner normal forms.
--
-- The normal forms are not indexed by the number of variables, to
-- avoid equality proof computations at compile-time.

infix 7 _*x^1+_+_

data Normal : Type where
  -- A constant.
  con : (m : ℕ) → Normal

  -- "Lifts" the normal form the given number of steps, plus one: this
  -- means that the 1 + n "outermost" variables are out of scope in
  -- the argument.
  lift : (n : ℕ) → Normal → Normal

  -- The normal form p₁ *x^1+ k + p₂ stands for "p₁ times x^(1 + k)
  -- plus p₂", where x is the outermost variable. This variable is not
  -- in scope in p₂.
  _*x^1+_+_ : (p₁ : Normal) (k : ℕ) (p₂ : Normal) → Normal

private variable
  p p₁ p₂ p₃ p₄ : Normal

-- A head function that returns 0 for empty lists.

head : List ℕ → ℕ
head = head-with-default 0

-- The semantics of a normal form.
--
-- The first element in the environment (the list) is used for the
-- outermost variable, and so on. If there is no binding for a
-- variable in the environment, then that variable is treated as being
-- zero.

⟦_⟧ : Normal → List ℕ → ℕ
⟦ con n           ⟧ _ = n
⟦ lift n p        ⟧ ρ = ⟦ p ⟧ (drop (suc n) ρ)
⟦ p₁ *x^1+ k + p₂ ⟧ ρ = ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (tail ρ)

------------------------------------------------------------------------
-- Canonical normal forms

opaque

  -- Is the term an application of _*x^1+_+_?

  Plus : Normal → Type
  Plus (con _)         = ⊥
  Plus (lift _ _)      = ⊥
  Plus (_ *x^1+ _ + _) = ⊤

  -- Is the normal form allowed to be used as the first argument of a
  -- canonical application of _*x^1+_+_?

  OK-as-arg-1 : Normal → Type
  OK-as-arg-1 (con m)         = m ≢ 0
  OK-as-arg-1 (lift _ _)      = ⊤
  OK-as-arg-1 (_ *x^1+ _ + p) = p ≢ con 0

  -- Canonical normal forms.
  --
  -- The idea is that canonical normal forms should be unique, but
  -- that is not proved in this file.

  Canonical : Normal → Type
  Canonical (con _)           = ⊤
  Canonical (lift _ p)        = Plus p × Canonical p
  Canonical (p₁ *x^1+ _ + p₂) =
    OK-as-arg-1 p₁ × Canonical p₁ × Canonical p₂

------------------------------------------------------------------------
-- An equality test

-- An equality test for normal forms.

infix 4 _≟_

_≟_ : (_ _ : Normal) → Bool
con m₁           ≟ con m₂           = m₁ == m₂
lift n₁ p₁       ≟ lift n₂ p₂       = (n₁ == n₂) ∧ (p₁ ≟ p₂)
p₁ *x^1+ k₁ + p₂ ≟ p₃ *x^1+ k₂ + p₄ = (k₁ == k₂) ∧ (p₁ ≟ p₃) ∧ (p₂ ≟ p₄)
_                ≟ _                = false

opaque

  -- Injectivity lemmas.

  con-injective : con m₁ ≡ con m₂ → m₁ ≡ m₂
  con-injective = cong λ where
    (con m) → m
    _       → 0

  lift-injective : lift n₁ p₁ ≡ lift n₂ p₂ → n₁ ≡ n₂ × p₁ ≡ p₂
  lift-injective =
    _↔_.from ≡×≡↔≡ ∘ cong λ where
      (lift n p) → n , p
      _          → 0 , con 0

  *x^1++-injective :
    p₁ *x^1+ k₁ + p₂ ≡ p₃ *x^1+ k₂ + p₄ → k₁ ≡ k₂ × p₁ ≡ p₃ × p₂ ≡ p₄
  *x^1++-injective =
    _↔_.from (≡×≡↔≡ F.∘ ∃-cong (λ _ → ≡×≡↔≡)) ∘ cong λ where
      (p₁ *x^1+ k + p₂) → k , p₁ , p₂
      _                 → 0 , con 0 , con 0

  -- Disjointness lemmas.

  lift≢con : lift n p ≢ con m
  lift≢con = Bool.true≢false ∘ cong λ where
    (con _) → false
    _       → true

  *x^1++≢con : p₁ *x^1+ k + p₂ ≢ con m
  *x^1++≢con = Bool.true≢false ∘ cong λ where
    (con _) → false
    _       → true

  *x^1++≢lift : p₁ *x^1+ k + p₂ ≢ lift n p₃
  *x^1++≢lift = Bool.true≢false ∘ cong λ where
    (lift _ _) → false
    _          → true

opaque

  -- The equality test above is correctly implemented.

  ≟-correct : ∀ p₁ p₂ → T (p₁ ≟ p₂) ⇔ p₁ ≡ p₂
  ≟-correct (con m₁) (con m₂) =
    T (m₁ == m₂)     ↔⟨ T[==]↔≡ ⟩
    m₁ ≡ m₂          ↝⟨ record { to = cong con; from = con-injective } ⟩□
    con m₁ ≡ con m₂  □
  ≟-correct (lift n₁ p₁) (lift n₂ p₂) =
    T ((n₁ == n₂) ∧ (p₁ ≟ p₂))  ↔⟨ T-∧↔T×T (n₁ == _) ⟩
    T (n₁ == n₂) × T (p₁ ≟ p₂)  ↝⟨ from-isomorphism T[==]↔≡ ×-cong ≟-correct _ _ ⟩
    n₁ ≡ n₂ × p₁ ≡ p₂           ↝⟨ record { to = uncurry (cong₂ lift); from = lift-injective } ⟩□
    lift n₁ p₁ ≡ lift n₂ p₂     □
  ≟-correct (p₁ *x^1+ k₁ + p₂) (p₃ *x^1+ k₂ + p₄) =
    T ((k₁ == k₂) ∧ (p₁ ≟ p₃) ∧ (p₂ ≟ p₄))    ↔⟨ T-∧↔T×T (k₁ == _) ⟩
    T (k₁ == k₂) × T ((p₁ ≟ p₃) ∧ (p₂ ≟ p₄))  ↔⟨ T[==]↔≡ ×-cong T-∧↔T×T (p₁ ≟ _) ⟩
    k₁ ≡ k₂ × T (p₁ ≟ p₃) × T (p₂ ≟ p₄)       ↝⟨ F.id ×-cong ≟-correct _ _ ×-cong ≟-correct _ _ ⟩
    k₁ ≡ k₂ × p₁ ≡ p₃ × p₂ ≡ p₄               ↝⟨ record
                                                   { to   = λ (eq₁ , eq₂ , eq₃) → cong₂ (uncurry _*x^1+_+_) (cong₂ _,_ eq₂ eq₁) eq₃
                                                   ; from = *x^1++-injective
                                                   } ⟩□
    p₁ *x^1+ k₁ + p₂ ≡ p₃ *x^1+ k₂ + p₄       □
  ≟-correct (con _) (lift _ _) =
    record { to = λ (); from = lift≢con ∘ sym }
  ≟-correct (con _) (_ *x^1+ _ + _) =
    record { to = λ (); from = *x^1++≢con ∘ sym }
  ≟-correct (lift _ _) (con _) =
    record { to = λ (); from = lift≢con }
  ≟-correct (lift _ _) (_ *x^1+ _ + _) =
    record { to = λ (); from = *x^1++≢lift ∘ sym }
  ≟-correct (_ *x^1+ _ + _) (con _) =
    record { to = λ (); from = *x^1++≢con }
  ≟-correct (_ *x^1+ _ + _) (lift _ _) =
    record { to = λ (); from = *x^1++≢lift }

------------------------------------------------------------------------
-- Normalisation

-- Lifting.

liftᴺ : ℕ → Normal → Normal
liftᴺ _        (con m)     = con m
liftᴺ n₁       (lift n₂ p) = lift (n₁ + n₂) p
liftᴺ zero     p           = p
liftᴺ (suc n)  p           = lift n p

-- Variable zero.

var₀ᴺ : Normal
var₀ᴺ = con 1 *x^1+ 0 + con 0

-- The given variable.

varᴺ : ℕ → Normal
varᴺ x = liftᴺ x var₀ᴺ

mutual

  -- Addition.

  infixl 7 _+ᴺ_

  _+ᴺ_ : Normal → Normal → Normal
  con m₁             +ᴺ con m₂             = con (m₁ + m₂)
  con m              +ᴺ (p₁ *x^1+ k + p₂)  = p₁ *x^1+ k +
                                             (con m +ᴺ p₂)
  lift n p₁          +ᴺ p₂                 = lift-plus (suc n) p₁ p₂
  p₁                 +ᴺ lift n p₂          = plus-lift p₁ (suc n) p₂
  (p₁ *x^1+ k + p₂)  +ᴺ con m              = p₁ *x^1+ k +
                                             (p₂ +ᴺ con m)
  (p₁ *x^1+ k₁ + p₂) +ᴺ (p₃ *x^1+ k₂ + p₄) =
    plus-times (p₁ *x^1+ k₁ + (p₂ +ᴺ p₄)) p₃ (suc k₂)

  -- The normal form lift-plus n p₁ p₂ stands for "p₁, lifted n steps,
  -- plus p₂".

  lift-plus : ℕ → Normal → Normal → Normal
  lift-plus zero p₁ p₂ =
    p₁ +ᴺ p₂
  lift-plus (suc n) p (con m) =
    lift n (p +ᴺ con m)
  lift-plus (suc n₁) p₁ (lift n₂ p₂) =
    lift-helper n₁ p₁ n₂ p₂
  lift-plus (suc n) p₁ (p₂ *x^1+ k + p₃) =
    p₂ *x^1+ k + lift-plus n p₁ p₃

  -- The normal form plus-lift p₁ n p₂ stands for "p₁ plus (p₂, lifted
  -- n steps)". This function is not implemented in terms of lift-plus
  -- in the obvious way (plus-lift p₁ n p₂ = lift-plus n p₂ p₁)
  -- because that would (at the time of writing) make Agda's
  -- termination checker complain.

  plus-lift : Normal → ℕ → Normal → Normal
  plus-lift p₁ zero p₂ =
    p₁ +ᴺ p₂
  plus-lift (con m) (suc n) p =
    lift n (con m +ᴺ p)
  plus-lift (lift n₁ p₁) (suc n₂) p₂ =
    lift-helper n₁ p₁ n₂ p₂
  plus-lift (p₁ *x^1+ k + p₂) (suc n) p₃ =
    p₁ *x^1+ k + plus-lift p₂ n p₃

  private

    -- A function used in the implementations of lift-plus and
    -- plus-lift.

    lift-helper : ℕ → Normal → ℕ → Normal → Normal
    lift-helper n₁ p₁ n₂ p₂ with n₁ <= n₂
    … | true  = lift n₁ (plus-lift p₁ (n₂ ∸ n₁) p₂)
    … | false = lift n₂ (lift-plus (n₁ ∸ n₂) p₁ p₂)

  -- The normal form times-plus p₁ k p₂ stands for "p₁ times x^k plus
  -- p₂", where x is the outermost variable. Note that x is in scope
  -- in p₂.

  times-plus : Normal → ℕ → Normal → Normal
  times-plus p₁ zero p₂ =
    p₁ +ᴺ p₂
  times-plus p₁ (suc k) (con m) =
    p₁ *x^1+ k + con m
  times-plus p₁ (suc k) (lift zero p₂) =
    p₁ *x^1+ k + p₂
  times-plus p₁ (suc k) (lift (suc n) p₂) =
    p₁ *x^1+ k + lift n p₂
  times-plus p₁ (suc k₁) (p₂ *x^1+ k₂ + p₃) =
    times-helper p₁ k₁ p₂ k₂ p₃

  -- The normal form plus-times p₁ p₂ k stands for "p₁ plus p₂ times
  -- x^k", where x is the outermost variable. Note that x is in scope
  -- in p₂. This function is not implemented in terms of lift-plus in
  -- the obvious way (plus-times p₁ p₂ k = times-plus p₂ k p₁) because
  -- that would (at the time of writing) make Agda's termination
  -- checker complain.

  plus-times : Normal → Normal → ℕ → Normal
  plus-times p₁ p₂ zero =
    p₁ +ᴺ p₂
  plus-times (con m) p₂ (suc k) =
    p₂ *x^1+ k + con m
  plus-times (lift zero p₁) p₂ (suc k) =
    p₂ *x^1+ k + p₁
  plus-times (lift (suc n) p₁) p₂ (suc k) =
    p₂ *x^1+ k + lift n p₁
  plus-times (p₁ *x^1+ k₁ + p₂) p₃ (suc k₂) =
    times-helper p₁ k₁ p₃ k₂ p₂

  private

    -- A function used in the implementations of times-plus and
    -- plus-times.

    times-helper : Normal → ℕ → Normal → ℕ → Normal → Normal
    times-helper p₁ k₁ p₂ k₂ p₃ with k₁ <= k₂
    … | true  = plus-times p₁ p₂ (k₂ ∸ k₁) *x^1+ k₁ + p₃
    … | false = times-plus p₁ (k₁ ∸ k₂) p₂ *x^1+ k₂ + p₃

-- The normal form p₁ *x k + p₂ stands for "p₁ times x^k plus p₂",
-- where x is the outermost variable. This variable is not in scope in
-- p₂.

infix 7 _*x^_+_

_*x^_+_ : Normal → ℕ → Normal → Normal
p₁                    *x^ zero   + p₂ = p₁ +ᴺ liftᴺ 1 p₂
con 0                 *x^ _      + p₂ = liftᴺ 1 p₂
(p₁ *x^1+ k₁ + con 0) *x^ k₂     + p₂ = p₁ *x^1+ (k₁ + k₂) + p₂
p₁                    *x^ suc k₂ + p₂ = p₁ *x^1+ k₂ + p₂

-- The normal form times-plusᶜ p₁ k p₂ stands for "p₁ times x^k plus
-- p₂", where x is the outermost variable. Note that x is in scope
-- in p₂.
--
-- Unlike times-plus this function produces canonical forms given only
-- the assumption that both normal form arguments are canonical (see
-- ¬-times-plus-Canonical and times-plusᶜ-Canonical below).

times-plusᶜ : Normal → ℕ → Normal → Normal
times-plusᶜ p₁ zero p₂ =
  p₁ +ᴺ p₂
times-plusᶜ p₁ (suc k) (con m) =
  p₁ *x^ suc k + con m
times-plusᶜ p₁ (suc k) (lift zero p₂) =
  p₁ *x^ suc k + p₂
times-plusᶜ p₁ (suc k) (lift (suc n) p₂) =
  p₁ *x^ suc k + lift n p₂
times-plusᶜ p₁ (suc k₁) (p₂ *x^1+ k₂ + p₃) with k₁ <= k₂
… | true  = times-plusᶜ p₂ (k₂ ∸ k₁) p₁ *x^ suc k₁ + p₃
… | false = times-plusᶜ p₁ (k₁ ∸ k₂) p₂ *x^ suc k₂ + p₃

mutual

  -- Multiplication.

  infixl 8 _*ᴺ_

  _*ᴺ_ : Normal → Normal → Normal
  con m₁             *ᴺ con m₂             = con (m₁ * m₂)
  con 0              *ᴺ (_ *x^1+ _ + _)    = con 0
  con m              *ᴺ (p₁ *x^1+ k + p₂)  = con m *ᴺ p₁ *x^1+ k +
                                             con m *ᴺ p₂
  lift n p₁          *ᴺ p₂                 = lift-times (suc n) p₁ p₂
  p₁                 *ᴺ lift n p₂          = times-lift p₁ (suc n) p₂
  (_ *x^1+ _ + _)    *ᴺ con 0              = con 0
  (p₁ *x^1+ k + p₂)  *ᴺ con m              = p₁ *ᴺ con m *x^1+ k +
                                             p₂ *ᴺ con m
  (p₁ *x^1+ k₁ + p₂) *ᴺ (p₃ *x^1+ k₂ + p₄) with k₁ <= k₂
  … | true =
    times-plusᶜ
      (times-plusᶜ
         (times-plusᶜ (p₁ *ᴺ p₃) (suc k₁) (lift-times 1 p₂ p₃))
         (k₂ ∸ k₁) (times-lift p₁ 1 p₄))
      (suc k₁) (liftᴺ 1 (p₂ *ᴺ p₄))
  … | false =
    times-plusᶜ
      (times-plusᶜ
         (times-plusᶜ (p₁ *ᴺ p₃) (suc k₂) (times-lift p₁ 1 p₄))
         (k₁ ∸ k₂) (lift-times 1 p₂ p₃))
      (suc k₂) (liftᴺ 1 (p₂ *ᴺ p₄))

  -- The normal form lift-times n p₁ p₂ stands for "p₁, lifted n
  -- steps, times p₂".

  lift-times : ℕ → Normal → Normal → Normal
  lift-times zero p₁ p₂ =
    p₁ *ᴺ p₂
  lift-times (suc n) p (con m) =
    liftᴺ (suc n) (p *ᴺ con m)
  lift-times (suc n₁) p₁ (lift n₂ p₂) with n₁ <= n₂
  … | true  = liftᴺ (suc n₁) (times-lift p₁ (n₂ ∸ n₁) p₂)
  … | false = liftᴺ (suc n₂) (lift-times (n₁ ∸ n₂) p₁ p₂)
  lift-times (suc n) p₁ (p₂ *x^1+ k + p₃) =
    lift-times (suc n) p₁ p₂ *x^ suc k + lift-times n p₁ p₃

  -- The normal form times-lift p₁ n p₂ stands for "p₁ times (p₂,
  -- lifted n steps)".

  times-lift : Normal → ℕ → Normal → Normal
  times-lift p₁ n p₂ = lift-times n p₂ p₁

-- Exponentiation.
--
-- This function could perhaps be optimised.

infixr 9 _^ᴺ_

_^ᴺ_ : Normal → ℕ → Normal
p ^ᴺ zero  = con 1
p ^ᴺ suc n = p *ᴺ p ^ᴺ n

------------------------------------------------------------------------
-- Normalisation produces correct values

-- These properties establish that the normalisation functions defined
-- above produce normal forms with the right semantics. See below for
-- proofs showing that the functions produce canonical normal forms,
-- given canonical inputs.

private opaque

  -- Some lemmas used below.

  *^∸*^suc≡*^suc :
    ∀ m → k₂ ≤ k₁ →
    m * n ^ (k₁ ∸ k₂) * n ^ suc k₂ ≡
    m * n ^ suc k₁
  *^∸*^suc≡*^suc {k₂} {k₁} {n} m k₂≤k₁ =
    m * n ^ (k₁ ∸ k₂) * n ^ suc k₂    ≡⟨ sym (*-assoc m) ⟩
    m * (n ^ (k₁ ∸ k₂) * n ^ suc k₂)  ≡⟨ cong (_*_ m) (sym (^+≡^*^ (_ ∸ k₂))) ⟩
    m * n ^ (k₁ ∸ k₂ + suc k₂)        ≡⟨ cong (_*_ m ∘ _^_ _) (sym (suc+≡+suc (_ ∸ k₂))) ⟩
    m * n ^ suc (k₁ ∸ k₂ + k₂)        ≡⟨ cong (_*_ m ∘ _^_ n ∘ suc) (∸+≡ k₂≤k₁) ⟩∎
    m * n ^ suc k₁                    ∎

  **^*^≡**^+ :
    ∀ m k₁ → m * n ^ k₁ * n ^ k₂ ≡ m * n ^ (k₁ + k₂)
  **^*^≡**^+ {n} {k₂} m k₁ =
    m * n ^ k₁ * n ^ k₂    ≡⟨ sym (*-assoc m) ⟩
    m * (n ^ k₁ * n ^ k₂)  ≡⟨ cong (_*_ m) (sym (^+≡^*^ k₁)) ⟩∎
    m * n ^ (k₁ + k₂)      ∎

  *-lemmaᵃ :
    ∀ n₁ → k₁ ≤ k₂ →
    ((n₁ * x ^ k₁ + n₂) * x ^ (k₂ ∸ k₁) + n₃) * x ^ k₁ + n₄ ≡
    n₁ * x ^ (k₂ + k₁) +
    n₂ * x ^ k₂ +
    n₃ * x ^ k₁ +
    n₄
  *-lemmaᵃ {k₁} {k₂} {x} {n₂} {n₃} {n₄} n₁ k₁≤k₂ =
    ((n₁ * x ^ k₁ + n₂) * x ^ (k₂ ∸ k₁) + n₃) * x ^ k₁ + n₄              ≡⟨ cong (flip _+_ _) $ cong (flip _*_ _) $ cong (flip _+_ _) $
                                                                            trans (*-+-distribʳ (n₁ * _)) $
                                                                            cong (flip _+_ (n₂ * _)) $
                                                                            **^*^≡**^+ {k₂ = _ ∸ k₁} n₁ k₁ ⟩

    (n₁ * x ^ (k₁ + (k₂ ∸ k₁)) + n₂ * x ^ (k₂ ∸ k₁) + n₃) * x ^ k₁ + n₄  ≡⟨ cong (flip _+_ _) $ cong (flip _*_ _) $ cong (flip _+_ _) $
                                                                            cong (flip _+_ _) $ cong (_*_ n₁) $ cong (x ^_) $
                                                                            +[∸]≡ k₁≤k₂ ⟩

    (n₁ * x ^ k₂ + n₂ * x ^ (k₂ ∸ k₁) + n₃) * x ^ k₁ + n₄                ≡⟨ cong (flip _+_ n₄) $
                                                                            trans (*-+-distribʳ (n₁ * _ + _)) $
                                                                            cong (flip _+_ (n₃ * _)) $
                                                                            trans (*-+-distribʳ (n₁ * _)) $
                                                                            cong₂ _+_ (**^*^≡**^+ n₁ k₂) (**^*^≡**^+ n₂ (_ ∸ k₁)) ⟩
    n₁ * x ^ (k₂ + k₁) +
    n₂ * x ^ (k₂ ∸ k₁ + k₁) +
    n₃ * x ^ k₁ +
    n₄                                                                   ≡⟨ cong (flip _+_ n₄) $ cong (flip _+_ (n₃ * _)) $ cong (_+_ _) $
                                                                            cong ((n₂ *_) ∘ (_^_ x)) $
                                                                            trans (sym (+-comm k₁)) $
                                                                            +[∸]≡ k₁≤k₂ ⟩∎
    n₁ * x ^ (k₂ + k₁) +
    n₂ * x ^ k₂ +
    n₃ * x ^ k₁ +
    n₄                                                                   ∎

  *-lemmaᵇ :
    ∀ m₁ k₁ →
    (m₁ * x ^ k₁ + n₁) * (m₂ * x ^ k₂ + n₂) ≡
    m₁ * m₂ * x ^ (k₁ + k₂) +
    m₁ * n₂ * x ^ k₁ +
    n₁ * m₂ * x ^ k₂ +
    n₁ * n₂
  *-lemmaᵇ {x} {n₁} {m₂} {k₂} {n₂} m₁ k₁ =
    (m₁ * x ^ k₁ + n₁) * (m₂ * x ^ k₂ + n₂)  ≡⟨ *-+-distribʳ (m₁ * _) ⟩

    m₁ * x ^ k₁ * (m₂ * x ^ k₂ + n₂) +
    n₁ * (m₂ * x ^ k₂ + n₂)                  ≡⟨ cong₂ _+_ (*-+-distribˡ (m₁ * _)) (*-+-distribˡ n₁) ⟩

    (m₁ * x ^ k₁) * (m₂ * x ^ k₂) +
    (m₁ * x ^ k₁) * n₂ +
    (n₁ * (m₂ * x ^ k₂) + n₁ * n₂)           ≡⟨ cong₂ _+_
                                                  (cong₂ _+_
                                                     (trans (*-assoc (m₁ * _)) $
                                                      trans
                                                         (cong (flip _*_ _) $
                                                          trans (sym (*-assoc m₁)) $
                                                          trans (cong (_*_ m₁) (sym (*-comm m₂))) $
                                                          *-assoc m₁) $
                                                      **^*^≡**^+ (m₁ * _) k₁)
                                                     (trans (sym (*-assoc m₁)) $
                                                      trans (cong (_*_ m₁) (sym (*-comm n₂))) $
                                                      *-assoc m₁))
                                                  (cong (flip _+_ _) $
                                                   *-assoc n₁) ⟩
    m₁ * m₂ * x ^ (k₁ + k₂) +
    m₁ * n₂ * x ^ k₁ +
    (n₁ * m₂ * x ^ k₂ + n₁ * n₂)             ≡⟨ +-assoc (m₁ * _ * _ + _) ⟩∎

    m₁ * m₂ * x ^ (k₁ + k₂) +
    m₁ * n₂ * x ^ k₁ +
    n₁ * m₂ * x ^ k₂ +
    n₁ * n₂                                  ∎

  *-lemma₁ :
    ∀ m₁ → k₁ ≤ k₂ →
    ((m₁ * m₂ * x ^ suc k₁ + n₁ * m₂) * x ^ (k₂ ∸ k₁) + m₁ * n₂) *
      x ^ suc k₁ +
    n₁ * n₂ ≡
    (m₁ * x ^ suc k₁ + n₁) * (m₂ * x ^ suc k₂ + n₂)
  *-lemma₁ {k₁} {k₂} {m₂} {x} {n₁} {n₂} m₁ k₁≤k₂ =
    ((m₁ * m₂ * x ^ suc k₁ + n₁ * m₂) * x ^ (k₂ ∸ k₁) + m₁ * n₂) *
      x ^ suc k₁ +
    n₁ * n₂                                                         ≡⟨ *-lemmaᵃ (m₁ * _) (suc≤suc k₁≤k₂) ⟩

    m₁ * m₂ * x ^ (suc k₂ + suc k₁) +
    n₁ * m₂ * x ^ suc k₂ +
    m₁ * n₂ * x ^ suc k₁ +
    n₁ * n₂                                                         ≡⟨ cong (flip _+_ (n₁ * _)) $
                                                                       trans (sym (+-assoc (m₁ * _ * _))) $
                                                                       trans
                                                                         (cong₂ _+_
                                                                            (cong (_*_ (m₁ * _)) $ cong (x ^_) (+-comm (suc k₂)))
                                                                            (+-comm (n₁ * _ * _))) $
                                                                       +-assoc (m₁ * _ * _) ⟩
    m₁ * m₂ * x ^ (suc k₁ + suc k₂) +
    m₁ * n₂ * x ^ suc k₁ +
    n₁ * m₂ * x ^ suc k₂ +
    n₁ * n₂                                                         ≡⟨ sym (*-lemmaᵇ {x = x} m₁ (suc k₁)) ⟩∎

    (m₁ * x ^ suc k₁ + n₁) * (m₂ * x ^ suc k₂ + n₂)                 ∎

  *-lemma₂ :
    ∀ m₁ → k₁ ≤ k₂ →
    ((m₁ * m₂ * x ^ suc k₁ + m₁ * n₂) * x ^ (k₂ ∸ k₁) + n₁ * m₂) *
      x ^ suc k₁ +
    n₁ * n₂ ≡
    (m₁ * x ^ suc k₂ + n₁) * (m₂ * x ^ suc k₁ + n₂)
  *-lemma₂ {k₁} {k₂} {m₂} {x} {n₂} {n₁} m₁ k₁≤k₂ =
    ((m₁ * m₂ * x ^ suc k₁ + m₁ * n₂) * x ^ (k₂ ∸ k₁) + n₁ * m₂) *
      x ^ suc k₁ +
    n₁ * n₂                                                         ≡⟨ *-lemmaᵃ (m₁ * _) (suc≤suc k₁≤k₂) ⟩

    m₁ * m₂ * x ^ (suc k₂ + suc k₁) +
    m₁ * n₂ * x ^ suc k₂ +
    n₁ * m₂ * x ^ suc k₁ +
    n₁ * n₂                                                         ≡⟨ sym (*-lemmaᵇ {x = x} m₁ (suc k₂)) ⟩∎

    (m₁ * x ^ suc k₂ + n₁) * (m₂ * x ^ suc k₁ + n₂)                 ∎

opaque

  -- The function liftᴺ is correctly defined.

  liftᴺ-correct :
    ∀ n p →
    ⟦ liftᴺ n p ⟧ ρ ≡
    ⟦ p ⟧ (drop n ρ)
  liftᴺ-correct _ (con _) =
    refl _
  liftᴺ-correct {ρ} n (lift m p) =
    ⟦ p ⟧ (drop (suc (n + m)) ρ)        ≡⟨ cong ⟦ p ⟧ (cong (flip drop _) (suc+≡+suc n)) ⟩
    ⟦ p ⟧ (drop (n + suc m) ρ)          ≡⟨ cong ⟦ p ⟧ (sym (drop-drop n)) ⟩∎
    ⟦ p ⟧ (drop (suc m) (drop n ρ))  ∎
  liftᴺ-correct {ρ} zero (p₁ *x^1+ k + p₂) =
    ⟦ p₁ *x^1+ k + p₂ ⟧ ρ  ∎
  liftᴺ-correct {ρ} (suc n) (p₁ *x^1+ k + p₂) =
    ⟦ p₁ *x^1+ k + p₂ ⟧ (drop (suc n) ρ)  ∎

opaque

  -- A variant of liftᴺ-correct.

  liftᴺ-1-correct :
    ∀ p →
    ⟦ liftᴺ 1 p ⟧ ρ ≡
    ⟦ p ⟧ (tail ρ)
  liftᴺ-1-correct {ρ} p =
    ⟦ liftᴺ 1 p ⟧ ρ      ≡⟨ liftᴺ-correct 1 p ⟩
    ⟦ p ⟧ (drop 1 ρ)  ≡⟨ cong ⟦ p ⟧ (sym (tail≡drop-1 ρ)) ⟩∎
    ⟦ p ⟧ (tail ρ)    ∎

opaque

  -- The function var₀ᴺ is correctly defined.

  var₀ᴺ-correct :
    ∀ ρ →
    ⟦ var₀ᴺ ⟧ ρ ≡
    head ρ
  var₀ᴺ-correct [] =
    0  ∎
  var₀ᴺ-correct (n ∷ _) =
    1 * n ^ 1 + 0  ≡⟨ +-right-identity ⟩
    1 * n ^ 1      ≡⟨ *-left-identity ⟩
    n ^ 1          ≡⟨ ^-right-identity ⟩∎
    n              ∎

opaque

  -- The function varᴺ is correctly defined.

  varᴺ-correct :
    (x : ℕ) →
    ⟦ varᴺ x ⟧ ρ ≡ index-with-default 0 ρ x
  varᴺ-correct {ρ} x =
    ⟦ liftᴺ x var₀ᴺ ⟧ ρ       ≡⟨ liftᴺ-correct x (con 1 *x^1+ 0 + con 0) ⟩
    ⟦ var₀ᴺ ⟧ (drop x ρ)      ≡⟨ var₀ᴺ-correct (drop x ρ) ⟩
    head (drop x ρ)           ≡⟨ sym (index-head-drop x) ⟩∎
    index-with-default 0 ρ x  ∎

opaque mutual

  -- The function _+ᴺ_ is correctly defined.

  +ᴺ-correct :
    ∀ p₁ p₂ →
    ⟦ p₁ +ᴺ p₂ ⟧ ρ ≡ ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ
  +ᴺ-correct (con m₁) (con m₂) =
    m₁ + m₂  ∎
  +ᴺ-correct {ρ} (con m) (p₁ *x^1+ k + p₂) =
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ con m +ᴺ p₂ ⟧ (tail ρ)  ≡⟨ cong (_+_ _) (+ᴺ-correct (con m) p₂) ⟩
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + (m + ⟦ p₂ ⟧ (tail ρ))     ≡⟨ +-assoc (⟦ p₁ ⟧ _ * _) ⟩
    (⟦ p₁ ⟧ ρ * head ρ ^ suc k + m) + ⟦ p₂ ⟧ (tail ρ)     ≡⟨ cong (flip _+_ _) (+-comm (⟦ p₁ ⟧ _ * _)) ⟩
    (m + ⟦ p₁ ⟧ ρ * head ρ ^ suc k) + ⟦ p₂ ⟧ (tail ρ)     ≡⟨ sym (+-assoc m) ⟩∎
    m + (⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (tail ρ))     ∎
  +ᴺ-correct (lift n p₁) p₂ =
    lift-plus-correct (suc n) p₁ p₂
  +ᴺ-correct {ρ} p₁@(con _) (lift n p₂) =
    plus-lift-correct {ρ = ρ} p₁ (suc n) p₂
  +ᴺ-correct p₁@(_ *x^1+ _ + _) (lift n p₂) =
    plus-lift-correct p₁ (suc n) p₂
  +ᴺ-correct {ρ} (p₁ *x^1+ k + p₂) (con m) =
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ +ᴺ con m ⟧ (tail ρ)  ≡⟨ cong (_+_ _) (+ᴺ-correct p₂ (con m)) ⟩
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + (⟦ p₂ ⟧ (tail ρ) + m)     ≡⟨ +-assoc (⟦ p₁ ⟧ _ * _) ⟩∎
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (tail ρ) + m       ∎
  +ᴺ-correct {ρ} (p₁ *x^1+ k₁ + p₂) (p₃ *x^1+ k₂ + p₄) =
    ⟦ plus-times (p₁ *x^1+ k₁ + (p₂ +ᴺ p₄)) p₃ (suc k₂) ⟧ ρ  ≡⟨ plus-times-correct (p₁ *x^1+ k₁ + (p₂ +ᴺ p₄)) p₃ (suc k₂) ⟩

    ⟦ p₁ *x^1+ k₁ + (p₂ +ᴺ p₄) ⟧ ρ +
    ⟦ p₃ ⟧ ρ * head ρ ^ suc k₂                               ≡⟨⟩

    (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ +ᴺ p₄ ⟧ (tail ρ)) +
    ⟦ p₃ ⟧ ρ * head ρ ^ suc k₂                               ≡⟨ cong (flip _+_ (⟦ p₃ ⟧ _ * _) ∘ _+_ (⟦ p₁ ⟧ _ * _)) $
                                                                +ᴺ-correct p₂ p₄ ⟩
    (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ +
     (⟦ p₂ ⟧ (tail ρ) + ⟦ p₄ ⟧ (tail ρ))) +
    ⟦ p₃ ⟧ ρ * head ρ ^ suc k₂                               ≡⟨ cong (flip _+_ _) (+-assoc (⟦ p₁ ⟧ _ * _)) ⟩

    ((⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ ⟧ (tail ρ)) +
     ⟦ p₄ ⟧ (tail ρ)) +
    ⟦ p₃ ⟧ ρ * head ρ ^ suc k₂                               ≡⟨ sym (+-assoc (⟦ p₁ ⟧ _ * _ + _)) ⟩

    (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ ⟧ (tail ρ)) +
    (⟦ p₄ ⟧ (tail ρ) + ⟦ p₃ ⟧ ρ * head ρ ^ suc k₂)           ≡⟨ cong (_+_ (⟦ p₁ ⟧ _ * _ + _)) (+-comm (⟦ p₄ ⟧ _)) ⟩

    (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ ⟧ (tail ρ)) +
    (⟦ p₃ ⟧ ρ * head ρ ^ suc k₂ + ⟦ p₄ ⟧ (tail ρ))           ≡⟨⟩

    ⟦ p₁ *x^1+ k₁ + p₂ ⟧ ρ + ⟦ p₃ *x^1+ k₂ + p₄ ⟧ ρ          ∎

  -- The function lift-plus is correctly defined.

  lift-plus-correct :
    ∀ n p₁ p₂ →
    ⟦ lift-plus n p₁ p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ (drop n ρ) + ⟦ p₂ ⟧ ρ
  lift-plus-correct {ρ} zero p₁ p₂ =
    ⟦ p₁ +ᴺ p₂ ⟧ ρ       ≡⟨ +ᴺ-correct p₁ p₂ ⟩∎
    ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ  ∎
  lift-plus-correct {ρ} (suc n) p (con m) =
    ⟦ p +ᴺ con m ⟧ (drop (suc n) ρ)  ≡⟨ +ᴺ-correct p (con m) ⟩∎
    ⟦ p ⟧ (drop (suc n) ρ) + m       ∎
  lift-plus-correct (suc n₁) p₁ (lift n₂ p₂) =
    lift-helper-correct n₁ p₁ n₂ p₂
  lift-plus-correct {ρ} (suc m) p₁ (p₂ *x^1+ k + p₃) =
    ⟦ p₂ ⟧ ρ * head ρ ^ suc k + ⟦ lift-plus m p₁ p₃ ⟧ (tail ρ)  ≡⟨ cong (⟦ p₂ ⟧ _ * _ +_) (lift-plus-correct m p₁ p₃) ⟩

    ⟦ p₂ ⟧ ρ * head ρ ^ suc k +
    (⟦ p₁ ⟧ (drop m (tail ρ)) + ⟦ p₃ ⟧ (tail ρ))                ≡⟨ cong (_+_ (⟦ p₂ ⟧ _ * _) ∘ flip _+_ _ ∘ ⟦ p₁ ⟧) $
                                                                   drop-tail ρ ⟩
    ⟦ p₂ ⟧ ρ * head ρ ^ suc k +
    (⟦ p₁ ⟧ (drop (suc m) ρ) + ⟦ p₃ ⟧ (tail ρ))                 ≡⟨ trans (+-assoc (⟦ p₂ ⟧ _ * _)) $
                                                                   trans (cong (_+ ⟦ p₃ ⟧ (tail ρ)) (+-comm (⟦ p₂ ⟧ _ * _))) $
                                                                   sym (+-assoc (⟦ p₁ ⟧ _)) ⟩∎
    ⟦ p₁ ⟧ (drop (suc m) ρ) +
    (⟦ p₂ ⟧ ρ * head ρ ^ suc k + ⟦ p₃ ⟧ (tail ρ))               ∎

  -- The function plus-lift is correctly defined.

  plus-lift-correct :
    ∀ p₁ n p₂ →
    ⟦ plus-lift p₁ n p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ (drop n ρ)
  plus-lift-correct {ρ} p₁ zero p₂ =
    ⟦ p₁ +ᴺ p₂ ⟧ ρ       ≡⟨ +ᴺ-correct p₁ p₂ ⟩∎
    ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ  ∎
  plus-lift-correct {ρ} (con m) (suc n) p =
    ⟦ con m +ᴺ p ⟧ (drop (suc n) ρ)  ≡⟨ +ᴺ-correct (con m) p ⟩∎
    m + ⟦ p ⟧ (drop (suc n) ρ)       ∎
  plus-lift-correct (lift n₁ p₁) (suc n₂) p₂ =
    lift-helper-correct n₁ p₁ n₂ p₂
  plus-lift-correct {ρ} (p₁ *x^1+ k + p₂) (suc m) p₃ =
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ plus-lift p₂ m p₃ ⟧ (tail ρ)  ≡⟨ cong (⟦ p₁ ⟧ _ * _ +_) (plus-lift-correct p₂ m p₃) ⟩

    ⟦ p₁ ⟧ ρ * head ρ ^ suc k +
    (⟦ p₂ ⟧ (tail ρ) + ⟦ p₃ ⟧ (drop m (tail ρ)))                ≡⟨ cong (_+_ (⟦ p₁ ⟧ _ * _) ∘ _+_ _ ∘ ⟦ p₃ ⟧) $
                                                                   drop-tail ρ ⟩
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k +
    (⟦ p₂ ⟧ (tail ρ) + ⟦ p₃ ⟧ (drop (suc m) ρ))                 ≡⟨ +-assoc (⟦ p₁ ⟧ _ * _) ⟩∎

    ⟦ p₁ ⟧ ρ * head ρ ^ suc k +
    ⟦ p₂ ⟧ (tail ρ) + ⟦ p₃ ⟧ (drop (suc m) ρ)                   ∎

  private

    -- The function lift-helper is correctly defined.

    lift-helper-correct :
      ∀ n₁ p₁ n₂ p₂ →
      ⟦ lift-helper n₁ p₁ n₂ p₂ ⟧ ρ ≡
      ⟦ p₁ ⟧ (drop (suc n₁) ρ) +
      ⟦ p₂ ⟧ (drop (suc n₂) ρ)
    lift-helper-correct {ρ} n₁ p₁ n₂ p₂
      with n₁ <= n₂ | T[<=]↔≤ {m = n₁} {n = n₂}
    … | true | n₁≤n₂↔ =
      ⟦ plus-lift p₁ (n₂ ∸ n₁) p₂ ⟧ (drop (suc n₁) ρ)      ≡⟨ plus-lift-correct p₁ (n₂ ∸ n₁) p₂ ⟩

      ⟦ p₁ ⟧ (drop (suc n₁) ρ) +
      ⟦ p₂ ⟧ (drop (n₂ ∸ n₁) (drop (suc n₁) ρ))            ≡⟨ cong ((⟦ p₁ ⟧ _ +_) ∘ ⟦ p₂ ⟧) $
                                                              drop-drop {xs = ρ} (suc n₁) ⟩
      ⟦ p₁ ⟧ (drop (suc n₁) ρ) +
      ⟦ p₂ ⟧ (drop (suc n₁ + (n₂ ∸ n₁)) ρ)                 ≡⟨ cong ((⟦ p₁ ⟧ _ +_) ∘ ⟦ p₂ ⟧ ∘ flip drop ρ ∘ suc) $
                                                              +[∸]≡ (_↔_.to n₁≤n₂↔ _) ⟩∎
      ⟦ p₁ ⟧ (drop (suc n₁) ρ) + ⟦ p₂ ⟧ (drop (suc n₂) ρ)  ∎
    … | false | n₁≤n₂↔ =
      ⟦ lift-plus (n₁ ∸ n₂) p₁ p₂ ⟧ (drop (suc n₂) ρ)      ≡⟨ lift-plus-correct (n₁ ∸ n₂) p₁ p₂ ⟩

      ⟦ p₁ ⟧ (drop (n₁ ∸ n₂) (drop (suc n₂) ρ)) +
      ⟦ p₂ ⟧ (drop (suc n₂) ρ)                             ≡⟨ cong ((_+ ⟦ p₂ ⟧ _) ∘ ⟦ p₁ ⟧) $
                                                              drop-drop {xs = ρ} (suc n₂) ⟩
      ⟦ p₁ ⟧ (drop (suc n₂ + (n₁ ∸ n₂)) ρ) +
      ⟦ p₂ ⟧ (drop (suc n₂) ρ)                             ≡⟨ cong ((_+ ⟦ p₂ ⟧ _) ∘ ⟦ p₁ ⟧ ∘ flip drop ρ ∘ suc) $
                                                              +[∸]≡ (≰→≥ (_↔_.from n₁≤n₂↔)) ⟩∎
      ⟦ p₁ ⟧ (drop (suc n₁) ρ) + ⟦ p₂ ⟧ (drop (suc n₂) ρ)  ∎

  -- The function times-plus is correctly defined.

  times-plus-correct :
    ∀ p₁ k p₂ →
    ⟦ times-plus p₁ k p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ ρ * head ρ ^ k + ⟦ p₂ ⟧ ρ
  times-plus-correct {ρ} p₁ zero p₂ =
    ⟦ p₁ +ᴺ p₂ ⟧ ρ           ≡⟨ +ᴺ-correct p₁ p₂ ⟩
    ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ      ≡⟨ cong (flip _+_ _) (sym (*-right-identity (⟦ p₁ ⟧ _))) ⟩∎
    ⟦ p₁ ⟧ ρ * 1 + ⟦ p₂ ⟧ ρ  ∎
  times-plus-correct {ρ} p (suc k) (con m) =
    ⟦ p ⟧ ρ * head ρ ^ suc k + m  ∎
  times-plus-correct {ρ} p₁ (suc k) (lift zero p₂) =
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (tail ρ)    ≡⟨ cong (⟦ p₁ ⟧ _ * _ +_) (cong ⟦ p₂ ⟧ (tail≡drop-1 ρ)) ⟩∎
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (drop 1 ρ)  ∎
  times-plus-correct {ρ} p₁ (suc k) (lift (suc m) p₂) =
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (drop (suc m) (tail ρ))  ≡⟨ cong (⟦ p₁ ⟧ _ * _ +_) (cong ⟦ p₂ ⟧ (drop-tail ρ)) ⟩∎
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (drop (2 + m) ρ)         ∎
  times-plus-correct p₁ (suc k₁) (p₂ *x^1+ k₂ + p₃) =
    times-helper-correct p₁ k₁ p₂ k₂ p₃

  -- The function plus-times is correctly defined.

  plus-times-correct :
    ∀ p₁ p₂ k →
    ⟦ plus-times p₁ p₂ k ⟧ ρ ≡
    ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ * head ρ ^ k
  plus-times-correct {ρ} p₁ p₂ zero =
    ⟦ p₁ +ᴺ p₂ ⟧ ρ           ≡⟨ +ᴺ-correct p₁ p₂ ⟩
    ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ      ≡⟨ cong (_+_ _) (sym (*-right-identity (⟦ p₂ ⟧ _))) ⟩∎
    ⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ * 1  ∎
  plus-times-correct {ρ} (con m) p (suc k) =
    ⟦ p ⟧ ρ * head ρ ^ suc k + m  ≡⟨ sym (+-comm m) ⟩∎
    m + ⟦ p ⟧ ρ * head ρ ^ suc k  ∎
  plus-times-correct {ρ} (lift zero p₁) p₂ (suc k) =
    ⟦ p₂ ⟧ ρ * head ρ ^ suc k + ⟦ p₁ ⟧ (tail ρ)    ≡⟨ sym (+-comm (⟦ p₁ ⟧ _)) ⟩
    ⟦ p₁ ⟧ (tail ρ) + ⟦ p₂ ⟧ ρ * head ρ ^ suc k    ≡⟨ cong (flip _+_ _) (cong ⟦ p₁ ⟧ (tail≡drop-1 ρ)) ⟩∎
    ⟦ p₁ ⟧ (drop 1 ρ) + ⟦ p₂ ⟧ ρ * head ρ ^ suc k  ∎
  plus-times-correct {ρ} (lift (suc m) p₁) p₂ (suc k) =
    ⟦ p₂ ⟧ ρ * head ρ ^ suc k + ⟦ p₁ ⟧ (drop (suc m) (tail ρ))  ≡⟨ sym (+-comm (⟦ p₁ ⟧ _)) ⟩
    ⟦ p₁ ⟧ (drop (suc m) (tail ρ)) + ⟦ p₂ ⟧ ρ * head ρ ^ suc k  ≡⟨ cong (flip _+_ _ ∘ ⟦ p₁ ⟧) (drop-tail ρ) ⟩∎
    ⟦ p₁ ⟧ (drop (2 + m) ρ) + ⟦ p₂ ⟧ ρ * head ρ ^ suc k         ∎
  plus-times-correct {ρ} (p₁ *x^1+ k₁ + p₂) p₃ (suc k₂) =
    ⟦ times-helper p₁ k₁ p₃ k₂ p₂ ⟧ ρ               ≡⟨ times-helper-correct p₁ k₁ p₃ k₂ p₂ ⟩

    ⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ +
    (⟦ p₃ ⟧ ρ * head ρ ^ suc k₂ + ⟦ p₂ ⟧ (tail ρ))  ≡⟨ trans (cong (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ +_) (+-comm (⟦ p₃ ⟧ _ * _))) $
                                                       +-assoc (⟦ p₁ ⟧ _ * _) ⟩∎
    ⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ ⟧ (tail ρ) +
    ⟦ p₃ ⟧ ρ * head ρ ^ suc k₂                      ∎

  private

    -- The function times-helper is correctly defined.

    times-helper-correct :
      ∀ p₁ k₁ p₂ k₂ p₃ →
      ⟦ times-helper p₁ k₁ p₂ k₂ p₃ ⟧ ρ ≡
      ⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ +
      (⟦ p₂ ⟧ ρ * head ρ ^ suc k₂ + ⟦ p₃ ⟧ (tail ρ))
    times-helper-correct {ρ} p₁ k₁ p₂ k₂ p₃
      with k₁ <= k₂ | T[<=]↔≤ {m = k₁} {n = k₂}
    … | true | k₁≤k₂↔ =
      ⟦ plus-times p₁ p₂ (k₂ ∸ k₁) ⟧ ρ * head ρ ^ suc k₁ +
      ⟦ p₃ ⟧ (tail ρ)                                                 ≡⟨ cong (flip _+_ _ ∘ flip _*_ _) $
                                                                         plus-times-correct p₁ p₂ (k₂ ∸ k₁) ⟩
      (⟦ p₁ ⟧ ρ + ⟦ p₂ ⟧ ρ * head ρ ^ (k₂ ∸ k₁)) * head ρ ^ suc k₁ +
      ⟦ p₃ ⟧ (tail ρ)                                                 ≡⟨ cong (flip _+_ _) $
                                                                         *-+-distribʳ (⟦ p₁ ⟧ _) ⟩
      (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ +
       ⟦ p₂ ⟧ ρ * head ρ ^ (k₂ ∸ k₁) * head ρ ^ suc k₁) +
      ⟦ p₃ ⟧ (tail ρ)                                                 ≡⟨ cong (flip _+_ (⟦ p₃ ⟧ (tail ρ)) ∘ _+_ (⟦ p₁ ⟧ _ * _)) $
                                                                         *^∸*^suc≡*^suc (⟦ p₂ ⟧ _) ( (_↔_.to k₁≤k₂↔ _)) ⟩
      (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ ⟧ ρ * head ρ ^ suc k₂) +
      ⟦ p₃ ⟧ (tail ρ)                                                 ≡⟨ sym (+-assoc (⟦ p₁ ⟧ _ * _)) ⟩∎

      ⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ +
      (⟦ p₂ ⟧ ρ * head ρ ^ suc k₂ + ⟦ p₃ ⟧ (tail ρ))                  ∎
    … | false | k₁≤k₂↔ =
      ⟦ times-plus p₁ (k₁ ∸ k₂) p₂ ⟧ ρ * head ρ ^ suc k₂ +
      ⟦ p₃ ⟧ (tail ρ)                                                 ≡⟨ cong (flip _+_ _ ∘ flip _*_ _) $
                                                                         times-plus-correct p₁ (k₁ ∸ k₂) p₂ ⟩
      (⟦ p₁ ⟧ ρ * head ρ ^ (k₁ ∸ k₂) + ⟦ p₂ ⟧ ρ) * head ρ ^ suc k₂ +
      ⟦ p₃ ⟧ (tail ρ)                                                 ≡⟨ cong (flip _+_ _) (*-+-distribʳ (⟦ p₁ ⟧ _ * _)) ⟩

      (⟦ p₁ ⟧ ρ * head ρ ^ (k₁ ∸ k₂) * head ρ ^ suc k₂ +
       ⟦ p₂ ⟧ ρ * head ρ ^ suc k₂) +
      ⟦ p₃ ⟧ (tail ρ)                                                 ≡⟨ cong (flip _+_ (⟦ p₃ ⟧ (tail ρ)) ∘ flip _+_ (⟦ p₂ ⟧ _ * _)) $
                                                                         *^∸*^suc≡*^suc (⟦ p₁ ⟧ _) ((≰→≥ (_↔_.from k₁≤k₂↔))) ⟩
      (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ ⟧ ρ * head ρ ^ suc k₂) +
      ⟦ p₃ ⟧ (tail ρ)                                                 ≡⟨ sym (+-assoc (⟦ p₁ ⟧ _ * _)) ⟩∎

      ⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ +
      (⟦ p₂ ⟧ ρ * head ρ ^ suc k₂ + ⟦ p₃ ⟧ (tail ρ))                  ∎

opaque

  -- One can express times-plus in terms of plus-times (up to semantic
  -- equivalence).

  times-plus≡plus-times :
    ∀ p₁ k p₂ →
    ⟦ times-plus p₁ k p₂ ⟧ ρ ≡
    ⟦ plus-times p₂ p₁ k ⟧ ρ
  times-plus≡plus-times {ρ} p₁ k p₂ =
    ⟦ times-plus p₁ k p₂ ⟧ ρ          ≡⟨ times-plus-correct _ k _ ⟩
    ⟦ p₁ ⟧ ρ * head ρ ^ k + ⟦ p₂ ⟧ ρ  ≡⟨ sym (+-comm (⟦ p₂ ⟧ _)) ⟩
    ⟦ p₂ ⟧ ρ + ⟦ p₁ ⟧ ρ * head ρ ^ k  ≡⟨ sym (plus-times-correct _ _ k) ⟩∎
    ⟦ plus-times p₂ p₁ k ⟧ ρ          ∎

opaque

  -- The function _*x^_+_ is correctly defined.

  *x^+-correct :
    ∀ p₁ k p₂ →
    ⟦ p₁ *x^ k + p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ ρ * head ρ ^ k + ⟦ p₂ ⟧ (tail ρ)
  *x^+-correct {ρ} p₁ zero p₂ =
    ⟦ p₁ +ᴺ liftᴺ 1 p₂ ⟧ ρ          ≡⟨ +ᴺ-correct p₁ _ ⟩
    ⟦ p₁ ⟧ ρ + ⟦ liftᴺ 1 p₂ ⟧ ρ     ≡⟨ cong₂ _+_ (sym (*-right-identity (⟦ p₁ ⟧ _))) (liftᴺ-1-correct p₂) ⟩∎
    ⟦ p₁ ⟧ ρ * 1 + ⟦ p₂ ⟧ (tail ρ)  ∎
  *x^+-correct {ρ} (con 0) (suc k) p =
    ⟦ liftᴺ 1 p ⟧ ρ  ≡⟨ liftᴺ-1-correct p ⟩∎
    ⟦ p ⟧ (tail ρ)   ∎
  *x^+-correct (con (suc _)) (suc _) _ =
    refl _
  *x^+-correct (lift _ _) (suc _) _ =
    refl _
  *x^+-correct {ρ} (p₁ *x^1+ k₁ + con 0) (suc k₂) p₂ =
    ⟦ p₁ ⟧ ρ * head ρ ^ (suc k₁ + suc k₂) + ⟦ p₂ ⟧ (tail ρ)  ≡⟨ cong (flip _+_ _) $ cong (_*_ (⟦ p₁ ⟧ _)) $
                                                                ^+≡^*^ {m = head ρ} (suc k₁) ⟩
    ⟦ p₁ ⟧ ρ * (head ρ ^ suc k₁ * head ρ ^ suc k₂) +
    ⟦ p₂ ⟧ (tail ρ)                                          ≡⟨ cong (flip _+_ _) $
                                                                trans (*-assoc (⟦ p₁ ⟧ _)) $
                                                                cong (flip _*_ _) $ sym $
                                                                +-right-identity {n = ⟦ p₁ ⟧ _ * _} ⟩∎
    (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + zero) * head ρ ^ suc k₂ +
    ⟦ p₂ ⟧ (tail ρ)                                          ∎
  *x^+-correct (_ *x^1+ _ + con (suc _)) (suc _) _ =
    refl _
  *x^+-correct (_ *x^1+ _ + lift _ _) (suc _) _ =
    refl _
  *x^+-correct (_ *x^1+ _ + (_ *x^1+ _ + _)) (suc _) _ =
    refl _

opaque

  -- One can express times-plusᶜ in terms of times-plus (up to
  -- semantic equivalence).

  times-plusᶜ≡times-plus :
    ∀ p₁ k p₂ →
    ⟦ times-plusᶜ p₁ k p₂ ⟧ ρ ≡
    ⟦ times-plus p₁ k p₂ ⟧ ρ
  times-plusᶜ≡times-plus _ zero _ =
    refl _
  times-plusᶜ≡times-plus p (suc _) (con _) =
    *x^+-correct p _ _
  times-plusᶜ≡times-plus p (suc _) (lift zero _) =
    *x^+-correct p _ _
  times-plusᶜ≡times-plus p (suc _) (lift (suc _) _) =
    *x^+-correct p _ _
  times-plusᶜ≡times-plus {ρ} p₁ (suc k₁) (p₂ *x^1+ k₂ + p₃) with k₁ <= k₂
  … | true =
    ⟦ times-plusᶜ p₂ (k₂ ∸ k₁) p₁ *x^ suc k₁ + p₃ ⟧ ρ                     ≡⟨ *x^+-correct (times-plusᶜ _ (_ ∸ k₁) _) _ _ ⟩

    ⟦ times-plusᶜ p₂ (k₂ ∸ k₁) p₁ ⟧ ρ * head ρ ^ suc k₁ +
    ⟦ p₃ ⟧ (tail ρ)                                                       ≡⟨ cong (flip _+_ _ ∘ flip _*_ _) $
                                                                             times-plusᶜ≡times-plus _ (_ ∸ k₁) _ ⟩

    ⟦ times-plus p₂ (k₂ ∸ k₁) p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₃ ⟧ (tail ρ)  ≡⟨ cong (flip _+_ _ ∘ flip _*_ _) $
                                                                             times-plus≡plus-times _ (_ ∸ k₁) _ ⟩∎
    ⟦ plus-times p₁ p₂ (k₂ ∸ k₁) ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₃ ⟧ (tail ρ)  ∎
  … | false =
    ⟦ times-plusᶜ p₁ (k₁ ∸ k₂) p₂ *x^ suc k₂ + p₃ ⟧ ρ                     ≡⟨ *x^+-correct (times-plusᶜ _ (_ ∸ k₂) _) _ _ ⟩

    ⟦ times-plusᶜ p₁ (k₁ ∸ k₂) p₂ ⟧ ρ * head ρ ^ suc k₂ +
    ⟦ p₃ ⟧ (tail ρ)                                                       ≡⟨ cong (flip _+_ _ ∘ flip _*_ _) $
                                                                             times-plusᶜ≡times-plus _ (_ ∸ k₂) _ ⟩∎
    ⟦ times-plus p₁ (k₁ ∸ k₂) p₂ ⟧ ρ * head ρ ^ suc k₂ + ⟦ p₃ ⟧ (tail ρ)  ∎

opaque

  -- The function times-plusᶜ is correctly defined.

  times-plusᶜ-correct :
    ∀ p₁ k p₂ →
    ⟦ times-plusᶜ p₁ k p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ ρ * head ρ ^ k + ⟦ p₂ ⟧ ρ
  times-plusᶜ-correct {ρ} p₁ k p₂ =
    ⟦ times-plusᶜ p₁ k p₂ ⟧ ρ         ≡⟨ times-plusᶜ≡times-plus _ k _ ⟩
    ⟦ times-plus p₁ k p₂ ⟧ ρ          ≡⟨ times-plus-correct _ k _ ⟩∎
    ⟦ p₁ ⟧ ρ * head ρ ^ k + ⟦ p₂ ⟧ ρ  ∎

opaque mutual

  -- The function _*ᴺ_ is correctly defined.

  *ᴺ-correct :
    ∀ p₁ p₂ →
    ⟦ p₁ *ᴺ p₂ ⟧ ρ ≡ ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ ρ
  *ᴺ-correct (con m₁) (con m₂) =
    m₁ * m₂  ∎
  *ᴺ-correct (con 0) (_ *x^1+ _ + _) =
    0  ∎
  *ᴺ-correct {ρ} (con m@(suc _)) (p₁ *x^1+ k + p₂) =
    ⟦ con m *ᴺ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ con m *ᴺ p₂ ⟧ (tail ρ)  ≡⟨ cong₂ _+_ (cong (flip _*_ _) (*ᴺ-correct (con m) p₁))
                                                                        (*ᴺ-correct (con m) p₂) ⟩

    (m * ⟦ p₁ ⟧ ρ) * head ρ ^ suc k + m * ⟦ p₂ ⟧ (tail ρ)          ≡⟨ trans (cong (flip _+_ _) (sym (*-assoc m {n = ⟦ p₁ ⟧ _}))) $
                                                                      sym (*-+-distribˡ m {n = ⟦ p₁ ⟧ _ * _}) ⟩∎
    m * (⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (tail ρ))              ∎
  *ᴺ-correct {ρ} (p₁ *x^1+ k + p₂) (con 0) =
    0                                                          ≡⟨ sym (*-right-zero (⟦ p₁ ⟧ _ * _ + _)) ⟩∎
    (⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (tail ρ)) * 0  ∎
  *ᴺ-correct {ρ} (p₁ *x^1+ k + p₂) (con m@(suc _)) =
    ⟦ p₁ *ᴺ con m ⟧ ρ * head ρ ^ suc k + ⟦ p₂ *ᴺ con m ⟧ (tail ρ)  ≡⟨ cong₂ _+_ (cong (flip _*_ _) (*ᴺ-correct p₁ (con m)))
                                                                        (*ᴺ-correct p₂ (con m)) ⟩

    ⟦ p₁ ⟧ ρ * m * head ρ ^ suc k + ⟦ p₂ ⟧ (tail ρ) * m            ≡⟨ trans
                                                                        (cong (flip _+_ _) $
                                                                         trans (sym (*-assoc (⟦ p₁ ⟧ _))) $
                                                                         trans (cong (_*_ (⟦ p₁ ⟧ _)) (*-comm m)) $
                                                                         *-assoc (⟦ p₁ ⟧ _)) $
                                                                      sym (*-+-distribʳ (⟦ p₁ ⟧ _ * _)) ⟩∎
    (⟦ p₁ ⟧ ρ * head ρ ^ suc k + ⟦ p₂ ⟧ (tail ρ)) * m              ∎
  *ᴺ-correct {ρ} p₁@(con _) (lift n p₂) =
    ⟦ times-lift p₁ (suc n) p₂ ⟧ ρ      ≡⟨ times-lift-correct p₁ (suc _) p₂ ⟩∎
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ (drop (suc n) ρ)  ∎
  *ᴺ-correct {ρ} p₁@(_ *x^1+ _ + _) (lift n p₂) =
    ⟦ times-lift p₁ (suc n) p₂ ⟧ ρ      ≡⟨ times-lift-correct p₁ (suc _) _ ⟩∎
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ (drop (suc n) ρ)  ∎
  *ᴺ-correct {ρ} (lift n p₁) p₂ =
    ⟦ lift-times (suc n) p₁ p₂ ⟧ ρ      ≡⟨ lift-times-correct (suc _) _ p₂ ⟩∎
    ⟦ p₁ ⟧ (drop (suc n) ρ) * ⟦ p₂ ⟧ ρ  ∎
  *ᴺ-correct {ρ} (p₁ *x^1+ k₁ + p₂) (p₃ *x^1+ k₂ + p₄)
    with k₁ <= k₂ | T[<=]↔≤ {m = k₁} {n = k₂}
  … | true | k₁≤k₂↔ =
    ⟦ times-plusᶜ
        (times-plusᶜ
           (times-plusᶜ (p₁ *ᴺ p₃) (suc k₁) (lift-times 1 p₂ p₃))
           (k₂ ∸ k₁) (times-lift p₁ 1 p₄))
        (suc k₁) (liftᴺ 1 (p₂ *ᴺ p₄)) ⟧ ρ                          ≡⟨ trans (times-plusᶜ-correct _ (suc _) (liftᴺ _ (p₂ *ᴺ _))) $
                                                                      cong₂ _+_
                                                                        (cong (flip _*_ _) $
                                                                         trans (times-plusᶜ-correct _ (_ ∸ k₁) _) $
                                                                         cong₂ _+_
                                                                           (cong (flip _*_ _) $
                                                                            trans (times-plusᶜ-correct _ (suc _) (lift-times 1 _ p₃)) $
                                                                            cong₂ _+_
                                                                              (cong (flip _*_ _) (*ᴺ-correct p₁ _))
                                                                              (lift-times-1-correct _ p₃))
                                                                           (times-lift-1-correct p₁ _))
                                                                        (trans (liftᴺ-1-correct (p₂ *ᴺ _)) $
                                                                         *ᴺ-correct p₂ _) ⟩
    ((⟦ p₁ ⟧ ρ * ⟦ p₃ ⟧ ρ * head ρ ^ suc k₁ +
      ⟦ p₂ ⟧ (tail ρ) * ⟦ p₃ ⟧ ρ) *
     head ρ ^ (k₂ ∸ k₁) +
     ⟦ p₁ ⟧ ρ * ⟦ p₄ ⟧ (tail ρ)) *
    head ρ ^ suc k₁ +
    ⟦ p₂ ⟧ (tail ρ) * ⟦ p₄ ⟧ (tail ρ)                              ≡⟨ *-lemma₁ (⟦ p₁ ⟧ _) (_↔_.to k₁≤k₂↔ _) ⟩∎

    (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ ⟧ (tail ρ)) *
    (⟦ p₃ ⟧ ρ * head ρ ^ suc k₂ + ⟦ p₄ ⟧ (tail ρ))                 ∎
  … | false | k₁≤k₂↔ =
    ⟦ times-plusᶜ
        (times-plusᶜ
           (times-plusᶜ (p₁ *ᴺ p₃) (suc k₂) (times-lift p₁ 1 p₄))
           (k₁ ∸ k₂) (lift-times 1 p₂ p₃))
        (suc k₂) (liftᴺ 1 (p₂ *ᴺ p₄)) ⟧ ρ                          ≡⟨ trans (times-plusᶜ-correct _ (suc _) (liftᴺ _ (p₂ *ᴺ _))) $
                                                                      cong₂ _+_
                                                                        (cong (flip _*_ _) $
                                                                         trans (times-plusᶜ-correct _ (_ ∸ k₂) _) $
                                                                         cong₂ _+_
                                                                           (cong (flip _*_ _) $
                                                                            trans (times-plusᶜ-correct _ (suc _) (times-lift p₁ 1 p₄)) $
                                                                            cong₂ _+_
                                                                              (cong (flip _*_ _) (*ᴺ-correct p₁ _))
                                                                              (times-lift-1-correct p₁ _))
                                                                           (lift-times-1-correct _ p₃))
                                                                        (trans (liftᴺ-1-correct (p₂ *ᴺ _)) $
                                                                         *ᴺ-correct p₂ _) ⟩
    ((⟦ p₁ ⟧ ρ * ⟦ p₃ ⟧ ρ * head ρ ^ suc k₂ +
      ⟦ p₁ ⟧ ρ * ⟦ p₄ ⟧ (tail ρ)) *
     head ρ ^ (k₁ ∸ k₂) +
     ⟦ p₂ ⟧ (tail ρ) * ⟦ p₃ ⟧ ρ) *
    head ρ ^ suc k₂ +
    ⟦ p₂ ⟧ (tail ρ) * ⟦ p₄ ⟧ (tail ρ)                              ≡⟨ *-lemma₂ (⟦ p₁ ⟧ _) (≰→≥ (_↔_.from k₁≤k₂↔)) ⟩∎


    (⟦ p₁ ⟧ ρ * head ρ ^ suc k₁ + ⟦ p₂ ⟧ (tail ρ)) *
    (⟦ p₃ ⟧ ρ * head ρ ^ suc k₂ + ⟦ p₄ ⟧ (tail ρ))                 ∎

  -- The function lift-times is correctly defined.

  lift-times-correct :
    ∀ n p₁ p₂ →
    ⟦ lift-times n p₁ p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ (drop n ρ) * ⟦ p₂ ⟧ ρ
  lift-times-correct {ρ} zero p₁ p₂ =
    ⟦ p₁ *ᴺ p₂ ⟧ ρ       ≡⟨ *ᴺ-correct p₁ _ ⟩∎
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ ρ  ∎
  lift-times-correct {ρ} (suc n) p₁ (con m) =
    ⟦ liftᴺ (suc n) (p₁ *ᴺ con m) ⟧ ρ  ≡⟨ liftᴺ-correct (suc _) (p₁ *ᴺ _) ⟩
    ⟦ p₁ *ᴺ con m ⟧ (drop (suc n) ρ)   ≡⟨ *ᴺ-correct p₁ _ ⟩∎
    ⟦ p₁ ⟧ (drop (suc n) ρ) * m        ∎
  lift-times-correct {ρ} (suc n₁) p₁ (lift n₂ p₂)
    with n₁ <= n₂ | T[<=]↔≤ {m = n₁} {n = n₂}
  … | true | n₁≤n₂↔ =
    ⟦ liftᴺ (suc n₁) (times-lift p₁ (n₂ ∸ n₁) p₂) ⟧ ρ                     ≡⟨ liftᴺ-correct (suc _) (times-lift _ (_ ∸ n₁) _) ⟩
    ⟦ times-lift p₁ (n₂ ∸ n₁) p₂ ⟧ (drop (suc n₁) ρ)                      ≡⟨ times-lift-correct _ (_ ∸ n₁) _ ⟩
    ⟦ p₁ ⟧ (drop (suc n₁) ρ) * ⟦ p₂ ⟧ (drop (n₂ ∸ n₁) (drop (suc n₁) ρ))  ≡⟨ cong (_*_ (⟦ p₁ ⟧ _) ∘ ⟦ p₂ ⟧) (drop-drop {xs = ρ} (suc n₁)) ⟩
    ⟦ p₁ ⟧ (drop (suc n₁) ρ) * ⟦ p₂ ⟧ (drop (suc n₁ + (n₂ ∸ n₁)) ρ)       ≡⟨ cong (_*_ (⟦ p₁ ⟧ _) ∘ ⟦ p₂ ⟧ ∘ flip drop ρ ∘ suc) $
                                                                             +[∸]≡ (_↔_.to n₁≤n₂↔ _) ⟩∎
    ⟦ p₁ ⟧ (drop (suc n₁) ρ) * ⟦ p₂ ⟧ (drop (suc n₂) ρ)                   ∎
  … | false | n₁≤n₂↔ =
    ⟦ liftᴺ (suc n₂) (lift-times (n₁ ∸ n₂) p₁ p₂) ⟧ ρ                     ≡⟨ liftᴺ-correct (suc _) (lift-times (_ ∸ n₂) _ _) ⟩
    ⟦ lift-times (n₁ ∸ n₂) p₁ p₂ ⟧ (drop (suc n₂) ρ)                      ≡⟨ lift-times-correct (_ ∸ n₂) _ _ ⟩
    ⟦ p₁ ⟧ (drop (n₁ ∸ n₂) (drop (suc n₂) ρ)) * ⟦ p₂ ⟧ (drop (suc n₂) ρ)  ≡⟨ cong (flip _*_ _ ∘ ⟦ p₁ ⟧) (drop-drop {xs = ρ} (suc n₂)) ⟩
    ⟦ p₁ ⟧ (drop (suc n₂ + (n₁ ∸ n₂)) ρ) * ⟦ p₂ ⟧ (drop (suc n₂) ρ)       ≡⟨ cong (flip _*_ _ ∘ ⟦ p₁ ⟧ ∘ flip drop ρ ∘ suc) $
                                                                             +[∸]≡ (≰→≥ (_↔_.from n₁≤n₂↔)) ⟩∎
    ⟦ p₁ ⟧ (drop (suc n₁) ρ) * ⟦ p₂ ⟧ (drop (suc n₂) ρ)                   ∎
  lift-times-correct {ρ} (suc n) p₁ (p₂ *x^1+ k + p₃) =
    ⟦ lift-times (suc n) p₁ p₂ *x^ suc k + lift-times n p₁ p₃ ⟧ ρ  ≡⟨ *x^+-correct (lift-times (suc _) _ p₂) (suc _) _ ⟩

    ⟦ lift-times (suc n) p₁ p₂ ⟧ ρ * head ρ ^ suc k +
    ⟦ lift-times n p₁ p₃ ⟧ (tail ρ)                                ≡⟨ cong₂ _+_ (cong (flip _*_ _) (lift-times-correct (suc _) _ p₂))
                                                                        (lift-times-correct n _ _) ⟩
    ⟦ p₁ ⟧ (drop (suc n) ρ) * ⟦ p₂ ⟧ ρ * head ρ ^ suc k +
    ⟦ p₁ ⟧ (drop n (tail ρ)) * ⟦ p₃ ⟧ (tail ρ)                     ≡⟨ cong₂ _+_ (sym (*-assoc (⟦ p₁ ⟧ _)))
                                                                        (cong (flip _*_ _ ∘ ⟦ p₁ ⟧) (drop-tail ρ)) ⟩
    ⟦ p₁ ⟧ (drop (suc n) ρ) * (⟦ p₂ ⟧ ρ * head ρ ^ suc k) +
    ⟦ p₁ ⟧ (drop (suc n) ρ) * ⟦ p₃ ⟧ (tail ρ)                      ≡⟨ sym (*-+-distribˡ (⟦ p₁ ⟧ _)) ⟩∎

    ⟦ p₁ ⟧ (drop (suc n) ρ) *
    (⟦ p₂ ⟧ ρ * head ρ ^ suc k + ⟦ p₃ ⟧ (tail ρ))                  ∎

  -- A variant of lift-times-correct.

  lift-times-1-correct :
    ∀ p₁ p₂ →
    ⟦ lift-times 1 p₁ p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ (tail ρ) * ⟦ p₂ ⟧ ρ
  lift-times-1-correct {ρ} p₁ p₂ =
    ⟦ lift-times 1 p₁ p₂ ⟧ ρ      ≡⟨ lift-times-correct 1 _ p₂ ⟩
    ⟦ p₁ ⟧ (drop 1 ρ) * ⟦ p₂ ⟧ ρ  ≡⟨ cong (_* _) (cong ⟦ p₁ ⟧ (sym (tail≡drop-1 ρ))) ⟩∎
    ⟦ p₁ ⟧ (tail ρ) * ⟦ p₂ ⟧ ρ    ∎

  -- The function times-lift is correctly defined.

  times-lift-correct :
    ∀ p₁ n p₂ →
    ⟦ times-lift p₁ n p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ (drop n ρ)
  times-lift-correct {ρ} p₁ n p₂ =
    ⟦ times-lift p₁ n p₂ ⟧ ρ      ≡⟨ lift-times-correct n _ _ ⟩
    ⟦ p₂ ⟧ (drop n ρ) * ⟦ p₁ ⟧ ρ  ≡⟨ sym (*-comm (⟦ p₁ ⟧ _)) ⟩∎
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ (drop n ρ)  ∎

  -- A variant of times-lift-correct.

  times-lift-1-correct :
    ∀ p₁ p₂ →
    ⟦ times-lift p₁ 1 p₂ ⟧ ρ ≡
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ (tail ρ)
  times-lift-1-correct {ρ} p₁ p₂ =
    ⟦ times-lift p₁ 1 p₂ ⟧ ρ      ≡⟨ times-lift-correct p₁ 1 _ ⟩
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ (drop 1 ρ)  ≡⟨ cong ((⟦ p₁ ⟧ _ *_) ∘ ⟦ p₂ ⟧) (sym (tail≡drop-1 ρ)) ⟩∎
    ⟦ p₁ ⟧ ρ * ⟦ p₂ ⟧ (tail ρ)    ∎

opaque

  -- The function _^ᴺ_ is correctly defined.

  ^ᴺ-correct :
    ∀ p n →
    ⟦ p ^ᴺ n ⟧ ρ ≡ ⟦ p ⟧ ρ ^ n
  ^ᴺ-correct _ zero =
    1  ∎
  ^ᴺ-correct {ρ} p (suc n) =
    ⟦ p *ᴺ p ^ᴺ n ⟧ ρ       ≡⟨ *ᴺ-correct p (p ^ᴺ n) ⟩
    ⟦ p ⟧ ρ * ⟦ p ^ᴺ n ⟧ ρ  ≡⟨ cong (⟦ p ⟧ _ *_) (^ᴺ-correct p n) ⟩∎
    ⟦ p ⟧ ρ * ⟦ p ⟧ ρ ^ n   ∎

------------------------------------------------------------------------
-- Normalisation produces canonical normal forms

opaque
  unfolding OK-as-arg-1

  -- If OK-as-arg-1 p holds, then p is not con 0.

  OK-as-arg-1→≢con-0 : OK-as-arg-1 p → p ≢ con 0
  OK-as-arg-1→≢con-0 {p = con _}         = _∘ con-injective
  OK-as-arg-1→≢con-0 {p = lift _ _}      = λ _ → lift≢con
  OK-as-arg-1→≢con-0 {p = _ *x^1+ _ + _} = λ _ → *x^1++≢con

opaque
  unfolding Plus

  -- If Plus p holds, then p is not an application of con.

  Plus→≢con : Plus p → p ≢ con m
  Plus→≢con {p = lift _ _}      _ = lift≢con
  Plus→≢con {p = _ *x^1+ _ + _} _ = *x^1++≢con

opaque
  unfolding Plus

  -- Certain functions preserve/establish Plus.

  con-+ᴺ-Plus : ∀ p → Plus p → Plus (con m +ᴺ p)
  con-+ᴺ-Plus (_ *x^1+ _ + _) _ = _

  +ᴺ-con-Plus : ∀ p → Plus p → Plus (p +ᴺ con m)
  +ᴺ-con-Plus (_ *x^1+ _ + _) _ = _

  plus-times-Plus : ∀ p₁ → Plus (plus-times p₁ p₂ (suc k))
  plus-times-Plus     (con _)          = _
  plus-times-Plus     (lift zero _)    = _
  plus-times-Plus     (lift (suc _) _) = _
  plus-times-Plus {k} (_ *x^1+ k₁ + _) with k₁ <= k
  … | true  = _
  … | false = _

  lift-plus-Plus :
    ∀ n p₂ → Plus p₁ → Plus p₂ → Plus (lift-plus n p₁ p₂)
  lift-plus-Plus {p₁ = _ *x^1+ _ + _} zero (_ *x^1+ _ + _) _ _ =
    plus-times-Plus (_ *x^1+ _ + _)
  lift-plus-Plus (suc _) (_ *x^1+ _ + _) _ =
    _

  plus-lift-Plus :
    ∀ p₁ n → Plus p₁ → Plus p₂ → Plus (plus-lift p₁ n p₂)
  plus-lift-Plus {p₂ = _ *x^1+ _ + _} (_ *x^1+ _ + _) zero _ _ =
    plus-times-Plus (_ *x^1+ _ + _)
  plus-lift-Plus (_ *x^1+ _ + _) (suc _) _ =
    _

opaque
  unfolding Canonical

  -- Certain functions preserve "is not equal to con 0".

  liftᴺ-≢-con-0 :
    ∀ n p → p ≢ con 0 → liftᴺ n p ≢ con 0
  liftᴺ-≢-con-0 _       (con _)         ok = ok
  liftᴺ-≢-con-0 _       (lift _ _)      ok = lift≢con
  liftᴺ-≢-con-0 zero    (_ *x^1+ _ + _) ok = *x^1++≢con
  liftᴺ-≢-con-0 (suc _) (_ *x^1+ _ + _) ok = lift≢con

  mutual

    +ᴺ-≢-con-0 :
      ∀ p₁ p₂ → p₁ ≢ con 0 ⊎ p₂ ≢ con 0 → p₁ +ᴺ p₂ ≢ con 0
    +ᴺ-≢-con-0 (con _) (con _) (inj₁ ok) =
      ok ∘ cong con ∘ proj₁ ∘ +≡0→ ∘ con-injective
    +ᴺ-≢-con-0 (con _) (con _) (inj₂ ok) =
      ok ∘ cong con ∘ proj₂ ∘ +≡0→ ∘ con-injective
    +ᴺ-≢-con-0 p₁@(con _) (lift _ p₂) _ =
      plus-lift-≢-con-0 {p₂ = p₂} p₁ _ (inj₁ +≢0)
    +ᴺ-≢-con-0 (con _) (_ *x^1+ _ + _) _ =
      *x^1++≢con
    +ᴺ-≢-con-0 (lift n _) p _ =
      lift-plus-≢-con-0 (suc _) p (inj₁ +≢0)
    +ᴺ-≢-con-0 (_ *x^1+ _ + _) (con _) _ =
      *x^1++≢con
    +ᴺ-≢-con-0 p@(_ *x^1+ _ + _) (lift n _) _ =
      plus-lift-≢-con-0 p (suc n) (inj₁ +≢0)
    +ᴺ-≢-con-0 (_ *x^1+ _ + _) (_ *x^1+ _ + _) _ =
      plus-times-≢-con-0 (_ *x^1+ _ + _) _ (inj₁ +≢0)

    lift-plus-≢-con-0 :
      ∀ n p₂ → n ≢ 0 ⊎ p₁ ≢ con 0 ⊎ p₂ ≢ con 0 →
      lift-plus n p₁ p₂ ≢ con 0
    lift-plus-≢-con-0 zero _ (inj₁ 0≢0) =
      ⊥-elim (0≢0 (refl _))
    lift-plus-≢-con-0 zero _ (inj₂ ok) =
      +ᴺ-≢-con-0 _ _ ok
    lift-plus-≢-con-0 (suc _) (con _) _ =
      lift≢con
    lift-plus-≢-con-0 (suc n₁) (lift n₂ _) _ with n₁ <= n₂
    … | true  = lift≢con
    … | false = lift≢con
    lift-plus-≢-con-0 (suc _) (_ *x^1+ _ + _) _ =
      *x^1++≢con

    plus-lift-≢-con-0 :
      ∀ p₁ n → n ≢ 0 ⊎ p₁ ≢ con 0 ⊎ p₂ ≢ con 0 →
      plus-lift p₁ n p₂ ≢ con 0
    plus-lift-≢-con-0 _ zero (inj₁ 0≢0) =
      ⊥-elim (0≢0 (refl _))
    plus-lift-≢-con-0 _ zero (inj₂ ok) =
      +ᴺ-≢-con-0 _ _ ok
    plus-lift-≢-con-0 (con _) (suc _) _ =
      lift≢con
    plus-lift-≢-con-0 (lift n₁ _) (suc n₂) _ with n₁ <= n₂
    … | true  = lift≢con
    … | false = lift≢con
    plus-lift-≢-con-0 (_ *x^1+ _ + _) (suc _) _ =
      *x^1++≢con

    plus-times-≢-con-0 :
      ∀ p₁ k → k ≢ 0 ⊎ p₁ ≢ con 0 ⊎ p₂ ≢ con 0 →
      plus-times p₁ p₂ k ≢ con 0
    plus-times-≢-con-0 _ zero (inj₁ 0≢0) =
      ⊥-elim (0≢0 (refl _))
    plus-times-≢-con-0 _ zero (inj₂ ok) =
      +ᴺ-≢-con-0 _ _ ok
    plus-times-≢-con-0 (con _) (suc _) _ =
      *x^1++≢con
    plus-times-≢-con-0 (lift zero _) (suc _) _ =
      *x^1++≢con
    plus-times-≢-con-0 (lift (suc _) _) (suc _) _ =
      *x^1++≢con
    plus-times-≢-con-0 (_ *x^1+ k₁ + _) (suc k₂) _
      with k₁ <= k₂
    … | true  = *x^1++≢con
    … | false = *x^1++≢con

  *x^+-≢-con-0 :
    ∀ p₁ k → p₁ ≢ con 0 ⊎ p₂ ≢ con 0 →
    p₁ *x^ k + p₂ ≢ con 0
  *x^+-≢-con-0 p zero ok =
    +ᴺ-≢-con-0 p _ (⊎-map id (liftᴺ-≢-con-0 _ _) ok)
  *x^+-≢-con-0 (con 0) (suc _) (inj₁ con-0≢con-0) =
    ⊥-elim (con-0≢con-0 (refl _))
  *x^+-≢-con-0 (con 0) (suc _) (inj₂ ok) =
    liftᴺ-≢-con-0 _ _ ok
  *x^+-≢-con-0 (con (suc _)) (suc _) _ =
    *x^1++≢con
  *x^+-≢-con-0 (lift _ _) (suc _) _ =
    *x^1++≢con
  *x^+-≢-con-0 (_ *x^1+ _ + con 0) (suc _) _ =
    *x^1++≢con
  *x^+-≢-con-0 (_ *x^1+ _ + con (suc _)) (suc _) _ =
    *x^1++≢con
  *x^+-≢-con-0 (_ *x^1+ _ + lift _ _) (suc _) _ =
    *x^1++≢con
  *x^+-≢-con-0 (_ *x^1+ _ + (_ *x^1+ _ + _)) (suc _) _ =
    *x^1++≢con

  times-plusᶜ-≢-con-0 :
    ∀ k p₂ → Canonical p₁ → Canonical p₂ → p₁ ≢ con 0 ⊎ p₂ ≢ con 0 →
    times-plusᶜ p₁ k p₂ ≢ con 0
  times-plusᶜ-≢-con-0 zero _ _ _ ok =
    +ᴺ-≢-con-0 _ _ ok
  times-plusᶜ-≢-con-0 (suc _) (con _) _ _ ok =
    *x^+-≢-con-0 _ (suc _) ok
  times-plusᶜ-≢-con-0 (suc _) (lift zero (_ *x^1+ _ + _)) _ _ ok =
    *x^+-≢-con-0 _ (suc _) (⊎-map id (λ _ → *x^1++≢con) ok)
  times-plusᶜ-≢-con-0 (suc _) (lift (suc _) (_ *x^1+ _ + _)) _ _ ok =
    *x^+-≢-con-0 _ (suc _) (⊎-map id (λ _ → lift≢con) ok)
  times-plusᶜ-≢-con-0 (suc k₁) (_ *x^1+ k₂ + _) c₁ (ok , c₂ , _) _
    with k₁ <= k₂
  … | true =
    *x^+-≢-con-0 (times-plusᶜ _ (_ ∸ k₁) _) (suc k₁)
      (inj₁ $
       times-plusᶜ-≢-con-0 (_ ∸ k₁) _ c₂ c₁
         (inj₁ (OK-as-arg-1→≢con-0 ok)))
  … | false =
    *x^+-≢-con-0 (times-plusᶜ _ (_ ∸ k₂) _) (suc k₂)
      (inj₁ $
       times-plusᶜ-≢-con-0 (_ ∸ k₂) _ c₁ c₂
         (inj₂ (OK-as-arg-1→≢con-0 ok)))

opaque
  unfolding OK-as-arg-1

  -- Certain functions preserve OK-as-arg-1.

  liftᴺ-OK-as-arg-1 :
    ∀ n p → n ≢ 0 × p ≢ con 0 ⊎ OK-as-arg-1 p →
    OK-as-arg-1 (liftᴺ n p)
  liftᴺ-OK-as-arg-1 _ (con _) (inj₁ (_ , ok)) =
    ok ∘ cong con
  liftᴺ-OK-as-arg-1 _ (con _) (inj₂ ok) =
    ok
  liftᴺ-OK-as-arg-1 _ (lift _ _) _ =
    _
  liftᴺ-OK-as-arg-1 zero (_ *x^1+ _ + _) (inj₁ (0≢0 , _)) =
    ⊥-elim (0≢0 (refl _))
  liftᴺ-OK-as-arg-1 zero (_ *x^1+ _ + _) (inj₂ ok) =
    ok
  liftᴺ-OK-as-arg-1 (suc _) (_ *x^1+ _ + _) _ =
    _

  mutual

    +ᴺ-OK-as-arg-1 :
      ∀ p₁ p₂ → OK-as-arg-1 p₁ → OK-as-arg-1 p₂ →
      OK-as-arg-1 (p₁ +ᴺ p₂)
    +ᴺ-OK-as-arg-1 (con _) (con _) ok _ =
      ok ∘ proj₁ ∘ +≡0→
    +ᴺ-OK-as-arg-1 (con _) (lift _ _) _ _ =
      _
    +ᴺ-OK-as-arg-1 (con _) (_ *x^1+ _ + con _) ok _ =
      ok ∘ proj₁ ∘ +≡0→ ∘ con-injective
    +ᴺ-OK-as-arg-1 (con _) (_ *x^1+ _ + lift _ _) _ _ =
      lift≢con
    +ᴺ-OK-as-arg-1 (con _) (_ *x^1+ _ + (_ *x^1+ _ + _)) _ _ =
      *x^1++≢con
    +ᴺ-OK-as-arg-1 (lift _ _) _ _ ok =
      lift-plus-OK-as-arg-1 (suc _) _ (inj₁ +≢0)
        ok
    +ᴺ-OK-as-arg-1 p₁@(_ *x^1+ _ + _) (lift n _) ok _ =
      plus-lift-OK-as-arg-1 p₁ (suc n) ok
        (inj₁ +≢0)
    +ᴺ-OK-as-arg-1 (_ *x^1+ _ + con _) (con _) _ ok =
      ok ∘ proj₂ ∘ +≡0→ ∘ con-injective
    +ᴺ-OK-as-arg-1 (_ *x^1+ _ + lift _ _) (con _) _ _ =
      lift≢con
    +ᴺ-OK-as-arg-1 (_ *x^1+ _ + (_ *x^1+ _ + _)) (con _) _ _ =
      *x^1++≢con
    +ᴺ-OK-as-arg-1 (_ *x^1+ _ + _) (_ *x^1+ _ + _) ok _ =
      plus-times-OK-as-arg-1 (_ *x^1+ _ + _) (suc _)
        (+ᴺ-≢-con-0 _ _ (inj₁ ok)) (inj₁ (+≢0 , _))

    lift-plus-OK-as-arg-1 :
      ∀ n p₂ → n ≢ 0 ⊎ OK-as-arg-1 p₁ → OK-as-arg-1 p₂ →
      OK-as-arg-1 (lift-plus n p₁ p₂)
    lift-plus-OK-as-arg-1 zero _ (inj₁ 0≢0) _ =
      ⊥-elim (0≢0 (refl _))
    lift-plus-OK-as-arg-1 {p₁} zero _ (inj₂ ok₁) ok₂ =
      +ᴺ-OK-as-arg-1 p₁ _ ok₁ ok₂
    lift-plus-OK-as-arg-1 (suc _) (con _) _ =
      _
    lift-plus-OK-as-arg-1 (suc n₁) (lift n₂ _) _
      with n₁ <= n₂
    … | true  = _
    … | false = _
    lift-plus-OK-as-arg-1 (suc n) (_ *x^1+ _ + _) _ ok =
      lift-plus-≢-con-0 n _ (inj₂ (inj₂ ok))

    plus-lift-OK-as-arg-1 :
      ∀ p₁ n → OK-as-arg-1 p₁ → n ≢ 0 ⊎ OK-as-arg-1 p₂ →
      OK-as-arg-1 (plus-lift p₁ n p₂)
    plus-lift-OK-as-arg-1 _ zero _ (inj₁ 0≢0) =
      ⊥-elim (0≢0 (refl _))
    plus-lift-OK-as-arg-1 p₁ zero ok₁ (inj₂ ok₂) =
      +ᴺ-OK-as-arg-1 p₁ _ ok₁ ok₂
    plus-lift-OK-as-arg-1 (con _) (suc _) _ =
      _
    plus-lift-OK-as-arg-1 (lift n₁ _) (suc n₂) _
      with n₁ <= n₂
    … | true  = _
    … | false = _
    plus-lift-OK-as-arg-1 (_ *x^1+ _ + _) (suc n) ok _ =
      plus-lift-≢-con-0 _ n (inj₂ (inj₁ ok))

    plus-times-OK-as-arg-1 :
      ∀ p₁ k →
      OK-as-arg-1 p₁ →
      k ≢ 0 × Plus p₁ ⊎ Canonical p₁ × OK-as-arg-1 p₂ →
      OK-as-arg-1 (plus-times p₁ p₂ k)
    plus-times-OK-as-arg-1 _ zero _ (inj₁ (0≢0 , _)) =
      ⊥-elim (0≢0 (refl _))
    plus-times-OK-as-arg-1 _ zero ok₁ (inj₂ (_ , ok₂)) =
      +ᴺ-OK-as-arg-1 _ _ ok₁ ok₂
    plus-times-OK-as-arg-1 (con _) (suc _) ok _ =
      ok ∘ con-injective
    plus-times-OK-as-arg-1
      (lift zero _) (suc _) _ (inj₂ ((ok , _) , _)) =
      Plus→≢con ok
    plus-times-OK-as-arg-1 (lift (suc _) _) (suc _) _ _ =
      lift≢con
    plus-times-OK-as-arg-1 (_ *x^1+ k₁ + _) (suc k₂) ok _
      with k₁ <= k₂
    … | true  = ok
    … | false = ok

    times-plus-OK-as-arg-1 :
      ∀ k p₂ →
      k ≢ 0 × Plus p₂ ⊎ Canonical p₂ × OK-as-arg-1 p₁ →
      OK-as-arg-1 p₂ →
      OK-as-arg-1 (times-plus p₁ k p₂)
    times-plus-OK-as-arg-1 zero _ (inj₁ (0≢0 , _)) _ =
      ⊥-elim (0≢0 (refl _))
    times-plus-OK-as-arg-1 zero _ (inj₂ (_ , ok₁)) ok₂ =
      +ᴺ-OK-as-arg-1 _ _ ok₁ ok₂
    times-plus-OK-as-arg-1 (suc _) (con _) _ ok =
      ok ∘ con-injective
    times-plus-OK-as-arg-1
      (suc _) (lift zero _) (inj₂ ((ok , _) , _)) _ =
      Plus→≢con ok
    times-plus-OK-as-arg-1 (suc _) (lift (suc _) _) _ _ =
      lift≢con
    times-plus-OK-as-arg-1 (suc k₁) (_ *x^1+ k₂ + _) _ ok
      with k₁ <= k₂
    … | true  = ok
    … | false = ok

  *x^-+-OK-as-arg-1 :
    ∀ p₁ k → k ≢ 0 ⊎ OK-as-arg-1 p₁ → p₂ ≢ con 0 →
    OK-as-arg-1 (p₁ *x^ k + p₂)
  *x^-+-OK-as-arg-1 _ zero (inj₁ 0≢0) _ =
    ⊥-elim (0≢0 (refl _))
  *x^-+-OK-as-arg-1 _ zero (inj₂ ok₁) ok₂ =
    +ᴺ-OK-as-arg-1 _ _ ok₁
      (liftᴺ-OK-as-arg-1 _ _ (inj₁ (+≢0 , ok₂)))
  *x^-+-OK-as-arg-1 (con 0) (suc _) _ ok =
    liftᴺ-OK-as-arg-1 _ _ (inj₁ (+≢0 , ok))
  *x^-+-OK-as-arg-1 (con (suc _)) (suc _) _ ok =
    ok
  *x^-+-OK-as-arg-1 (lift _ _) (suc _) _ ok =
    ok
  *x^-+-OK-as-arg-1 (_ *x^1+ _ + con 0) (suc _) _ ok =
    ok
  *x^-+-OK-as-arg-1 (_ *x^1+ _ + con (suc _)) (suc _) _ ok =
    ok
  *x^-+-OK-as-arg-1 (_ *x^1+ _ + lift _ _) (suc _) _ ok =
    ok
  *x^-+-OK-as-arg-1 (_ *x^1+ _ + (_ *x^1+ _ + _)) (suc _) _ ok =
    ok

  times-plusᶜ-OK-as-arg-1 :
    ∀ k p₂ → k ≢ 0 × Plus p₂ ⊎ Canonical p₂ × OK-as-arg-1 p₁ →
    OK-as-arg-1 p₂ →
    OK-as-arg-1 (times-plusᶜ p₁ k p₂)
  times-plusᶜ-OK-as-arg-1 zero _ (inj₁ (0≢0 , _)) _ =
    ⊥-elim (0≢0 (refl _))
  times-plusᶜ-OK-as-arg-1 zero _ (inj₂ (_ , ok₁)) ok₂ =
    +ᴺ-OK-as-arg-1 _ _ ok₁ ok₂
  times-plusᶜ-OK-as-arg-1 {p₁} (suc _) (con _) _ ok =
    *x^-+-OK-as-arg-1 p₁ (suc _) (inj₁ +≢0) (ok ∘ con-injective)
  times-plusᶜ-OK-as-arg-1
    {p₁} (suc _) (lift zero _) (inj₂ ((plus , _) , _)) _ =
    *x^-+-OK-as-arg-1 p₁ (suc _) (inj₁ +≢0) (Plus→≢con plus)
  times-plusᶜ-OK-as-arg-1 {p₁} (suc _) (lift (suc _) _) _ _ =
    *x^-+-OK-as-arg-1 p₁ (suc _) (inj₁ +≢0) lift≢con
  times-plusᶜ-OK-as-arg-1 (suc k₁) (_ *x^1+ k₂ + _) _ ok
    with k₁ <= k₂
  … | true =
    *x^-+-OK-as-arg-1 (times-plusᶜ _ (_ ∸ k₁) _) (suc k₁)
      (inj₁ +≢0) ok
  … | false =
    *x^-+-OK-as-arg-1 (times-plusᶜ _ (_ ∸ k₂) _) (suc k₂)
      (inj₁ +≢0) ok

opaque
  unfolding Canonical

  -- Certain functions establish/preserve canonicity.

  liftᴺ-Canonical :
    ∀ n p → Canonical p → Canonical (liftᴺ n p)
  liftᴺ-Canonical _       (con _)         _ = _
  liftᴺ-Canonical _       (lift _ p)      c = c
  liftᴺ-Canonical zero    (_ *x^1+ _ + _) c = c
  liftᴺ-Canonical (suc _) (_ *x^1+ _ + _) c = _ , c

  var₀ᴺ-Canonical : Canonical var₀ᴺ
  var₀ᴺ-Canonical = +≢0 , _

  varᴺ-Canonical : (x : ℕ) → Canonical (varᴺ x)
  varᴺ-Canonical x = liftᴺ-Canonical x var₀ᴺ var₀ᴺ-Canonical

  mutual

    +ᴺ-Canonical :
      ∀ p₁ p₂ → Canonical p₁ → Canonical p₂ → Canonical (p₁ +ᴺ p₂)
    +ᴺ-Canonical (con _) (con _) _ _ =
      _
    +ᴺ-Canonical p₁@(con _) (lift n _) c₁ (plus , c₂) =
      plus-lift-Canonical p₁ (suc n) c₁ plus c₂
    +ᴺ-Canonical (con _) (_ *x^1+ _ + _) _ (ok , c₁ , c₂) =
      ok , c₁ , +ᴺ-Canonical (con _) _ _ c₂
    +ᴺ-Canonical (lift n p₁) p₂ (plus , c₁) c₂ =
      lift-plus-Canonical (suc n) _ plus c₁ c₂
    +ᴺ-Canonical p₁@(_ *x^1+ _ + _) (lift n _) c₁ (plus , c₂) =
      plus-lift-Canonical p₁ (suc n) c₁ plus c₂
    +ᴺ-Canonical (_ *x^1+ _ + _) (con _) (ok , c₁ , c₂) _ =
      ok , c₁ , +ᴺ-Canonical _ (con _) c₂ _
    +ᴺ-Canonical
      (_ *x^1+ _ + _) (_ *x^1+ k₂ + _) (ok₁ , c₁ , c₂) (ok₂ , c₃ , c₄) =
      plus-times-Canonical (_ *x^1+ _ + _) (suc k₂)
        (ok₁ , c₁ , +ᴺ-Canonical _ _ c₂ c₄) ok₂ c₃

    lift-plus-Canonical :
      ∀ n p₂ → Plus p₁ → Canonical p₁ → Canonical p₂ →
      Canonical (lift-plus n p₁ p₂)
    lift-plus-Canonical zero _ _ c₁ c₂ =
      +ᴺ-Canonical _ _ c₁ c₂
    lift-plus-Canonical (suc _) (con _) plus c _ =
      +ᴺ-con-Plus _ plus , +ᴺ-Canonical _ (con _) c _
    lift-plus-Canonical (suc _) (lift _ _) plus₁ c₁ (plus₂ , c₂) =
      lift-helper-Canonical _ _ _ _ plus₁ c₁ plus₂ c₂
    lift-plus-Canonical (suc n) (_ *x^1+ _ + _) plus c₁ (ok , c₂ , c₃) =
      ok , c₂ , lift-plus-Canonical n _ plus c₁ c₃

    plus-lift-Canonical :
      ∀ p₁ n → Canonical p₁ → Plus p₂ → Canonical p₂ →
      Canonical (plus-lift p₁ n p₂)
    plus-lift-Canonical _ zero c₁ _ c₂ =
      +ᴺ-Canonical _ _ c₁ c₂
    plus-lift-Canonical (con _) (suc _) _ plus c =
      con-+ᴺ-Plus _ plus , +ᴺ-Canonical (con _) _ _ c
    plus-lift-Canonical (lift _ _) (suc _) (plus₁ , c₁) plus₂ c₂ =
      lift-helper-Canonical _ _ _ _ plus₁ c₁ plus₂ c₂
    plus-lift-Canonical (_ *x^1+ _ + _) (suc n) (ok , c₁ , c₂) plus c₃ =
      ok , c₁ , plus-lift-Canonical _ n c₂ plus c₃

    private

      lift-helper-Canonical :
        ∀ n₁ p₁ n₂ p₂ →
        Plus p₁ → Canonical p₁ → Plus p₂ → Canonical p₂ →
        Canonical (lift-helper n₁ p₁ n₂ p₂)
      lift-helper-Canonical n₁ _ n₂ _ plus₁ c₁ plus₂ c₂
        with n₁ <= n₂
      … | true =
        plus-lift-Plus _ (_ ∸ n₁) plus₁ plus₂ ,
        plus-lift-Canonical _ (_ ∸ n₁) c₁ plus₂ c₂
      … | false =
        lift-plus-Plus (_ ∸ n₂) _ plus₁ plus₂ ,
        lift-plus-Canonical (_ ∸ n₂) _ plus₁ c₁ c₂

    plus-times-Canonical :
      ∀ p₁ k → Canonical p₁ → OK-as-arg-1 p₂ → Canonical p₂ →
      Canonical (plus-times p₁ p₂ k)
    plus-times-Canonical _ zero c₁ _ c₂ =
      +ᴺ-Canonical _ _ c₁ c₂
    plus-times-Canonical (con _) (suc _) _ ok c =
      ok , c , _
    plus-times-Canonical (lift zero _) (suc _) (_ , c₁) ok c₂ =
      ok , c₂ , c₁
    plus-times-Canonical (lift (suc _) _) (suc _) c₁ ok c₂ =
      ok , c₂ , c₁
    plus-times-Canonical
      (_ *x^1+ _ + _) (suc _) (ok₁ , c₁ , c₂) ok₂ c₃ =
      times-helper-Canonical _ _ _ _ _ ok₁ c₁ ok₂ c₃ c₂

    times-plus-Canonical :
      ∀ k p₂ → OK-as-arg-1 p₁ → Canonical p₁ → Canonical p₂ →
      Canonical (times-plus p₁ k p₂)
    times-plus-Canonical zero _ _ c₁ c₂ =
      +ᴺ-Canonical _ _ c₁ c₂
    times-plus-Canonical (suc _) (con _) ok c _ =
      ok , c , _
    times-plus-Canonical (suc _) (lift zero _) ok c₁ (_ , c₂) =
      ok , c₁ , c₂
    times-plus-Canonical (suc _) (lift (suc _) _) ok c₁ c₂ =
      ok , c₁ , c₂
    times-plus-Canonical
      (suc _) (_ *x^1+ _ + _) ok₁ c₁ (ok₂ , c₂ , c₃) =
      times-helper-Canonical _ _ _ _ _ ok₁ c₁ ok₂ c₂ c₃

    private

      times-helper-Canonical :
        ∀ p₁ k₁ p₂ k₂ p₃ →
        OK-as-arg-1 p₁ → Canonical p₁ →
        OK-as-arg-1 p₂ → Canonical p₂ →
        Canonical p₃ →
        Canonical (times-helper p₁ k₁ p₂ k₂ p₃)
      times-helper-Canonical _ k₁ _ k₂ _ ok₁ c₁ ok₂ c₂ c₃
        with k₁ <= k₂
      … | true =
        plus-times-OK-as-arg-1 _ (_ ∸ k₁) ok₁ (inj₂ (c₁ , ok₂)) ,
        plus-times-Canonical _ (_ ∸ k₁) c₁ ok₂ c₂ , c₃
      … | false =
        times-plus-OK-as-arg-1 (_ ∸ k₂) _ (inj₂ (c₂ , ok₁)) ok₂ ,
        times-plus-Canonical (_ ∸ k₂) _ ok₁ c₁ c₂ , c₃

  *x^+-Canonical :
    ∀ p₁ k p₂ →
    Canonical p₁ → Canonical p₂ →
    Canonical (p₁ *x^ k + p₂)
  *x^+-Canonical _ zero _ c₁ c₂ =
    +ᴺ-Canonical _ _ c₁ (liftᴺ-Canonical _ _ c₂)
  *x^+-Canonical (con 0) (suc _) _ _ c =
    liftᴺ-Canonical _ _ c
  *x^+-Canonical (con (suc _)) (suc _) _ _ c =
    +≢0 , _ , c
  *x^+-Canonical (lift _ _) (suc _) _ c₁ c₂ =
    _ , c₁ , c₂
  *x^+-Canonical (_ *x^1+ _ + con 0) (suc _) _ (first , c₁ , _) c₂ =
    first , c₁ , c₂
  *x^+-Canonical (_ *x^1+ _ + con (suc _)) (suc _) _ c₁ c₂ =
    0≢+ ∘ con-injective ∘ sym , c₁ , c₂
  *x^+-Canonical (_ *x^1+ _ + lift _ _) (suc _) _ c₁ c₂ =
    lift≢con , c₁ , c₂
  *x^+-Canonical (_ *x^1+ _ + (_ *x^1+ _ + _)) (suc _) _ c₁ c₂ =
    *x^1++≢con , c₁ , c₂

  times-plusᶜ-Canonical :
    ∀ k p₂ → Canonical p₁ → Canonical p₂ →
    Canonical (times-plusᶜ p₁ k p₂)
  times-plusᶜ-Canonical zero _ c₁ c₂ =
    +ᴺ-Canonical _ _ c₁ c₂
  times-plusᶜ-Canonical {p₁} (suc _) (con _) c _ =
    *x^+-Canonical p₁ (suc _) _ c _
  times-plusᶜ-Canonical {p₁} (suc _) (lift zero _) c₁ (_ , c₂) =
    *x^+-Canonical p₁ (suc _) _ c₁ c₂
  times-plusᶜ-Canonical {p₁} (suc _) (lift (suc _) _) c₁ c₂ =
    *x^+-Canonical p₁ (suc _) _ c₁ c₂
  times-plusᶜ-Canonical (suc k₁) (_ *x^1+ k₂ + _) c₁ (ok , c₂ , c₃)
    with k₁ <= k₂
  … | true =
    *x^+-Canonical (times-plusᶜ _ (_ ∸ k₁) _) (suc _) _
      (times-plusᶜ-Canonical (_ ∸ k₁) _ c₂ c₁) c₃
  … | false =
    *x^+-Canonical (times-plusᶜ _ (_ ∸ k₂) _) (suc _) _
      (times-plusᶜ-Canonical (_ ∸ k₂) _ c₁ c₂) c₃

  mutual

    -- Some lemmas about "is not equal to con 0" and OK-as-arg-1 are
    -- proved here, because they are proved mutually with lemmas about
    -- canonicity.

    *ᴺ-≢-con-0 :
      ∀ p₁ p₂ → Canonical p₁ → p₁ ≢ con 0 → Canonical p₂ → p₂ ≢ con 0 →
      p₁ *ᴺ p₂ ≢ con 0
    *ᴺ-≢-con-0 (con _) (con _) _ ok₁ _ ok₂ =
      [ ok₁ ∘ cong con , ok₂ ∘ cong con ] ∘ *≡0→ ∘ con-injective
    *ᴺ-≢-con-0 (con 0) (_ *x^1+ _ + _) _ ok _ _ =
      ok
    *ᴺ-≢-con-0 (con (suc _)) (_ *x^1+ _ + _) _ _ _ _ =
      *x^1++≢con
    *ᴺ-≢-con-0 (_ *x^1+ _ + _) (con 0) _ _ _ ok =
      ⊥-elim (ok (refl _))
    *ᴺ-≢-con-0 (_ *x^1+ _ + _) (con (suc _)) _ _ _ _ =
      *x^1++≢con
    *ᴺ-≢-con-0 (lift n _) (con _) (plus , c₁) _ c₂ ok =
      lift-times-≢-con-0 (suc n) _ c₁ (Plus→≢con plus) c₂ ok
    *ᴺ-≢-con-0 (lift n _) (_ *x^1+ _ + _) (plus , c₁) _ c₂ ok =
      lift-times-≢-con-0 (suc n) _ c₁ (Plus→≢con plus) c₂ ok
    *ᴺ-≢-con-0 (lift n _) (lift _ _) (plus , c₁) _ c₂ ok =
      lift-times-≢-con-0 (suc n) _ c₁ (Plus→≢con plus) c₂ ok
    *ᴺ-≢-con-0 (con _) (lift _ _) _ ok (plus , c) _ =
      times-lift-≢-con-0 (suc _) _ ok c (Plus→≢con plus)
    *ᴺ-≢-con-0 (_ *x^1+ _ + _) (lift _ _) c₁ ok (plus , c₂) _ =
      times-lift-≢-con-0 (suc _) c₁ ok c₂ (Plus→≢con plus)
    *ᴺ-≢-con-0
      (_ *x^1+ k₁ + _) (_ *x^1+ k₂ + _) (ok₁ , c₁ , c₂) _
      (ok₂ , c₃ , c₄) _
      with k₁ <= k₂
    … | true =
      let c₅  = *ᴺ-Canonical _ _ c₁ c₃
          c₆  = lift-times-Canonical 1 _ c₂ c₃
          c₇  = times-lift-Canonical 1 c₁ c₄
          c₈  = times-plusᶜ-Canonical (suc _) _ c₅ c₆
          c₉  = times-plusᶜ-Canonical (_ ∸ k₁) _ c₈ c₇
          c₁₀ = liftᴺ-Canonical _ _ (*ᴺ-Canonical _ _ c₂ c₄)
      in
      times-plusᶜ-≢-con-0 (suc _) _ c₉ c₁₀ $ inj₁ $
      times-plusᶜ-≢-con-0 (_ ∸ k₁) _ c₈ c₇ $ inj₁ $
      times-plusᶜ-≢-con-0 (suc _) _ c₅ c₆ $ inj₁ $
      *ᴺ-≢-con-0 _ _ c₁ (OK-as-arg-1→≢con-0 ok₁) c₃
        (OK-as-arg-1→≢con-0 ok₂)
    … | false =
      let c₅  = *ᴺ-Canonical _ _ c₁ c₃
          c₆  = lift-times-Canonical 1 _ c₂ c₃
          c₇  = times-lift-Canonical 1 c₁ c₄
          c₈  = times-plusᶜ-Canonical (suc _) _ c₅ c₇
          c₉  = times-plusᶜ-Canonical (_ ∸ k₂) _ c₈ c₆
          c₁₀ = liftᴺ-Canonical _ _ (*ᴺ-Canonical _ _ c₂ c₄)
      in
      times-plusᶜ-≢-con-0 (suc _) _ c₉ c₁₀ $ inj₁ $
      times-plusᶜ-≢-con-0 (_ ∸ k₂) _ c₈ c₆ $ inj₁ $
      times-plusᶜ-≢-con-0 (suc _) _ c₅ c₇ $ inj₁ $
      *ᴺ-≢-con-0 _ _ c₁ (OK-as-arg-1→≢con-0 ok₁) c₃
        (OK-as-arg-1→≢con-0 ok₂)

    times-lift-≢-con-0 :
      ∀ n → Canonical p₁ → p₁ ≢ con 0 → Canonical p₂ → p₂ ≢ con 0 →
      times-lift p₁ n p₂ ≢ con 0
    times-lift-≢-con-0 n c₁ ok₁ c₂ ok₂ =
      lift-times-≢-con-0 n _ c₂ ok₂ c₁ ok₁

    lift-times-≢-con-0 :
      ∀ n p₂ → Canonical p₁ → p₁ ≢ con 0 → Canonical p₂ → p₂ ≢ con 0 →
      lift-times n p₁ p₂ ≢ con 0
    lift-times-≢-con-0 zero _ c₁ ok₁ c₂ ok₂ =
      *ᴺ-≢-con-0 _ _ c₁ ok₁ c₂ ok₂
    lift-times-≢-con-0 (suc _) (con _) c ok₁ _ ok₂ =
      liftᴺ-≢-con-0 _ _ (*ᴺ-≢-con-0 _ _ c ok₁ _ ok₂)
    lift-times-≢-con-0 (suc n₁) (lift n₂ _) c₁ ok₁ (plus , c₂) _
      using ok₂ ← Plus→≢con plus
      with n₁ <= n₂
    … | true =
      liftᴺ-≢-con-0 (suc _) _
        (times-lift-≢-con-0 (_ ∸ n₁) c₁ ok₁ c₂ ok₂)
    … | false =
      liftᴺ-≢-con-0 (suc _) _
        (lift-times-≢-con-0 (_ ∸ n₂) _ c₁ ok₁ c₂ ok₂)
    lift-times-≢-con-0 (suc _) (_ *x^1+ _ + _) c₁ ok₁ (ok₂ , c₂ , _) _ =
      *x^+-≢-con-0 _ (suc _) $ inj₁ $
      lift-times-≢-con-0 (suc _) _ c₁ ok₁ c₂
        (OK-as-arg-1→≢con-0 ok₂)

    *ᴺ-OK-as-arg-1 :
      ∀ p₁ p₂ → Canonical p₁ → OK-as-arg-1 p₁ → Canonical p₂ →
      OK-as-arg-1 p₂ → OK-as-arg-1 (p₁ *ᴺ p₂)
    *ᴺ-OK-as-arg-1 (con _) (con _) _ ok₁ _ ok₂ =
      [ ok₁ , ok₂ ] ∘ *≡0→
    *ᴺ-OK-as-arg-1 (con 0) (_ *x^1+ _ + _) _ ok _ _ =
      ok
    *ᴺ-OK-as-arg-1
      (con (suc _)) (_ *x^1+ _ + _) _ ok₁ (_ , _ , c) ok₂ =
      *ᴺ-≢-con-0 _ _ _ (ok₁ ∘ con-injective) c ok₂
    *ᴺ-OK-as-arg-1 (_ *x^1+ _ + _) (con 0) _ _ _ ok =
      ok
    *ᴺ-OK-as-arg-1
      (_ *x^1+ _ + _) (con (suc _)) (_ , _ , c) ok₁ _ ok₂ =
      *ᴺ-≢-con-0 _ _ c ok₁ _ (ok₂ ∘ con-injective)
    *ᴺ-OK-as-arg-1 p@(con _) (lift _ _) _ ok (plus , c) _ =
      times-lift-OK-as-arg-1 p _ ok c
        (inj₁ (+≢0 , Plus→≢con plus))
    *ᴺ-OK-as-arg-1
      p@(_ *x^1+ _ + _) (lift _ _) c₁ ok (plus , c₂) _ =
      times-lift-OK-as-arg-1 p c₁ ok c₂
        (inj₁ (+≢0 , Plus→≢con plus))
    *ᴺ-OK-as-arg-1 (lift _ _) _ (plus , c₁) ok₁ c₂ ok₂ =
      lift-times-OK-as-arg-1 _ _ c₁ (inj₁ (+≢0 , Plus→≢con plus))
        c₂ ok₂
    *ᴺ-OK-as-arg-1
      (_ *x^1+ k₁ + _) (_ *x^1+ k₂ + _) (ok₁ , c₁ , c₂) ok₂
      (ok₃ , c₃ , c₄) ok₄
      with k₁ <= k₂
    … | true =
      let c₅ = lift-times-Canonical 1 _ c₂ c₃
          c₆ = times-lift-Canonical 1 c₁ c₄
          c₇ = liftᴺ-Canonical _ _ (*ᴺ-Canonical _ _ c₂ c₄)
      in
      times-plusᶜ-OK-as-arg-1 (suc _) _
        (inj₂ $ _,_ c₇ $
         times-plusᶜ-OK-as-arg-1 (_ ∸ k₁) _
           (inj₂ $ _,_ c₆ $
            times-plusᶜ-OK-as-arg-1 (suc _) _
              (inj₂ (c₅ , *ᴺ-OK-as-arg-1 _ _ c₁ ok₁ c₃ ok₃)) $
            lift-times-OK-as-arg-1 _ _ c₂ (inj₁ (+≢0 , ok₂)) c₃
              ok₃) $
         times-lift-OK-as-arg-1 _ c₁ ok₁ c₄ (inj₁ (+≢0 , ok₄))) $
      liftᴺ-OK-as-arg-1 _ _
        (inj₁ (+≢0 , *ᴺ-≢-con-0 _ _ c₂ ok₂ c₄ ok₄))
    … | false =
      let c₅ = lift-times-Canonical 1 _ c₂ c₃
          c₆ = times-lift-Canonical 1 c₁ c₄
          c₇ = liftᴺ-Canonical _ _ (*ᴺ-Canonical _ _ c₂ c₄)
      in
      times-plusᶜ-OK-as-arg-1 (suc _) _
        (inj₂ $ _,_ c₇ $
         times-plusᶜ-OK-as-arg-1 (_ ∸ k₂) _
           (inj₂ $ _,_ c₅ $
            times-plusᶜ-OK-as-arg-1 (suc _) _
              (inj₂ (c₆ , *ᴺ-OK-as-arg-1 _ _ c₁ ok₁ c₃ ok₃)) $
            times-lift-OK-as-arg-1 _ c₁ ok₁ c₄
              (inj₁ (+≢0 , ok₄))) $
         lift-times-OK-as-arg-1 _ _ c₂ (inj₁ (+≢0 , ok₂)) c₃
           ok₃) $
      liftᴺ-OK-as-arg-1 _ _
        (inj₁ (+≢0 , *ᴺ-≢-con-0 _ _ c₂ ok₂ c₄ ok₄))

    times-lift-OK-as-arg-1 :
      ∀ p₁ → Canonical p₁ → OK-as-arg-1 p₁ → Canonical p₂ →
      n ≢ 0 × p₂ ≢ con 0 ⊎ OK-as-arg-1 p₂ →
      OK-as-arg-1 (times-lift p₁ n p₂)
    times-lift-OK-as-arg-1 _ c₁ ok₁ c₂ ok₂ =
      lift-times-OK-as-arg-1 _ _ c₂ ok₂ c₁ ok₁

    lift-times-OK-as-arg-1 :
      ∀ n p₂ → Canonical p₁ →
      n ≢ 0 × p₁ ≢ con 0 ⊎ OK-as-arg-1 p₁ → Canonical p₂ →
      OK-as-arg-1 p₂ →
      OK-as-arg-1 (lift-times n p₁ p₂)
    lift-times-OK-as-arg-1 zero _ _ (inj₁ (0≢0 , _)) _ _ =
      ⊥-elim (0≢0 (refl _))
    lift-times-OK-as-arg-1 zero _ c₁ (inj₂ ok₁) c₂ ok₂ =
      *ᴺ-OK-as-arg-1 _ _ c₁ ok₁ c₂ ok₂
    lift-times-OK-as-arg-1 (suc _) (con _) c ok₁ _ ok₂ =
      liftᴺ-OK-as-arg-1 (suc _) _ $ inj₁
        (+≢0 ,
         *ᴺ-≢-con-0 _ _ c ([ proj₂ , OK-as-arg-1→≢con-0 ] ok₁) _
           (ok₂ ∘ con-injective))
    lift-times-OK-as-arg-1
      (suc n₁) (lift n₂ _) c₁ ok (plus , c₂) _
      using ok₁ ← [ proj₂ , OK-as-arg-1→≢con-0 ] ok
          | ok₂ ← Plus→≢con plus
      with n₁ <= n₂
    … | true =
      liftᴺ-OK-as-arg-1 (suc _) _
        (inj₁ (+≢0 , times-lift-≢-con-0 (_ ∸ n₁) c₁ ok₁ c₂ ok₂))
    … | false =
      liftᴺ-OK-as-arg-1 (suc _) _
        (inj₁ (+≢0 , lift-times-≢-con-0 (_ ∸ n₂) _ c₁ ok₁ c₂ ok₂))
    lift-times-OK-as-arg-1
      (suc n) (p *x^1+ _ + _) c₁ ok₁ (_ , _ , c₂) ok₂ =
      *x^-+-OK-as-arg-1 (lift-times (suc _) _ p) _ (inj₁ +≢0) $
      lift-times-≢-con-0 n _ c₁
        ([ proj₂ , OK-as-arg-1→≢con-0 ] ok₁) c₂ ok₂

    *ᴺ-Canonical :
      ∀ p₁ p₂ → Canonical p₁ → Canonical p₂ → Canonical (p₁ *ᴺ p₂)
    *ᴺ-Canonical (con _) (con _) _ _ =
      _
    *ᴺ-Canonical (con 0) (_ *x^1+ _ + _) _ _ =
      _
    *ᴺ-Canonical
      (con (suc _)) (_ *x^1+ _ + _) _ (first , c₁ , c₂) =
      *ᴺ-OK-as-arg-1 (con _) _ _ +≢0 c₁ first ,
      *ᴺ-Canonical (con _) _ _ c₁ ,
      *ᴺ-Canonical (con _) _ _ c₂
    *ᴺ-Canonical (_ *x^1+ _ + _) (con 0) _ _ =
      _
    *ᴺ-Canonical
      (p *x^1+ _ + _) (con (suc _)) (first , c₁ , c₂) _ =
      *ᴺ-OK-as-arg-1 p (con _) c₁ first _ +≢0 ,
      *ᴺ-Canonical _ (con _) c₁ _ ,
      *ᴺ-Canonical _ (con _) c₂ _
    *ᴺ-Canonical (con _) (lift n _) c₁ (_ , c₂) =
      times-lift-Canonical (suc n) c₁ c₂
    *ᴺ-Canonical p@(_ *x^1+ _ + _) (lift n _) c₁ (_ , c₂) =
      times-lift-Canonical {p₁ = p} (suc n) c₁ c₂
    *ᴺ-Canonical (lift n _) _ (_ , c₁) c₂ =
      lift-times-Canonical (suc n) _ c₁ c₂
    *ᴺ-Canonical
      (_ *x^1+ k₁ + _) (_ *x^1+ k₂ + _) (first₁ , c₁ , c₂)
      (first₂ , c₃ , c₄) with k₁ <= k₂
    … | true =
      let c₅  = *ᴺ-Canonical _ _ c₁ c₃
          c₆  = lift-times-Canonical 1 _ c₂ c₃
          c₇  = times-lift-Canonical 1 c₁ c₄
          c₈  = times-plusᶜ-Canonical (suc _) _ c₅ c₆
          c₉  = times-plusᶜ-Canonical (_ ∸ k₁) _ c₈ c₇
          c₁₀ = liftᴺ-Canonical _ _ (*ᴺ-Canonical _ _ c₂ c₄)
      in
      times-plusᶜ-Canonical (suc _) _ c₉ c₁₀
    … | false =
      let c₅  = *ᴺ-Canonical _ _ c₁ c₃
          c₆  = lift-times-Canonical 1 _ c₂ c₃
          c₇  = times-lift-Canonical 1 c₁ c₄
          c₈  = times-plusᶜ-Canonical (suc _) _ c₅ c₇
          c₉  = times-plusᶜ-Canonical (_ ∸ k₂) _ c₈ c₆
          c₁₀ = liftᴺ-Canonical _ _ (*ᴺ-Canonical _ _ c₂ c₄)
      in
      times-plusᶜ-Canonical (suc _) _ c₉ c₁₀

    lift-times-Canonical :
      ∀ n p₂ → Canonical p₁ → Canonical p₂ →
      Canonical (lift-times n p₁ p₂)
    lift-times-Canonical zero _ c₁ c₂ =
      *ᴺ-Canonical _ _ c₁ c₂
    lift-times-Canonical (suc _) (con _) c _ =
      liftᴺ-Canonical (suc _) _ (*ᴺ-Canonical _ _ c _)
    lift-times-Canonical (suc n₁) (lift n₂ _) c₁ (_ , c₂) with n₁ <= n₂
    … | true =
      liftᴺ-Canonical _ _ (times-lift-Canonical (_ ∸ n₁) c₁ c₂)
    … | false =
      liftᴺ-Canonical _ _ (lift-times-Canonical (_ ∸ n₂) _ c₁ c₂)
    lift-times-Canonical (suc n) (_ *x^1+ k + _) c₁ (_ , c₂ , c₃) =
      *x^+-Canonical _ (suc k) _
        (lift-times-Canonical (suc n) _ c₁ c₂)
        (lift-times-Canonical n _ c₁ c₃)

    times-lift-Canonical :
      ∀ n → Canonical p₁ → Canonical p₂ →
      Canonical (times-lift p₁ n p₂)
    times-lift-Canonical n c₁ c₂ =
      lift-times-Canonical n _ c₂ c₁

  ^ᴺ-Canonical :
    ∀ n → Canonical p → Canonical (p ^ᴺ n)
  ^ᴺ-Canonical zero _ =
    _
  ^ᴺ-Canonical (suc n) c =
    *ᴺ-Canonical _ _ c (^ᴺ-Canonical n c)

opaque

  -- The canonicity lemma for times-plusᶜ does not hold for
  -- times-plus.

  ¬-times-plus-Canonical :
    ¬ (∀ {p₁} k p₂ → Canonical p₁ → Canonical p₂ →
       Canonical (times-plus p₁ k p₂))
  ¬-times-plus-Canonical hyp =
    not-ok (hyp k′ _ c₁ c₂)
    where
    k′ : ℕ
    k′ = 1

    p₁′ p₂′ : Normal
    p₁′ = con 0
    p₂′ = con 0

    opaque
      unfolding Canonical

      c₁ : Canonical p₁′
      c₁ = _

      c₂ : Canonical p₂′
      c₂ = _

      not-ok : ¬ Canonical (times-plus p₁′ k′ p₂′)
      not-ok (0≢0 , _) = 0≢0 (refl _)
