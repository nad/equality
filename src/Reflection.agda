------------------------------------------------------------------------
-- Support for reflection
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Reflection
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

import Agda.Builtin.Bool as B
open import Agda.Builtin.Char
open import Agda.Builtin.Float
open import Agda.Builtin.Nat using (_==_)
import Agda.Builtin.Reflection
open import Agda.Builtin.String

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Monad eq
open import Nat eq

-- Reflection primitives.

open Agda.Builtin.Reflection public hiding (isMacro; withNormalisation)

-- The TC monad is a "raw monad".

instance

  raw-monad : ∀ {d} → Raw-monad {d = d} TC
  Raw-monad.return raw-monad = returnTC
  Raw-monad._>>=_ raw-monad  = bindTC

-- Converts B.Bool to and from Bool.

Bool⇔Bool : B.Bool ⇔ Bool
Bool⇔Bool = record { to = to; from = from }
  where
  to : B.Bool → Bool
  to B.false = false
  to B.true  = true

  from : Bool → B.Bool
  from false = B.false
  from true  = B.true

-- Variants of some definitions from Agda.Builtin.Reflection.

isMacro : Name → TC Bool
isMacro x = _⇔_.to Bool⇔Bool ⟨$⟩ Agda.Builtin.Reflection.isMacro x

withNormalisation : ∀ {a} {A : Set a} → Bool → TC A → TC A
withNormalisation =
  Agda.Builtin.Reflection.withNormalisation ∘ _⇔_.from Bool⇔Bool

-- Constructs a visible, relevant argument.

pattern varg x = arg (arg-info visible relevant) x

-- Constructs a hidden, relevant argument.

pattern harg x = arg (arg-info hidden relevant) x

-- An n-ary variant of pi.

pis : List (Abs (Arg Type)) → Type → Type
pis []             B = B
pis (abs x A ∷ As) B = pi A (abs x (pis As B))

mutual

  -- Checks if the terms are syntactically equal.
  --
  -- Pattern-matching lambdas and "unknown" are currently never seen
  -- as equal to anything.
  --
  -- Note that this function does not perform any kind of parameter
  -- reconstruction.

  eq-Term : Term → Term → Bool
  eq-Term (var x₁ ts₁)   (var x₂ ts₂)   = eq-ℕ x₁ x₂ ∧ eq-Args ts₁ ts₂
  eq-Term (con c₁ ts₁)   (con c₂ ts₂)   = eq-Name c₁ c₂ ∧ eq-Args ts₁ ts₂
  eq-Term (def f₁ ts₁)   (def f₂ ts₂)   = eq-Name f₁ f₂ ∧ eq-Args ts₁ ts₂
  eq-Term (lam v₁ t₁)    (lam v₂ t₂)    = eq-Visibility v₁ v₂ ∧ eq-Abs t₁ t₂
  eq-Term (pi a₁ b₁)     (pi a₂ b₂)     = eq-Arg a₁ a₁ ∧ eq-Abs b₁ b₂
  eq-Term (agda-sort s₁) (agda-sort s₂) = eq-Sort s₁ s₂
  eq-Term (lit l₁)       (lit l₂)       = eq-Literal l₁ l₂
  eq-Term (meta x₁ ts₁)  (meta x₂ ts₂)  = eq-Meta x₁ x₂ ∧ eq-Args ts₁ ts₂
  eq-Term _              _              = false

  eq-Name : Name → Name → Bool
  eq-Name x₁ x₂ = _⇔_.to Bool⇔Bool (primQNameEquality x₁ x₂)

  eq-ℕ : ℕ → ℕ → Bool
  eq-ℕ n₁ n₂ = _⇔_.to Bool⇔Bool (n₁ == n₂)

  eq-Meta : Meta → Meta → Bool
  eq-Meta x₁ x₂ = _⇔_.to Bool⇔Bool (primMetaEquality x₁ x₂)

  eq-String : String → String → Bool
  eq-String x₁ x₂ = _⇔_.to Bool⇔Bool (primStringEquality x₁ x₂)

  eq-Sort : Sort → Sort → Bool
  eq-Sort (set t₁) (set t₂) = eq-Term t₁ t₂
  eq-Sort (lit n₁) (lit n₂) = eq-ℕ n₁ n₂
  eq-Sort _        _        = false

  eq-Literal : Literal → Literal → Bool
  eq-Literal (nat n₁)    (nat n₂)    = eq-ℕ n₁ n₂
  eq-Literal (float x₁)  (float x₂)  = _⇔_.to Bool⇔Bool
                                         (primFloatEquality x₁ x₂)
  eq-Literal (char c₁)   (char c₂)   = _⇔_.to Bool⇔Bool
                                         (primCharEquality c₁ c₂)
  eq-Literal (string s₁) (string s₂) = eq-String s₁ s₂
  eq-Literal (name x₁)   (name x₂)   = eq-Name x₁ x₂
  eq-Literal (meta x₁)   (meta x₂)   = eq-Meta x₁ x₂
  eq-Literal _           _           = false

  eq-Args : List (Arg Term) → List (Arg Term) → Bool
  eq-Args []         []         = true
  eq-Args (t₁ ∷ ts₁) (t₂ ∷ ts₂) = eq-Arg t₁ t₂ ∧ eq-Args ts₁ ts₂
  eq-Args _          _          = false

  eq-Abs : Abs Term → Abs Term → Bool
  eq-Abs (abs s₁ t₁) (abs s₂ t₂) =
    eq-String s₁ s₂ ∧ eq-Term t₁ t₂

  eq-ArgInfo : ArgInfo → ArgInfo → Bool
  eq-ArgInfo (arg-info v₁ r₁) (arg-info v₂ r₂) =
    eq-Visibility v₁ v₂ ∧ eq-Relevance r₁ r₂

  eq-Arg : Arg Term → Arg Term → Bool
  eq-Arg (arg i₁ t₁) (arg i₂ t₂) =
    eq-ArgInfo i₁ i₂ ∧ eq-Term t₁ t₂

  eq-Visibility : Visibility → Visibility → Bool
  eq-Visibility visible   visible   = true
  eq-Visibility hidden    hidden    = true
  eq-Visibility instance′ instance′ = true
  eq-Visibility _         _         = false

  eq-Relevance : Relevance → Relevance → Bool
  eq-Relevance relevant   relevant   = true
  eq-Relevance irrelevant irrelevant = true
  eq-Relevance _          _          = false

-- Returns a fresh meta-variable of type Level.

fresh-level : TC Level
fresh-level =
  checkType unknown (def (quote Level) []) >>= λ ℓ →
  unquoteTC ℓ

-- Tries to apply the given term (of the given type) to the list of
-- arguments.

apply : Type → Term → List (Arg Term) → TC Term
apply A t []       = returnTC t
apply A t (a ∷ as) =
  reduce A      >>= λ A →
  apply₁ A t a  >>= λ { (A , t) →
  apply A t as        }
  where
  apply₁ : Type → Term → Arg Term → TC (Type × Term)
  apply₁ (meta x _) _ _ = blockOnMeta x
  apply₁ (pi (arg (arg-info visible relevant) A) B) t₁ (arg _ t₂) =
    bindTC fresh-level                 λ a →
    bindTC fresh-level                 λ b →
    bindTC (unquoteTC A)               λ (A : Set a) →
    bindTC (unquoteTC (lam visible B)) λ (B : A → Set b) →
    bindTC (unquoteTC t₁)              λ (t₁ : (x : A) → B x) →
    bindTC (unquoteTC t₂)              λ (t₂ : A) →
    bindTC (quoteTC (B t₂))            λ Bt₂ →
    bindTC (quoteTC (t₁ t₂))           λ t₁t₂ →
    return (Bt₂ , t₁t₂)
  apply₁ A _ _ =
    typeError (strErr "apply: not a pi" ∷ termErr A ∷ [])

mutual

  -- Renames the first variable to the second.
  --
  -- Applications of pattern-matching lambdas are replaced by
  -- "unknown".

  rename-term : ℕ → ℕ → Term → Term
  rename-term old new = λ where
    (var x args)      → var (rename-var old new x)
                            (rename-args old new args)
    (con c args)      → con c (rename-args old new args)
    (def f args)      → def f (rename-args old new args)
    (lam v t)         → lam v (rename-abs old new t)
    (pat-lam cs args) → unknown
    (pi a b)          → pi (rename-arg old new a) (rename-abs old new b)
    (agda-sort s)     → agda-sort (rename-sort old new s)
    (lit l)           → lit l
    (meta x args)     → meta x (rename-args old new args)
    unknown           → unknown

  rename-var : ℕ → ℕ → ℕ → ℕ
  rename-var old new x = if eq-ℕ x old then new else old

  rename-abs : ℕ → ℕ → Abs Term → Abs Term
  rename-abs old new (abs s t) =
    abs s (rename-term (suc old) (suc new) t)

  rename-arg : ℕ → ℕ → Arg Term → Arg Term
  rename-arg old new (arg i t) = arg i (rename-term old new t)

  rename-args : ℕ → ℕ → List (Arg Term) → List (Arg Term)
  rename-args old new = λ where
    []       → []
    (a ∷ as) → rename-arg old new a ∷ rename-args old new as

  rename-sort : ℕ → ℕ → Sort → Sort
  rename-sort old new = λ where
    (set t) → set (rename-term old new t)
    (lit n) → lit n
    unknown → unknown

mutual

  -- Weakening: weaken-term from by increases variables "from" and
  -- higher by "by". Applications of pattern-matching lambdas are
  -- replaced by "unknown".

  weaken-term : ℕ → ℕ → Term → Term
  weaken-term from by = λ where
    (var x args)      → var (weaken-var from by x)
                            (weaken-args from by args)
    (con c args)      → con c (weaken-args from by args)
    (def f args)      → def f (weaken-args from by args)
    (lam v t)         → lam v (weaken-abs from by t)
    (pat-lam cs args) → unknown
    (pi a b)          → pi (weaken-arg from by a) (weaken-abs from by b)
    (agda-sort s)     → agda-sort (weaken-sort from by s)
    (lit l)           → lit l
    (meta x args)     → meta x (weaken-args from by args)
    unknown           → unknown

  weaken-var : ℕ → ℕ → ℕ → ℕ
  weaken-var from by x = if from ≤? x then x + by else x

  weaken-abs : ℕ → ℕ → Abs Term → Abs Term
  weaken-abs from by (abs s t) =
    abs s (weaken-term (suc from) (suc by) t)

  weaken-arg : ℕ → ℕ → Arg Term → Arg Term
  weaken-arg from by (arg i t) = arg i (weaken-term from by t)

  weaken-args : ℕ → ℕ → List (Arg Term) → List (Arg Term)
  weaken-args from by = λ where
    []       → []
    (a ∷ as) → weaken-arg from by a ∷ weaken-args from by as

  weaken-sort : ℕ → ℕ → Sort → Sort
  weaken-sort from by = λ where
    (set t) → set (weaken-term from by t)
    (lit n) → lit n
    unknown → unknown

mutual

  -- Strengthening: strengthen-term from by subtracts "by" from
  -- variables "from" and higher. Applications of variable x, where
  -- from ≤ x and x < from + by, as well as applications of
  -- pattern-matching lambdas, are replaced by "unknown".

  strengthen-term : ℕ → ℕ → Term → Term
  strengthen-term from by = λ where
    (var x args)      → let args′ = strengthen-args from by args in
                        if from + by ≤? x
                        then var (x ∸ by) args′
                        else if from ≤? x
                        then unknown
                        else var x args′
    (con c args)      → con c (strengthen-args from by args)
    (def f args)      → def f (strengthen-args from by args)
    (lam v t)         → lam v (strengthen-abs from by t)
    (pat-lam cs args) → unknown
    (pi a b)          → pi (strengthen-arg from by a)
                           (strengthen-abs from by b)
    (agda-sort s)     → agda-sort (strengthen-sort from by s)
    (lit l)           → lit l
    (meta x args)     → meta x (strengthen-args from by args)
    unknown           → unknown

  strengthen-abs : ℕ → ℕ → Abs Term → Abs Term
  strengthen-abs from by (abs s t) =
    abs s (strengthen-term (suc from) by t)

  strengthen-arg : ℕ → ℕ → Arg Term → Arg Term
  strengthen-arg from by (arg i t) = arg i (strengthen-term from by t)

  strengthen-args : ℕ → ℕ → List (Arg Term) → List (Arg Term)
  strengthen-args from by = λ where
    []       → []
    (a ∷ as) → strengthen-arg from by a ∷ strengthen-args from by as

  strengthen-sort : ℕ → ℕ → Sort → Sort
  strengthen-sort from by = λ where
    (set t) → set (strengthen-term from by t)
    (lit n) → lit n
    unknown → unknown
