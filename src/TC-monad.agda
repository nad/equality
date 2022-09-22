------------------------------------------------------------------------
-- Support for reflection
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module TC-monad
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

import Agda.Builtin.Bool as B
open import Agda.Builtin.Char
open import Agda.Builtin.Float
import Agda.Builtin.Reflection
open import Agda.Builtin.Strict
open import Agda.Builtin.String

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (Type)

import Maybe eq as _
open import Monad eq
open import Nat eq

-- Reflection primitives.

open Agda.Builtin.Reflection public
  hiding (isMacro; withNormalisation; runSpeculative)

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

withNormalisation : ∀ {a} {A : P.Type a} → Bool → TC A → TC A
withNormalisation =
  Agda.Builtin.Reflection.withNormalisation ∘ _⇔_.from Bool⇔Bool

runSpeculative : ∀ {a} {A : P.Type a} → TC (A × Bool) → TC A
runSpeculative =
  Agda.Builtin.Reflection.runSpeculative ∘
  (Σ-map id (_⇔_.from Bool⇔Bool) ⟨$⟩_)

-- Constructs a visible, relevant argument that is not erased

pattern varg x = arg (arg-info visible (modality relevant quantity-ω)) x

-- Constructs a hidden, relevant argument that is not erased.

pattern harg x = arg (arg-info hidden (modality relevant quantity-ω)) x

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
  eq-ℕ = _==_

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
  eq-ArgInfo (arg-info v₁ m₁) (arg-info v₂ m₂) =
    eq-Visibility v₁ v₂ ∧ eq-Modality m₁ m₂

  eq-Arg : Arg Term → Arg Term → Bool
  eq-Arg (arg i₁ t₁) (arg i₂ t₂) =
    eq-ArgInfo i₁ i₂ ∧ eq-Term t₁ t₂

  eq-Visibility : Visibility → Visibility → Bool
  eq-Visibility visible   visible   = true
  eq-Visibility hidden    hidden    = true
  eq-Visibility instance′ instance′ = true
  eq-Visibility _         _         = false

  eq-Modality : Modality → Modality → Bool
  eq-Modality (modality r₁ q₁) (modality r₂ q₂) =
    eq-Relevance r₁ r₂ ∧ eq-Quantity q₁ q₂

  eq-Relevance : Relevance → Relevance → Bool
  eq-Relevance relevant   relevant   = true
  eq-Relevance irrelevant irrelevant = true
  eq-Relevance _          _          = false

  eq-Quantity : Quantity → Quantity → Bool
  eq-Quantity quantity-0 quantity-0 = true
  eq-Quantity quantity-ω quantity-ω = true
  eq-Quantity _          _          = false

-- Returns a fresh meta-variable of type Level.

fresh-level : TC Level
fresh-level =
  checkType unknown (def (quote Level) []) >>= λ ℓ →
  unquoteTC ℓ

-- Tries to apply the given term (of the given type) to the list of
-- arguments. The type of the resulting term is also returned.

apply : Type → Term → List (Arg Term) → TC (Type × Term)
apply A t []       = returnTC (A , t)
apply A t (a ∷ as) =
  reduce A      >>= λ A →
  apply₁ A t a  >>= λ { (A , t) →
  apply A t as        }
  where
  apply₁ : Type → Term → Arg Term → TC (Type × Term)
  apply₁ (pi (arg i₁@(arg-info k _) A) B) t₁ (arg i₂ t₂) =
    if not (eq-ArgInfo i₁ i₂)
    then typeError (strErr "apply: argument info mismatch" ∷ [])
    else
      bindTC fresh-level                   λ a →
      bindTC fresh-level                   λ b →
      bindTC (unquoteTC A)                 λ (A : P.Type a) →
      bindTC (unquoteTC (lam visible B))   λ (B : A → P.Type b) →
      bindTC (unquoteTC t₂)                λ (t₂ : A) →
      bindTC (quoteTC (B t₂))              λ Bt₂ →
      case k of λ where
        visible →
          bindTC (unquoteTC t₁)            λ (t₁ : (x : A) → B x) →
          bindTC (quoteTC (t₁ t₂))         λ t₁t₂ →
          return (Bt₂ , t₁t₂)
        hidden →
          bindTC (unquoteTC t₁)            λ (t₁ : {x : A} → B x) →
          bindTC (quoteTC (t₁ {x = t₂}))   λ t₁t₂ →
          return (Bt₂ , t₁t₂)
        instance′ →
          bindTC (unquoteTC t₁)            λ (t₁ : ⦃ x : A ⦄ → B x) →
          bindTC (quoteTC (t₁ ⦃ x = t₂ ⦄)) λ t₁t₂ →
          return (Bt₂ , t₁t₂)
  apply₁ (meta x _) _ _ = blockOnMeta x
  apply₁ A          _ _ =
    typeError (strErr "apply: not a pi" ∷ termErr A ∷ [])

mutual

  -- The number of variables bound in the pattern(s).

  bound-in-pattern : Pattern → ℕ
  bound-in-pattern (con _ ps) = bound-in-patterns ps
  bound-in-pattern (dot _)    = 0
  bound-in-pattern (var _)    = 1
  bound-in-pattern (lit _)    = 0
  bound-in-pattern (proj _)   = 0
  bound-in-pattern (absurd _) = 1

  bound-in-patterns : List (Arg Pattern) → ℕ
  bound-in-patterns []             = 0
  bound-in-patterns (arg _ p ∷ ps) =
    bound-in-pattern p + bound-in-patterns ps

mutual

  -- Renames the first variable to the second.
  --
  -- Pattern-matching lambdas are replaced by "unknown".

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
    (set t)     → set (rename-term old new t)
    (prop t)    → prop (rename-term old new t)
    (lit n)     → lit n
    (propLit n) → propLit n
    (inf n)     → inf n
    unknown     → unknown

mutual

  -- Weakening: weaken-term from by increases variables "from" and
  -- higher by "by".
  --
  -- Pattern-matching lambdas are replaced by "unknown".

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
  weaken-var from by x = if from <= x then x + by else x

  weaken-abs : ℕ → ℕ → Abs Term → Abs Term
  weaken-abs from by (abs s t) =
    abs s (weaken-term (suc from) by t)

  weaken-arg : ℕ → ℕ → Arg Term → Arg Term
  weaken-arg from by (arg i t) = arg i (weaken-term from by t)

  weaken-args : ℕ → ℕ → List (Arg Term) → List (Arg Term)
  weaken-args from by = λ where
    []       → []
    (a ∷ as) → weaken-arg from by a ∷ weaken-args from by as

  weaken-sort : ℕ → ℕ → Sort → Sort
  weaken-sort from by = λ where
    (set t)     → set (weaken-term from by t)
    (prop t)    → prop (weaken-term from by t)
    (lit n)     → lit n
    (propLit n) → propLit n
    (inf n)     → inf n
    unknown     → unknown

mutual

  -- Strengthening: strengthen-term from by subtracts "by" from
  -- variables "from" and higher. Applications of variable x, where
  -- from ≤ x and x < from + by, are replaced by "unknown".
  --
  -- Pattern-matching lambdas are replaced by "unknown".

  strengthen-term : ℕ → ℕ → Term → Term
  strengthen-term from by = λ where
    (var x args)      → let args′ = strengthen-args from by args in
                        if from + by <= x
                        then var (x ∸ by) args′
                        else if from <= x
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
    (set t)     → set (strengthen-term from by t)
    (prop t)    → prop (strengthen-term from by t)
    (lit n)     → lit n
    (propLit n) → propLit n
    (inf n)     → inf n
    unknown     → unknown

mutual

  -- The result of any-term and similar functions.
  --
  -- Note that "definitely true" can be returned even if the term
  -- contains meta-variables, the term unknown, the sort unknown, or
  -- pattern-matching lambdas.

  Any-result : P.Type
  Any-result = Any-result′ Bool

  -- A generalisation of Any-result. (Without the type parameter the
  -- raw monad instance below would not work.)

  data Any-result′ (A : P.Type) : P.Type where
    definitely : A → Any-result′ A
    -- The result is definitely true or false.
    meta : Meta → Any-result′ A
    -- There is no positive evidence that the result is true. At least
    -- one meta-variable (the given one) was encountered, and if this
    -- meta-variable is instantiated in a certain way, then the
    -- predicate might hold (depending on what the predicate is,
    -- any-term does not analyse the predicate).
    unknown : Any-result′ A
    -- There is no positive evidence that the result is true. The term
    -- contains the term unknown, the sort unknown, or a
    -- pattern-matching lambda (and pattern-matching lambdas are not
    -- analysed), or fuel ran out.

instance

  -- Any-result′ is a raw monad.

  Any-result-raw-monad : Raw-monad Any-result′
  Raw-monad.return Any-result-raw-monad = definitely
  Raw-monad._>>=_  Any-result-raw-monad = λ where
    (definitely x) f → f x
    (meta m)       f → meta m
    unknown        f → unknown

mutual

  -- Tries to figure out if the given predicate holds for some free
  -- variable in the given term. The predicate is adjusted when
  -- any-term goes under a binder.

  any-term : (ℕ → Bool) → Term → Any-result
  any-term p = λ where
    (var x args)      → (any-var p x ∨_) ⟨$⟩ any-args p args
    (con _ args)      → any-args p args
    (def _ args)      → any-args p args
    (lam _ t)         → any-abs p t
    (pat-lam cs args) → unknown
    (pi a b)          → _∨_ ⟨$⟩ any-arg p a ⊛ any-abs p b
    (agda-sort s)     → any-sort p s
    (lit l)           → definitely false
    (meta m args)     → case any-args p args of λ where
                          (definitely false) → meta m
                          r                  → r
    unknown           → unknown

  any-var : (ℕ → Bool) → ℕ → Bool
  any-var p x = p x

  any-abs : (ℕ → Bool) → Abs Term → Any-result
  any-abs p (abs _ t) =
    any-term (λ where
                zero    → false
                (suc n) → p n)
             t

  any-arg : (ℕ → Bool) → Arg Term → Any-result
  any-arg p (arg i t) = any-term p t

  any-args : (ℕ → Bool) → List (Arg Term) → Any-result
  any-args p = λ where
    []       → definitely false
    (a ∷ as) → _∨_ ⟨$⟩ any-arg p a ⊛ any-args p as

  any-sort : (ℕ → Bool) → Sort → Any-result
  any-sort p = λ where
    (set t)     → any-term p t
    (prop t)    → any-term p t
    (lit n)     → definitely false
    (propLit n) → definitely false
    (inf n)     → definitely false
    unknown     → unknown

-- Figures out if the given variable is bound in the given term.

bound? : ℕ → Term → Any-result
bound? x = any-term (eq-ℕ x)

-- Figures out if variables less than the given variable are bound
-- in the given term.

<bound? : ℕ → Term → Any-result
<bound? x = any-term (λ y → suc y <= x)

-- Does the type seem to be "dependent" (a sequence of one or more Π's
-- where at least one of the codomains mentions the bound variable)?
--
-- Hidden arguments are reconstructed if argument reconstruction has
-- been activated.

is-dependent
  : ℕ     -- Fuel.
  → Bool  -- Skip a maximal prefix of domains that are not visible?
  → Type
  → TC Any-result
is-dependent zero    _    _ = return unknown
is-dependent (suc n) skip t = do
  t ← reduce t
  case t of λ where
    (pi a@(arg (arg-info v _) _) (abs x b)) →
      let cont skip = extendContext x a $ is-dependent n skip b
          check     = case bound? 0 b of λ where
            (definitely false) → cont false
            is-bound           → return is-bound
      in case skip of λ where
        false → check
        true  → case eq-Visibility v visible of λ where
          true  → check
          false → cont true
    (meta m _) → return (meta m)
    _          → return (definitely false)
