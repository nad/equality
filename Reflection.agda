------------------------------------------------------------------------
-- Support for reflection
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Reflection where

open import Prelude
open import Equality.Decision-procedures

------------------------------------------------------------------------
-- Names

-- Names.

postulate Name : Set

{-# BUILTIN QNAME Name #-}

-- Equality of names.

private
  primitive
    primQNameEquality : Name → Name → Bool

infix 4 _≟-Name_

_≟-Name_ : Name → Name → Bool
_≟-Name_ = primQNameEquality

------------------------------------------------------------------------
-- Terms

-- Is the argument implicit?

Implicit? = Bool

-- Arguments.

data Arg A : Set where
  arg : (im? : Implicit?) (x : A) → Arg A

{-# BUILTIN ARG    Arg #-}
{-# BUILTIN ARGARG arg #-}

-- Terms.

data Term : Set where
  -- Variable applied to arguments.
  var     : (x : ℕ) (args : List (Arg Term)) → Term
  -- Constructor applied to arguments.
  con     : (c : Name) (args : List (Arg Term)) → Term
  -- Identifier applied to arguments.
  def     : (f : Name) (args : List (Arg Term)) → Term
  -- Explicit or implicit λ abstraction.
  lam     : (im? : Implicit?) (t : Term) → Term
  -- Pi-type.
  pi      : (t₁ : Arg Term) (t₂ : Term) → Term
  -- An arbitrary sort (Set, for instance).
  sort    : Term
  -- Anything.
  unknown : Term

{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}

-- Equality of terms.

mutual

  infix 4 _≟-Arg_ _≟-Args_ _≟_

  _≟-Arg_ : Arg Term → Arg Term → Bool
  arg e a ≟-Arg arg e′ a′ = ⌊ e ≟-Bool e′ ⌋ ∧ (a ≟-Term a′)

  _≟-Args_ : List (Arg Term) → List (Arg Term) → Bool
  []         ≟-Args []           = true
  (a ∷ args) ≟-Args (a′ ∷ args′) = (a ≟-Arg a′) ∧ (args ≟-Args args′)
  _          ≟-Args _            = false

  _≟-Term_ : Term → Term → Bool
  var x args ≟-Term var x′ args′ = ⌊ x ≟-ℕ x′ ⌋ ∧ (args ≟-Args args′)
  con c args ≟-Term con c′ args′ = (c ≟-Name c′) ∧ (args ≟-Args args′)
  def f args ≟-Term def f′ args′ = (f ≟-Name f′) ∧ (args ≟-Args args′)
  lam im? t  ≟-Term lam im?′ t′  = ⌊ im? ≟-Bool im?′ ⌋ ∧ (t ≟-Term t′)
  pi t₁ t₂   ≟-Term pi t₁′ t₂′   = (t₁ ≟-Arg t₁′) ∧ (t₂ ≟-Term t₂′)
  sort       ≟-Term sort         = true
  unknown    ≟-Term unknown      = true
  _          ≟-Term _            = false
