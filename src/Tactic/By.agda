------------------------------------------------------------------------
-- Some tactics aimed at making equational reasoning proofs more
-- readable
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Tactic.By where

import Agda.Builtin.Bool as B
open import Agda.Builtin.Nat using (_==_)
open import Agda.Primitive
open import Agda.Builtin.Reflection

open import Equality.Propositional hiding (cong₂)
open import Prelude

open import Equality.Decision-procedures
open import List equality-with-J

private

  -- Constructs a visible, relevant argument.

  varg : {A : Set} → A → Arg A
  varg = arg (arg-info visible relevant)

  -- Constructs a hidden, relevant argument.

  harg : {A : Set} → A → Arg A
  harg = arg (arg-info hidden relevant)

  -- Constructs a "cong" function (like cong and cong₂ in Equality)
  -- for functions with the given name and the given number of
  -- arguments.

  make-cong-called : Name → ℕ → TC ⊤
  make-cong-called cong n =
    bindTC (declareDef (varg cong) the-type) λ _ →
    defineFun cong (the-clause ∷ [])
    where
    the-type : Type
    the-type = levels (suc n)
      where
      arguments : ℕ → ℕ → List (Arg Term)
      arguments delta (suc m) = varg (var (3 * m + 1 + delta) []) ∷
                                arguments delta m
      arguments delta zero    = []

      equalities : ℕ → Type
      equalities (suc m) =
        pi (harg (var (m + 2 + 3 * (n ∸ suc m)) [])) $ abs "x" $
        pi (harg (var (m + 3 + 3 * (n ∸ suc m)) [])) $ abs "y" $
        pi (varg (def (quote _≡_)
                      (varg (var 1 []) ∷
                       varg (var 0 []) ∷ []))) $ abs "x≡y" $
           equalities m
      equalities zero =
        def (quote _≡_)
            (varg (var (3 * n) (arguments 1 n)) ∷
             varg (var (3 * n) (arguments 0 n)) ∷
             [])

      function-type : ℕ → Type
      function-type (suc m) = pi (varg (var n []))
                                 (abs "_" (function-type m))
      function-type zero    = var n []

      types : ℕ → Type
      types (suc m) = pi (harg (agda-sort (set (var n [])))) $ abs "A" $
                         types m
      types zero    = pi (varg (function-type n)) $ abs "f" $
                         equalities n

      levels : ℕ → Type
      levels (suc n) = pi (harg (def (quote Level) [])) $ abs "a" $
                          levels n
      levels zero    = types (suc n)

    the-clause : Clause
    the-clause =
      clause (varg (var "f") ∷ replicate n (varg (con (quote refl) [])))
             (con (quote refl) [])

  unquoteDecl cong₁ = make-cong-called cong₁ 1
  unquoteDecl cong₂ = make-cong-called cong₂ 2
  unquoteDecl cong₃ = make-cong-called cong₃ 3
  unquoteDecl cong₄ = make-cong-called cong₄ 4
  unquoteDecl cong₅ = make-cong-called cong₅ 5

  -- Constructs a "cong" function (like cong and cong₂ in Equality)
  -- for functions with the given number of arguments. The name of the
  -- constructed function is returned. The cong functions for
  -- functions with 1 up to 5 arguments are cached to avoid creating
  -- lots of copies of the same functions.

  make-cong : ℕ → TC Name
  make-cong 1 = returnTC (quote cong₁)
  make-cong 2 = returnTC (quote cong₂)
  make-cong 3 = returnTC (quote cong₃)
  make-cong 4 = returnTC (quote cong₄)
  make-cong 5 = returnTC (quote cong₅)
  make-cong n =
    bindTC (freshName "cong") λ cong →
    bindTC (make-cong-called cong n) λ _ →
    returnTC cong

  -- Tries to apply the term to the list of arguments.

  apply : Term → List (Arg Term) → TC Term
  apply (var x xs)      ys = returnTC (var x      (xs ++ ys))
  apply (con x xs)      ys = returnTC (con x      (xs ++ ys))
  apply (def x xs)      ys = returnTC (def x      (xs ++ ys))
  apply (pat-lam cs xs) ys = returnTC (pat-lam cs (xs ++ ys))
  apply (meta x xs)     ys = returnTC (meta x     (xs ++ ys))
  apply t               _  =
    typeError (strErr "apply" ∷ termErr t ∷ [])

  -- The tactic refine A t goal tries to use the term t (of type A),
  -- applied to as many fresh meta-variables as possible (based on its
  -- type), to solve the given goal. If this fails, then an attempt is
  -- made to solve the goal using "sym (x metas)" instead.

  refine : Type → Term → Term → TC Term
  refine A t goal =
    bindTC (normalise A) λ A →
    refine-with-type [] A
    where
    with-sym : Bool → Term → Term
    with-sym true  t = def (quote sym) (varg t ∷ [])
    with-sym false t = t

    try : Bool → Term → TC Term
    try use-sym t =
      bindTC (unify t′ goal) λ _ →
      returnTC t′
      where
      t′ = with-sym use-sym t

    refine-with-type : List (Arg Term) → Type → TC Term
    refine-with-type args (meta x _)               = blockOnMeta x
    refine-with-type args (pi (arg i _) (abs _ τ)) =
      refine-with-type (arg i unknown ∷ args) τ
    refine-with-type args _                        =
      bindTC (apply t (reverse args)) λ t →
      catchTC (try false t)           $
      catchTC (try true  t)           $
      typeError (strErr "refine failed" ∷ [])

  -- The call by-tactic t goal tries to use (non-dependent) "cong"
  -- functions, reflexivity and t (via refine) to solve the given goal
  -- (which must be an equality).
  --
  -- The constructed term is returned.

  by-tactic : {A : Set} → A → Term → TC Term
  by-tactic {A} t goal =
    bindTC (quoteTC A) λ A →
    bindTC (quoteTC t) λ t →
    by-tactic′ fuel A t goal
    where
    -- Fuel, used to ensure termination. (Termination could perhaps be
    -- proved in some way, but using fuel was easier.)

    fuel : ℕ
    fuel = 1000000

    -- The tactic's main loop.

    by-tactic′ : ℕ → Type → Term → Term → TC Term
    by-tactic′ zero    _ _ _    = typeError
                                    (strErr "by: no more fuel" ∷ [])
    by-tactic′ (suc n) A t goal =
      bindTC (inferType goal)          λ goal-type →
      bindTC (reduce goal-type)        λ goal-type →
      bindTC (block-if-meta goal-type) λ _ →
      catchTC (try-refl goal-type)     $
      catchTC (refine A t goal)        $
      try-cong goal-type
      where
      -- Error messages.

      ill-formed failure : {A : Set} → TC A
      ill-formed = typeError (strErr "by: ill-formed goal" ∷ [])
      failure    = typeError (strErr "by failed" ∷ [])

      -- Blocks if the goal type is not sufficiently concrete. Raises
      -- a type error if the goal type is not an equality.

      block-if-meta : Type → TC ⊤
      block-if-meta (meta m _)                            = blockOnMeta m
      block-if-meta
        (def (quote _≡_)
             (_ ∷ _ ∷ arg _ (meta m _) ∷ _))              = blockOnMeta m
      block-if-meta
        (def (quote _≡_)
             (_ ∷ _ ∷ _ ∷ arg _ (meta m _) ∷ _))          = blockOnMeta m
      block-if-meta (def (quote _≡_) (_ ∷ _ ∷ _ ∷ _ ∷ _)) = returnTC _
      block-if-meta _                                     = ill-formed

      -- Tries to solve the goal using reflexivity.

      try-refl : Type → TC Term
      try-refl (def (quote _≡_) (a ∷ A ∷ arg _ lhs ∷ _)) =
        bindTC (unify t′ goal) λ _ →
        returnTC t′
        where
        t′ = con (quote refl) (a ∷ A ∷ harg lhs ∷ [])
      try-refl _ = ill-formed

      -- Tries to solve the goal using one of the "cong" functions.

      try-cong : Term → TC Term
      try-cong (def (quote _≡_) (_ ∷ _ ∷ arg _ y ∷ arg _ z ∷ [])) =
        bindTC (heads y z)                     λ { (head , ys , zs) →
        bindTC (arguments ys zs)               λ args →
        bindTC (make-cong (length args))       λ cong →
        let t = def cong (varg head ∷ args) in
        bindTC (unify t goal)                  λ _ →
        returnTC t                             }
        where
        -- Checks if the heads are equal. Returns the (unique) head,
        -- along with the two argument lists.

        heads : Term → Term →
                TC (Term × List (Arg Term) × List (Arg Term))
        heads = λ
          { (def y ys) (def z zs) → helper (primQNameEquality y z)
                                           (def y []) (def z []) ys zs
          ; (con y ys) (con z zs) → helper (primQNameEquality y z)
                                           (con y []) (con z []) ys zs
          ; (var y ys) (var z zs) → helper (y == z)
                                           (var y []) (var z []) ys zs
          ; _          _          → failure
          }
          where
          helper : B.Bool → _ → _ → _ → _ → _
          helper B.true  y _ ys zs = returnTC (y , ys , zs)
          helper B.false y z _  _  =
            typeError (strErr "by: distinct heads:" ∷
                       termErr y ∷ termErr z ∷ [])

        -- Tries to prove that the argument lists are equal.

        arguments : List (Arg Term) → List (Arg Term) →
                    TC (List (Arg Term))
        arguments [] []                             = returnTC []
        arguments (arg (arg-info visible _) y ∷ ys)
                  (arg (arg-info visible _) z ∷ zs) =
                   -- Relevance is ignored.

          bindTC (checkType unknown
                    (def (quote _≡_) (varg y ∷ varg z ∷ []))) λ goal →
          bindTC (by-tactic′ n A t goal) λ t →
          bindTC (arguments ys zs) λ args →
          returnTC (varg t ∷ args)

        -- Hidden and instance arguments are ignored.

        arguments (arg (arg-info hidden _) _ ∷ ys) zs    = arguments ys zs
        arguments (arg (arg-info instance′ _) _ ∷ ys) zs = arguments ys zs
        arguments ys (arg (arg-info hidden _) _ ∷ zs)    = arguments ys zs
        arguments ys (arg (arg-info instance′ _) _ ∷ zs) = arguments ys zs

        arguments _ _ = failure

      try-cong _ = ill-formed

macro

  -- The call by t tries to use t (along with congruence, reflexivity
  -- and symmetry) to solve the goal, which must be an equality.

  by : {A : Set} → A → Term → TC ⊤
  by t goal =
    bindTC (by-tactic t goal) λ _ →
    returnTC _

  -- If by t would have been successful, then debug-by t raises an
  -- error message that includes the term that would have been
  -- constructed by by.

  debug-by : {A : Set} → A → Term → TC ⊤
  debug-by {A} t goal =
    bindTC (by-tactic t goal) λ t →
    typeError (strErr "Term found by by:" ∷ termErr t ∷ [])

-- A definition that provides no information. Intended to be used
-- together with the by tactic: "by definition".

definition : ⊤
definition = _

------------------------------------------------------------------------
-- Some unit tests

private

  module Tests
    (assumption : 48 ≡ 42)
    (lemma      : ∀ n → n + 8 ≡ n + 2)
    (f          : ℕ → ℕ → ℕ → ℕ)
    where

    test₁ : 40 + 2 ≡ 42
    test₁ = by definition

    test₂ : 48 ≡ 42 → 42 ≡ 48
    test₂ eq = by eq

    test₃ : (f : ℕ → ℕ) → f 42 ≡ f 48
    test₃ f = by assumption

    test₄ : (f : ℕ → ℕ) → f 48 ≡ f 42
    test₄ f = by assumption

    test₅ : (f : ℕ → ℕ → ℕ) → f 42 48 ≡ f 48 42
    test₅ f = by assumption

    test₆ : (f : ℕ → ℕ → ℕ → ℕ) → f 42 45 48 ≡ f 48 45 42
    test₆ f = by assumption

    test₇ : f 48 (f 42 45 48) 42 ≡ f 48 (f 48 45 42) 48
    test₇ = by assumption

    g : ℕ → ℕ → ℕ → ℕ
    g zero    _ _ = 12
    g (suc _) _ _ = 12

    test₈ : ∀ n → g n (g n 45 48) 42 ≡ g n (g n 45 42) 48
    test₈ n = by assumption

    test₉ : (f : ℕ → ℕ) → f 42 ≡ f 48
    test₉ f = by (lemma 40)
