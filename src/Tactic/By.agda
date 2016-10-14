------------------------------------------------------------------------
-- Some tactics aimed at making equational reasoning proofs more
-- readable
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Tactic.By where

import Agda.Builtin.Bool as B
open import Agda.Builtin.Char
open import Agda.Builtin.Float
open import Agda.Builtin.Nat using (_==_)
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Agda.Primitive

open import Equality.Propositional
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

  -- Converts B.Bool to Bool.

  to-Bool : B.Bool → Bool
  to-Bool B.false = false
  to-Bool B.true  = true

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
    eq-Name x₁ x₂ = to-Bool (primQNameEquality x₁ x₂)

    eq-ℕ : ℕ → ℕ → Bool
    eq-ℕ n₁ n₂ = to-Bool (n₁ == n₂)

    eq-Meta : Meta → Meta → Bool
    eq-Meta x₁ x₂ = to-Bool (primMetaEquality x₁ x₂)

    eq-String : String → String → Bool
    eq-String x₁ x₂ = to-Bool (primStringEquality x₁ x₂)

    eq-Sort : Sort → Sort → Bool
    eq-Sort (set t₁) (set t₂) = eq-Term t₁ t₂
    eq-Sort (lit n₁) (lit n₂) = eq-ℕ n₁ n₂
    eq-Sort _        _        = false

    eq-Literal : Literal → Literal → Bool
    eq-Literal (nat n₁)    (nat n₂)    = eq-ℕ n₁ n₂
    eq-Literal (float x₁)  (float x₂)  = to-Bool (primFloatEquality x₁ x₂)
    eq-Literal (char c₁)   (char c₂)   = to-Bool (primCharEquality c₁ c₂)
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
    bindTC (checkType unknown (def (quote Level) [])) λ ℓ →
    unquoteTC ℓ

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

  unquoteDecl cong₃  = make-cong-called cong₃   3
  unquoteDecl cong₄  = make-cong-called cong₄   4
  unquoteDecl cong₅  = make-cong-called cong₅   5
  unquoteDecl cong₆  = make-cong-called cong₆   6
  unquoteDecl cong₇  = make-cong-called cong₇   7
  unquoteDecl cong₈  = make-cong-called cong₈   8
  unquoteDecl cong₉  = make-cong-called cong₉   9
  unquoteDecl cong₁₀ = make-cong-called cong₁₀ 10

  -- Constructs a "cong" function (like cong and cong₂ in Equality)
  -- for functions with the given number of arguments. The name of the
  -- constructed function is returned (for 1 and 2 the functions in
  -- Equality are returned). The cong functions for functions with 3
  -- up to 10 arguments are cached to avoid creating lots of copies of
  -- the same functions.

  make-cong : ℕ → TC Name
  make-cong  1 = returnTC (quote cong)
  make-cong  2 = returnTC (quote cong₂)
  make-cong  3 = returnTC (quote cong₃)
  make-cong  4 = returnTC (quote cong₄)
  make-cong  5 = returnTC (quote cong₅)
  make-cong  6 = returnTC (quote cong₆)
  make-cong  7 = returnTC (quote cong₇)
  make-cong  8 = returnTC (quote cong₈)
  make-cong  9 = returnTC (quote cong₉)
  make-cong 10 = returnTC (quote cong₁₀)
  make-cong n  =
    bindTC (freshName "cong") λ cong →
    bindTC (make-cong-called cong n) λ _ →
    returnTC cong

  -- Tries to apply the given term (of the given type, which must live
  -- in Set₀) to the list of arguments.

  apply : Type → Term → List (Arg Term) → TC Term
  apply A t []       = returnTC t
  apply A t (a ∷ as) =
    bindTC (reduce A)     λ A →
    bindTC (apply₁ A t a) λ { (A , t) →
    apply A t as          }
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
      returnTC (Bt₂ , t₁t₂)
    apply₁ A _ _ =
      typeError (strErr "apply: not a pi" ∷ termErr A ∷ [])

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
      bindTC (apply A t (reverse args)) λ t →
      catchTC (try false t)             $
      catchTC (try true  t)             $
      typeError (strErr "refine failed" ∷ [])

  -- The call by-tactic t goal tries to use (non-dependent) "cong"
  -- functions, reflexivity and t (via refine) to solve the given goal
  -- (which must be an equality).
  --
  -- The constructed term is returned.

  by-tactic : ∀ {a} {A : Set a} → A → Term → TC Term
  by-tactic {A = A} t goal =
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
        -- Checks if the heads are equal. If they are, then the
        -- function figures out how many arguments are equal, and
        -- returns the (unique) head applied to these arguments, plus
        -- two lists containing the remaining arguments.

        heads : Term → Term →
                TC (Term × List (Arg Term) × List (Arg Term))
        heads = λ
          { (def y ys) (def z zs) → helper (primQNameEquality y z)
                                           (def y) (def z) ys zs
          ; (con y ys) (con z zs) → helper (primQNameEquality y z)
                                           (con y) (con z) ys zs
          ; (var y ys) (var z zs) → helper (y == z)
                                           (var y) (var z) ys zs
          ; _          _          → failure
          }
          where
          find-equal-arguments :
            List (Arg Term) → List (Arg Term) →
            List (Arg Term) × List (Arg Term) × List (Arg Term)
          find-equal-arguments []       zs       = [] , [] , zs
          find-equal-arguments ys       []       = [] , ys , []
          find-equal-arguments (y ∷ ys) (z ∷ zs) with eq-Arg y z
          ... | false = [] , y ∷ ys , z ∷ zs
          ... | true  with find-equal-arguments ys zs
          ...   | (es , ys′ , zs′) = y ∷ es , ys′ , zs′

          helper : B.Bool → _ → _ → _ → _ → _
          helper B.false y z _  _  =
            typeError (strErr "by: distinct heads:" ∷
                       termErr (y []) ∷ termErr (z []) ∷ [])
          helper B.true  y _ ys zs =
            let es , ys′ , zs′ = find-equal-arguments ys zs in
            returnTC (y es , ys′ , zs′)

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

  by : ∀ {a} {A : Set a} → A → Term → TC ⊤
  by t goal =
    bindTC (by-tactic t goal) λ _ →
    returnTC _

  -- If by t would have been successful, then debug-by t raises an
  -- error message that includes the term that would have been
  -- constructed by by.

  debug-by : ∀ {a} {A : Set a} → A → Term → TC ⊤
  debug-by t goal =
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

    test₁₀ : (f : ℕ → ℕ) → f 42 ≡ f 48
    test₁₀ f = by (λ (_ : ⊤) → assumption)

    fst : ∀ {a b} {A : Set a} {B : A → Set b} →
          Σ A B → A
    fst = proj₁

    test₁₁ : (f : ℕ × ℕ → ℕ × ℕ) → (∀ x → f x ≡ x) →
             fst (f (12 , 73)) ≡ fst {B = λ _ → ℕ} (12 , 73)
    test₁₁ _ hyp = by hyp
