------------------------------------------------------------------------
-- Some tactics aimed at making equational reasoning proofs more
-- readable
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Note that this module is not parametrised by a definition of
-- equality, it uses propositional equality.

module Tactic.By where

import Agda.Builtin.Bool as B
open import Agda.Builtin.Nat using (_==_)

open import Equality.Propositional
open import Prelude

open import List equality-with-J
open import Maybe equality-with-J
open import Monad equality-with-J
open import TC-monad equality-with-J

------------------------------------------------------------------------
-- The by tactic

private

  -- Constructs a "cong" function (similar to cong and cong₂ in
  -- Equality), with the given name, for functions with the given
  -- number of arguments.

  make-cong-called : Name → ℕ → TC ⊤
  make-cong-called cong n =
    declareDef (varg cong) the-type  >>= λ _ →
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

  -- Constructs a "cong" function (similar to cong and cong₂ in
  -- Equality) for functions with the given number of arguments. The
  -- name of the constructed function is returned (for 1 and 2 the
  -- functions in Equality are returned). The cong functions for
  -- functions with 3 up to 10 arguments are cached to avoid creating
  -- lots of copies of the same functions.

  make-cong : ℕ → TC Name
  make-cong  1 = return (quote cong)
  make-cong  2 = return (quote cong₂)
  make-cong  3 = return (quote cong₃)
  make-cong  4 = return (quote cong₄)
  make-cong  5 = return (quote cong₅)
  make-cong  6 = return (quote cong₆)
  make-cong  7 = return (quote cong₇)
  make-cong  8 = return (quote cong₈)
  make-cong  9 = return (quote cong₉)
  make-cong 10 = return (quote cong₁₀)
  make-cong n  =
    freshName "cong"        >>= λ cong →
    make-cong-called cong n >>= λ _ →
    return cong

  -- The computation apply-to-metas A t tries to apply the term t to
  -- as many fresh meta-variables as possible (based on its type, A).
  -- The type of the resulting term is returned.

  apply-to-metas : Type → Term → TC (Type × Term)
  apply-to-metas A t =
    compute-args fuel [] A >>= λ args →
    apply A t args
    where
    -- Fuel, used to ensure termination.

    fuel : ℕ
    fuel = 100

    mutual

      compute-args : ℕ → List (Arg Term) → Type → TC (List (Arg Term))
      compute-args zero _ _ =
        typeError (strErr "apply-to-metas failed" ∷ [])
      compute-args (suc n) args τ =
        reduce τ               >>= λ τ →
        compute-args′ n args τ

      compute-args′ : ℕ → List (Arg Term) → Type → TC (List (Arg Term))
      compute-args′ n args (pi a@(arg i _) (abs _ τ)) =
        extendContext a $
        compute-args n (arg i unknown ∷ args) τ
      compute-args′ n args (meta x _) = blockOnMeta x
      compute-args′ n args _          = return (reverse args)

  -- The tactic refine A t goal tries to use the term t (of type A),
  -- applied to as many fresh meta-variables as possible (based on its
  -- type), to solve the given goal. If this fails, then an attempt is
  -- made to solve the goal using "sym (t metas)" instead.

  refine : Type → Term → Term → TC Term
  refine A t goal =
    apply-to-metas A t    >>= λ { (_ , t) →
    catchTC (try false t) $
    catchTC (try true  t) $
    typeError (strErr "refine failed" ∷ []) }
    where
    with-sym : Bool → Term → Term
    with-sym true  t = def (quote sym) (varg t ∷ [])
    with-sym false t = t

    try : Bool → Term → TC Term
    try use-sym t =
      unify t′ goal >>= λ _ →
      return t′
      where
      t′ = with-sym use-sym t

  -- The call by-tactic t goal tries to use (non-dependent) "cong"
  -- functions, reflexivity and t (via refine) to solve the given goal
  -- (which must be an equality).
  --
  -- The constructed term is returned.

  by-tactic : ∀ {a} {A : Set a} → A → Term → TC Term
  by-tactic {A = A} t goal =
    quoteTC A >>= λ A →
    quoteTC t >>= λ t →
    by-tactic′ fuel A t goal
    where
    -- Fuel, used to ensure termination. (Termination could perhaps be
    -- proved in some way, but using fuel was easier.)

    fuel : ℕ
    fuel = 100

    -- The tactic's main loop.

    by-tactic′ : ℕ → Type → Term → Term → TC Term
    by-tactic′ zero    _ _ _    = typeError
                                    (strErr "by: no more fuel" ∷ [])
    by-tactic′ (suc n) A t goal =
      inferType goal               >>= λ goal-type →
      reduce goal-type             >>= λ goal-type →
      block-if-meta goal-type      >>= λ _ →
      catchTC (try-refl goal-type) $
      catchTC (refine A t goal)    $
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
      block-if-meta (def (quote _≡_) (_ ∷ _ ∷ _ ∷ _ ∷ _)) = return _
      block-if-meta _                                     = ill-formed

      -- Tries to solve the goal using reflexivity.

      try-refl : Type → TC Term
      try-refl (def (quote _≡_) (a ∷ A ∷ arg _ lhs ∷ _)) = do
        unify t′ goal

        -- If unification succeeds, but the goal is not solved by
        -- refl, then this attempt is aborted. (This check was
        -- suggested by Ulf Norell.) Potential future improvement:
        -- If unification results in unsolved constraints, block until
        -- progress has been made on those constraints.
        con (quote refl) _ ← reduce goal
          where _ → failure

        return t′
        where
        t′ = con (quote refl) (a ∷ A ∷ harg lhs ∷ [])
      try-refl _ = ill-formed

      -- Tries to solve the goal using one of the "cong" functions.

      try-cong : Term → TC Term
      try-cong (def (quote _≡_) (_ ∷ _ ∷ arg _ y ∷ arg _ z ∷ [])) =
        heads y z                              >>= λ { (head , ys , zs) →
        arguments ys zs                        >>= λ args →
        make-cong (length args)                >>= λ cong →
        let t = def cong (varg head ∷ args) in
        unify t goal                           >>= λ _ →
        return t                               }
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
            return (y es , ys′ , zs′)

        -- Tries to prove that the argument lists are equal.

        arguments : List (Arg Term) → List (Arg Term) →
                    TC (List (Arg Term))
        arguments [] []                             = return []
        arguments (arg (arg-info visible _) y ∷ ys)
                  (arg (arg-info visible _) z ∷ zs) =
                   -- Relevance is ignored.

          checkType unknown
            (def (quote _≡_) (varg y ∷ varg z ∷ [])) >>= λ goal →
          by-tactic′ n A t goal                      >>= λ t →
          arguments ys zs                            >>= λ args →
          return (varg t ∷ args)

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
    by-tactic t goal >>= λ _ →
    return _

  -- If by t would have been successful, then debug-by t raises an
  -- error message that includes the term that would have been
  -- constructed by by.

  debug-by : ∀ {a} {A : Set a} → A → Term → TC ⊤
  debug-by t goal =
    by-tactic t goal                                        >>= λ t →
    typeError (strErr "Term found by by:" ∷ termErr t ∷ [])

-- A definition that provides no information. Intended to be used
-- together with the by tactic: "by definition".

definition : ⊤
definition = _

------------------------------------------------------------------------
-- The ⟨by⟩ tactic

-- The tactic ⟨by⟩ t is intended for use with goals of the form
-- C [ ⟨ e₁ ⟩ ] ≡ e₂ (with some limitations). The tactic tries to
-- generate the term cong (λ x → C [ x ]) t′, where t′ is t applied to
-- as many meta-variables as possible (based on its type), and if that
-- term fails to unify with the goal type, then the term
-- cong (λ x → C [ x ]) (sym t′) is generated instead.

-- Used to mark the subterms that should be rewritten.
--
-- The idea to mark subterms in this way is taken from Bradley Hardy,
-- who used it in the Holes library
-- (https://github.com/bch29/agda-holes).

⟨_⟩ : ∀ {a} {A : Set a} → A → A
⟨_⟩ = id

{-# NOINLINE ⟨_⟩ #-}

private

  -- A non-macro variant of ⟨by⟩ that returns the (first) constructed
  -- term.

  ⟨by⟩-tactic : ∀ {a} {A : Set a} → A → Term → TC Term
  ⟨by⟩-tactic {A = A} t goal =
    quoteTC A                               >>= λ A →
    reduce A                                >>= λ A →
    quoteTC t                               >>= λ t →
    apply-to-metas A t                      >>= λ { (A , t) →
    reduce A                                >>= λ A →
    inferType goal                          >>= λ goal-type →
    reduce goal-type                        >>= λ goal-type →
    construct-context goal-type             >>= λ f →
    construct-terms goal-type A t f         >>= λ { (t₁ , t₂) →
    catchTC (unify t₁ goal) (unify t₂ goal) >>= λ _ →
    return t₁                               }}
    where
    construct-terms : Type → Type → Term → Term → TC (Term × Term)
    construct-terms
      (def (quote _≡_) (harg b ∷ harg B ∷ _))
      (def (quote _≡_) (harg a ∷ harg A ∷ varg lhs ∷ varg rhs ∷ []))
      t f =
      return ( term (harg lhs ∷ harg rhs ∷ []) t
             , term (harg rhs ∷ harg lhs ∷ [])
                    (def (quote sym) (varg t ∷ []))
             )
      where
      term = λ args arg →
        def (quote cong)
            (harg a ∷ harg b ∷ harg A ∷ harg B ∷
             args ++ varg f ∷ varg arg ∷ [])

    construct-terms _ (meta m _) _ _ = blockOnMeta m
    construct-terms _ _          _ _ =
      typeError (strErr "⟨by⟩: ill-formed proof" ∷ [])

    mutual

      -- The natural number is the variable that should be used for
      -- the hole.

      context-term : ℕ → Term → TC Term
      context-term n = λ where
        (def f args)  → if eq-Name f (quote ⟨_⟩)
                        then return (var n [])
                        else def f ⟨$⟩ context-args n args
        (var x args)  → var (weaken-var n 1 x) ⟨$⟩ context-args n args
        (con c args)  → con c ⟨$⟩ context-args n args
        (lam v t)     → lam v ⟨$⟩ context-abs n t
        (pi a b)      → pi ⟨$⟩ context-arg n a ⊛ context-abs n b
        (meta m _)    → blockOnMeta m
        t             → return (weaken-term n 1 t)

      context-abs : ℕ → Abs Term → TC (Abs Term)
      context-abs n (abs s t) = abs s ⟨$⟩ context-term (suc n) t

      context-arg : ℕ → Arg Term → TC (Arg Term)
      context-arg n (arg i t) = arg i ⟨$⟩ context-term n t

      context-args : ℕ → List (Arg Term) → TC (List (Arg Term))
      context-args n = λ where
        []       → return []
        (a ∷ as) → _∷_ ⟨$⟩ context-arg n a ⊛ context-args n as

    construct-context : Term → TC Term
    construct-context (def (quote _≡_) (_ ∷ _ ∷ varg lhs ∷ _ ∷ [])) =
      context-term 0 lhs >>= λ body →
      return (lam visible (abs "x" body))

    construct-context (meta m _) = blockOnMeta m
    construct-context _          =
      typeError (strErr "⟨by⟩: ill-formed goal" ∷ [])

macro

  -- The ⟨by⟩ tactic.

  ⟨by⟩ : ∀ {a} {A : Set a} → A → Term → TC ⊤
  ⟨by⟩ t goal =
    ⟨by⟩-tactic t goal >>= λ _ →
    return _

  -- If ⟨by⟩ t would have been successful, then debug-⟨by⟩ t raises an
  -- error message that includes the (first) term that would have been
  -- constructed by ⟨by⟩.

  debug-⟨by⟩ : ∀ {a} {A : Set a} → A → Term → TC ⊤
  debug-⟨by⟩ t goal =
    ⟨by⟩-tactic t goal                                        >>= λ t →
    typeError (strErr "Term found by ⟨by⟩:" ∷ termErr t ∷ [])

------------------------------------------------------------------------
-- Some unit tests

private

  module Tests
    (assumption : 48 ≡ 42)
    (lemma      : ∀ n → n + 8 ≡ n + 2)
    (f          : ℕ → ℕ → ℕ → ℕ)
    where

    g : ℕ → ℕ → ℕ → ℕ
    g zero    _ _ = 12
    g (suc _) _ _ = 12

    fst : ∀ {a b} {A : Set a} {B : A → Set b} →
          Σ A B → A
    fst = proj₁

    {-# NOINLINE fst #-}

    -- Tests for by.

    module By where

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

      test₈ : ∀ n → g n (g n 45 48) 42 ≡ g n (g n 45 42) 48
      test₈ n = by assumption

      test₉ : (f : ℕ → ℕ) → f 42 ≡ f 48
      test₉ f = by (lemma 40)

      test₁₀ : (f : ℕ → ℕ) → f 42 ≡ f 48
      test₁₀ f = by (λ (_ : ⊤) → assumption)

      test₁₁ : (f : ℕ × ℕ → ℕ × ℕ) → (∀ x → ⟨ _≡_ ⟩ (f x) x) →
               fst (f (12 , 73)) ≡ fst {B = λ _ → ℕ} (12 , 73)
      test₁₁ _ hyp = by hyp

      -- Two test cases for the extra check in try-refl.

      test₁₂ : (h : ℕ → Maybe ℕ) →
               ((n : ℕ) → h n ≡ just n) →
               (n : ℕ) → suc ⟨$⟩ h n ≡ suc ⟨$⟩ return n
      test₁₂ h hyp n =
        suc ⟨$⟩ h n       ≡⟨ by (hyp n) ⟩∎
        suc ⟨$⟩ return n  ∎

      test₁₃ : (h : List ⊤ → Maybe (List ⊤)) →
               ((xs : List ⊤) → h xs ≡ just xs) →
               (x : ⊤) (xs : List ⊤) → _
      test₁₃ h hyp x xs =
        _∷_ ⟨$⟩ return x ⊛ h xs       ≡⟨ by (hyp xs) ⟩∎
        _∷_ ⟨$⟩ return x ⊛ return xs  ∎

    -- Tests for ⟨by⟩.

    module ⟨By⟩ where

      test₁ : ⟨ 40 + 2 ⟩ ≡ 42
      test₁ = ⟨by⟩ refl

      test₂ : 48 ≡ 42 → ⟨ 42 ⟩ ≡ 48
      test₂ eq = ⟨by⟩ eq

      test₃ : (f : ℕ → ℕ) → f ⟨ 42 ⟩ ≡ f 48
      test₃ f = ⟨by⟩ assumption

      test₄ : (f : ℕ → ℕ) → f ⟨ 48 ⟩ ≡ f 42
      test₄ f = ⟨by⟩ assumption

      test₅ : (f : ℕ → ℕ → ℕ) → f ⟨ 42 ⟩ ⟨ 42 ⟩ ≡ f 48 48
      test₅ f = ⟨by⟩ assumption

      test₆ : (f : ℕ → ℕ → ℕ → ℕ) → f ⟨ 48 ⟩ 45 ⟨ 48 ⟩ ≡ f 42 45 42
      test₆ f = ⟨by⟩ assumption

      test₇ : f ⟨ 48 ⟩ (f ⟨ 48 ⟩ 45 ⟨ 48 ⟩) ⟨ 48 ⟩ ≡ f 42 (f 42 45 42) 42
      test₇ = ⟨by⟩ assumption

      test₈ : ∀ n → g n (g n 45 ⟨ 48 ⟩) ⟨ 48 ⟩ ≡ g n (g n 45 42) 42
      test₈ n = ⟨by⟩ assumption

      test₉ : (f : ℕ → ℕ) → f ⟨ 42 ⟩ ≡ f 48
      test₉ f = ⟨by⟩ (lemma 40)

      test₁₀ : (f : ℕ → ℕ) → f ⟨ 42 ⟩ ≡ f 48
      test₁₀ f = ⟨by⟩ (λ (_ : ⊤) → assumption)

      test₁₁ : (f : ℕ × ℕ → ℕ × ℕ) → (∀ x → ⟨ _≡_ ⟩ (f x) x) →
               fst ⟨ f (12 , 73) ⟩ ≡ fst {B = λ _ → ℕ} (12 , 73)
      test₁₁ _ hyp = ⟨by⟩ hyp

      test₁₂ : (h : ℕ → Maybe ℕ) →
               ((n : ℕ) → h n ≡ just n) →
               (n : ℕ) → suc ⟨$⟩ h n ≡ suc ⟨$⟩ return n
      test₁₂ h hyp n =
        suc ⟨$⟩ ⟨ h n ⟩   ≡⟨ ⟨by⟩ (hyp n) ⟩∎
        suc ⟨$⟩ return n  ∎

      test₁₃ : (h : List ⊤ → Maybe (List ⊤)) →
               ((xs : List ⊤) → h xs ≡ just xs) →
               (x : ⊤) (xs : List ⊤) → _
      test₁₃ h hyp x xs =
        _∷_ ⟨$⟩ return x ⊛ ⟨ h xs ⟩   ≡⟨ ⟨by⟩ (hyp xs) ⟩∎
        _∷_ ⟨$⟩ return x ⊛ return xs  ∎

      test₁₄ : (h : List ℕ → Maybe (List ℕ)) →
               ((xs : List ℕ) → h xs ≡ just xs) →
               (x : ℕ) (xs : List ℕ) → _
      test₁₄ h hyp x xs =
        _∷_ ⟨$⟩ ⟨ h xs ⟩   ≡⟨ ⟨by⟩ (hyp xs) ⟩∎
        _∷_ ⟨$⟩ return xs  ∎

      test₁₅ : 48 ≡ 42 →
               _≡_ {A = ℕ → ℕ} (λ x → x + ⟨ 42 ⟩) (λ x → x + 48)
      test₁₅ hyp = ⟨by⟩ hyp
