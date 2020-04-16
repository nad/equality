------------------------------------------------------------------------
-- Code used to construct tactics aimed at making equational reasoning
-- proofs more readable
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Tactic.By {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

import Agda.Builtin.Bool as B
open import Agda.Builtin.Nat using (_==_)
open import Agda.Builtin.String

open import Prelude

open import List eq
open import Monad eq
open import Monad.State eq hiding (set)
open import TC-monad eq

-- Constructs the type of a "cong" function for functions with the
-- given number of arguments. The first argument must be a function
-- that constructs the type of equalities between its two arguments.

type-of-cong : (Term → Term → Type) → ℕ → Type
type-of-cong equality n = levels (suc n)
  where
  -- The examples below are given for n = 3.

  -- Generates x₁ x₂ x₃ or y₁ y₂ y₃.
  arguments : ℕ → ℕ → List (Arg Term)
  arguments delta (suc m) = varg (var (delta + 2 * m + 1 + n) []) ∷
                            arguments delta m
  arguments delta zero    = []

  -- Generates x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → f x₁ x₂ x₃ ≡ f y₁ y₂ y₃.
  equalities : ℕ → Type
  equalities (suc m) =
    pi (varg (equality (var (1 + 2 * m + 1 + (n ∸ suc m)) [])
                       (var (0 + 2 * m + 1 + (n ∸ suc m)) []))) $
       abs "x≡y" $
       equalities m
  equalities zero =
    equality (var n (arguments 1 n))
             (var n (arguments 0 n))

  -- Generates A → B → C → D.
  function-type : ℕ → Type
  function-type (suc m) = pi (varg (var (3 * n) []))
                             (abs "_" (function-type m))
  function-type zero    = var (3 * n) []

  -- Generates ∀ {x₁ y₁ x₂ y₂ x₃ y₃} → …
  variables : ℕ → Type
  variables (suc m) =
    pi (harg unknown) $ abs "x"   $
    pi (harg unknown) $ abs "y"   $
       variables m
  variables zero    =
    pi (varg (function-type n)) $ abs "f" $
       equalities n

  -- Generates
  -- {A : Set a} {B : Set b} {C : Set c} {D : Set d} → ….
  types : ℕ → Type
  types (suc m) = pi (harg (agda-sort (set (var n [])))) $ abs "A" $
                     types m
  types zero    = variables n

  -- Generates {a b c d : Level} → ….
  levels : ℕ → Type
  levels (suc n) = pi (harg (def (quote Level) [])) $ abs "a" $
                      levels n
  levels zero    = types (suc n)

-- Used to mark the subterms that should be rewritten by the ⟨by⟩
-- tactic.
--
-- The idea to mark subterms in this way is taken from Bradley
-- Hardy, who used it in the Holes library
-- (https://github.com/bch29/agda-holes).

⟨_⟩ : ∀ {a} {A : Set a} → A → A
⟨_⟩ = id

{-# NOINLINE ⟨_⟩ #-}

module _
  (deconstruct-equality :
     Type → TC (Maybe (Term × Type × Term × Term)))
  -- Tries to deconstruct a type which is expected to be an equality,
  -- _≡_ {a = a} {A = A} x y, but in reduced form. Upon success the
  -- level a, the type A, the left-hand side x, and the right-hand
  -- side y are returned. If it is hard to determine a or A, then
  -- unknown can be returned instead. If the type does not have the
  -- right form, then nothing is returned.
  (sym : Term → Term)
  -- An implementation of symmetry.
  where

  private

    -- A variant of blockOnMeta which can print a debug message.

    blockOnMeta′ : {A : Set} → String → Meta → TC A
    blockOnMeta′ s m = do
      debugPrint "by" 20
        (strErr "by/⟨by⟩ is blocking on meta" ∷
         strErr (primShowMeta m) ∷ strErr "in" ∷ strErr s ∷ [])
      blockOnMeta m

    -- A variant of deconstruct-equality with the following
    -- differences:
    -- * If the type is a meta-variable, then the computation blocks.
    -- * If the type does not have the right form (and is not a
    --   meta-variable), then a type error is raised, and the given
    --   list is used as the error message.

    deconstruct-equality′ :
      List ErrorPart → Type → TC (Term × Type × Term × Term)
    deconstruct-equality′ err (meta m _) =
      blockOnMeta′ "deconstruct-equality′" m
    deconstruct-equality′ err t = do
      just r ← deconstruct-equality t
        where nothing → typeError err
      return r

    -- The computation apply-to-metas A t tries to apply the term t to
    -- as many fresh meta-variables as possible (based on its type,
    -- A). The type of the resulting term is returned.

    apply-to-metas : Type → Term → TC (Type × Term)
    apply-to-metas A t = apply A t =<< compute-args fuel [] A
      where
      -- Fuel, used to ensure termination.

      fuel : ℕ
      fuel = 100

      mutual

        compute-args :
          ℕ → List (Arg Term) → Type → TC (List (Arg Term))
        compute-args zero _ _ =
          typeError (strErr "apply-to-metas failed" ∷ [])
        compute-args (suc n) args τ =
          compute-args′ n args =<< reduce τ

        compute-args′ :
          ℕ → List (Arg Term) → Type → TC (List (Arg Term))
        compute-args′ n args (pi a@(arg i _) (abs _ τ)) =
          extendContext a $
          compute-args n (arg i unknown ∷ args) τ
        compute-args′ n args (meta x _) =
          blockOnMeta′ "apply-to-metas" x
        compute-args′ n args _ = return (reverse args)

  -- The ⟨by⟩ tactic.
  --
  -- The tactic ⟨by⟩ t is intended for use with goals of the form
  -- C [ ⟨ e₁ ⟩ ] ≡ e₂ (with some limitations). The tactic tries to
  -- generate the term cong (λ x → C [ x ]) t′, where t′ is t applied
  -- to as many meta-variables as possible (based on its type), and if
  -- that term fails to unify with the goal type, then the term
  -- cong (λ x → C [ x ]) (sym t′) is generated instead.

  module ⟨By⟩
    (cong : Term → Term → Term → Term → Term)
    -- An implementation of cong. Arguments: left-hand side,
    -- right-hand side, function, equality.
    (cong-with-lhs-and-rhs : Bool)
    -- Should the cong function be applied to the "left-hand side" and
    -- the "right-hand side" (the two sides of the inferred type of
    -- the constructed equality proof), or should those arguments be
    -- left for Agda's unification machinery?
    where

    private

      -- A non-macro variant of ⟨by⟩ that returns the (first)
      -- constructed term.

      ⟨by⟩-tactic : ∀ {a} {A : Set a} → A → Term → TC Term
      ⟨by⟩-tactic {A = A} t goal = do
        -- To avoid wasted work the first block below, which can block
        -- the tactic, is run before the second one.

        goal-type       ← reduce =<< inferType goal
        _ , _ , lhs , _ ← deconstruct-equality′ err₁ goal-type
        f               ← construct-context lhs

        A     ← quoteTC A
        t     ← quoteTC t
        A , t ← apply-to-metas A t

        if not cong-with-lhs-and-rhs
          then conclude unknown unknown f t
          else do
            A                 ← reduce A
            _ , _ , lhs , rhs ← deconstruct-equality′ err₂ A
            conclude lhs rhs f t
        where
        err₁ = strErr "⟨by⟩: ill-formed goal"  ∷ []
        err₂ = strErr "⟨by⟩: ill-formed proof" ∷ []

        try : Term → TC ⊤
        try t = do
          debugPrint "by" 10 $
            strErr "Term tried by ⟨by⟩:" ∷ termErr t ∷ []
          unify t goal

        conclude : Term → Term → Term → Term → TC Term
        conclude lhs rhs f t = do
          let t₁ = cong lhs rhs f t
              t₂ = cong rhs lhs f (sym t)
          catchTC (try t₁) (try t₂)
          return t₁

        mutual

          -- The natural number argument is the variable that should
          -- be used for the hole. The natural number in the state is
          -- the number of occurrences of the marker that have been
          -- found.

          -- The code traverses arguments from right to left: in some
          -- cases it is better to block on the last meta-variable
          -- than the first one (because the first one might get
          -- instantiated before the last one, so when the last one is
          -- instantiated all the others have hopefully already been
          -- instantiated).

          context-term : ℕ → Term → StateT ℕ TC Term
          context-term n = λ where
            (def f args)  → if eq-Name f (quote ⟨_⟩)
                            then modify suc >> return (var n [])
                            else def f ⟨$⟩ context-args n args
            (var x args)  → var (weaken-var n 1 x) ⟨$⟩
                            context-args n args
            (con c args)  → con c ⟨$⟩ context-args n args
            (lam v t)     → lam v ⟨$⟩ context-abs n t
            (pi a b)      → flip pi ⟨$⟩ context-abs n b ⊛ context-arg n a
            (meta m _)    → liftʳ $ blockOnMeta′ "construct-context" m
            t             → return (weaken-term n 1 t)

          context-abs : ℕ → Abs Term → StateT ℕ TC (Abs Term)
          context-abs n (abs s t) = abs s ⟨$⟩ context-term (suc n) t

          context-arg : ℕ → Arg Term → StateT ℕ TC (Arg Term)
          context-arg n (arg i t) = arg i ⟨$⟩ context-term n t

          context-args :
            ℕ → List (Arg Term) → StateT ℕ TC (List (Arg Term))
          context-args n = λ where
            []       → return []
            (a ∷ as) → flip _∷_ ⟨$⟩ context-args n as ⊛ context-arg n a

        construct-context : Term → TC Term
        construct-context lhs = do
          debugPrint "by" 20
            (strErr "⟨by⟩ was given the left-hand side" ∷
             termErr lhs ∷ [])
          body , n ← run (context-term 0 lhs) 0
          case n of λ where
            (suc _) → return (lam visible (abs "x" body))
            zero    → typeError $
              strErr "⟨by⟩: no occurrence of ⟨_⟩ found" ∷ []

    macro

      -- The ⟨by⟩ tactic.

      ⟨by⟩ : ∀ {a} {A : Set a} → A → Term → TC ⊤
      ⟨by⟩ t goal = do
        ⟨by⟩-tactic t goal
        return _

      -- Unit tests can be found in Tactic.By.Parametrised.Tests,
      -- Tactic.By.Propositional, Tactic.By.Path and Tactic.By.Id.

      -- If ⟨by⟩ t would have been successful, then debug-⟨by⟩ t
      -- raises an error message that includes the (first) term that
      -- would have been constructed by ⟨by⟩.

      debug-⟨by⟩ : ∀ {a} {A : Set a} → A → Term → TC ⊤
      debug-⟨by⟩ t goal = do
        t ← ⟨by⟩-tactic t goal
        typeError (strErr "Term found by ⟨by⟩:" ∷ termErr t ∷ [])

  -- The by tactic.

  module By
    (equality : Term → Term → Type)
    -- Constructs the type of equalities between its two arguments.
    (refl : Term → Term → Term → Term)
    -- An implementation of reflexivity. Should take a level a, a type
    -- A : Set a, and a value x : A, and return a proof of x ≡ x.
    (make-cong : ℕ → TC Name)
    -- The computation make-cong n should generate a "cong" function
    -- for functions with n arguments. The type of this function
    -- should match that generated by type-of-cong equality n. (The
    -- functions are used fully applied, and implicit arguments are
    -- not given explicitly, so hopefully the ordering of implicit
    -- arguments with respect to each other and the explicit arguments
    -- does not matter.)
    (extra-check-in-try-refl : Bool)
    -- When the by tactic tries to solve a subgoal using reflexivity,
    -- should it make sure that, afterwards, the goal meta-variable
    -- reduces to something that is not a meta-variable?
    where

    private

      -- The call by-tactic t goal tries to use (non-dependent) "cong"
      -- functions, reflexivity and t (via refine) to solve the given
      -- goal (which must be an equality).
      --
      -- The constructed term is returned.

      by-tactic : ∀ {a} {A : Set a} → A → Term → TC Term
      by-tactic {A = A} t goal = do
        A ← quoteTC A
        t ← quoteTC t
        _ , t ← apply-to-metas A t
        by-tactic′ fuel t goal
        where
        -- Fuel, used to ensure termination. (Termination could
        -- perhaps be proved in some way, but using fuel was easier.)

        fuel : ℕ
        fuel = 100

        -- The tactic's main loop.

        by-tactic′ : ℕ → Term → Term → TC Term
        by-tactic′ zero    _ _    = typeError
                                      (strErr "by: no more fuel" ∷ [])
        by-tactic′ (suc n) t goal = do
          goal-type ← reduce =<< inferType goal
          block-if-meta goal-type
          catchTC (try-refl goal-type) $
            catchTC (try t) $
              catchTC (try (sym t)) $
                try-cong goal-type
          where
          -- Error messages.

          ill-formed : List ErrorPart
          ill-formed = strErr "by: ill-formed goal" ∷ []

          failure : {A : Set} → TC A
          failure = typeError (strErr "by failed" ∷ [])

          -- Blocks if the goal type is not sufficiently concrete.
          -- Raises a type error if the goal type is not an equality.

          block-if-meta : Type → TC ⊤
          block-if-meta type = do
            eq ← deconstruct-equality′ ill-formed type
            case eq of λ where
              (_ , _ , meta m _ , _) → blockOnMeta′
                                         "block-if-meta (left)"  m
              (_ , _ , _ , meta m _) → blockOnMeta′
                                         "block-if-meta (right)" m
              _                      → return _

          -- Tries to solve the goal using reflexivity.

          try-refl : Type → TC Term
          try-refl type = do
            a , A , lhs , _ ← deconstruct-equality′ ill-formed type

            let t′ = refl a A lhs
            unify t′ goal

            if not extra-check-in-try-refl
              then return t′
              else do
              -- If unification succeeds, but the goal is solved by a
              -- meta-variable, then this attempt is aborted. (A check
              -- similar to this one was suggested by Ulf Norell.)
              -- Potential future improvement: If unification results
              -- in unsolved constraints, block until progress has
              -- been made on those constraints.
              goal ← reduce goal
              case goal of λ where
                (meta _ _) → failure
                _          → return t′

          -- Tries to solve the goal using the given term.

          try : Term → TC Term
          try t = do
            unify t goal
            return t

          -- Tries to solve the goal using one of the "cong"
          -- functions.

          try-cong : Type → TC Term
          try-cong type = do
            _ , _ , y , z  ← deconstruct-equality′ ill-formed type
            head , ys , zs ← heads y z
            args           ← arguments ys zs
            cong           ← make-cong (length args)
            let t = def cong (varg head ∷ args)
            unify t goal
            return t
            where
            -- Checks if the heads are equal. If they are, then the
            -- function figures out how many arguments are equal, and
            -- returns the (unique) head applied to these arguments,
            -- plus two lists containing the remaining arguments.

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
                      (arg (arg-info visible _) z ∷ zs) = do
                       -- Relevance is ignored.

              goal ← checkType unknown (equality y z)
              t    ← by-tactic′ n t goal
              args ← arguments ys zs
              return (varg t ∷ args)

            -- Hidden and instance arguments are ignored.

            arguments (arg (arg-info hidden _) _ ∷ ys) zs    = arguments ys zs
            arguments (arg (arg-info instance′ _) _ ∷ ys) zs = arguments ys zs
            arguments ys (arg (arg-info hidden _) _ ∷ zs)    = arguments ys zs
            arguments ys (arg (arg-info instance′ _) _ ∷ zs) = arguments ys zs

            arguments _ _ = failure

    macro

      -- The call by t tries to use t (along with congruence,
      -- reflexivity and symmetry) to solve the goal, which must be an
      -- equality.

      by : ∀ {a} {A : Set a} → A → Term → TC ⊤
      by t goal = do
        by-tactic t goal
        return _

      -- Unit tests can be found in Tactic.By.Propositional,
      -- Tactic.By.Path and Tactic.By.Id.

      -- If by t would have been successful, then debug-by t raises an
      -- error message that includes the term that would have been
      -- constructed by by.

      debug-by : ∀ {a} {A : Set a} → A → Term → TC ⊤
      debug-by t goal = do
        t ← by-tactic t goal
        typeError (strErr "Term found by by:" ∷ termErr t ∷ [])

    -- A definition that provides no information. Intended to be used
    -- together with the by tactic: "by definition".

    definition : ⊤
    definition = _

-- A module that exports both tactics.

module Tactics
  (deconstruct-equality : Type → TC (Maybe (Term × Type × Term × Term)))
  (equality : Term → Term → Type)
  (refl : Term → Term → Term → Term)
  (sym : Term → Term)
  (cong : Term → Term → Term → Term → Term)
  (cong-with-lhs-and-rhs : Bool)
  (make-cong : ℕ → TC Name)
  (extra-check-in-try-refl : Bool)
  where

  open ⟨By⟩ deconstruct-equality sym cong cong-with-lhs-and-rhs public
  open By deconstruct-equality sym equality refl make-cong
          extra-check-in-try-refl public
