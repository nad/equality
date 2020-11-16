------------------------------------------------------------------------
-- Abstract binding trees, based on Harper's "Practical Foundations
-- for Programming Languages"
------------------------------------------------------------------------

-- Operators are not indexed by symbolic parameters.

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Abstract-binding-tree
  {e⁺}
  (equality-with-paths : ∀ {a p} → P.Equality-with-paths a p e⁺)
  where

open P.Derived-definitions-and-properties equality-with-paths

open import Dec
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (swap) renaming ([_,_] to [_,_]′)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms equality-with-paths
open import Equivalence equality-with-J as Eq using (_≃_)
open import Erased.Cubical equality-with-paths as E
open import Finite-subset.Listed equality-with-paths
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc
open import List equality-with-J using (H-level-List)

private
  variable
    @0 p₁ p₂ p₃ : Level

------------------------------------------------------------------------
-- Signatures

private
 module Dummy where

  -- Signatures for abstract binding trees.

  record Signature ℓ : Type (lsuc ℓ) where
    infix 4 _≟S_ _≟O_ _≟V_

    field
      -- A set of sorts with decidable erased equality.
      Sort : Type ℓ
      _≟S_ : Decidable-erased-equality Sort

    -- Valences.

    Valence : Type ℓ
    Valence = List Sort × Sort

    field
      -- Codomain-indexed operators with decidable erased equality and
      -- domains.
      Op     : @0 Sort → Type ℓ
      _≟O_   : ∀ {@0 s} → Decidable-erased-equality (Op s)
      domain : ∀ {@0 s} → Op s → List Valence

      -- A sort-indexed type of variables with decidable erased
      -- equality.
      Var  : @0 Sort → Type ℓ
      _≟V_ : ∀ {@0 s} → Decidable-erased-equality (Var s)

    -- Non-indexed variables.

    ∃Var : Type ℓ
    ∃Var = ∃ λ (s : Sort) → Var s

    -- Finite subsets of variables.
    --
    -- This type is used by the substitution functions, so it might
    -- make sense to make it possible to switch to a more efficient
    -- data structure. (For instance, if variables are natural
    -- numbers, then it should suffice to store an upper bound of the
    -- variables in the term.)

    Vars : Type ℓ
    Vars = Finite-subset-of ∃Var

    field
      -- One can always find a fresh variable.
      fresh : ∀ {s} (xs : Vars) →
              ∃ λ (x : Var s) → Erased (¬ (_ , x) ∈ xs)

    -- Arities.

    Arity : Type ℓ
    Arity = List Valence × Sort

    -- An operator's arity.

    arity : ∀ {s} → Op s → Arity
    arity {s = s} o = domain o , s

open Dummy public using (Signature) hiding (module Signature)

-- Definitions depending on a signature. Defined in a separate module
-- to avoid problems with record modules.

module Signature {ℓ} (sig : Signature ℓ) where

  open Dummy.Signature sig public

  private
    variable
      @0 s s′ s₁ s₂ s₃ : Sort
      @0 ss            : List Sort
      @0 v             : Valence
      @0 vs            : List Valence
      @0 o             : Op s
      @0 x y z         : Var s
      @0 A             : Type ℓ
      @0 wf            : A

  ----------------------------------------------------------------------
  -- Variants of some functions from the signature

  -- A variant of fresh that does not return an erased proof.

  fresh-not-erased :
    ∀ {s} (xs : Vars) → ∃ λ (x : Var s) → ¬ (_ , x) ∈ xs
  fresh-not-erased =
    Σ-map id (Stable-¬ _) ∘ fresh

  -- Erased equality is decidable for ∃Var.

  infix 4 _≟∃V_

  _≟∃V_ : Decidable-erased-equality ∃Var
  _≟∃V_ =
    decidable-erased⇒decidable-erased⇒Σ-decidable-erased _≟S_ _≟V_

  ----------------------------------------------------------------------
  -- Some types are sets

  -- Sort is a set (in erased contexts).

  @0 Sort-set : Is-set Sort
  Sort-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟S_

  -- Valence is a set (in erased contexts).

  @0 Valence-set : Is-set Valence
  Valence-set = ×-closure 2
    (H-level-List 0 Sort-set)
    Sort-set

  -- Arity is a set (in erased contexts).

  @0 Arity-set : Is-set Arity
  Arity-set = ×-closure 2
    (H-level-List 0 Valence-set)
    Sort-set

  -- Var s is a set (in erased contexts).

  @0 Var-set : Is-set (Var s)
  Var-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟V_

  -- ∃Var is a set (in erased contexts).

  @0 ∃Var-set : Is-set ∃Var
  ∃Var-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟∃V_

  ----------------------------------------------------------------------
  -- Term skeletons

  -- Term skeletons are terms without variables.

  mutual

    -- Terms.

    data Tmˢ : @0 Sort → Type ℓ where
      var : ∀ {s} → Tmˢ s
      op  : (o : Op s) → Argsˢ (domain o) → Tmˢ s

    -- Sequences of arguments.

    data Argsˢ : @0 List Valence → Type ℓ where
      nil  : Argsˢ []
      cons : Argˢ v → Argsˢ vs → Argsˢ (v ∷ vs)

    -- Arguments.

    data Argˢ : @0 Valence → Type ℓ where
      nil  : Tmˢ s → Argˢ ([] , s)
      cons : ∀ {s} → Argˢ (ss , s′) → Argˢ (s ∷ ss , s′)

  private
    variable
      @0 tˢ  : Tmˢ s
      @0 asˢ : Argsˢ vs
      @0 aˢ  : Argˢ v

  ----------------------------------------------------------------------
  -- Raw terms

  -- Raw (possibly ill-scoped) terms.

  mutual

    Tm : Tmˢ s → Type ℓ
    Tm {s = s} var       = Var s
    Tm         (op o as) = Args as

    Args : Argsˢ vs → Type ℓ
    Args nil         = ↑ _ ⊤
    Args (cons a as) = Arg a × Args as

    Arg : Argˢ v → Type ℓ
    Arg (nil t)          = Tm t
    Arg (cons {s = s} a) = Var s × Arg a

  ----------------------------------------------------------------------
  -- Renaming

  -- A cast lemma.

  cast-Var : @0 s ≡ s′ → Var s → Var s′
  cast-Var = substᴱ Var

  -- Renaming.

  module _ {s} (x y : Var s) where

    rename-Var : ∀ {s′} → Var s′ → Var s′
    rename-Var z = case (_ , x) ≟∃V (_ , z) of λ where
      (no _)        → z
      (yes [ x≡z ]) → cast-Var (cong proj₁ x≡z) y

    mutual

      -- The term rename-Tm tˢ t is t with each (free or bound)
      -- occurrence of x replaced by y.

      rename-Tm : (tˢ : Tmˢ s′) → Tm tˢ → Tm tˢ
      rename-Tm var        z  = rename-Var z
      rename-Tm (op o asˢ) as = rename-Args asˢ as

      rename-Args : (asˢ : Argsˢ vs) → Args asˢ → Args asˢ
      rename-Args nil           _        = _
      rename-Args (cons aˢ asˢ) (a , as) =
        rename-Arg aˢ a , rename-Args asˢ as

      rename-Arg : (aˢ : Argˢ v) → Arg aˢ → Arg aˢ
      rename-Arg (nil tˢ)  t       = rename-Tm tˢ t
      rename-Arg (cons aˢ) (x , a) =
        rename-Var x , rename-Arg aˢ a

  ----------------------------------------------------------------------
  -- Well-formed terms

  private
    variable
      @0 xs ys : Vars

  -- Predicates for well-formed variables, terms and arguments.

  Wf-var : ∀ {s} → Vars → Var s → Type ℓ
  Wf-var xs x = (_ , x) ∈ xs

  mutual

    Wf-tm : ∀ {s} → Vars → (tˢ : Tmˢ s) → Tm tˢ → Type ℓ
    Wf-tm xs var        = Wf-var xs
    Wf-tm xs (op o asˢ) = Wf-args xs asˢ

    Wf-args : ∀ {vs} → Vars → (asˢ : Argsˢ vs) → Args asˢ → Type ℓ
    Wf-args _  nil           _        = ↑ _ ⊤
    Wf-args xs (cons aˢ asˢ) (a , as) =
      Wf-arg xs aˢ a × Wf-args xs asˢ as

    Wf-arg : ∀ {v} → Vars → (aˢ : Argˢ v) → Arg aˢ → Type ℓ
    Wf-arg xs (nil tˢ)  t       = Wf-tm xs tˢ t
    Wf-arg xs (cons aˢ) (x , a) =
      ∀ y → ¬ (_ , y) ∈ xs →
      Wf-arg ((_ , y) ∷ xs) aˢ (rename-Arg x y aˢ a)

  -- Well-formed variables.

  Variable : @0 Vars → @0 Sort → Type ℓ
  Variable xs s = ∃ λ (x : Var s) → Erased (Wf-var xs x)

  -- Well-formed terms.

  Term : @0 Vars → @0 Sort → Type ℓ
  Term xs s =
    ∃ λ (tˢ : Tmˢ s) → ∃ λ (t : Tm tˢ) → Erased (Wf-tm xs tˢ t)

  pattern var-wf x wf        = var , x , [ wf ]
  pattern op-wf o asˢ as wfs = op o asˢ , as , [ wfs ]

  -- Well-formed sequences of arguments.

  Arguments : @0 Vars → @0 List Valence → Type ℓ
  Arguments xs vs =
    ∃ λ (asˢ : Argsˢ vs) → ∃ λ (as : Args asˢ) →
    Erased (Wf-args xs asˢ as)

  pattern nil-wfs                     = nil , lift tt , [ lift tt ]
  pattern cons-wfs aˢ asˢ a as wf wfs =
    cons aˢ asˢ , (a , as) , [ wf , wfs ]

  -- Well-formed arguments.

  Argument : @0 Vars → @0 Valence → Type ℓ
  Argument xs v =
    ∃ λ (aˢ : Argˢ v) → ∃ λ (a : Arg aˢ) → Erased (Wf-arg xs aˢ a)

  pattern nil-wf tˢ t wf    = nil tˢ , t , [ wf ]
  pattern cons-wf aˢ x a wf = cons aˢ , (x , a) , [ wf ]

  ----------------------------------------------------------------------
  -- Some rearrangement lemmas

  -- A rearrangement lemma for Tmˢ.

  Tmˢ≃ :
    Tmˢ s ≃
    ((∃ λ s′ → Erased (s′ ≡ s)) ⊎
     (∃ λ (o : Op s) → Argsˢ (domain o)))
  Tmˢ≃ = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = λ where
          (inj₂ _)             → refl _
          (inj₁ (s′ , [ eq ])) → elim¹ᴱ
            (λ eq → to (substᴱ Tmˢ eq var) ≡
                    inj₁ (s′ , [ eq ]))
            (to (substᴱ Tmˢ (refl _) var)  ≡⟨ cong to substᴱ-refl ⟩
             to var                        ≡⟨⟩
             inj₁ (s′ , [ refl _ ])        ∎)
            eq
      }
    ; left-inverse-of = λ where
        (op _ _) → refl _
        var      → substᴱ-refl
    })
    where
    RHS : @0 Sort → Type ℓ
    RHS s =
      (∃ λ s′ → Erased (s′ ≡ s)) ⊎
      (∃ λ (o : Op s) → Argsˢ (domain o))

    to : Tmˢ s → RHS s
    to var       = inj₁ (_ , [ refl _ ])
    to (op o as) = inj₂ (o , as)

    from : RHS s → Tmˢ s
    from (inj₁ (s′ , [ eq ])) = substᴱ Tmˢ eq var
    from (inj₂ (o , as))      = op o as

  -- A rearrangement lemma for Argsˢ.

  Argsˢ≃ :
    Argsˢ vs ≃
    (Erased ([] ≡ vs) ⊎
     (∃ λ ((([ v ] , _) , [ vs′ ] , _) :
           (∃ λ v → Argˢ (erased v)) ×
           (∃ λ vs′ → Argsˢ (erased vs′))) →
        Erased (v ∷ vs′ ≡ vs)))
  Argsˢ≃ = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of = from∘to
    })
    where
    RHS : @0 List Valence → Type ℓ
    RHS vs =
      (Erased ([] ≡ vs) ⊎
      (∃ λ ((([ v ] , _) , [ vs′ ] , _) :
            (∃ λ v → Argˢ (erased v)) ×
            (∃ λ vs′ → Argsˢ (erased vs′))) →
         Erased (v ∷ vs′ ≡ vs)))

    to : Argsˢ vs → RHS vs
    to nil         = inj₁ [ refl _ ]
    to (cons a as) = inj₂ (((_ , a) , _ , as) , [ refl _ ])

    from : RHS vs → Argsˢ vs
    from (inj₁ [ eq ]) =
      substᴱ Argsˢ eq nil
    from (inj₂ (((_ , a) , _ , as) , [ eq ])) =
      substᴱ Argsˢ eq (cons a as)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ [ eq ]) = elim¹ᴱ
      (λ eq → to (substᴱ Argsˢ eq nil) ≡ inj₁ [ eq ])
      (to (substᴱ Argsˢ (refl _) nil)  ≡⟨ cong to substᴱ-refl ⟩
       to nil                          ≡⟨⟩
       inj₁ [ refl _ ]                 ∎)
      eq
    to∘from (inj₂ (((_ , a) , _ , as) , [ eq ])) = elim¹ᴱ
      (λ eq → to (substᴱ Argsˢ eq (cons a as)) ≡
              inj₂ (((_ , a) , _ , as) , [ eq ]))
      (to (substᴱ Argsˢ (refl _) (cons a as))  ≡⟨ cong to substᴱ-refl ⟩
       to (cons a as)                          ≡⟨⟩
       inj₂ (((_ , a) , _ , as) , [ refl _ ])  ∎)
      eq

    from∘to : ∀ x → from (to x) ≡ x
    from∘to nil        = substᴱ-refl
    from∘to (cons _ _) = substᴱ-refl

  -- A rearrangement lemma for Argˢ.

  Argˢ≃ :
    Argˢ v ≃
    ((∃ λ (([ s ] , _) : ∃ λ s → Tmˢ (erased s)) →
        Erased (([] , s) ≡ v)) ⊎
     (∃ λ ((s , [ ss , s′ ] , _) : Sort × ∃ λ v → Argˢ (erased v)) →
      Erased ((s ∷ ss , s′) ≡ v)))
  Argˢ≃ = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = to
        ; from = from
        }
      ; right-inverse-of = to∘from
      }
    ; left-inverse-of = from∘to
    })
    where
    RHS : @0 Valence → Type ℓ
    RHS v =
      (∃ λ (([ s ] , _) : ∃ λ s → Tmˢ (erased s)) →
         Erased (([] , s) ≡ v)) ⊎
      (∃ λ ((s , [ ss , s′ ] , _) : Sort × ∃ λ v → Argˢ (erased v)) →
       Erased ((s ∷ ss , s′) ≡ v))

    to : Argˢ v → RHS v
    to (nil t)  = inj₁ ((_ , t) , [ refl _ ])
    to (cons a) = inj₂ ((_ , _ , a) , [ refl _ ])

    from : RHS v → Argˢ v
    from (inj₁ ((_ , t) , [ eq ]))     = substᴱ Argˢ eq (nil t)
    from (inj₂ ((_ , _ , a) , [ eq ])) = substᴱ Argˢ eq (cons a)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ ((_ , t) , [ eq ])) = elim¹ᴱ
      (λ eq → to (substᴱ Argˢ eq (nil t)) ≡
              inj₁ ((_ , t) , [ eq ]))
      (to (substᴱ Argˢ (refl _) (nil t))  ≡⟨ cong to substᴱ-refl ⟩
       to (nil t)                         ≡⟨⟩
       inj₁ ((_ , t) , [ refl _ ])        ∎)
      eq
    to∘from (inj₂ ((_ , _ , a) , [ eq ])) = elim¹ᴱ
      (λ eq → to (substᴱ Argˢ eq (cons a)) ≡
              inj₂ ((_ , _ , a) , [ eq ]))
      (to (substᴱ Argˢ (refl _) (cons a))  ≡⟨ cong to substᴱ-refl ⟩
       to (cons a)                         ≡⟨⟩
       inj₂ ((_ , _ , a) , [ refl _ ])     ∎)
      eq

    from∘to : ∀ x → from (to x) ≡ x
    from∘to (nil _)  = substᴱ-refl
    from∘to (cons _) = substᴱ-refl

  ----------------------------------------------------------------------
  -- Alternative definitions of Tm/Args/Arg and Term/Arguments/Argument

  -- The following three definitions are indexed by /erased/
  -- skeletons.

  mutual

    data Tm′ : @0 Tmˢ s → Type ℓ where
      var : Var s → Tm′ (var {s = s})
      op  : Args′ asˢ → Tm′ (op o asˢ)

    data Args′ : @0 Argsˢ vs → Type ℓ where
      nil  : Args′ nil
      cons : Arg′ aˢ → Args′ asˢ → Args′ (cons aˢ asˢ)

    data Arg′ : @0 Argˢ v → Type ℓ where
      nil  : Tm′ tˢ → Arg′ (nil tˢ)
      cons : {@0 aˢ : Argˢ v} →
             Var s → Arg′ aˢ → Arg′ (cons {s = s} aˢ)

  -- Lemmas used by Tm′≃Tm, Args′≃Args and Arg′≃Arg below.

  private

    module ′≃ where

      mutual

        to-Tm : Tm′ tˢ → Tm tˢ
        to-Tm (var x) = x
        to-Tm (op as) = to-Args as

        to-Args : Args′ asˢ → Args asˢ
        to-Args nil         = _
        to-Args (cons a as) = to-Arg a , to-Args as

        to-Arg : Arg′ aˢ → Arg aˢ
        to-Arg (nil t)    = to-Tm t
        to-Arg (cons x a) = x , to-Arg a

      mutual

        from-Tm : (tˢ : Tmˢ s) → Tm tˢ → Tm′ tˢ
        from-Tm var        x  = var x
        from-Tm (op o asˢ) as = op (from-Args asˢ as)

        from-Args : (asˢ : Argsˢ vs) → Args asˢ → Args′ asˢ
        from-Args nil           _        = nil
        from-Args (cons aˢ asˢ) (a , as) =
          cons (from-Arg aˢ a) (from-Args asˢ as)

        from-Arg : (aˢ : Argˢ v) → Arg aˢ → Arg′ aˢ
        from-Arg (nil tˢ)  t       = nil (from-Tm tˢ t)
        from-Arg (cons aˢ) (x , a) = cons x (from-Arg aˢ a)

      mutual

        to-from-Tm :
          (tˢ : Tmˢ s) (t : Tm tˢ) → to-Tm (from-Tm tˢ t) ≡ t
        to-from-Tm var        x  = refl _
        to-from-Tm (op o asˢ) as = to-from-Args asˢ as

        to-from-Args :
          (asˢ : Argsˢ vs) (as : Args asˢ) →
          to-Args (from-Args asˢ as) ≡ as
        to-from-Args nil           _        = refl _
        to-from-Args (cons aˢ asˢ) (a , as) =
          cong₂ _,_ (to-from-Arg aˢ a) (to-from-Args asˢ as)

        to-from-Arg :
          (aˢ : Argˢ v) (a : Arg aˢ) → to-Arg (from-Arg aˢ a) ≡ a
        to-from-Arg (nil tˢ)  t       = to-from-Tm tˢ t
        to-from-Arg (cons aˢ) (x , a) = cong (x ,_) (to-from-Arg aˢ a)

      mutual

        from-to-Tm :
          (tˢ : Tmˢ s) (t : Tm′ tˢ) → from-Tm tˢ (to-Tm t) ≡ t
        from-to-Tm var      (var x) = refl _
        from-to-Tm (op _ _) (op as) = cong op (from-to-Args as)

        from-to-Args :
          {asˢ : Argsˢ vs} (as : Args′ asˢ) →
          from-Args asˢ (to-Args as) ≡ as
        from-to-Args nil         = refl _
        from-to-Args (cons a as) =
          cong₂ cons (from-to-Arg a) (from-to-Args as)

        from-to-Arg :
          {aˢ : Argˢ v} (a : Arg′ aˢ) → from-Arg aˢ (to-Arg a) ≡ a
        from-to-Arg (nil t)    = cong nil (from-to-Tm _ t)
        from-to-Arg (cons x a) = cong (cons x) (from-to-Arg a)

  -- The alternative definitions of Tm, Args and Arg are pointwise
  -- equivalent to the original ones.

  Tm′≃Tm : {tˢ : Tmˢ s} → Tm′ tˢ ≃ Tm tˢ
  Tm′≃Tm {tˢ = tˢ} = Eq.↔→≃
    to-Tm
    (from-Tm _)
    (to-from-Tm tˢ)
    (from-to-Tm _)
    where
    open ′≃

  Args′≃Args : {asˢ : Argsˢ vs} → Args′ asˢ ≃ Args asˢ
  Args′≃Args = Eq.↔→≃
    to-Args
    (from-Args _)
    (to-from-Args _)
    from-to-Args
    where
    open ′≃

  Arg′≃Arg : {aˢ : Argˢ v} → Arg′ aˢ ≃ Arg aˢ
  Arg′≃Arg {aˢ = aˢ} = Eq.↔→≃
    to-Arg
    (from-Arg _)
    (to-from-Arg aˢ)
    from-to-Arg
    where
    open ′≃

  -- The following alternative definitions of Term, Arguments and
  -- Argument use Tm′/Args′/Arg′ instead of Tm/Args/Arg.

  Term′ : @0 Vars → @0 Sort → Type ℓ
  Term′ xs s =
    ∃ λ (tˢ : Tmˢ s) → ∃ λ (t : Tm′ tˢ) →
      Erased (Wf-tm xs tˢ (_≃_.to Tm′≃Tm t))

  Arguments′ : @0 Vars → @0 List Valence → Type ℓ
  Arguments′ xs vs =
    ∃ λ (asˢ : Argsˢ vs) → ∃ λ (as : Args′ asˢ) →
    Erased (Wf-args xs asˢ (_≃_.to Args′≃Args as))

  Argument′ : @0 Vars → @0 Valence → Type ℓ
  Argument′ xs v =
    ∃ λ (aˢ : Argˢ v) → ∃ λ (a : Arg′ aˢ) →
      Erased (Wf-arg xs aˢ (_≃_.to Arg′≃Arg a))

  -- These alternative definitions are also pointwise equivalent to
  -- the original ones.

  Term′≃Term : Term′ xs s ≃ Term xs s
  Term′≃Term = ∃-cong λ _ → Σ-cong Tm′≃Tm λ _ → F.id

  Arguments′≃Arguments : Arguments′ xs vs ≃ Arguments xs vs
  Arguments′≃Arguments = ∃-cong λ _ → Σ-cong Args′≃Args λ _ → F.id

  Argument′≃Argument : Argument′ xs v ≃ Argument xs v
  Argument′≃Argument = ∃-cong λ _ → Σ-cong Arg′≃Arg λ _ → F.id

  ----------------------------------------------------------------------
  -- Decision procedures for equality

  -- "Erased mere equality" is decidable for ∃Var.

  merely-equal?-∃Var : (x y : ∃Var) → Dec-Erased ∥ x ≡ y ∥
  merely-equal?-∃Var x y with x ≟∃V y
  … | yes [ x≡y ] = yes [ ∣ x≡y ∣ ]
  … | no  [ x≢y ] = no  [ x≢y ∘ Trunc.rec ∃Var-set id ]

  private

    -- An instance of delete.

    del : ∃Var → Finite-subset-of ∃Var → Finite-subset-of ∃Var
    del = delete merely-equal?-∃Var

  -- Erased equality is decidable for Tmˢ, Argsˢ and Argˢ.

  infix 4 _≟Tmˢ_ _≟Argsˢ_ _≟Argˢ_

  mutual

    _≟Tmˢ_ : Decidable-erased-equality (Tmˢ s)
    var ≟Tmˢ var = yes [ refl _ ]

    var ≟Tmˢ op _ _ =            $⟨ no [ (λ ()) ] ⟩
      Dec-Erased ⊥               ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎)) ⟩□
      Dec-Erased (var ≡ op _ _)  □

    op _ _ ≟Tmˢ var =            $⟨ no [ (λ ()) ] ⟩
      Dec-Erased ⊥               ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎)) ⟩□
      Dec-Erased (op _ _ ≡ var)  □

    op o₁ as₁ ≟Tmˢ op o₂ as₂ =              $⟨ decidable-erased⇒dec-erased⇒Σ-dec-erased _≟O_ (λ _ → _ ≟Argsˢ as₂) ⟩
      Dec-Erased ((o₁ , as₁) ≡ (o₂ , as₂))  ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂) ⟩□
      Dec-Erased (op o₁ as₁ ≡ op o₂ as₂)    □

    _≟Argsˢ_ : Decidable-erased-equality (Argsˢ vs)
    nil ≟Argsˢ nil =                        $⟨ yes [ refl _ ] ⟩
      Dec-Erased ([ refl _ ] ≡ [ refl _ ])  ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Argsˢ≃) F.∘ from-isomorphism Bijection.≡↔inj₁≡inj₁) ⟩□
      Dec-Erased (nil ≡ nil)                □

    cons a₁ as₁ ≟Argsˢ cons a₂ as₂ =                            $⟨ dec-erased⇒dec-erased⇒×-dec-erased
                                                                     (set⇒dec-erased⇒dec-erased⇒Σ-dec-erased
                                                                        (H-level-Erased 2 (×-closure 2 (H-level-List 0 Sort-set) Sort-set))
                                                                        (yes [ refl _ ])
                                                                        (λ _ → _ ≟Argˢ a₂))
                                                                     (set⇒dec-erased⇒dec-erased⇒Σ-dec-erased
                                                                        (H-level-Erased 2 (H-level-List 0 Valence-set))
                                                                        (yes [ refl _ ])
                                                                        (λ _ → _ ≟Argsˢ as₂)) ⟩

      Dec-Erased (((_ , a₁) , _ , as₁) ≡ ((_ , a₂) , _ , as₂))  ↝⟨ Dec-Erased-map (from-isomorphism $ ignore-propositional-component $
                                                                   H-level-Erased 1 (H-level-List 0 Valence-set)) ⟩
      Dec-Erased ((((_ , a₁) , _ , as₁) , [ refl _ ]) ≡
           (((_ , a₂) , _ , as₂) , [ refl _ ]))                 ↝⟨ Dec-Erased-map (
                                                                   from-isomorphism (Eq.≃-≡ Argsˢ≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂) ⟩□
      Dec-Erased (cons a₁ as₁ ≡ cons a₂ as₂)                    □

    _≟Argˢ_ : Decidable-erased-equality (Argˢ v)
    nil t₁ ≟Argˢ nil t₂ =                                             $⟨ set⇒dec-erased⇒dec-erased⇒Σ-dec-erased
                                                                           (H-level-Erased 2 Sort-set)
                                                                           (yes [ refl _ ])
                                                                           (λ _ → _ ≟Tmˢ t₂) ⟩
      Dec-Erased ((_ , t₁) ≡ (_ , t₂))                                ↝⟨ Dec-Erased-map (from-isomorphism $ ignore-propositional-component $
                                                                         H-level-Erased 1 Valence-set) ⟩
      Dec-Erased (((_ , t₁) , [ refl _ ]) ≡ ((_ , t₂) , [ refl _ ]))  ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Argˢ≃) F.∘
                                                                         from-isomorphism Bijection.≡↔inj₁≡inj₁) ⟩□
      Dec-Erased (nil t₁ ≡ nil t₂)                                    □

    cons a₁ ≟Argˢ cons a₂ =                      $⟨ dec-erased⇒dec-erased⇒×-dec-erased
                                                      (yes [ refl _ ])
                                                      (set⇒dec-erased⇒dec-erased⇒Σ-dec-erased
                                                         (H-level-Erased 2 Valence-set)
                                                         (yes [ refl _ ])
                                                         (λ _ → _ ≟Argˢ a₂)) ⟩
      Dec-Erased ((_ , _ , a₁) ≡ (_ , _ , a₂))   ↝⟨ Dec-Erased-map (from-isomorphism $ ignore-propositional-component $
                                                    H-level-Erased 1 Valence-set) ⟩
      Dec-Erased (((_ , _ , a₁) , [ refl _ ]) ≡
                  ((_ , _ , a₂) , [ refl _ ]))   ↝⟨ Dec-Erased-map (
                                                    from-isomorphism (Eq.≃-≡ Argˢ≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂) ⟩□
      Dec-Erased (cons a₁ ≡ cons a₂)             □

  -- Erased equality is decidable for Tm, Args and Arg.

  mutual

    equal?-Tm : ∀ {s} (tˢ : Tmˢ s) → Decidable-erased-equality (Tm tˢ)
    equal?-Tm var        x₁  x₂  = x₁ ≟V x₂
    equal?-Tm (op o asˢ) as₁ as₂ = equal?-Args asˢ as₁ as₂

    equal?-Args :
      ∀ {vs} (asˢ : Argsˢ vs) → Decidable-erased-equality (Args asˢ)
    equal?-Args nil           _          _          = yes [ refl _ ]
    equal?-Args (cons aˢ asˢ) (a₁ , as₁) (a₂ , as₂) =
      dec-erased⇒dec-erased⇒×-dec-erased
        (equal?-Arg aˢ a₁ a₂)
        (equal?-Args asˢ as₁ as₂)

    equal?-Arg :
      ∀ {v} (aˢ : Argˢ v) → Decidable-erased-equality (Arg aˢ)
    equal?-Arg (nil tˢ)  t₁        t₂        = equal?-Tm tˢ t₁ t₂
    equal?-Arg (cons aˢ) (x₁ , a₁) (x₂ , a₂) =
      dec-erased⇒dec-erased⇒×-dec-erased
        (x₁ ≟V x₂)
        (equal?-Arg aˢ a₁ a₂)

  -- Erased equality is decidable for Tm′, Args′ and Arg′.
  --
  -- (Presumably it is possible to prove this without converting to
  -- Tm/Args/Arg, and in that case the sort and skeleton arguments can
  -- perhaps be erased.)

  _≟Tm′_ :
    ∀ {s} {tˢ : Tmˢ s} →
    Decidable-erased-equality (Tm′ tˢ)
  _≟Tm′_ {tˢ = tˢ} t₁ t₂ =                            $⟨ equal?-Tm tˢ _ _ ⟩
    Dec-Erased (_≃_.to Tm′≃Tm t₁ ≡ _≃_.to Tm′≃Tm t₂)  ↝⟨ Dec-Erased-map (from-equivalence (Eq.≃-≡ Tm′≃Tm)) ⟩□
    Dec-Erased (t₁ ≡ t₂)                              □

  _≟Args′_ :
    ∀ {vs} {asˢ : Argsˢ vs} →
    Decidable-erased-equality (Args′ asˢ)
  _≟Args′_ {asˢ = asˢ} as₁ as₂ =                                $⟨ equal?-Args asˢ _ _ ⟩
    Dec-Erased (_≃_.to Args′≃Args as₁ ≡ _≃_.to Args′≃Args as₂)  ↝⟨ Dec-Erased-map (from-equivalence (Eq.≃-≡ Args′≃Args)) ⟩□
    Dec-Erased (as₁ ≡ as₂)                                      □

  _≟Arg′_ :
    ∀ {v} {aˢ : Argˢ v} →
    Decidable-erased-equality (Arg′ aˢ)
  _≟Arg′_ {aˢ = aˢ} a₁ a₂ =                               $⟨ equal?-Arg aˢ _ _ ⟩
    Dec-Erased (_≃_.to Arg′≃Arg a₁ ≡ _≃_.to Arg′≃Arg a₂)  ↝⟨ Dec-Erased-map (from-equivalence (Eq.≃-≡ Arg′≃Arg)) ⟩□
    Dec-Erased (a₁ ≡ a₂)                                  □

  -- The Wf predicates are propositional.

  @0 Wf-var-propositional :
    Is-proposition (Wf-var xs x)
  Wf-var-propositional = ∈-propositional

  mutual

    @0 Wf-tm-propositional :
      (tˢ : Tmˢ s) {t : Tm tˢ} → Is-proposition (Wf-tm xs tˢ t)
    Wf-tm-propositional var        = ∈-propositional
    Wf-tm-propositional (op o asˢ) = Wf-args-propositional asˢ

    @0 Wf-args-propositional :
      (asˢ : Argsˢ vs) {as : Args asˢ} →
      Is-proposition (Wf-args xs asˢ as)
    Wf-args-propositional nil _ _ = refl _

    Wf-args-propositional (cons aˢ asˢ) (wf₁ , wfs₁) (wf₂ , wfs₂) =
      cong₂ _,_
        (Wf-arg-propositional aˢ wf₁ wf₂)
        (Wf-args-propositional asˢ wfs₁ wfs₂)

    @0 Wf-arg-propositional :
      (aˢ : Argˢ v) {a : Arg aˢ} →
      Is-proposition (Wf-arg xs aˢ a)
    Wf-arg-propositional (nil tˢ) = Wf-tm-propositional tˢ

    Wf-arg-propositional (cons aˢ) wf₁ wf₂ =
      ⟨ext⟩ λ y → ⟨ext⟩ λ y∉xs →
        Wf-arg-propositional aˢ (wf₁ y y∉xs) (wf₂ y y∉xs)

  -- Erased equality is decidable for Variable.

  infix 4 _≟Variable_

  _≟Variable_ : ∀ {s} → Decidable-erased-equality (Variable xs s)
  _≟Variable_ =
    decidable-erased⇒decidable-erased⇒Σ-decidable-erased
      _≟V_
      λ _ _ → yes [ []-cong [ Wf-var-propositional _ _ ] ]

  -- Erased equality is decidable for Term′, Arguments′ and Argument′.

  infix 4 _≟Term′_ _≟Arguments′_ _≟Argument′_

  _≟Term′_ : ∀ {s} → Decidable-erased-equality (Term′ xs s)
  _≟Term′_ =
    decidable-erased⇒decidable-erased⇒Σ-decidable-erased
      _≟Tmˢ_
      λ {tˢ} →
        decidable-erased⇒decidable-erased⇒Σ-decidable-erased
          _≟Tm′_
          λ _ _ → yes [ []-cong [ Wf-tm-propositional tˢ _ _ ] ]

  _≟Arguments′_ : ∀ {vs} → Decidable-erased-equality (Arguments′ xs vs)
  _≟Arguments′_ =
    decidable-erased⇒decidable-erased⇒Σ-decidable-erased
      _≟Argsˢ_
      λ {asˢ} →
        decidable-erased⇒decidable-erased⇒Σ-decidable-erased
          _≟Args′_
          λ _ _ → yes [ []-cong [ Wf-args-propositional asˢ _ _ ] ]

  _≟Argument′_ : ∀ {v} → Decidable-erased-equality (Argument′ xs v)
  _≟Argument′_ =
    decidable-erased⇒decidable-erased⇒Σ-decidable-erased
      _≟Argˢ_
      λ {aˢ} →
        decidable-erased⇒decidable-erased⇒Σ-decidable-erased
          _≟Arg′_
          λ _ _ → yes [ []-cong [ Wf-arg-propositional aˢ _ _ ] ]

  -- Erased equality is decidable for Term, Arguments and Argument.
  --
  -- TODO: Is it possible to prove this without converting to
  -- Term′/Arguments′/Argument′? I attempted to prove this for Term by
  -- using _≟Tmˢ_ and equal?-Tm, but my attempt failed because the
  -- skeleton argument of Term is not erased, so I could not use
  -- decidable-erased⇒decidable-erased⇒Σ-decidable-erased (which, at
  -- the time of writing, has an argument P of type @0 A → Type p).

  infix 4 _≟Term_ _≟Arguments_ _≟Argument_

  _≟Term_ : ∀ {s} → Decidable-erased-equality (Term xs s)
  _≟Term_ {xs = xs} {s = s} =               $⟨ _≟Term′_ ⟩
    Decidable-erased-equality (Term′ xs s)  ↝⟨ Decidable-erased-equality-map (_≃_.surjection Term′≃Term) ⟩□
    Decidable-erased-equality (Term xs s)   □

  _≟Arguments_ : ∀ {vs} → Decidable-erased-equality (Arguments xs vs)
  _≟Arguments_ {xs = xs} {vs = vs} =              $⟨ _≟Arguments′_ ⟩
    Decidable-erased-equality (Arguments′ xs vs)  ↝⟨ Decidable-erased-equality-map (_≃_.surjection Arguments′≃Arguments) ⟩□
    Decidable-erased-equality (Arguments xs vs)   □

  _≟Argument_ : ∀ {v} → Decidable-erased-equality (Argument xs v)
  _≟Argument_ {xs = xs} {v = v} =               $⟨ _≟Argument′_ ⟩
    Decidable-erased-equality (Argument′ xs v)  ↝⟨ Decidable-erased-equality-map (_≃_.surjection Argument′≃Argument) ⟩□
    Decidable-erased-equality (Argument xs v)   □

  -- Tmˢ, Argsˢ, Argˢ, Tm, Args, Arg, Tm′, Args′, Arg′, Variable,
  -- Term, Arguments, Argument, Term′, Arguments′ and Argument′ are
  -- sets (pointwise, in erased contexts).

  @0 Tmˢ-set : Is-set (Tmˢ s)
  Tmˢ-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Tmˢ_

  @0 Argsˢ-set : Is-set (Argsˢ vs)
  Argsˢ-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Argsˢ_

  @0 Argˢ-set : Is-set (Argˢ v)
  Argˢ-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Argˢ_

  @0 Tm-set : ∀ {s} (tˢ : Tmˢ s) → Is-set (Tm tˢ)
  Tm-set tˢ =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ (equal?-Tm tˢ)

  @0 Args-set : ∀ {vs} {asˢ : Argsˢ vs} → Is-set (Args asˢ)
  Args-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ (equal?-Args _)

  @0 Arg-set : ∀ {v} (aˢ : Argˢ v) → Is-set (Arg aˢ)
  Arg-set aˢ =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ (equal?-Arg aˢ)

  @0 Tm′-set : ∀ {s} {tˢ : Tmˢ s} → Is-set (Tm′ tˢ)
  Tm′-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Tm′_

  @0 Args′-set : ∀ {vs} {asˢ : Argsˢ vs} → Is-set (Args′ asˢ)
  Args′-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Args′_

  @0 Arg′-set : ∀ {v} {aˢ : Argˢ v} → Is-set (Arg′ aˢ)
  Arg′-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Arg′_

  @0 Variable-set : ∀ {s} → Is-set (Variable xs s)
  Variable-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Variable_

  @0 Term-set : ∀ {s} → Is-set (Term xs s)
  Term-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Term_

  @0 Arguments-set : ∀ {vs} → Is-set (Arguments xs vs)
  Arguments-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Arguments_

  @0 Argument-set : ∀ {v} → Is-set (Argument xs v)
  Argument-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Argument_

  @0 Term′-set : ∀ {s} → Is-set (Term′ xs s)
  Term′-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Term′_

  @0 Arguments′-set : ∀ {vs} → Is-set (Arguments′ xs vs)
  Arguments′-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Arguments′_

  @0 Argument′-set : ∀ {v} → Is-set (Argument′ xs v)
  Argument′-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Argument′_

  ----------------------------------------------------------------------
  -- An elimination principle for well-formed terms ("structural
  -- induction modulo fresh renaming")

  -- The eliminators' arguments.

  record Wf-elim
           (P-tm   : ∀ {@0 xs s}  → Term xs s       → Type p₁)
           (P-args : ∀ {@0 xs vs} → Arguments xs vs → Type p₂)
           (P-arg  : ∀ {@0 xs v}  → Argument xs v   → Type p₃)
           : Type (ℓ ⊔ p₁ ⊔ p₂ ⊔ p₃) where
    no-eta-equality
    field
      varʳ : ∀ {s} (x : Var s) (@0 x∈ : (_ , x) ∈ xs) →
             P-tm (var-wf x x∈)
      opʳ  : ∀ (o : Op s) asˢ as (@0 wfs : Wf-args xs asˢ as) →
             P-args (asˢ , as , [ wfs ]) →
             P-tm (op-wf o asˢ as wfs)

      nilʳ  : P-args {xs = xs} nil-wfs
      consʳ : ∀ aˢ a asˢ as
              (@0 wf : Wf-arg {v = v} xs aˢ a)
              (@0 wfs : Wf-args {vs = vs} xs asˢ as) →
              P-arg (aˢ , a , [ wf ]) → P-args (asˢ , as , [ wfs ]) →
              P-args (cons-wfs aˢ asˢ a as wf wfs)

      nilʳ′  : ∀ tˢ t (@0 wf : Wf-tm {s = s} xs tˢ t) →
               P-tm (tˢ , t , [ wf ]) →
               P-arg (nil-wf tˢ t wf)
      consʳ′ : ∀ {s} (aˢ : Argˢ v) (x : Var s) a (@0 wf) →
               (∀ y (@0 y∉ : ¬ (_ , y) ∈ xs) →
                P-arg (aˢ , rename-Arg x y aˢ a , [ wf y y∉ ])) →
               P-arg (cons-wf aˢ x a wf)

  -- The eliminators.

  -- TODO: Can one define a more efficient eliminator that collects up
  -- all the renamings?

  module _
    {P-tm   : ∀ {@0 xs s}  → Term xs s       → Type p₁}
    {P-args : ∀ {@0 xs vs} → Arguments xs vs → Type p₂}
    {P-arg  : ∀ {@0 xs v}  → Argument xs v   → Type p₃}
    (e : Wf-elim P-tm P-args P-arg)
    where

    open Wf-elim

    private

     mutual

      wf-elim-Term′ :
        (tˢ : Tmˢ s) (t : Tm tˢ) (@0 wf : Wf-tm xs tˢ t) →
        P-tm (tˢ , t , [ wf ])
      wf-elim-Term′ var        x  wf  = e .varʳ x wf
      wf-elim-Term′ (op o asˢ) as wfs =
        e .opʳ o asˢ as wfs (wf-elim-Arguments′ asˢ as wfs)

      wf-elim-Arguments′ :
        (asˢ : Argsˢ vs) (as : Args asˢ) (@0 wfs : Wf-args xs asˢ as) →
        P-args (asˢ , as , [ wfs ])
      wf-elim-Arguments′ nil _ _ = e .nilʳ

      wf-elim-Arguments′ (cons aˢ asˢ) (a , as) (wf , wfs) =
        e .consʳ aˢ a asˢ as wf wfs
          (wf-elim-Argument′ aˢ a wf)
          (wf-elim-Arguments′ asˢ as wfs)

      wf-elim-Argument′ :
        (aˢ : Argˢ v) (a : Arg aˢ) (@0 wf : Wf-arg xs aˢ a) →
        P-arg (aˢ , a , [ wf ])
      wf-elim-Argument′ (nil tˢ) t wf =
        e .nilʳ′ tˢ t wf (wf-elim-Term′ tˢ t wf)

      wf-elim-Argument′ (cons aˢ) (x , a) wf =
        e .consʳ′ aˢ x a wf λ y y∉ →
          wf-elim-Argument′ aˢ (rename-Arg x y aˢ a) (wf y y∉)

    wf-elim-Term : (t : Term xs s) → P-tm t
    wf-elim-Term (tˢ , t , [ wf ]) = wf-elim-Term′ tˢ t wf

    wf-elim-Arguments : (as : Arguments xs vs) → P-args as
    wf-elim-Arguments (asˢ , as , [ wfs ]) =
      wf-elim-Arguments′ asˢ as wfs

    wf-elim-Argument : (a : Argument xs v) → P-arg a
    wf-elim-Argument (aˢ , a , [ wf ]) = wf-elim-Argument′ aˢ a wf

  ----------------------------------------------------------------------
  -- Some lemmas related to cast-Var

  abstract

    -- When no arguments are erased one can express cast-Var in a
    -- different way.

    cast-Var-not-erased :
      ∀ {s s′} {s≡s′ : s ≡ s′} {x} →
      cast-Var s≡s′ x ≡ subst (λ s → Var s) s≡s′ x
    cast-Var-not-erased {s≡s′ = s≡s′} {x = x} =
      substᴱ Var s≡s′ x           ≡⟨ substᴱ≡subst ⟩∎
      subst (λ s → Var s) s≡s′ x  ∎

    -- If eq has type s₁ ≡ s₂, then s₁ paired up with x (as an element
    -- of ∃Var) is equal to s₂ paired up with cast-Var eq x (if none
    -- of these inputs are erased).

    ≡,cast-Var :
      ∀ {s₁ s₂ x} {eq : s₁ ≡ s₂} →
      _≡_ {A = ∃Var} (s₁ , x) (s₂ , cast-Var eq x)
    ≡,cast-Var {s₁ = s₁} {s₂ = s₂} {x = x} {eq = eq} =
      Σ-≡,≡→≡ eq
        (subst (λ s → Var s) eq x  ≡⟨ sym cast-Var-not-erased ⟩∎
         cast-Var eq x             ∎)

    -- A "computation rule".

    cast-Var-refl :
      ∀ {@0 s} {x : Var s} →
      cast-Var (refl s) x ≡ x
    cast-Var-refl {x = x} =
      substᴱ Var (refl _) x  ≡⟨ substᴱ-refl ⟩∎
      x                      ∎

    -- A fusion lemma for cast-Var.

    cast-Var-cast-Var :
      {x : Var s₁} {@0 eq₁ : s₁ ≡ s₂} {@0 eq₂ : s₂ ≡ s₃} →
      cast-Var eq₂ (cast-Var eq₁ x) ≡ cast-Var (trans eq₁ eq₂) x
    cast-Var-cast-Var {x = x} {eq₁ = eq₁} {eq₂ = eq₂} =
      subst (λ ([ s ]) → Var s) ([]-cong [ eq₂ ])
        (subst (λ ([ s ]) → Var s) ([]-cong [ eq₁ ]) x)        ≡⟨ subst-subst _ _ _ _ ⟩

      subst (λ ([ s ]) → Var s)
        (trans ([]-cong [ eq₁ ]) ([]-cong [ eq₂ ])) x          ≡⟨ cong (flip (subst _) _) $ sym []-cong-[trans] ⟩∎

      subst (λ ([ s ]) → Var s) ([]-cong [ trans eq₁ eq₂ ]) x  ∎

    -- The proof given to cast-Var can be replaced.

    cast-Var-irrelevance :
      {x : Var s₁} {@0 eq₁ eq₂ : s₁ ≡ s₂} →
      cast-Var eq₁ x ≡ cast-Var eq₂ x
    cast-Var-irrelevance = congᴱ (λ eq → cast-Var eq _) (Sort-set _ _)

    -- If cast-Var's proof argument is constructed (in a certain way)
    -- from a (non-erased) proof of a kind of equality between
    -- cast-Var's variable argument and another variable, then the
    -- result is equal to the other variable.

    cast-Var-Σ-≡,≡←≡ :
      ∀ {s₁ s₂} {x₁ : Var s₁} {x₂ : Var s₂}
      (eq : _≡_ {A = ∃Var} (s₁ , x₁) (s₂ , x₂)) →
      cast-Var (proj₁ (Σ-≡,≡←≡ eq)) x₁ ≡ x₂
    cast-Var-Σ-≡,≡←≡ {x₁ = x₁} {x₂ = x₂} eq =
      cast-Var (proj₁ (Σ-≡,≡←≡ eq)) x₁             ≡⟨ cast-Var-not-erased ⟩
      subst (λ s → Var s) (proj₁ (Σ-≡,≡←≡ eq)) x₁  ≡⟨ proj₂ (Σ-≡,≡←≡ eq) ⟩∎
      x₂                                           ∎

  ----------------------------------------------------------------------
  -- Some renaming lemmas

  abstract

    -- Two "computation rules".

    rename-Var-≡ :
      ∀ {s s′} {x y : Var s} {z : Var s′} →
      (@0 x≡z : _≡_ {A = ∃Var} (_ , x) (_ , z)) →
      rename-Var x y z ≡ cast-Var (cong proj₁ x≡z) y
    rename-Var-≡ {x = x} {y = y} {z = z} x≡z with (_ , x) ≟∃V (_ , z)
    … | no [ x≢z ]   = ⊥-elim (_↔_.to Erased-⊥↔⊥ [ x≢z x≡z ])
    … | yes [ x≡z′ ] =
      cast-Var (cong proj₁ x≡z′) y  ≡⟨ cast-Var-irrelevance ⟩∎
      cast-Var (cong proj₁ x≡z)  y  ∎

    rename-Var-≢ :
      ∀ {s s′} {x y : Var s} {z : Var s′} →
      @0 _≢_ {A = ∃Var} (_ , x) (_ , z) → rename-Var x y z ≡ z
    rename-Var-≢ {x = x} {z = z} x≢z with (_ , x) ≟∃V (_ , z)
    … | no _        = refl _
    … | yes [ x≡z ] = ⊥-elim (_↔_.to Erased-⊥↔⊥ [ x≢z x≡z ])

    -- Equality to a pair of a certain form involving rename-Var can
    -- be expressed without reference to rename-Var (in erased
    -- contexts).

    @0 ≡,rename-Var≃ :
      ∀ {s s′} {x y : Var s} {z : Var s′} {p : ∃Var} →
      (p ≡ (_ , rename-Var x y z))
        ≃
      (_≡_ {A = ∃Var} (_ , x) (_ , z) × p ≡ (_ , y) ⊎
       _≢_ {A = ∃Var} (_ , x) (_ , z) × p ≡ (_ , z))
    ≡,rename-Var≃ {x = x} {y = y} {z = z} {p = p} =
      p ≡ (_ , rename-Var x y z)                          ↔⟨ ×-⊎-distrib-right F.∘
                                                             (inverse $ drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                              propositional⇒inhabited⇒contractible
                                                                (Dec-closure-propositional ext ∃Var-set)
                                                                (_≃_.to Dec-Erased≃Dec (_ ≟∃V _))) ⟩
      ((_ , x) ≡ (_ , z)) × p ≡ (_ , rename-Var x y z) ⊎
      ((_ , x) ≢ (_ , z)) × p ≡ (_ , rename-Var x y z)    ↝⟨ (∃-cong λ eq → ≡⇒↝ _ $ cong (p ≡_) (

          _ , rename-Var x y z                                  ≡⟨ cong (_ ,_) $ rename-Var-≡ eq ⟩
          _ , cast-Var _ y                                      ≡⟨ sym ≡,cast-Var ⟩∎
          _ , y                                                 ∎))
                                                               ⊎-cong
                                                             (∃-cong λ neq → ≡⇒↝ _ $ cong (λ x → _ ≡ (_ , x)) $
                                                              rename-Var-≢ neq) ⟩□
      ((_ , x) ≡ (_ , z)) × p ≡ (_ , y) ⊎
      ((_ , x) ≢ (_ , z)) × p ≡ (_ , z)                   □

    -- A variant of the previous lemma.

    @0 ≡,rename-Var≃′ :
      ∀ {s s′} {x y : Var s} {z : Var s′} {p : ∃Var} →
      (p ≡ (_ , rename-Var x y z))
        ≃
      (p ≡ (_ , y) × _≡_ {A = ∃Var} (_ , x) (_ , z) ⊎
       p ≢ (_ , x) × p ≡ (_ , z))
    ≡,rename-Var≃′ {x = x} {y = y} {z = z} {p = p} =
      p ≡ (_ , rename-Var x y z)         ↝⟨ ≡,rename-Var≃ ⟩

      (_ , x) ≡ (_ , z) × p ≡ (_ , y) ⊎
      (_ , x) ≢ (_ , z) × p ≡ (_ , z)    ↔⟨ (×-comm ⊎-cong ×-cong₁ λ p≡z → →-cong₁ ext ≡-comm F.∘ ≡⇒↝ _ (cong (_ ≢_) (sym p≡z))) ⟩□

      p ≡ (_ , y) × (_ , x) ≡ (_ , z) ⊎
      p ≢ (_ , x) × p ≡ (_ , z)          □

    -- The functions rename-Var and cast-Var commute.

    rename-Var-cast-Var :
      ∀ {s s₁ s₂} {x y : Var s} {z : Var s₁} {@0 eq : s₁ ≡ s₂} →
      rename-Var x y (cast-Var eq z) ≡ cast-Var eq (rename-Var x y z)
    rename-Var-cast-Var
      {s = s} {s₁ = s₁} {s₂ = s₂} {x = x} {y = y} {z = z} {eq = eq}
      with (_ , x) ≟∃V (_ , z)
         | (_ , x) ≟∃V (_ , cast-Var eq z)
    … | yes [ x≡z ] | yes [ x≡z′ ] =
      cast-Var (cong proj₁ x≡z′) y               ≡⟨ cast-Var-irrelevance ⟩
      cast-Var (trans (cong proj₁ x≡z) eq) y     ≡⟨ sym cast-Var-cast-Var ⟩∎
      cast-Var eq (cast-Var (cong proj₁ x≡z) y)  ∎
    … | no _        | no _        = refl _
    … | yes [ x≡z ] | no [ x≢z′ ] =
      ⊥-elim $ _↔_.to Erased-⊥↔⊥
        [ x≢z′ ((_ , x)              ≡⟨ x≡z ⟩
                (_ , z)              ≡⟨ ≡,cast-Var ⟩∎
                (_ , cast-Var eq z)  ∎)
        ]
    … | no [ x≢z ] | yes [ x≡z′ ] =
      ⊥-elim $ _↔_.to Erased-⊥↔⊥
        [ x≢z ((_ , x)              ≡⟨ x≡z′ ⟩
               (_ , cast-Var eq z)  ≡⟨ sym ≡,cast-Var ⟩∎
               (_ , z)              ∎)
        ]

  -- Renamings can sometimes be reordered in a certain way.

  module _
    {s₁ s₂} {x₁ y₁ : Var s₁} {x₂ y₂ : Var s₂}
    (hyp : ¬ ((_≡_ {A = ∃Var} (_ , x₂) (_ , x₁) ×
               _≢_ {A = ∃Var} (_ , x₂) (_ , y₁)
                 ⊎
               _≡_ {A = ∃Var} (_ , x₂) (_ , y₁) ×
               _≢_ {A = ∃Var} (_ , x₂) (_ , x₁))
                ×
              _≢_ {A = ∃Var} (_ , x₁) (_ , y₂))
             ⊎
           _≡_ {A = ∃Var} (_ , y₁) (_ , y₂))
    where

    abstract

      rename-Var-swap :
        ∀ {s} {z : Var s} →
        rename-Var x₁ y₁ (rename-Var x₂ y₂ z) ≡
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)
      rename-Var-swap {z = z} =
        lemma ((_ , x₁) ≟∃V (_ , z))
              ((_ , x₂) ≟∃V (_ , z))
              ((_ , x₂) ≟∃V (_ , y₁))
              ((_ , x₁) ≟∃V (_ , y₂))
        where
        lemma :
          Dec-Erased (_≡_ {A = ∃Var} (_ , x₁) (_ , z)) →
          Dec-Erased (_≡_ {A = ∃Var} (_ , x₂) (_ , z)) →
          Dec-Erased (_≡_ {A = ∃Var} (_ , x₂) (_ , y₁)) →
          Dec-Erased (_≡_ {A = ∃Var} (_ , x₁) (_ , y₂)) →
          rename-Var x₁ y₁ (rename-Var x₂ y₂ z) ≡
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)
        lemma (no [ x₁≢z ]) (no [ x₂≢z ]) _ _ =
          rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≢ x₂≢z ⟩
          rename-Var x₁ y₁ z                                        ≡⟨ rename-Var-≢ x₁≢z ⟩
          z                                                         ≡⟨ sym $ rename-Var-≢ x₂≢z ⟩
          rename-Var x₂ (rename-Var x₁ y₁ y₂) z                     ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≢ x₁≢z ⟩∎
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

        lemma (no [ x₁≢z ]) (yes [ x₂≡z ]) _ _ =
          rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≡ x₂≡z ⟩
          rename-Var x₁ y₁ (cast-Var _ y₂)                          ≡⟨ rename-Var-cast-Var ⟩
          cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ sym $ rename-Var-≡ x₂≡z ⟩
          rename-Var x₂ (rename-Var x₁ y₁ y₂) z                     ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≢ x₁≢z ⟩∎
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

        lemma (yes [ x₁≡z ]) (yes [ x₂≡z ]) (yes [ x₂≡y₁ ]) _ =
          rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≡ x₂≡z ⟩
          rename-Var x₁ y₁ (cast-Var _ y₂)                          ≡⟨ rename-Var-cast-Var ⟩
          cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ cast-Var-irrelevance ⟩
          cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ sym cast-Var-cast-Var ⟩
          cast-Var _ (cast-Var _ (rename-Var x₁ y₁ y₂))             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≡ x₂≡y₁ ⟩
          cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

        lemma (yes [ x₁≡z ]) (yes [ x₂≡z ])
              (no [ x₂≢y₁ ]) (yes [ x₁≡y₂ ]) =
          rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≡ x₂≡z ⟩
          rename-Var x₁ y₁ (cast-Var _ y₂)                          ≡⟨ rename-Var-cast-Var ⟩
          cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ cong (cast-Var _) $ rename-Var-≡ x₁≡y₂ ⟩
          cast-Var _ (cast-Var _ y₁)                                ≡⟨ cast-Var-cast-Var ⟩
          cast-Var _ y₁                                             ≡⟨ cast-Var-irrelevance ⟩
          cast-Var _ y₁                                             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≢ x₂≢y₁ ⟩
          cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

        lemma (yes [ x₁≡z ]) (yes [ x₂≡z ])
              (no [ x₂≢y₁ ]) (no [ x₁≢y₂ ]) =
          case hyp of λ where
            (inj₁ hyp) →
              ⊥-elim $ _↔_.to Erased-⊥↔⊥
                [ hyp (inj₁ (trans x₂≡z (sym x₁≡z) , x₂≢y₁) , x₁≢y₂) ]
            (inj₂ hyp) →
              rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≡ x₂≡z ⟩
              rename-Var x₁ y₁ (cast-Var _ y₂)                          ≡⟨ rename-Var-cast-Var ⟩
              cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ cong (cast-Var _) $ rename-Var-≢ x₁≢y₂ ⟩
              cast-Var _ y₂                                             ≡⟨ cong (cast-Var _) $ sym $ cast-Var-Σ-≡,≡←≡ hyp ⟩
              cast-Var _ (cast-Var _ y₁)                                ≡⟨ cast-Var-cast-Var ⟩
              cast-Var _ y₁                                             ≡⟨ cast-Var-irrelevance ⟩
              cast-Var _ y₁                                             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≢ x₂≢y₁ ⟩
              cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
              rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
              rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

        lemma (yes [ x₁≡z ]) (no [ x₂≢z ]) (no [ x₂≢y₁ ]) _ =
          rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≢ x₂≢z ⟩
          rename-Var x₁ y₁ z                                        ≡⟨ rename-Var-≡ x₁≡z ⟩
          cast-Var _ y₁                                             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≢ x₂≢y₁ ⟩
          cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

        lemma (yes [ x₁≡z ]) (no [ x₂≢z ])
              (yes [ x₂≡y₁ ]) (yes [ x₁≡y₂ ]) =
          rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≢ x₂≢z ⟩
          rename-Var x₁ y₁ z                                        ≡⟨ rename-Var-≡ x₁≡z ⟩
          cast-Var _ y₁                                             ≡⟨ cast-Var-irrelevance ⟩
          cast-Var _ y₁                                             ≡⟨ sym cast-Var-cast-Var ⟩
          cast-Var _ (cast-Var _ y₁)                                ≡⟨ sym cast-Var-cast-Var ⟩
          cast-Var _ (cast-Var _ (cast-Var _ y₁))                   ≡⟨ sym $ cong (cast-Var _ ∘ cast-Var _) $ rename-Var-≡ x₁≡y₂ ⟩
          cast-Var _ (cast-Var _ (rename-Var x₁ y₁ y₂))             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≡ x₂≡y₁ ⟩
          cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
          rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

        lemma (yes [ x₁≡z ]) (no [ x₂≢z ])
              (yes [ x₂≡y₁ ]) (no [ x₁≢y₂ ]) =
          case hyp of λ where
            (inj₁ hyp) →
              ⊥-elim $ _↔_.to Erased-⊥↔⊥
                [ hyp (inj₂ (x₂≡y₁ , x₂≢z ∘ flip trans x₁≡z) , x₁≢y₂) ]
            (inj₂ hyp) →
              rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≢ x₂≢z ⟩
              rename-Var x₁ y₁ z                                        ≡⟨ rename-Var-≡ x₁≡z ⟩
              cast-Var _ y₁                                             ≡⟨ cast-Var-irrelevance ⟩
              cast-Var _ y₁                                             ≡⟨ sym cast-Var-cast-Var ⟩
              cast-Var _ (cast-Var _ y₁)                                ≡⟨ cong (cast-Var _) $ cast-Var-Σ-≡,≡←≡ hyp ⟩
              cast-Var _ y₂                                             ≡⟨ sym cast-Var-cast-Var ⟩
              cast-Var _ (cast-Var _ y₂)                                ≡⟨ sym $ cong (cast-Var _ ∘ cast-Var _) $ rename-Var-≢ x₁≢y₂ ⟩
              cast-Var _ (cast-Var _ (rename-Var x₁ y₁ y₂))             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≡ x₂≡y₁ ⟩
              cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
              rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
              rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

      mutual

        rename-Tm-swap :
          ∀ (tˢ : Tmˢ s) {t} →
          rename-Tm x₁ y₁ tˢ (rename-Tm x₂ y₂ tˢ t) ≡
          rename-Tm x₂ (rename-Var x₁ y₁ y₂) tˢ (rename-Tm x₁ y₁ tˢ t)
        rename-Tm-swap var        = rename-Var-swap
        rename-Tm-swap (op o asˢ) = rename-Args-swap asˢ

        rename-Args-swap :
          ∀ (asˢ : Argsˢ vs) {as} →
          rename-Args x₁ y₁ asˢ (rename-Args x₂ y₂ asˢ as) ≡
          rename-Args x₂ (rename-Var x₁ y₁ y₂) asˢ
            (rename-Args x₁ y₁ asˢ as)
        rename-Args-swap nil           = refl _
        rename-Args-swap (cons aˢ asˢ) =
          cong₂ _,_
            (rename-Arg-swap aˢ)
            (rename-Args-swap asˢ)

        rename-Arg-swap :
          ∀ (aˢ : Argˢ v) {a} →
          rename-Arg x₁ y₁ aˢ (rename-Arg x₂ y₂ aˢ a) ≡
          rename-Arg x₂ (rename-Var x₁ y₁ y₂) aˢ
            (rename-Arg x₁ y₁ aˢ a)
        rename-Arg-swap (nil tˢ)  = rename-Tm-swap tˢ
        rename-Arg-swap (cons aˢ) =
          cong₂ _,_
            rename-Var-swap
            (rename-Arg-swap aˢ)

  -- Nothing changes if a variable is renamed to itself.

  module _ {s′} {x : Var s′} where

    abstract

      @0 rename-Var-no-change : rename-Var x x y ≡ y
      rename-Var-no-change {y = y}
        with (_ , x) ≟∃V (_ , y)
      … | no  [ x≢y ] = refl _
      … | yes [ x≡y ] =
        cast-Var (cong proj₁ x≡y) x       ≡⟨ cast-Var-irrelevance ⟩
        cast-Var (proj₁ (Σ-≡,≡←≡ x≡y)) x  ≡⟨ cast-Var-Σ-≡,≡←≡ _ ⟩∎
        y                                 ∎

      mutual

        @0 rename-Tm-no-change :
          ∀ (tˢ : Tmˢ s) {t} →
          rename-Tm x x tˢ t ≡ t
        rename-Tm-no-change var        = rename-Var-no-change
        rename-Tm-no-change (op o asˢ) = rename-Args-no-change asˢ

        @0 rename-Args-no-change :
          ∀ (asˢ : Argsˢ vs) {as} →
          rename-Args x x asˢ as ≡ as
        rename-Args-no-change nil           = refl _
        rename-Args-no-change (cons aˢ asˢ) =
          cong₂ _,_
            (rename-Arg-no-change aˢ)
            (rename-Args-no-change asˢ)

        @0 rename-Arg-no-change :
          ∀ (aˢ : Argˢ v) {a} →
          rename-Arg x x aˢ a ≡ a
        rename-Arg-no-change (nil tˢ)  = rename-Tm-no-change tˢ
        rename-Arg-no-change (cons aˢ) =
          cong₂ _,_
            rename-Var-no-change
            (rename-Arg-no-change aˢ)

  ----------------------------------------------------------------------
  -- Free variables

  -- These functions return sets containing exactly the free
  -- variables.
  --
  -- Note that this code is not intended to be used at run-time.

  free-Var : ∀ {s} → Var s → Vars
  free-Var x = singleton (_ , x)

  mutual

    free-Tm : (tˢ : Tmˢ s) → Tm tˢ → Vars
    free-Tm var        x  = free-Var x
    free-Tm (op o asˢ) as = free-Args asˢ as

    free-Args : (asˢ : Argsˢ vs) → Args asˢ → Vars
    free-Args nil           _        = []
    free-Args (cons aˢ asˢ) (a , as) =
      free-Arg aˢ a ∪ free-Args asˢ as

    free-Arg : (aˢ : Argˢ v) → Arg aˢ → Vars
    free-Arg (nil tˢ)  t       = free-Tm tˢ t
    free-Arg (cons aˢ) (x , a) = del (_ , x) (free-Arg aˢ a)

  -- Some lemmas relating the set of free variables of a term to the
  -- set of free variables of the term after renaming.

  module _ {s} {x y : Var s} where

    abstract

      mutual

        @0 free-rename-⊆-Tm :
          ∀ (tˢ : Tmˢ s′) {t} →
          free-Tm tˢ (rename-Tm x y tˢ t) ⊆
          (_ , y) ∷ del (_ , x) (free-Tm tˢ t)
        free-rename-⊆-Tm var {t = z} p =
          p ∈ singleton (_ , rename-Var x y z)                 ↔⟨ ∈singleton≃ ⟩

          ∥ p ≡ (_ , rename-Var x y z) ∥                       ↔⟨ ∥∥-cong ≡,rename-Var≃′ ⟩

          p ≡ (_ , y) × (_ , x) ≡ (_ , z) ∥⊎∥
          p ≢ (_ , x) × p ≡ (_ , z)                            ↝⟨ proj₁ ∥⊎∥-cong Σ-map id ≡→∈∷ ⟩

          p ≡ (_ , y) ∥⊎∥ p ≢ (_ , x) × p ∈ singleton (_ , z)  ↔⟨ F.id ∥⊎∥-cong inverse (∈delete≃ merely-equal?-∃Var) ⟩

          p ≡ (_ , y) ∥⊎∥ p ∈ del (_ , x) (singleton (_ , z))  ↔⟨ inverse ∈∷≃ ⟩□

          p ∈ (_ , y) ∷ del (_ , x) (singleton (_ , z))        □

        free-rename-⊆-Tm (op o asˢ) = free-rename-⊆-Args asˢ

        @0 free-rename-⊆-Args :
          ∀ (asˢ : Argsˢ vs) {as} →
          free-Args asˢ (rename-Args x y asˢ as) ⊆
          (_ , y) ∷ del (_ , x) (free-Args asˢ as)
        free-rename-⊆-Args nil _ ()

        free-rename-⊆-Args (cons aˢ asˢ) {as = a , as} p =
          p ∈ free-Arg aˢ (rename-Arg x y aˢ a) ∪
              free-Args asˢ (rename-Args x y asˢ as)                    ↔⟨ ∈∪≃ ⟩

          p ∈ free-Arg aˢ (rename-Arg x y aˢ a) ∥⊎∥
          p ∈ free-Args asˢ (rename-Args x y asˢ as)                    ↝⟨ free-rename-⊆-Arg aˢ p ∥⊎∥-cong free-rename-⊆-Args asˢ p ⟩

          p ∈ (_ , y) ∷ del (_ , x) (free-Arg aˢ a) ∥⊎∥
          p ∈ (_ , y) ∷ del (_ , x) (free-Args asˢ as)                  ↔⟨ ∈∷≃ ∥⊎∥-cong ∈∷≃ ⟩

          (p ≡ (_ , y) ∥⊎∥ p ∈ del (_ , x) (free-Arg aˢ a)) ∥⊎∥
          (p ≡ (_ , y) ∥⊎∥ p ∈ del (_ , x) (free-Args asˢ as))          ↔⟨ inverse truncate-left-∥⊎∥ F.∘
                                                                           (Trunc.idempotent ∥⊎∥-cong F.id) F.∘
                                                                           ∥⊎∥-assoc F.∘
                                                                           (F.id
                                                                              ∥⊎∥-cong
                                                                            (inverse ∥⊎∥-assoc F.∘ (∥⊎∥-comm ∥⊎∥-cong F.id) F.∘ ∥⊎∥-assoc)) F.∘
                                                                           inverse ∥⊎∥-assoc ⟩
          p ≡ (_ , y) ∥⊎∥
          p ∈ del (_ , x) (free-Arg aˢ a) ∥⊎∥
          p ∈ del (_ , x) (free-Args asˢ as)                            ↔⟨ inverse $
                                                                           (F.id
                                                                              ∥⊎∥-cong
                                                                            (∈∪≃ F.∘
                                                                             ≡⇒↝ _ (cong (_ ∈_) $ delete-∪ merely-equal?-∃Var (free-Arg aˢ a)))) F.∘
                                                                           ∈∷≃ ⟩□
          p ∈ (_ , y) ∷ del (_ , x) (free-Arg aˢ a ∪ free-Args asˢ as)  □

        @0 free-rename-⊆-Arg :
          ∀ (aˢ : Argˢ v) {a} →
          free-Arg aˢ (rename-Arg x y aˢ a) ⊆
          (_ , y) ∷ del (_ , x) (free-Arg aˢ a)
        free-rename-⊆-Arg (nil tˢ) = free-rename-⊆-Tm tˢ

        free-rename-⊆-Arg (cons aˢ) {a = z , a} p =
          p ∈ del (_ , rename-Var x y z)
                (free-Arg aˢ (rename-Arg x y aˢ a))                ↔⟨ ∈delete≃ merely-equal?-∃Var ⟩

          p ≢ (_ , rename-Var x y z) ×
          p ∈ free-Arg aˢ (rename-Arg x y aˢ a)                    ↝⟨ Σ-map id (free-rename-⊆-Arg aˢ p) ⟩

          p ≢ (_ , rename-Var x y z) ×
          p ∈ (_ , y) ∷ del (_ , x) (free-Arg aˢ a)                ↔⟨ F.id ×-cong ∈∷≃ ⟩

          p ≢ (_ , rename-Var x y z) ×
          (p ≡ (_ , y) ∥⊎∥
           p ∈ del (_ , x) (free-Arg aˢ a))                        ↔⟨ (Π⊎↔Π×Π ext F.∘ →-cong₁ ext ≡,rename-Var≃) ×-cong Eq.id ⟩

          (¬ (((_ , x) ≡ (_ , z)) × p ≡ (_ , y)) ×
           ¬ (((_ , x) ≢ (_ , z)) × p ≡ (_ , z))) ×
          (p ≡ (_ , y) ∥⊎∥
           p ∈ del (_ , x) (free-Arg aˢ a))                        ↝⟨ (uncurry λ (_ , hyp) → id ∥⊎∥-cong λ u∈ → lemma hyp u∈ , u∈) ⟩

          p ≡ (_ , y) ∥⊎∥
          p ≢ (_ , z) ×
          p ∈ del (_ , x) (free-Arg aˢ a)                          ↔⟨ inverse $ (F.id ∥⊎∥-cong ∈delete≃ merely-equal?-∃Var) F.∘ ∈∷≃ ⟩

          p ∈ (_ , y) ∷ del (_ , z) (del (_ , x) (free-Arg aˢ a))  ↔⟨ ≡⇒↝ equivalence $ cong (λ x → p ∈ (_ , y) ∷ x) $
                                                                      delete-comm merely-equal?-∃Var (free-Arg aˢ a) ⟩□
          p ∈ (_ , y) ∷ del (_ , x) (del (_ , z) (free-Arg aˢ a))  □
          where
          lemma :
            ¬ (((_ , x) ≢ (_ , z)) × p ≡ (_ , z)) →
            p ∈ del (_ , x) (free-Arg aˢ a) →
            p ≢ (_ , z)
          lemma hyp p∈ =
            p ≡ (_ , z)                        ↝⟨ (λ eq → eq , hyp ∘ (_, eq)) ⟩
            p ≡ (_ , z) × ¬ (_ , x) ≢ (_ , z)  ↝⟨ Σ-map id (λ eq → case (_ ≟∃V _) of [ erased , ⊥-elim ∘ eq ∘ erased ]′) ⟩
            p ≡ (_ , z) × (_ , x) ≡ (_ , z)    ↝⟨ (uncurry λ eq₁ eq₂ → trans eq₁ (sym eq₂)) ⟩
            p ≡ (_ , x)                        ↝⟨ proj₁ (_≃_.to (∈delete≃ {z = free-Arg aˢ a} merely-equal?-∃Var) p∈) ⟩□
            ⊥                                  □

      mutual

        @0 ⊆-free-rename-Tm :
          ∀ (tˢ : Tmˢ s′) {t} →
          free-Tm tˢ t ⊆
          (_ , x) ∷ (_ , y) ∷ free-Tm tˢ (rename-Tm x y tˢ t)
        ⊆-free-rename-Tm var {t = z} p =
          p ∈ singleton (_ , z)                                           ↔⟨ ∈singleton≃ ⟩

          ∥ p ≡ (_ , z) ∥                                                 ↝⟨ (Trunc.rec ∥⊎∥-propositional λ p≡z → case p ≟∃V (_ , x) of
                                                                                [ ∣inj₁∣ ∘ erased
                                                                                , ∣inj₂∣ ∘ ∣inj₂∣ ∘ ∣inj₂∣ ∘ (_, p≡z) ∘ erased
                                                                                ]′) ⟩
          p ≡ (_ , x) ∥⊎∥ p ≡ (_ , y) ∥⊎∥
          (p ≡ (_ , y) × (_ , x) ≡ (_ , z) ∥⊎∥
           p ≢ (_ , x) × p ≡ (_ , z))                                     ↔⟨ inverse $ F.id ∥⊎∥-cong F.id ∥⊎∥-cong ∥∥-cong ≡,rename-Var≃′ ⟩

          p ≡ (_ , x) ∥⊎∥ p ≡ (_ , y) ∥⊎∥ ∥ p ≡ (_ , rename-Var x y z) ∥  ↔⟨ inverse $
                                                                             (F.id ∥⊎∥-cong (F.id ∥⊎∥-cong ∈singleton≃) F.∘ ∈∷≃) F.∘ ∈∷≃ ⟩□
          p ∈ (_ , x) ∷ (_ , y) ∷ singleton (_ , rename-Var x y z)        □

        ⊆-free-rename-Tm (op o asˢ) = ⊆-free-rename-Args asˢ

        @0 ⊆-free-rename-Args :
          ∀ (asˢ : Argsˢ vs) {as} →
          free-Args asˢ as ⊆
          (_ , x) ∷ (_ , y) ∷ free-Args asˢ (rename-Args x y asˢ as)
        ⊆-free-rename-Args nil _ ()

        ⊆-free-rename-Args (cons aˢ asˢ) {as = a , as} p =
          p ∈ free-Arg aˢ a ∪ free-Args asˢ as                            ↔⟨ ∈∪≃ ⟩

          p ∈ free-Arg aˢ a ∥⊎∥ p ∈ free-Args asˢ as                      ↝⟨ ⊆-free-rename-Arg aˢ p ∥⊎∥-cong ⊆-free-rename-Args asˢ p ⟩

          p ∈ (_ , x) ∷ (_ , y) ∷ free-Arg aˢ (rename-Arg x y aˢ a) ∥⊎∥
          p ∈ (_ , x) ∷ (_ , y) ∷ free-Args asˢ (rename-Args x y asˢ as)  ↔⟨ inverse $
                                                                             ∈∪≃ F.∘
                                                                             ≡⇒↝ _ (cong (p ∈_) $
                                                                                    ∪-distrib-left {y = free-Arg aˢ (rename-Arg x y aˢ a)}
                                                                                                   ((_ , x) ∷ (_ , y) ∷ [])) ⟩□
          p ∈ (_ , x) ∷ (_ , y) ∷
              free-Arg aˢ (rename-Arg x y aˢ a) ∪
              free-Args asˢ (rename-Args x y asˢ as)                      □

        @0 ⊆-free-rename-Arg :
          ∀ (aˢ : Argˢ v) {a} →
          free-Arg aˢ a ⊆
          (_ , x) ∷ (_ , y) ∷ free-Arg aˢ (rename-Arg x y aˢ a)
        ⊆-free-rename-Arg (nil tˢ) = ⊆-free-rename-Tm tˢ

        ⊆-free-rename-Arg (cons aˢ) {a = z , a} p =
          p ∈ del (_ , z) (free-Arg aˢ a)            ↔⟨ ∈delete≃ merely-equal?-∃Var ⟩

          p ≢ (_ , z) × p ∈ free-Arg aˢ a            ↝⟨ Σ-map id (⊆-free-rename-Arg aˢ p) ⟩

          p ≢ (_ , z) ×
          p ∈ (_ , x) ∷ (_ , y) ∷
              free-Arg aˢ (rename-Arg x y aˢ a)      ↔⟨ F.id ×-cong (F.id ∥⊎∥-cong ∈∷≃) F.∘ ∈∷≃ ⟩

          p ≢ (_ , z) ×
          (p ≡ (_ , x) ∥⊎∥ p ≡ (_ , y) ∥⊎∥
           p ∈ free-Arg aˢ (rename-Arg x y aˢ a))    ↝⟨ case p ≟∃V (_ , y) of
                                                          [ (λ ([ p≡y ]) _ → ∣inj₂∣ (∣inj₁∣ p≡y))
                                                          , (λ ([ p≢y ]) → uncurry λ p≢z → id ∥⊎∥-cong id ∥⊎∥-cong (lemma p≢y p≢z ,_))
                                                          ]′ ⟩
          p ≡ (_ , x) ∥⊎∥ p ≡ (_ , y) ∥⊎∥
          p ≢ (_ , rename-Var x y z) ×
          p ∈ free-Arg aˢ (rename-Arg x y aˢ a)      ↔⟨ inverse $ (F.id ∥⊎∥-cong (F.id ∥⊎∥-cong ∈delete≃ merely-equal?-∃Var) F.∘ ∈∷≃) F.∘ ∈∷≃ ⟩□

          p ∈ (_ , x) ∷ (_ , y) ∷
              del (_ , rename-Var x y z)
                (free-Arg aˢ (rename-Arg x y aˢ a))  □
          where
          lemma : p ≢ (_ , y) → p ≢ (_ , z) → p ≢ (_ , rename-Var x y z)
          lemma p≢y p≢z =
            p ≡ (_ , rename-Var x y z)         ↔⟨ ≡,rename-Var≃ ⟩

            (_ , x) ≡ (_ , z) × p ≡ (_ , y) ⊎
            (_ , x) ≢ (_ , z) × p ≡ (_ , z)    ↝⟨ p≢y ∘ proj₂ ⊎-cong p≢z ∘ proj₂ ⟩

            ⊥ ⊎ ⊥                              ↔⟨ ⊎-right-identity ⟩□

            ⊥                                  □

  -- An alternative definition of what it means for a variable to be
  -- free in a term.
  --
  -- This definition is based on Harper's.

  module _ {s} (x : Var s) where

    Free-in-var′ :
      ∀ {s′} → Var s′ →
      ∃ λ (A : Type ℓ) → Erased (Is-proposition A)
    Free-in-var′ y =
        _≡_ {A = ∃Var} (_ , x) (_ , y)
      , [ ∃Var-set ]

    mutual

      Free-in-term′ :
        ∀ (tˢ : Tmˢ s′) t →
        @0 Wf-tm ((_ , x) ∷ xs) tˢ t →
        ∃ λ (A : Type ℓ) → Erased (Is-proposition A)
      Free-in-term′ var y _ = Free-in-var′ y

      Free-in-term′ (op o asˢ) as wf =
        Free-in-arguments′ asˢ as wf

      Free-in-arguments′ :
        ∀ (asˢ : Argsˢ vs) as →
        @0 Wf-args ((_ , x) ∷ xs) asˢ as →
        ∃ λ (A : Type ℓ) → Erased (Is-proposition A)
      Free-in-arguments′ nil _ _ = ⊥ , [ ⊥-propositional ]

      Free-in-arguments′ (cons aˢ asˢ) (a , as) (wf , wfs) =
          (proj₁ (Free-in-argument′ aˢ a wf) ∥⊎∥
           proj₁ (Free-in-arguments′ asˢ as wfs))
        , [ ∥⊎∥-propositional ]

      Free-in-argument′ :
        ∀ (aˢ : Argˢ v) a →
        @0 Wf-arg ((_ , x) ∷ xs) aˢ a →
        ∃ λ (A : Type ℓ) → Erased (Is-proposition A)
      Free-in-argument′ (nil tˢ) t wf = Free-in-term′ tˢ t wf

      Free-in-argument′ {xs = xs} (cons aˢ) (y , a) wf =
        Π _ λ z → Π (Erased (¬ (_ , z) ∈ (_ , x) ∷ xs)) λ ([ z∉ ]) →
        Free-in-argument′
          aˢ
          (rename-Arg y z aˢ a)
          (subst (λ xs → Wf-arg xs aˢ (rename-Arg y z aˢ a))
                 swap
                 (wf z z∉))
        where
        Π :
          (A : Type ℓ) →
          (A → ∃ λ (B : Type ℓ) → Erased (Is-proposition B)) →
          ∃ λ (B : Type ℓ) → Erased (Is-proposition B)
        Π A B =
            (∀ x → proj₁ (B x))
          , [ (Π-closure ext 1 λ x →
               erased (proj₂ (B x)))
            ]

    Free-in-variable : ∀ {s′} → Variable ((_ , x) ∷ xs) s′ → Type ℓ
    Free-in-variable (y , _) = proj₁ (Free-in-var′ y)

    Free-in-term : Term ((_ , x) ∷ xs) s′ → Type ℓ
    Free-in-term (t , tˢ , [ wf ]) =
      proj₁ (Free-in-term′ t tˢ wf)

    Free-in-arguments : Arguments ((_ , x) ∷ xs) vs → Type ℓ
    Free-in-arguments (as , asˢ , [ wfs ]) =
      proj₁ (Free-in-arguments′ as asˢ wfs)

    Free-in-argument : Argument ((_ , x) ∷ xs) v → Type ℓ
    Free-in-argument (a , aˢ , [ wf ]) =
      proj₁ (Free-in-argument′ a aˢ wf)

  -- The alternative definition of what it means for a variable to be
  -- free in a term is propositional (in erased contexts).

  module _ {s} {x : Var s} where

    abstract

      @0 Free-in-variable-propositional :
        ∀ {s′} (y : Variable ((_ , x) ∷ xs) s′) →
        Is-proposition (Free-in-variable x y)
      Free-in-variable-propositional (y , _) =
        erased (proj₂ (Free-in-var′ _ y))

      @0 Free-in-term-propositional :
        (t : Term ((_ , x) ∷ xs) s′) →
        Is-proposition (Free-in-term x t)
      Free-in-term-propositional (t , tˢ , [ wf ]) =
        erased (proj₂ (Free-in-term′ _ t tˢ wf))

      @0 Free-in-arguments-propositional :
        (as : Arguments ((_ , x) ∷ xs) vs) →
        Is-proposition (Free-in-arguments x as)
      Free-in-arguments-propositional (as , asˢ , [ wfs ]) =
        erased (proj₂ (Free-in-arguments′ _ as asˢ wfs))

      @0 Free-in-argument-propositional :
        (a : Argument ((_ , x) ∷ xs) v) →
        Is-proposition (Free-in-argument x a)
      Free-in-argument-propositional (a , aˢ , [ wf ]) =
        erased (proj₂ (Free-in-argument′ _ a aˢ wf))

  abstract

    -- Variables that are free according to the alternative definition
    -- are in the set of free variables (in erased contexts).

    Free-free-Var :
      ∀ {s s′} {x : Var s} {y : Var s′}
      (@0 wf : Wf-var ((_ , x) ∷ xs) y) →
      Free-in-variable x (y , [ wf ]) → (_ , x) ∈ free-Var y
    Free-free-Var _ = ≡→∈singleton

    mutual

      @0 Free-free-Tm :
        ∀ {s} {x : Var s} {xs}
        (tˢ : Tmˢ s′) {t} (wf : Wf-tm ((_ , x) ∷ xs) tˢ t) →
        Free-in-term x (tˢ , t , [ wf ]) → (_ , x) ∈ free-Tm tˢ t
      Free-free-Tm var        wf  = Free-free-Var wf
      Free-free-Tm (op o asˢ) wfs = Free-free-Args asˢ wfs

      @0 Free-free-Args :
        ∀ {s} {x : Var s} {xs}
        (asˢ : Argsˢ vs) {as} (wfs : Wf-args ((_ , x) ∷ xs) asˢ as) →
        Free-in-arguments x (asˢ , as , [ wfs ]) →
        (_ , x) ∈ free-Args asˢ as
      Free-free-Args {x = x} (cons aˢ asˢ) {as = a , as} (wf , wfs) =
        Free-in-argument x (aˢ , a , [ wf ]) ∥⊎∥
        Free-in-arguments x (asˢ , as , [ wfs ])                ↝⟨ Free-free-Arg aˢ wf ∥⊎∥-cong Free-free-Args asˢ wfs ⟩

        (_ , x) ∈ free-Arg aˢ a ∥⊎∥ (_ , x) ∈ free-Args asˢ as  ↔⟨ inverse ∈∪≃ ⟩□

        (_ , x) ∈ free-Arg aˢ a ∪ free-Args asˢ as              □

      @0 Free-free-Arg :
        ∀ {s} {x : Var s} {xs}
        (aˢ : Argˢ v) {a} (wf : Wf-arg ((_ , x) ∷ xs) aˢ a) →
        Free-in-argument x (aˢ , a , [ wf ]) → (_ , x) ∈ free-Arg aˢ a
      Free-free-Arg (nil tˢ) = Free-free-Tm tˢ

      Free-free-Arg {x = x} {xs = xs} (cons aˢ) {a = y , a} wf =
        let xxs              = (_ , x) ∷ xs
            x₁ ,         x₁∉ = fresh-not-erased xxs
            x₂ , x₂≢x₁ , x₂∉ =                                       $⟨ fresh-not-erased ((_ , x₁) ∷ xxs) ⟩
              (∃ λ x₂ → ¬ (_ , x₂) ∈ (_ , x₁) ∷ xxs)                 ↝⟨ (∃-cong λ _ → →-cong₁ ext ∈∷≃) ⟩
              (∃ λ x₂ → ¬ ((_ , x₂) ≡ (_ , x₁) ∥⊎∥ (_ , x₂) ∈ xxs))  ↝⟨ (∃-cong λ _ → Π∥⊎∥↔Π×Π λ _ → ⊥-propositional) ⟩□
              (∃ λ x₂ → (_ , x₂) ≢ (_ , x₁) × ¬ (_ , x₂) ∈ xxs)      □
        in
        (∀ z (z∉ : Erased (¬ (_ , z) ∈ (_ , x) ∷ xs)) →
         Free-in-argument x
           ( aˢ
           , rename-Arg y z aˢ a
           , [ subst (λ xs → Wf-arg xs aˢ (rename-Arg y z aˢ a))
                     swap
                     (wf z (erased z∉)) ]
           ))                                                 ↝⟨ (λ hyp z z∉ → Free-free-Arg
                                                                                 aˢ
                                                                                 (subst (λ xs → Wf-arg xs aˢ (rename-Arg y z aˢ a))
                                                                                        swap
                                                                                        (wf z z∉))
                                                                                 (hyp z [ z∉ ])) ⟩
        (∀ z → ¬ (_ , z) ∈ (_ , x) ∷ xs →
         (_ , x) ∈ free-Arg aˢ (rename-Arg y z aˢ a))         ↝⟨ (λ hyp z z∉ → free-rename-⊆-Arg aˢ _ (hyp z z∉)) ⦂ (_ → _) ⟩

        (∀ z → ¬ (_ , z) ∈ (_ , x) ∷ xs →
         (_ , x) ∈ (_ , z) ∷ fs)                              ↝⟨ (λ hyp → hyp x₁ x₁∉ , hyp x₂ x₂∉) ⟩

        (_ , x) ∈ (_ , x₁) ∷ fs ×
        (_ , x) ∈ (_ , x₂) ∷ fs                               ↔⟨ ∈∷≃ ×-cong ∈∷≃ ⟩

        ((_ , x) ≡ (_ , x₁) ∥⊎∥ (_ , x) ∈ fs) ×
        ((_ , x) ≡ (_ , x₂) ∥⊎∥ (_ , x) ∈ fs)                 ↔⟨ (Σ-∥⊎∥-distrib-right (λ _ → ∃Var-set) ∥⊎∥-cong F.id) F.∘
                                                                 Σ-∥⊎∥-distrib-left ∥⊎∥-propositional ⟩
        ((_ , x) ≡ (_ , x₁) × (_ , x) ≡ (_ , x₂) ∥⊎∥
         (_ , x) ∈ fs × (_ , x) ≡ (_ , x₂)) ∥⊎∥
        ((_ , x) ≡ (_ , x₁) ∥⊎∥ (_ , x) ∈ fs) × (_ , x) ∈ fs  ↝⟨ ((λ (y≡x₁ , y≡x₂) → x₂≢x₁ (trans (sym y≡x₂) y≡x₁)) ∥⊎∥-cong proj₁) ∥⊎∥-cong proj₂ ⟩

        (⊥ ∥⊎∥ (_ , x) ∈ fs) ∥⊎∥ (_ , x) ∈ fs                 ↔⟨ ∥⊎∥-idempotent ∈-propositional F.∘
                                                                 (∥⊎∥-left-identity ∈-propositional ∥⊎∥-cong F.id) ⟩□
        (_ , x) ∈ fs                                          □
        where
        fs = del (_ , y) (free-Arg aˢ a)

    -- Every member of the set of free variables is free according to
    -- the alternative definition (in erased contexts).

    @0 free-Free-Var :
      ∀ {s′ s} {x : Var s′} {y : Var s}
      (wf : Wf-var ((_ , x) ∷ xs) y) →
      (_ , x) ∈ free-Var y → Free-in-variable x (y , [ wf ])
    free-Free-Var {x = x} {y = y} _ =
      (_ , x) ∈ singleton (_ , y)  ↔⟨ ∈singleton≃ ⟩
      ∥ (_ , x) ≡ (_ , y) ∥        ↔⟨ ∥∥↔ ∃Var-set ⟩□
      (_ , x) ≡ (_ , y)            □

    mutual

      @0 free-Free-Tm :
        ∀ {s′} {x : Var s′} {xs}
        (tˢ : Tmˢ s) {t} (wf : Wf-tm ((_ , x) ∷ xs) tˢ t) →
        (_ , x) ∈ free-Tm tˢ t → Free-in-term x (tˢ , t , [ wf ])
      free-Free-Tm var        = free-Free-Var
      free-Free-Tm (op o asˢ) = free-Free-Args asˢ

      @0 free-Free-Args :
        ∀ {s′} {x : Var s′} {xs}
        (asˢ : Argsˢ vs) {as} (wf : Wf-args ((_ , x) ∷ xs) asˢ as) →
        (_ , x) ∈ free-Args asˢ as →
        Free-in-arguments x (asˢ , as , [ wf ])
      free-Free-Args
        {x = x} (cons aˢ asˢ) {as = a , as} (wf , wfs) =

        (_ , x) ∈ free-Arg aˢ a ∪ free-Args asˢ as              ↔⟨ ∈∪≃ ⟩

        (_ , x) ∈ free-Arg aˢ a ∥⊎∥ (_ , x) ∈ free-Args asˢ as  ↝⟨ free-Free-Arg aˢ wf ∥⊎∥-cong free-Free-Args asˢ wfs ⟩□

        Free-in-argument x (aˢ , a , [ wf ]) ∥⊎∥
        Free-in-arguments x (asˢ , as , [ wfs ])                □

      @0 free-Free-Arg :
        ∀ {s′} {x : Var s′} {xs}
        (aˢ : Argˢ v) {a} (wf : Wf-arg ((_ , x) ∷ xs) aˢ a) →
        (_ , x) ∈ free-Arg aˢ a → Free-in-argument x (aˢ , a , [ wf ])
      free-Free-Arg (nil tˢ) = free-Free-Tm tˢ

      free-Free-Arg {x = x} {xs = xs} (cons aˢ) {a = y , a} wf =
        (_ , x) ∈ del (_ , y) (free-Arg aˢ a)                     ↔⟨ ∈delete≃ merely-equal?-∃Var ⟩

        (_ , x) ≢ (_ , y) × (_ , x) ∈ free-Arg aˢ a               ↝⟨ Σ-map id (λ x∈ _ → ⊆-free-rename-Arg aˢ _ x∈) ⟩

        (_ , x) ≢ (_ , y) ×
        (∀ z → (_ , x) ∈ (_ , y) ∷ (_ , z) ∷
                         free-Arg aˢ (rename-Arg y z aˢ a))       ↝⟨ (uncurry λ x≢y →
                                                                      ∀-cong _ λ _ x∈ z∉ →
                                                                      to-implication (∈≢∷≃ (z∉ ∘ ≡→∈∷ ∘ sym) F.∘ ∈≢∷≃ x≢y) x∈) ⟩
        (∀ z → ¬ (_ , z) ∈ (_ , x) ∷ xs →
               (_ , x) ∈ free-Arg aˢ (rename-Arg y z aˢ a))       ↝⟨ (λ x∈ z z∉ → free-Free-Arg aˢ
                                                                                    (subst (λ xs → Wf-arg xs aˢ (rename-Arg y z aˢ a))
                                                                                           swap
                                                                                           (wf z (erased z∉)))
                                                                                    (x∈ z (Stable-¬ _ z∉))) ⟩□
        (∀ z (z∉ : Erased (¬ (_ , z) ∈ (_ , x) ∷ xs)) →
         Free-in-argument x
           ( aˢ
           , rename-Arg y z aˢ a
           , [ subst (λ xs → Wf-arg xs aˢ (rename-Arg y z aˢ a))
                     swap
                     (wf z (erased z∉)) ]
           ))                                                     □

  ----------------------------------------------------------------------
  -- Lemmas related to the Wf predicates

  abstract

    -- Weakening of the Wf predicates.

    @0 weaken-Wf-var : xs ⊆ ys → Wf-var xs x → Wf-var ys x
    weaken-Wf-var xs⊆ys = xs⊆ys _

    mutual

      @0 weaken-Wf-tm :
        xs ⊆ ys → ∀ (tˢ : Tmˢ s) {t} →
        Wf-tm xs tˢ t → Wf-tm ys tˢ t
      weaken-Wf-tm xs⊆ys var        = weaken-Wf-var xs⊆ys
      weaken-Wf-tm xs⊆ys (op o asˢ) = weaken-Wf-args xs⊆ys asˢ

      @0 weaken-Wf-args :
        xs ⊆ ys → ∀ (asˢ : Argsˢ vs) {as} →
        Wf-args xs asˢ as → Wf-args ys asˢ as
      weaken-Wf-args xs⊆ys nil           = id
      weaken-Wf-args xs⊆ys (cons aˢ asˢ) =
        Σ-map (weaken-Wf-arg xs⊆ys aˢ)
              (weaken-Wf-args xs⊆ys asˢ)

      @0 weaken-Wf-arg :
        xs ⊆ ys → ∀ (aˢ : Argˢ v) {a} →
        Wf-arg xs aˢ a → Wf-arg ys aˢ a
      weaken-Wf-arg xs⊆ys (nil tˢ)  = weaken-Wf-tm xs⊆ys tˢ
      weaken-Wf-arg xs⊆ys (cons aˢ) =
        λ wf y y∉ys →
          weaken-Wf-arg (∷-cong-⊆ xs⊆ys) aˢ (wf y (y∉ys ∘ xs⊆ys _))

    -- A term is well-formed for its set of free variables.

    mutual

      @0 wf-free-Tm :
        ∀ (tˢ : Tmˢ s) {t} → Wf-tm (free-Tm tˢ t) tˢ t
      wf-free-Tm var        = ≡→∈∷ (refl _)
      wf-free-Tm (op o asˢ) = wf-free-Args asˢ

      @0 wf-free-Args :
        ∀ (asˢ : Argsˢ vs) {as} →
        Wf-args (free-Args asˢ as) asˢ as
      wf-free-Args nil           = _
      wf-free-Args (cons aˢ asˢ) =
          weaken-Wf-arg (λ _ → ∈→∈∪ˡ) aˢ (wf-free-Arg aˢ)
        , weaken-Wf-args (λ _ → ∈→∈∪ʳ (free-Arg aˢ _))
                         asˢ (wf-free-Args asˢ)

      @0 wf-free-Arg :
        ∀ (aˢ : Argˢ v) {a : Arg aˢ} → Wf-arg (free-Arg aˢ a) aˢ a
      wf-free-Arg (nil tˢ)              = wf-free-Tm tˢ
      wf-free-Arg (cons aˢ) {a = x , a} = λ y y∉ →
                                                        $⟨ wf-free-Arg aˢ ⟩
        Wf-arg (free-Arg aˢ (rename-Arg x y aˢ a))
          aˢ (rename-Arg x y aˢ a)                      ↝⟨ weaken-Wf-arg (free-rename-⊆-Arg aˢ) aˢ ⟩□

        Wf-arg ((_ , y) ∷ del (_ , x) (free-Arg aˢ a))
          aˢ (rename-Arg x y aˢ a)                      □

    -- If a term is well-formed with respect to a set of variables xs,
    -- then xs is a superset of the term's set of free variables.

    mutual

      @0 free-⊆-Tm :
        ∀ (tˢ : Tmˢ s) {t} → Wf-tm xs tˢ t → free-Tm tˢ t ⊆ xs
      free-⊆-Tm {xs = xs} var {t = x} wf y =
        y ∈ singleton (_ , x)  ↔⟨ ∈singleton≃ ⟩
        ∥ y ≡ (_ , x) ∥        ↔⟨ ∥∥↔ ∃Var-set ⟩
        y ≡ (_ , x)            ↝⟨ (λ eq → subst (_∈ xs) (sym eq) wf) ⟩□
        y ∈ xs                 □
      free-⊆-Tm (op o asˢ) = free-⊆-Args asˢ

      @0 free-⊆-Args :
        ∀ (asˢ : Argsˢ vs) {as} →
        Wf-args xs asˢ as → free-Args asˢ as ⊆ xs
      free-⊆-Args           nil           _          _ = λ ()
      free-⊆-Args {xs = xs} (cons aˢ asˢ) (wf , wfs) y =
        y ∈ free-Arg aˢ _ ∪ free-Args asˢ _        ↔⟨ ∈∪≃ ⟩
        y ∈ free-Arg aˢ _ ∥⊎∥ y ∈ free-Args asˢ _  ↝⟨ free-⊆-Arg aˢ wf y ∥⊎∥-cong free-⊆-Args asˢ wfs y ⟩
        y ∈ xs ∥⊎∥ y ∈ xs                          ↔⟨ ∥⊎∥-idempotent ∈-propositional ⟩□
        y ∈ xs                                     □

      @0 free-⊆-Arg :
        ∀ (aˢ : Argˢ v) {a} → Wf-arg xs aˢ a → free-Arg aˢ a ⊆ xs
      free-⊆-Arg (nil tˢ) = free-⊆-Tm tˢ

      free-⊆-Arg {xs = xs} (cons {s = s} aˢ) {a = x , a} wf y =
        y ∈ del (_ , x) (free-Arg aˢ a)  ↔⟨ ∈delete≃ merely-equal?-∃Var ⟩
        y ≢ (_ , x) × y ∈ free-Arg aˢ a  ↝⟨ uncurry lemma ⟩□
        y ∈ xs                           □
        where
        lemma : y ≢ (_ , x) → _
        lemma y≢x =
          let fs               = free-Arg aˢ a
              x₁ ,         x₁∉ = fresh-not-erased (xs ∪ fs)
              x₂ , x₂≢x₁ , x₂∉ =                                       $⟨ fresh-not-erased ((_ , x₁) ∷ xs ∪ fs) ⟩
                (∃ λ x₂ → ¬ (_ , x₂) ∈ (_ , x₁) ∷ xs ∪ fs)             ↝⟨ (∃-cong λ _ → →-cong₁ ext ∈∷≃) ⟩
                (∃ λ x₂ →
                   ¬ ((_ , x₂) ≡ (_ , x₁) ∥⊎∥ (_ , x₂) ∈ xs ∪ fs))     ↝⟨ (∃-cong λ _ → Π∥⊎∥↔Π×Π λ _ → ⊥-propositional) ⟩□
                (∃ λ x₂ → (_ , x₂) ≢ (_ , x₁) × ¬ (_ , x₂) ∈ xs ∪ fs)  □
          in
          y ∈ free-Arg aˢ a                                            ↝⟨ (λ y∈ _ z∉ → (λ y≡z → z∉ (subst (_∈ _) y≡z y∈))
                                                                                     , ⊆-free-rename-Arg aˢ _ y∈) ⟩
          (∀ z → ¬ (_ , z) ∈ free-Arg aˢ a →
           y ≢ (_ , z) ×
           y ∈ (_ , x) ∷ (_ , z) ∷ free-Arg aˢ (rename-Arg x z aˢ a))  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → uncurry λ y≢z →
                                                                           to-implication (∈≢∷≃ y≢z F.∘ ∈≢∷≃ y≢x)) ⟩
          (∀ z → ¬ (_ , z) ∈ free-Arg aˢ a →
           y ∈ free-Arg aˢ (rename-Arg x z aˢ a))                      ↝⟨ (λ hyp →
                                                                               free-⊆-Arg aˢ (wf x₁ (x₁∉ ∘ ∈→∈∪ˡ)) y (hyp x₁ (x₁∉ ∘ ∈→∈∪ʳ xs))
                                                                             , free-⊆-Arg aˢ (wf x₂ (x₂∉ ∘ ∈→∈∪ˡ)) y (hyp x₂ (x₂∉ ∘ ∈→∈∪ʳ xs))) ⟩

          y ∈ (_ , x₁) ∷ xs × y ∈ (_ , x₂) ∷ xs                        ↔⟨ ∈∷≃ ×-cong ∈∷≃ ⟩

          (y ≡ (_ , x₁) ∥⊎∥ y ∈ xs) ×
          (y ≡ (_ , x₂) ∥⊎∥ y ∈ xs)                                    ↔⟨ (Σ-∥⊎∥-distrib-right (λ _ → ∃Var-set) ∥⊎∥-cong F.id) F.∘
                                                                          Σ-∥⊎∥-distrib-left ∥⊎∥-propositional ⟩
          (y ≡ (_ , x₁) × y ≡ (_ , x₂) ∥⊎∥ y ∈ xs × y ≡ (_ , x₂)) ∥⊎∥
          (y ≡ (_ , x₁) ∥⊎∥ y ∈ xs) × y ∈ xs                           ↝⟨ ((λ (y≡x₁ , y≡x₂) → x₂≢x₁ (trans (sym y≡x₂) y≡x₁)) ∥⊎∥-cong proj₁)
                                                                            ∥⊎∥-cong
                                                                          proj₂ ⟩

          (⊥ ∥⊎∥ y ∈ xs) ∥⊎∥ y ∈ xs                                    ↔⟨ ∥⊎∥-idempotent ∈-propositional F.∘
                                                                          (∥⊎∥-left-identity ∈-propositional ∥⊎∥-cong F.id) ⟩□
          y ∈ xs                                                       □

    private

      -- A lemma used to prove strengthening below.

      ∉→⊆∷→⊆ :
        ∀ {x : ∃Var} {xs ys : Vars} →
        ¬ x ∈ xs → xs ⊆ x ∷ ys → xs ⊆ ys
      ∉→⊆∷→⊆ {x = x} {xs = xs} {ys = ys} x∉ xs⊆x∷ys z =
        z ∈ xs              ↝⟨ (λ z∈ → x∉ ∘ flip (subst (_∈ _)) z∈ , z∈) ⟩
        z ≢ x × z ∈ xs      ↝⟨ Σ-map id (xs⊆x∷ys _) ⟩
        z ≢ x × z ∈ x ∷ ys  ↔⟨ ∃-cong ∈≢∷≃ ⟩
        z ≢ x × z ∈ ys      ↝⟨ proj₂ ⟩□
        z ∈ ys              □

    -- Strengthening of the Wf predicates.

    @0 strengthen-Wf-var :
      ¬ (_ , x) ∈ singleton {A = ∃Var} (_ , y) →
      Wf-var ((_ , x) ∷ xs) y → Wf-var xs y
    strengthen-Wf-var {x = x} {y = y} {xs = xs} x∉ =
      (_ , y) ∈ (_ , x) ∷ xs                        ↔⟨ ∈∷≃ ⟩
      (_ , y) ≡ (_ , x) ∥⊎∥ (_ , y) ∈ xs            ↔⟨ ≡-comm ∥⊎∥-cong F.id ⟩
      (_ , x) ≡ (_ , y) ∥⊎∥ (_ , y) ∈ xs            ↝⟨ ≡→∈singleton ∥⊎∥-cong id ⟩
      (_ , x) ∈ singleton (_ , y) ∥⊎∥ (_ , y) ∈ xs  ↔⟨ drop-⊥-left-∥⊎∥ ∈-propositional x∉ ⟩□
      (_ , y) ∈ xs                                  □

    -- TODO: It might be possible to avoid the code duplication seen
    -- below (and elsewhere) by using a simple universe.

    @0 strengthen-Wf-tm :
      ∀ (tˢ : Tmˢ s) {t} →
      ¬ (_ , x) ∈ free-Tm tˢ t →
      Wf-tm ((_ , x) ∷ xs) tˢ t → Wf-tm xs tˢ t
    strengthen-Wf-tm {x = x} {xs = xs} tˢ {t = t} x∉ =
      Wf-tm ((_ , x) ∷ xs) tˢ t                      ↝⟨ free-⊆-Tm tˢ ⟩
      free-Tm tˢ t ⊆ (_ , x) ∷ xs                    ↝⟨ ∉→⊆∷→⊆ x∉ ⟩
      free-Tm tˢ t ⊆ xs                              ↝⟨ _, wf-free-Tm tˢ ⟩
      free-Tm tˢ t ⊆ xs × Wf-tm (free-Tm tˢ t) tˢ t  ↝⟨ (λ (sub , wf) → weaken-Wf-tm sub tˢ wf) ⟩□
      Wf-tm xs tˢ t                                  □

    @0 strengthen-Wf-args :
      ∀ (asˢ : Argsˢ vs) {as} →
      ¬ (_ , x) ∈ free-Args asˢ as →
      Wf-args ((_ , x) ∷ xs) asˢ as → Wf-args xs asˢ as
    strengthen-Wf-args {x = x} {xs = xs} asˢ {as = as} x∉ =
      Wf-args ((_ , x) ∷ xs) asˢ as                              ↝⟨ free-⊆-Args asˢ ⟩
      free-Args asˢ as ⊆ (_ , x) ∷ xs                            ↝⟨ ∉→⊆∷→⊆ x∉ ⟩
      free-Args asˢ as ⊆ xs                                      ↝⟨ _, wf-free-Args asˢ ⟩
      free-Args asˢ as ⊆ xs × Wf-args (free-Args asˢ as) asˢ as  ↝⟨ (λ (sub , wf) → weaken-Wf-args sub asˢ wf) ⟩□
      Wf-args xs asˢ as                                          □

    @0 strengthen-Wf-arg :
      ∀ (aˢ : Argˢ v) {a} →
      ¬ (_ , x) ∈ free-Arg aˢ a →
      Wf-arg ((_ , x) ∷ xs) aˢ a → Wf-arg xs aˢ a
    strengthen-Wf-arg {x = x} {xs = xs} aˢ {a = a} x∉ =
      Wf-arg ((_ , x) ∷ xs) aˢ a                        ↝⟨ free-⊆-Arg aˢ ⟩
      free-Arg aˢ a ⊆ (_ , x) ∷ xs                      ↝⟨ ∉→⊆∷→⊆ x∉ ⟩
      free-Arg aˢ a ⊆ xs                                ↝⟨ _, wf-free-Arg aˢ ⟩
      free-Arg aˢ a ⊆ xs × Wf-arg (free-Arg aˢ a) aˢ a  ↝⟨ (λ (sub , wf) → weaken-Wf-arg sub aˢ wf) ⟩□
      Wf-arg xs aˢ a                                    □

    private

      -- A lemma used below.

      ⊆∷delete→⊆∷→⊆∷ :
        ∀ {x y : ∃Var} {xs ys zs} →
        xs ⊆ x ∷ del y ys →
        ys ⊆ y ∷ zs →
        xs ⊆ x ∷ zs
      ⊆∷delete→⊆∷→⊆∷ {x = x} {y = y} {xs = xs} {ys = ys} {zs = zs}
                     xs⊆ ys⊆ z =
        z ∈ xs                        ↝⟨ xs⊆ z ⟩
        z ∈ x ∷ del y ys              ↔⟨ (F.id ∥⊎∥-cong ∈delete≃ merely-equal?-∃Var) F.∘ ∈∷≃ ⟩
        z ≡ x ∥⊎∥ z ≢ y × z ∈ ys      ↝⟨ id ∥⊎∥-cong id ×-cong ys⊆ z ⟩
        z ≡ x ∥⊎∥ z ≢ y × z ∈ y ∷ zs  ↔⟨ (F.id ∥⊎∥-cong ∃-cong λ z≢y → ∈≢∷≃ z≢y) ⟩
        z ≡ x ∥⊎∥ z ≢ y × z ∈ zs      ↝⟨ id ∥⊎∥-cong proj₂ ⟩
        z ≡ x ∥⊎∥ z ∈ zs              ↔⟨ inverse ∈∷≃ ⟩□
        z ∈ x ∷ zs                    □

    -- Renaming preserves well-formedness.

    @0 rename-Wf-var :
      Wf-var ((_ , x) ∷ xs) z →
      Wf-var ((_ , y) ∷ xs) (rename-Var x y z)
    rename-Wf-var {x = x} {xs = xs} {z = z} {y = y} z∈
      with (_ , x) ≟∃V (_ , z)
    … | no [ x≢z ] =            $⟨ z∈ ⟩
        (_ , z) ∈ (_ , x) ∷ xs  ↔⟨ ∈≢∷≃ (x≢z ∘ sym) ⟩
        (_ , z) ∈ xs            ↝⟨ ∈→∈∷ ⟩□
        (_ , z) ∈ (_ , y) ∷ xs  □

    … | yes [ x≡z ] =
      ≡→∈∷ $ Σ-≡,≡→≡
        (sym (cong proj₁ x≡z))
        (subst (λ s → Var s) (sym (cong proj₁ x≡z))
           (cast-Var (cong proj₁ x≡z) y)             ≡⟨ cong (subst _ _) cast-Var-not-erased ⟩

         subst (λ s → Var s) (sym (cong proj₁ x≡z))
           (subst (λ s → Var s) (cong proj₁ x≡z) y)  ≡⟨ subst-sym-subst _ ⟩∎

         y                                           ∎)

    @0 rename-Wf-tm :
      ∀ (tˢ : Tmˢ s) {t} →
      Wf-tm ((_ , x) ∷ xs) tˢ t →
      Wf-tm ((_ , y) ∷ xs) tˢ (rename-Tm x y tˢ t)
    rename-Wf-tm {x = x} {xs = xs} {y = y} tˢ {t = t} wf =             $⟨ wf-free-Tm tˢ ⟩
      Wf-tm (free-Tm tˢ (rename-Tm x y tˢ t)) tˢ (rename-Tm x y tˢ t)  ↝⟨ weaken-Wf-tm
                                                                            (⊆∷delete→⊆∷→⊆∷ (free-rename-⊆-Tm tˢ) (free-⊆-Tm tˢ wf)) tˢ ⟩□
      Wf-tm ((_ , y) ∷ xs) tˢ (rename-Tm x y tˢ t)                     □

    @0 rename-Wf-args :
      ∀ (asˢ : Argsˢ vs) {as} →
      Wf-args ((_ , x) ∷ xs) asˢ as →
      Wf-args ((_ , y) ∷ xs) asˢ (rename-Args x y asˢ as)
    rename-Wf-args {x = x} {xs = xs} {y = y} asˢ {as = as} wfs =
                                                           $⟨ wf-free-Args asˢ ⟩
      Wf-args (free-Args asˢ (rename-Args x y asˢ as)) asˢ
              (rename-Args x y asˢ as)                     ↝⟨ weaken-Wf-args (⊆∷delete→⊆∷→⊆∷ (free-rename-⊆-Args asˢ) (free-⊆-Args asˢ wfs)) asˢ ⟩□

      Wf-args ((_ , y) ∷ xs) asˢ (rename-Args x y asˢ as)  □

    @0 rename-Wf-arg :
      ∀ (aˢ : Argˢ v) {a} →
      Wf-arg ((_ , x) ∷ xs) aˢ a →
      Wf-arg ((_ , y) ∷ xs) aˢ (rename-Arg x y aˢ a)
    rename-Wf-arg {x = x} {xs = xs} {y = y} aˢ {a = a} wf =
                                                      $⟨ wf-free-Arg aˢ ⟩
      Wf-arg (free-Arg aˢ (rename-Arg x y aˢ a)) aˢ
             (rename-Arg x y aˢ a)                    ↝⟨ weaken-Wf-arg (⊆∷delete→⊆∷→⊆∷ (free-rename-⊆-Arg aˢ) (free-⊆-Arg aˢ wf)) aˢ ⟩□

      Wf-arg ((_ , y) ∷ xs) aˢ (rename-Arg x y aˢ a)  □

    private

      -- A lemma used below.

      ∉→⊆∷∷→⊆∷→⊆∷ :
        ∀ {x y : ∃Var} {xs ys zs} →
        ¬ y ∈ xs →
        xs ⊆ x ∷ y ∷ ys →
        ys ⊆ y ∷ zs →
        xs ⊆ x ∷ zs
      ∉→⊆∷∷→⊆∷→⊆∷ {x = x} {y = y} {xs = xs} {ys = ys} {zs = zs}
                  y∉xs xs⊆x∷y∷ys ys⊆y∷zs = λ z →
        z ∈ xs                                          ↝⟨ (λ z∈xs → (λ z≡y → y∉xs (subst (_∈ _) z≡y z∈xs))
                                                                   , xs⊆x∷y∷ys z z∈xs) ⟩

        z ≢ y × z ∈ x ∷ y ∷ ys                          ↔⟨ (∃-cong λ _ → (F.id ∥⊎∥-cong ∈∷≃) F.∘ ∈∷≃) ⟩

        z ≢ y × (z ≡ x ∥⊎∥ z ≡ y ∥⊎∥ z ∈ ys)            ↝⟨ (∃-cong λ _ → F.id ∥⊎∥-cong F.id ∥⊎∥-cong ys⊆y∷zs z) ⟩

        z ≢ y × (z ≡ x ∥⊎∥ z ≡ y ∥⊎∥ z ∈ y ∷ zs)        ↔⟨ (∃-cong λ _ → F.id ∥⊎∥-cong F.id ∥⊎∥-cong ∈∷≃) ⟩

        z ≢ y × (z ≡ x ∥⊎∥ z ≡ y ∥⊎∥ z ≡ y ∥⊎∥ z ∈ zs)  ↔⟨ (∃-cong λ z≢y → F.id ∥⊎∥-cong (
                                                            drop-⊥-left-∥⊎∥ ∈-propositional z≢y F.∘
                                                            drop-⊥-left-∥⊎∥ ∥⊎∥-propositional z≢y)) ⟩

        z ≢ y × (z ≡ x ∥⊎∥ z ∈ zs)                      ↝⟨ proj₂ ⟩

        z ≡ x ∥⊎∥ z ∈ zs                                ↔⟨ inverse ∈∷≃ ⟩□

        z ∈ x ∷ zs                                      □

    -- If one renames with a fresh variable, and the renamed term is
    -- well-formed (with respect to a certain set of variables), then
    -- the original term is also well-formed (with respect to a
    -- certain set of variables).

    @0 renamee-Wf-var :
      _≢_ {A = ∃Var} (_ , y) (_ , z) →
      Wf-var ((_ , y) ∷ xs) (rename-Var x y z) →
      Wf-var ((_ , x) ∷ xs) z
    renamee-Wf-var {y = y} {z = z} {xs = xs} {x = x} y≢z
      with (_ , x) ≟∃V (_ , z)
    … | yes [ x≡z ] =
      (_ , cast-Var _ y) ∈ (_ , y) ∷ xs  ↝⟨ (λ _ → ≡→∈∷ (sym x≡z)) ⟩□
      (_ , z) ∈ (_ , x) ∷ xs             □
    … | no [ x≢z ] =
      (_ , z) ∈ (_ , y) ∷ xs              ↔⟨ ∈∷≃ ⟩
      (_ , z) ≡ (_ , y) ∥⊎∥ (_ , z) ∈ xs  ↔⟨ drop-⊥-left-∥⊎∥ ∈-propositional (y≢z ∘ sym) ⟩
      (_ , z) ∈ xs                        ↝⟨ ∈→∈∷ ⟩□
      (_ , z) ∈ (_ , x) ∷ xs              □

    @0 renamee-Wf-tm :
      ∀ (tˢ : Tmˢ s) {t} →
      ¬ (_ , y) ∈ free-Tm tˢ t →
      Wf-tm ((_ , y) ∷ xs) tˢ (rename-Tm x y tˢ t) →
      Wf-tm ((_ , x) ∷ xs) tˢ t
    renamee-Wf-tm {y = y} {xs = xs} {x = x} tˢ {t = t} y∉t =
      Wf-tm ((_ , y) ∷ xs) tˢ (rename-Tm x y tˢ t)    ↝⟨ free-⊆-Tm tˢ ⟩
      free-Tm tˢ (rename-Tm x y tˢ t) ⊆ (_ , y) ∷ xs  ↝⟨ ∉→⊆∷∷→⊆∷→⊆∷ y∉t (⊆-free-rename-Tm tˢ) ⟩
      free-Tm tˢ t ⊆ (_ , x) ∷ xs                     ↝⟨ (λ wf → weaken-Wf-tm wf tˢ (wf-free-Tm tˢ)) ⟩□
      Wf-tm ((_ , x) ∷ xs) tˢ t                       □

    @0 renamee-Wf-args :
      ∀ (asˢ : Argsˢ vs) {as} →
      ¬ (_ , y) ∈ free-Args asˢ as →
      Wf-args ((_ , y) ∷ xs) asˢ (rename-Args x y asˢ as) →
      Wf-args ((_ , x) ∷ xs) asˢ as
    renamee-Wf-args {y = y} {xs = xs} {x = x} asˢ {as = as} y∉as =
      Wf-args ((_ , y) ∷ xs) asˢ (rename-Args x y asˢ as)    ↝⟨ free-⊆-Args asˢ ⟩
      free-Args asˢ (rename-Args x y asˢ as) ⊆ (_ , y) ∷ xs  ↝⟨ ∉→⊆∷∷→⊆∷→⊆∷ y∉as (⊆-free-rename-Args asˢ) ⟩
      free-Args asˢ as ⊆ (_ , x) ∷ xs                        ↝⟨ (λ wf → weaken-Wf-args wf asˢ (wf-free-Args asˢ)) ⟩□
      Wf-args ((_ , x) ∷ xs) asˢ as                          □

    @0 renamee-Wf-arg :
      ∀ (aˢ : Argˢ v) {a} →
      ¬ (_ , y) ∈ free-Arg aˢ a →
      Wf-arg ((_ , y) ∷ xs) aˢ (rename-Arg x y aˢ a) →
      Wf-arg ((_ , x) ∷ xs) aˢ a
    renamee-Wf-arg {y = y} {xs = xs} {x = x} aˢ {a = a} y∉a =
      Wf-arg ((_ , y) ∷ xs) aˢ (rename-Arg x y aˢ a)    ↝⟨ free-⊆-Arg aˢ ⟩
      free-Arg aˢ (rename-Arg x y aˢ a) ⊆ (_ , y) ∷ xs  ↝⟨ ∉→⊆∷∷→⊆∷→⊆∷ y∉a (⊆-free-rename-Arg aˢ) ⟩
      free-Arg aˢ a ⊆ (_ , x) ∷ xs                      ↝⟨ (λ wf → weaken-Wf-arg wf aˢ (wf-free-Arg aˢ)) ⟩□
      Wf-arg ((_ , x) ∷ xs) aˢ a                        □

    -- If the "body of a lambda" is well-formed for all fresh
    -- variables, then it is well-formed for the bound variable.

    @0 body-Wf-var :
      ((y : Var s) →
       ¬ (_ , y) ∈ xs →
       Wf-var ((_ , y) ∷ xs) (rename-Var x y z)) →
      Wf-var ((_ , x) ∷ xs) z
    body-Wf-var {xs = xs} {z = z} wf =
      let y , [ y-fresh ] = fresh ((_ , z) ∷ xs)
          y∉xs            = y-fresh ∘ ∈→∈∷
          y≢z             = y-fresh ∘ ≡→∈∷
      in
      renamee-Wf-var y≢z (wf y y∉xs)

    @0 body-Wf-tm :
      ∀ (tˢ : Tmˢ s) {t} →
      ((y : Var s) →
       ¬ (_ , y) ∈ xs →
       Wf-tm ((_ , y) ∷ xs) tˢ (rename-Tm x y tˢ t)) →
      Wf-tm ((_ , x) ∷ xs) tˢ t
    body-Wf-tm {xs = xs} tˢ {t = t} wf =
      let y , [ y-fresh ] = fresh (xs ∪ free-Tm tˢ t)
          y∉xs            = y-fresh ∘ ∈→∈∪ˡ
          y∉t             = y-fresh ∘ ∈→∈∪ʳ xs
      in
      renamee-Wf-tm tˢ y∉t (wf y y∉xs)

    @0 body-Wf-args :
      ∀ (asˢ : Argsˢ vs) {as} →
      ((y : Var s) →
       ¬ (_ , y) ∈ xs →
       Wf-args ((_ , y) ∷ xs) asˢ (rename-Args x y asˢ as)) →
      Wf-args ((_ , x) ∷ xs) asˢ as
    body-Wf-args {xs = xs} asˢ {as = as} wfs =
      let y , [ y-fresh ] = fresh (xs ∪ free-Args asˢ as)
          y∉xs            = y-fresh ∘ ∈→∈∪ˡ
          y∉as            = y-fresh ∘ ∈→∈∪ʳ xs
      in
      renamee-Wf-args asˢ y∉as (wfs y y∉xs)

    @0 body-Wf-arg :
      ∀ (aˢ : Argˢ v) {a} →
      ((y : Var s) →
       ¬ (_ , y) ∈ xs →
       Wf-arg ((_ , y) ∷ xs) aˢ (rename-Arg x y aˢ a)) →
      Wf-arg ((_ , x) ∷ xs) aˢ a
    body-Wf-arg {xs = xs} aˢ {a = a} wf =
      let y , [ y-fresh ] = fresh (xs ∪ free-Arg aˢ a)
          y∉xs            = y-fresh ∘ ∈→∈∪ˡ
          y∉a             = y-fresh ∘ ∈→∈∪ʳ xs
      in
      renamee-Wf-arg aˢ y∉a (wf y y∉xs)

  ----------------------------------------------------------------------
  -- Weakening, casting and strengthening

  -- Weakening.

  weaken-Variable : @0 xs ⊆ ys → Variable xs s → Variable ys s
  weaken-Variable xs⊆ys (x , [ wf ]) =
    x , [ weaken-Wf-var xs⊆ys wf ]

  weaken-Term : @0 xs ⊆ ys → Term xs s → Term ys s
  weaken-Term xs⊆ys (tˢ , t , [ wf ]) =
    tˢ , t , [ weaken-Wf-tm xs⊆ys tˢ wf ]

  weaken-Arguments : @0 xs ⊆ ys → Arguments xs vs → Arguments ys vs
  weaken-Arguments xs⊆ys (asˢ , as , [ wfs ]) =
    asˢ , as , [ weaken-Wf-args xs⊆ys asˢ wfs ]

  weaken-Argument : @0 xs ⊆ ys → Argument xs v → Argument ys v
  weaken-Argument xs⊆ys (aˢ , a , [ wf ]) =
    aˢ , a , [ weaken-Wf-arg xs⊆ys aˢ wf ]

  -- Casting.

  cast-Variable :
    @0 xs ≡ ys → Variable xs s → Variable ys s
  cast-Variable eq = weaken-Variable (subst (_ ⊆_) eq ⊆-refl)

  cast-Term :
    @0 xs ≡ ys → Term xs s → Term ys s
  cast-Term eq = weaken-Term (subst (_ ⊆_) eq ⊆-refl)

  cast-Arguments :
    @0 xs ≡ ys → Arguments xs vs → Arguments ys vs
  cast-Arguments eq = weaken-Arguments (subst (_ ⊆_) eq ⊆-refl)

  cast-Argument :
    @0 xs ≡ ys → Argument xs v → Argument ys v
  cast-Argument eq = weaken-Argument (subst (_ ⊆_) eq ⊆-refl)

  -- Strengthening.

  strengthen-Variable :
    (y : Variable ((_ , x) ∷ xs) s) →
    @0 ¬ Free-in-variable x y →
    Variable xs s
  strengthen-Variable (y , [ wf ]) ¬free =
    y , [ strengthen-Wf-var (¬free ∘ free-Free-Var wf) wf ]

  strengthen-Term :
    (t : Term ((_ , x) ∷ xs) s) →
    @0 ¬ Free-in-term x t →
    Term xs s
  strengthen-Term (tˢ , t , [ wf ]) ¬free =
    tˢ , t , [ strengthen-Wf-tm tˢ (¬free ∘ free-Free-Tm tˢ wf) wf ]

  strengthen-Arguments :
    (as : Arguments ((_ , x) ∷ xs) vs) →
    @0 ¬ Free-in-arguments x as →
    Arguments xs vs
  strengthen-Arguments (asˢ , as , [ wfs ]) ¬free =
      asˢ
    , as
    , [ strengthen-Wf-args asˢ (¬free ∘ free-Free-Args asˢ wfs) wfs ]

  strengthen-Argument :
    (a : Argument ((_ , x) ∷ xs) v) →
    @0 ¬ Free-in-argument x a →
    Argument xs v
  strengthen-Argument (aˢ , a , [ wf ]) ¬free =
    aˢ , a , [ strengthen-Wf-arg aˢ (¬free ∘ free-Free-Arg aˢ wf) wf ]

  ----------------------------------------------------------------------
  -- Substitution

  module _ {s ys} (x : Var s) (t : Term ys s) where

    -- Substitution for variables.

    subst-Variable :
      ∀ {s′} → Variable ((_ , x) ∷ xs) s′ → Term (xs ∪ ys) s′
    subst-Variable {xs = xs} (y , [ y∈x∷xs ]) =
      case (_ , y) ≟∃V (_ , x) of λ where
        (no [ y≢x ])  → var-wf y (∈→∈∪ˡ (_≃_.to (∈≢∷≃ y≢x) y∈x∷xs))
        (yes [ y≡x ]) →
          substᴱ (λ p → Term (xs ∪ ys) (proj₁ p)) (sym y≡x) $
            Σ-map id
              (λ {tˢ} → Σ-map id
                          (E.map (weaken-Wf-tm (λ _ → ∈→∈∪ʳ xs) tˢ)))
              t

    -- Substitution for terms and arguments.

    private

      e : Wf-elim
            (λ {xs = xs′} {s = s} _ →
               ∀ {xs} → @0 xs′ ≡ (_ , x) ∷ xs → Term (xs ∪ ys) s)
            (λ {xs = xs′} {vs = vs} _ →
               ∀ {xs} → @0 xs′ ≡ (_ , x) ∷ xs → Arguments (xs ∪ ys) vs)
            (λ {xs = xs′} {v = v} _ →
               ∀ {xs} → @0 xs′ ≡ (_ , x) ∷ xs → Argument (xs ∪ ys) v)
      e .Wf-elim.varʳ x x∈ eq =
        subst-Variable (x , [ subst (_ ∈_) eq x∈ ])

      e .Wf-elim.opʳ o _ _ _ hyp eq = Σ-map (op o) id (hyp eq)

      e .Wf-elim.nilʳ = λ _ → nil-wfs

      e .Wf-elim.consʳ _ _ _ _ _ _ hyp hyps eq =
        Σ-zip cons (Σ-zip _,_ λ ([ wf ]) ([ wfs ]) → [ (wf , wfs) ])
          (hyp eq) (hyps eq)

      e .Wf-elim.nilʳ′ tˢ t wf hyp eq = Σ-map nil id (hyp eq)

      e .Wf-elim.consʳ′ {xs = xs′} aˢ y a wf hyp {xs = xs} eq =
        case (_ , x) ≟∃V (_ , y) of λ where
          (inj₁ [ x≡y ]) →
            -- If the bound variable matches x, keep the original
            -- term (with a new well-formedness proof).
            cons-wf aˢ y a
              (                                               $⟨ wf ⟩
               Wf-arg xs′ (cons aˢ) (y , a)                   ↝⟨ subst (λ xs → Wf-arg xs (cons aˢ) _) eq ⟩
               Wf-arg ((_ , x) ∷ xs) (cons aˢ) (y , a)        ↝⟨ strengthen-Wf-arg (cons aˢ) (
                 (_ , x) ∈ del (_ , y) (free-Arg aˢ a)             ↔⟨ ∈delete≃ merely-equal?-∃Var ⟩
                 (_ , x) ≢ (_ , y) × (_ , x) ∈ free-Arg aˢ a       ↝⟨ (_$ x≡y) ∘ proj₁ ⟩□
                 ⊥                                                 □) ⟩
               Wf-arg xs (cons aˢ) (y , a)                    ↝⟨ weaken-Wf-arg (λ _ → ∈→∈∪ˡ) (cons aˢ) ⟩□
               Wf-arg (xs ∪ ys) (cons aˢ) (y , a)             □)
          (inj₂ [ x≢y ]) →
            -- Otherwise, rename the bound variable to something fresh
            -- and keep substituting.
            let z , [ z∉ ]         = fresh ((_ , x) ∷ xs ∪ ys)
                aˢ′ , a′ , [ wf′ ] =
                  hyp z (z∉ ∘ ∈→∈∪ˡ ∘ subst (_ ∈_) eq)
                    ((_ , z) ∷ xs′           ≡⟨ cong (_ ∷_) eq ⟩
                     (_ , z) ∷ (_ , x) ∷ xs  ≡⟨ swap ⟩∎
                     (_ , x) ∷ (_ , z) ∷ xs  ∎)
            in
            cons-wf aˢ′ z a′
              (λ p _ →                                                   $⟨ wf′ ⟩
                 Wf-arg ((_ , z) ∷ xs ∪ ys) aˢ′ a′                       ↝⟨ rename-Wf-arg aˢ′ ⟩□
                 Wf-arg ((_ , p) ∷ xs ∪ ys) aˢ′ (rename-Arg z p aˢ′ a′)  □)

    subst-Term : ∀ {xs} → Term ((_ , x) ∷ xs) s′ → Term (xs ∪ ys) s′
    subst-Term t = wf-elim-Term e t (refl _)

    subst-Arguments :
      ∀ {xs} → Arguments ((_ , x) ∷ xs) vs → Arguments (xs ∪ ys) vs
    subst-Arguments as = wf-elim-Arguments e as (refl _)

    subst-Argument :
      ∀ {xs} → Argument ((_ , x) ∷ xs) v → Argument (xs ∪ ys) v
    subst-Argument a = wf-elim-Argument e a (refl _)
