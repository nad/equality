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

import Bijection equality-with-J as Bijection
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
    infix 4 _≟S_ _≟O_ _≟∃V_

    field
      -- A set of sorts with decidable equality.
      Sort : Type ℓ
      _≟S_ : Decidable-equality Sort

    -- Valences.

    Valence : Type ℓ
    Valence = List Sort × Sort

    field
      -- Codomain-indexed operators with decidable equality and
      -- domains.
      Op     : @0 Sort → Type ℓ
      _≟O_   : ∀ {@0 s} → Decidable-equality (Op s)
      domain : ∀ {@0 s} → Op s → List Valence

      -- A sort-indexed type of variables with decidable equality.
      Var : @0 Sort → Type ℓ

    -- Non-indexed variables.

    ∃Var : Type ℓ
    ∃Var = ∃ λ (s : Erased Sort) → Var (erased s)

    -- Finite subsets of variables.

    Vars : Type ℓ
    Vars = Finite-subset-of ∃Var

    field
      -- Decidable equality for non-indexed variables.
      _≟∃V_ : Decidable-equality ∃Var

      -- One can always find a fresh variable.
      fresh : ∀ {s} (xs : Vars) →
              ∃ λ (x : Var s) → ¬ (_ , x) ∈ xs

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
      @0 x y z         : Var s
      @0 A             : Type ℓ
      @0 wf            : A

  ----------------------------------------------------------------------
  -- Some types are sets

  -- Sort is a set.

  Sort-set : Is-set Sort
  Sort-set = decidable⇒set _≟S_

  -- Valence is a set.

  Valence-set : Is-set Valence
  Valence-set = ×-closure 2
    (H-level-List 0 Sort-set)
    Sort-set

  -- Arity is a set.

  Arity-set : Is-set Arity
  Arity-set = ×-closure 2
    (H-level-List 0 Valence-set)
    Sort-set

  -- ∃Var is a set.

  ∃Var-set : Is-set ∃Var
  ∃Var-set = decidable⇒set _≟∃V_

  ----------------------------------------------------------------------
  -- Term skeletons

  -- Term skeletons are terms without variables.

  mutual

    -- Terms.

    data Tmˢ (@0 s : Sort) : Type ℓ where
      var : Tmˢ s
      op  : (o : Op s) → Argsˢ (domain o) → Tmˢ s

    -- Sequences of arguments.

    data Argsˢ : @0 List Valence → Type ℓ where
      nil  : Argsˢ []
      cons : Argˢ v → Argsˢ vs → Argsˢ (v ∷ vs)

    -- Arguments.

    data Argˢ : @0 Valence → Type ℓ where
      nil  : Tmˢ s → Argˢ ([] , s)
      cons : ∀ {s} → Argˢ (ss , s′) → Argˢ (s ∷ ss , s′)

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

  cast-Var : [ s ] ≡ [ s′ ] → Var s → Var s′
  cast-Var = subst (λ ([ s ]) → Var s)

  -- Renaming.

  module _ (x y : Var s) where

    rename-Var : Var s′ → Var s′
    rename-Var z = case (_ , x) ≟∃V (_ , z) of λ where
      (no _)    → z
      (yes x≡z) → cast-Var (cong proj₁ x≡z) y

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

  Wf-var : Vars → Var s → Type ℓ
  Wf-var xs x = (_ , x) ∈ xs

  mutual

    Wf-tm : Vars → (tˢ : Tmˢ s) → Tm tˢ → Type ℓ
    Wf-tm xs var        = Wf-var xs
    Wf-tm xs (op o asˢ) = Wf-args xs asˢ

    Wf-args : Vars → (asˢ : Argsˢ vs) → Args asˢ → Type ℓ
    Wf-args _  nil           _        = ↑ _ ⊤
    Wf-args xs (cons aˢ asˢ) (a , as) =
      Wf-arg xs aˢ a × Wf-args xs asˢ as

    Wf-arg : Vars → (aˢ : Argˢ v) → Arg aˢ → Type ℓ
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

  Tmˢ≃ : Tmˢ s ≃ (⊤ ⊎ ∃ λ (o : Op s) → Argsˢ (domain o))
  Tmˢ≃ = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = λ where
                   var       → inj₁ _
                   (op o as) → inj₂ (o , as)
        ; from = λ where
                   (inj₁ _)        → var
                   (inj₂ (o , as)) → op o as
        }
      ; right-inverse-of = λ where
          (inj₁ _) → refl _
          (inj₂ _) → refl _
      }
    ; left-inverse-of = λ where
        var      → refl _
        (op _ _) → refl _
    })

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
    RHS : Erased (List Valence) → Type ℓ
    RHS [ vs ] =
      (Erased ([] ≡ vs) ⊎
      (∃ λ ((([ v ] , _) , [ vs′ ] , _) :
            (∃ λ v → Argˢ (erased v)) ×
            (∃ λ vs′ → Argsˢ (erased vs′))) →
         Erased (v ∷ vs′ ≡ vs)))

    to : Argsˢ vs → RHS [ vs ]
    to nil         = inj₁ [ refl _ ]
    to (cons a as) = inj₂ (((_ , a) , _ , as) , [ refl _ ])

    from : RHS [ vs ] → Argsˢ vs
    from (inj₁ [ eq ]) =
      subst (λ vs → Argsˢ (erased vs)) ([]-cong [ eq ]) nil
    from (inj₂ (((_ , a) , _ , as) , [ eq ])) =
      subst (λ vs → Argsˢ (erased vs)) ([]-cong [ eq ]) (cons a as)

    lemma₁ :
      ∀ {vs₁ vs₂ as} (eq : vs₁ ≡ vs₂) →
      to (subst (λ vs → Argsˢ (erased vs)) eq as) ≡
      subst RHS eq (to as)
    lemma₁ {as = as} = elim¹ _
      (to (subst (λ vs → Argsˢ (erased vs)) (refl _) as)  ≡⟨ cong to $ subst-refl _ _ ⟩
       to as                                              ≡⟨ sym $ subst-refl _ _ ⟩∎
       subst RHS (refl _) (to as)                         ∎)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ [ eq ]) =
      to (subst (λ vs → Argsˢ (erased vs)) ([]-cong [ eq ]) nil)  ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to nil)                         ≡⟨⟩

      subst RHS ([]-cong [ eq ]) (inj₁ [ refl _ ])                ≡⟨ push-subst-inj₁ _ _ ⟩

      inj₁ (subst (λ vs → Erased ([] ≡ erased vs))
                  ([]-cong [ eq ]) [ refl _ ])                    ≡⟨ cong inj₁ $ H-level-Erased 1 (H-level-List 0 Valence-set) _ _ ⟩∎

      inj₁ [ eq ]                                                 ∎

    to∘from (inj₂ ((([ v ] , a) , [ vs′ ] , as) , [ eq ])) =
      to (subst (λ vs → Argsˢ (erased vs)) ([]-cong [ eq ]) (cons a as))  ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to (cons a as))                         ≡⟨⟩

      subst RHS ([]-cong [ eq ])
            (inj₂ (((_ , a) , _ , as) , [ refl _ ]))                      ≡⟨ push-subst-inj₂ _ _ ⟩

      inj₂ (subst _
                  ([]-cong [ eq ])
                  (((_ , a) , _ , as) , [ refl _ ]))                      ≡⟨ cong inj₂ (push-subst-pair-× _ _) ⟩

      inj₂ ( ((_ , a) , _ , as)
           , subst (λ ([ vs ]) → Erased (v ∷ vs′ ≡ vs))
                   ([]-cong [ eq ])
                   [ refl _ ]
           )                                                              ≡⟨ cong (λ eq → inj₂ (((_ , a) , _ , as) , eq)) $
                                                                             H-level-Erased 1 (H-level-List 0 Valence-set) _ _ ⟩∎
      inj₂ (((_ , a) , _ , as) , [ eq ])                                  ∎

    lemma₂ :
      {as : Argsˢ vs} →
      subst (λ vs → Argsˢ (erased vs)) ([]-cong [ refl _ ]) as ≡ as
    lemma₂ {as = as} =
      subst (λ vs → Argsˢ (erased vs)) ([]-cong [ refl _ ]) as  ≡⟨ cong (λ eq → subst (λ vs → Argsˢ (erased vs)) eq _) []-cong-[refl] ⟩
      subst (λ vs → Argsˢ (erased vs)) (refl _) as              ≡⟨ subst-refl _ _ ⟩∎
      as                                                        ∎

    from∘to : ∀ x → from (to x) ≡ x
    from∘to nil        = lemma₂
    from∘to (cons _ _) = lemma₂

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
    RHS : Erased Valence → Type ℓ
    RHS [ v ] =
      (∃ λ (([ s ] , _) : ∃ λ s → Tmˢ (erased s)) →
         Erased (([] , s) ≡ v)) ⊎
      (∃ λ ((s , [ ss , s′ ] , _) : Sort × ∃ λ v → Argˢ (erased v)) →
       Erased ((s ∷ ss , s′) ≡ v))

    to : Argˢ v → RHS [ v ]
    to (nil t)          = inj₁ ((_ , t) , [ refl _ ])
    to (cons {s = s} a) = inj₂ ((s , _ , a) , [ refl _ ])

    from : RHS [ v ] → Argˢ v
    from (inj₁ ((_ , t) , [ eq ])) =
      subst (λ v → Argˢ (erased v)) ([]-cong [ eq ]) (nil t)
    from (inj₂ ((s , _ , a) , [ eq ])) =
      subst (λ v → Argˢ (erased v)) ([]-cong [ eq ]) (cons {s = s} a)

    lemma₁ :
      ∀ {v₁ v₂ a} (eq : v₁ ≡ v₂) →
      to (subst (λ v → Argˢ (erased v)) eq a) ≡
      subst RHS eq (to a)
    lemma₁ {a = a} = elim¹ _
      (to (subst (λ v → Argˢ (erased v)) (refl _) a)  ≡⟨ cong to $ subst-refl _ _ ⟩
       to a                                           ≡⟨ sym $ subst-refl _ _ ⟩∎
       subst RHS (refl _) (to a)                      ∎)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ (([ s ] , t) , [ eq ])) =
      to (subst (λ v → Argˢ (erased v)) ([]-cong [ eq ]) (nil t))      ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to (nil t))                          ≡⟨⟩

      subst RHS ([]-cong [ eq ]) (inj₁ ((_ , t) , [ refl _ ]))         ≡⟨ push-subst-inj₁ _ _ ⟩

      inj₁ (subst (λ v → ∃ λ (([ s ] , _) : ∃ λ s → Tmˢ (erased s)) →
                           Erased (([] , s) ≡ erased v))
                  ([]-cong [ eq ])
                  ((_ , t) , [ refl _ ]))                              ≡⟨ cong inj₁ $ push-subst-pair-× _ _ ⟩

      inj₁ ( (_ , t)
           , subst (λ v → Erased (([] , s) ≡ erased v))
                   ([]-cong [ eq ])
                   [ refl _ ]
           )                                                           ≡⟨ cong (λ eq → inj₁ ((_ , t) , eq)) $
                                                                          H-level-Erased 1 Valence-set _ _ ⟩∎
      inj₁ ((_ , t) , [ eq ])                                          ∎

    to∘from (inj₂ ((s , [ ss , s′ ] , a) , [ eq ])) =
      to (subst (λ v → Argˢ (erased v))
                ([]-cong [ eq ])
                (cons {s = s} a))                            ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to (cons {s = s} a))       ≡⟨⟩

      subst RHS ([]-cong [ eq ])
            (inj₂ ((s , _ , a) , [ refl _ ]))                ≡⟨ push-subst-inj₂ _ _ ⟩

      inj₂ (subst _
                  ([]-cong [ eq ])
                  ((s , _ , a) , [ refl _ ]))                ≡⟨ cong inj₂ (push-subst-pair-× _ _) ⟩

      inj₂ ( (s , _ , a)
           , subst (λ ([ v ]) → Erased ((s ∷ ss , s′) ≡ v))
                   ([]-cong [ eq ])
                   [ refl _ ]
           )                                                 ≡⟨ cong (λ eq → inj₂ ((s , _ , a) , eq)) $
                                                                H-level-Erased 1 Valence-set _ _ ⟩∎
      inj₂ ((s , _ , a) , [ eq ])                            ∎

    lemma₂ :
      {a : Argˢ v} →
      subst (λ v → Argˢ (erased v)) ([]-cong [ refl _ ]) a ≡ a
    lemma₂ {a = a} =
      subst (λ v → Argˢ (erased v)) ([]-cong [ refl _ ]) a  ≡⟨ cong (λ eq → subst (λ v → Argˢ (erased v)) eq _) []-cong-[refl] ⟩
      subst (λ v → Argˢ (erased v)) (refl _) a              ≡⟨ subst-refl _ _ ⟩∎
      a                                                     ∎

    from∘to : ∀ x → from (to x) ≡ x
    from∘to (nil _)  = lemma₂
    from∘to (cons _) = lemma₂

  ----------------------------------------------------------------------
  -- Equality is decidable

  -- "Mere equality" is decidable for ∃Var.

  merely-equal?-∃Var : (x y : ∃Var) → Dec ∥ x ≡ y ∥
  merely-equal?-∃Var x y = case x ≟∃V y of λ where
    (yes x≡y) → yes ∣ x≡y ∣
    (no x≢y)  → no (x≢y ∘ Trunc.rec ∃Var-set id)

  private

    -- An instance of delete.

    del : ∃Var → Finite-subset-of ∃Var → Finite-subset-of ∃Var
    del = delete merely-equal?-∃Var

  -- Equality is decidable for Var.

  infix 4 _≟V_

  _≟V_ : Decidable-equality (Var s)
  _≟V_ {s = s} x₁ x₂ =                                   $⟨ _ ≟∃V _ ⟩

    Dec (([ s ] , x₁) ≡ ([ s ] , x₂))                    ↝⟨ Dec-map $ from-isomorphism $ inverse Bijection.Σ-≡,≡↔≡ ⟩

    Dec (∃ λ (eq : [ s ] ≡ [ s ]) →
           subst (λ s → Var (erased s)) eq x₁ ≡ x₂)      ↝⟨ Dec-map $ from-isomorphism $ drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                            propositional⇒inhabited⇒contractible (H-level-Erased 2 Sort-set) (refl _) ⟩

    Dec (subst (λ s → Var (erased s)) _ x₁ ≡ x₂)         ↝⟨ ≡⇒↝ _ $ cong (λ eq → Dec (subst _ eq _ ≡ _)) $ H-level-Erased 2 Sort-set _ _ ⟩

    Dec (subst (λ s → Var (erased s)) (refl _) x₁ ≡ x₂)  ↝⟨ ≡⇒↝ _ $ cong (λ x → Dec (x ≡ _)) $ subst-refl _ _ ⟩□

    Dec (x₁ ≡ x₂)                                        □

  -- Equality is decidable for Tmˢ, Argsˢ and Argˢ.

  infix 4 _≟Tmˢ_ _≟Argsˢ_ _≟Argˢ_

  mutual

    _≟Tmˢ_ : Decidable-equality (Tmˢ s)
    var ≟Tmˢ var = yes (refl _)

    var ≟Tmˢ op _ _ =     $⟨ no (λ ()) ⟩
      Dec ⊥               ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (var ≡ op _ _)  □

    op _ _ ≟Tmˢ var =     $⟨ no (λ ()) ⟩
      Dec ⊥               ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (op _ _ ≡ var)  □

    op o₁ as₁ ≟Tmˢ op o₂ as₂ =       $⟨ Σ.decidable⇒dec⇒dec _≟O_ (λ _ → _ ≟Argsˢ as₂) ⟩
      Dec ((o₁ , as₁) ≡ (o₂ , as₂))  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□
      Dec (op o₁ as₁ ≡ op o₂ as₂)    □

    _≟Argsˢ_ : Decidable-equality (Argsˢ vs)
    nil ≟Argsˢ nil =                 $⟨ yes (refl _) ⟩
      Dec ([ refl _ ] ≡ [ refl _ ])  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Argsˢ≃) F.∘ from-isomorphism Bijection.≡↔inj₁≡inj₁ ⟩□
      Dec (nil ≡ nil)                □

    cons a₁ as₁ ≟Argsˢ cons a₂ as₂ =                     $⟨ ×.dec⇒dec⇒dec
                                                              (Σ.set⇒dec⇒dec⇒dec
                                                                 (H-level-Erased 2 (×-closure 2 (H-level-List 0 Sort-set) Sort-set))
                                                                 (yes (refl _))
                                                                 (λ _ → _ ≟Argˢ a₂))
                                                              (Σ.set⇒dec⇒dec⇒dec
                                                                 (H-level-Erased 2 (H-level-List 0 Valence-set))
                                                                 (yes (refl _))
                                                                 (λ _ → _ ≟Argsˢ as₂)) ⟩

      Dec (((_ , a₁) , _ , as₁) ≡ ((_ , a₂) , _ , as₂))  ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                            H-level-Erased 1 (H-level-List 0 Valence-set) ⟩
      Dec ((((_ , a₁) , _ , as₁) , [ refl _ ]) ≡
           (((_ , a₂) , _ , as₂) , [ refl _ ]))          ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Argsˢ≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□

      Dec (cons a₁ as₁ ≡ cons a₂ as₂)                    □

    _≟Argˢ_ : Decidable-equality (Argˢ v)
    nil t₁ ≟Argˢ nil t₂ =                                      $⟨ Σ.set⇒dec⇒dec⇒dec
                                                                    (H-level-Erased 2 Sort-set)
                                                                    (yes (refl _))
                                                                    (λ _ → _ ≟Tmˢ t₂) ⟩
      Dec ((_ , t₁) ≡ (_ , t₂))                                ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                                  H-level-Erased 1 Valence-set ⟩
      Dec (((_ , t₁) , [ refl _ ]) ≡ ((_ , t₂) , [ refl _ ]))  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Argˢ≃) F.∘
                                                                            from-isomorphism Bijection.≡↔inj₁≡inj₁ ⟩□
      Dec (nil t₁ ≡ nil t₂)                                    □

    cons a₁ ≟Argˢ cons a₂ =                                            $⟨ ×.dec⇒dec⇒dec
                                                                            (yes (refl _))
                                                                            (Σ.set⇒dec⇒dec⇒dec
                                                                               (H-level-Erased 2 Valence-set)
                                                                               (yes (refl _))
                                                                               (λ _ → _ ≟Argˢ a₂)) ⟩
      Dec ((_ , _ , a₁) ≡ (_ , _ , a₂))                                ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                                          H-level-Erased 1 Valence-set ⟩
      Dec (((_ , _ , a₁) , [ refl _ ]) ≡ ((_ , _ , a₂) , [ refl _ ]))  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Argˢ≃) F.∘
                                                                                    from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□
      Dec (cons a₁ ≡ cons a₂)                                          □

  -- Equality is decidable for Tm, Args and Arg.

  mutual

    equal?-Tm : (tˢ : Tmˢ s) → Decidable-equality (Tm tˢ)
    equal?-Tm var        x₁  x₂  = x₁ ≟V x₂
    equal?-Tm (op o asˢ) as₁ as₂ = equal?-Args asˢ as₁ as₂

    equal?-Args : (asˢ : Argsˢ vs) → Decidable-equality (Args asˢ)
    equal?-Args nil           _          _          = yes (refl _)
    equal?-Args (cons aˢ asˢ) (a₁ , as₁) (a₂ , as₂) =
      ×.dec⇒dec⇒dec
        (equal?-Arg aˢ a₁ a₂)
        (equal?-Args asˢ as₁ as₂)

    equal?-Arg : (aˢ : Argˢ v) → Decidable-equality (Arg aˢ)
    equal?-Arg (nil tˢ)  t₁        t₂        = equal?-Tm tˢ t₁ t₂
    equal?-Arg (cons aˢ) (x₁ , a₁) (x₂ , a₂) =
      ×.dec⇒dec⇒dec (x₁ ≟V x₂) (equal?-Arg aˢ a₁ a₂)

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

  -- Equality is decidable for Variable, Term, Arguments and Argument.

  infix 4 _≟Variable_ _≟Term_ _≟Arguments_ _≟Argument_

  _≟Variable_ : Decidable-equality (Variable xs s)
  _≟Variable_ =
    Σ.Dec._≟_
      _≟V_
      λ _ _ → yes ([]-cong [ Wf-var-propositional _ _ ])

  _≟Term_ : Decidable-equality (Term xs s)
  _≟Term_ =
    Σ.Dec._≟_
      _≟Tmˢ_
      λ {tˢ} →
        Σ.Dec._≟_
          (equal?-Tm tˢ)
          λ _ _ → yes ([]-cong [ Wf-tm-propositional tˢ _ _ ])

  _≟Arguments_ : Decidable-equality (Arguments xs vs)
  _≟Arguments_ =
    Σ.Dec._≟_
      _≟Argsˢ_
      λ {asˢ} →
        Σ.Dec._≟_
          (equal?-Args asˢ)
          λ _ _ → yes ([]-cong [ Wf-args-propositional asˢ _ _ ])

  _≟Argument_ : Decidable-equality (Argument xs v)
  _≟Argument_ =
    Σ.Dec._≟_
      _≟Argˢ_
      λ {aˢ} →
        Σ.Dec._≟_
          (equal?-Arg aˢ)
          λ _ _ → yes ([]-cong [ Wf-arg-propositional aˢ _ _ ])

  -- Variable, Term, Arguments and Argument are sets (pointwise).

  Variable-set : Is-set (Variable xs s)
  Variable-set = decidable⇒set _≟Variable_

  Term-set : Is-set (Term xs s)
  Term-set = decidable⇒set _≟Term_

  Arguments-set : Is-set (Arguments xs vs)
  Arguments-set = decidable⇒set _≟Arguments_

  Argument-set : Is-set (Argument xs v)
  Argument-set = decidable⇒set _≟Argument_

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
      varʳ : (x : Var s) (@0 x∈ : (_ , x) ∈ xs) →
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
  -- Some renaming lemmas

  -- Two "computation rules".

  rename-Var-≡ :
    {x y : Var s} {z : Var s′} →
    (x≡z : _≡_ {A = ∃Var} (_ , x) (_ , z)) →
    rename-Var x y z ≡ cast-Var (cong proj₁ x≡z) y
  rename-Var-≡ {x = x} {y = y} {z = z} x≡z with (_ , x) ≟∃V (_ , z)
  … | no x≢z   = ⊥-elim (x≢z x≡z)
  … | yes x≡z′ =
    cast-Var (cong proj₁ x≡z′) y  ≡⟨ cong (λ eq → cast-Var eq _) (H-level-Erased 2 Sort-set _ _) ⟩∎
    cast-Var (cong proj₁ x≡z)  y  ∎

  rename-Var-≢ :
    {x y : Var s} {z : Var s′} →
    _≢_ {A = ∃Var} (_ , x) (_ , z) → rename-Var x y z ≡ z
  rename-Var-≢ {x = x} {z = z} x≢z with (_ , x) ≟∃V (_ , z)
  … | no _    = refl _
  … | yes x≡z = ⊥-elim (x≢z x≡z)

  -- Equality to a pair of a certain form involving rename-Var can be
  -- expressed without reference to rename-Var.

  ≡,rename-Var≃ :
    {x y : Var s} {z : Var s′} {p : ∃Var} →
    (p ≡ (_ , rename-Var x y z))
      ≃
    ((_ , x) ≡ (_ , z) × p ≡ (_ , y) ⊎
     (_ , x) ≢ (_ , z) × p ≡ (_ , z))
  ≡,rename-Var≃ {x = x} {y = y} {z = z} {p = p} =
    p ≡ (_ , rename-Var x y z)                        ↔⟨ ×-⊎-distrib-right F.∘
                                                         (inverse $ drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                          propositional⇒inhabited⇒contractible
                                                            (Dec-closure-propositional ext ∃Var-set)
                                                            (_ ≟∃V _)) ⟩
    (_ , x) ≡ (_ , z) × p ≡ (_ , rename-Var x y z) ⊎
    (_ , x) ≢ (_ , z) × p ≡ (_ , rename-Var x y z)    ↝⟨ (∃-cong λ eq → ≡⇒↝ _ $ cong (p ≡_) (

        _ , rename-Var x y z                                                      ≡⟨ cong (_ ,_) $ rename-Var-≡ eq ⟩
        _ , cast-Var _ y                                                          ≡⟨ Σ-≡,≡→≡ (sym $ cong proj₁ eq)
                                                                                             (subst-sym-subst _) ⟩∎
        _ , y                                                                     ∎))
                                                            ⊎-cong
                                                         (∃-cong λ neq → ≡⇒↝ _ $ cong (λ x → _ ≡ (_ , x)) $ rename-Var-≢ neq) ⟩
    (_ , x) ≡ (_ , z) × p ≡ (_ , y) ⊎
    (_ , x) ≢ (_ , z) × p ≡ (_ , z)                   □

  -- A variant of the previous lemma.

  ≡,rename-Var≃′ :
    {x y : Var s} {z : Var s′} {p : ∃Var} →
    (p ≡ (_ , rename-Var x y z))
      ≃
    (p ≡ (_ , y) × (_ , x) ≡ (_ , z) ⊎
     p ≢ (_ , x) × p ≡ (_ , z))
  ≡,rename-Var≃′ {x = x} {y = y} {z = z} {p = p} =
    p ≡ (_ , rename-Var x y z)         ↝⟨ ≡,rename-Var≃ ⟩

    (_ , x) ≡ (_ , z) × p ≡ (_ , y) ⊎
    (_ , x) ≢ (_ , z) × p ≡ (_ , z)    ↔⟨ (×-comm ⊎-cong ×-cong₁ λ p≡z → →-cong₁ ext ≡-comm F.∘ ≡⇒↝ _ (cong (_ ≢_) (sym p≡z))) ⟩□

    p ≡ (_ , y) × (_ , x) ≡ (_ , z) ⊎
    p ≢ (_ , x) × p ≡ (_ , z)          □

  -- The functions rename-Var and cast-Var commute.

  rename-Var-cast-Var :
    ∀ {x y : Var s} {z : Var s₁} {eq : [ s₁ ] ≡ [ s₂ ]} →
    rename-Var x y (cast-Var eq z) ≡ cast-Var eq (rename-Var x y z)
  rename-Var-cast-Var {x = x} {y = y} {z = z} = elim¹
    (λ eq → rename-Var x y (cast-Var eq z) ≡
            cast-Var eq (rename-Var x y z))
    (rename-Var x y (cast-Var (refl _) z)  ≡⟨ cong (rename-Var _ _) $ subst-refl _ _ ⟩
     rename-Var x y z                      ≡⟨ sym $ subst-refl _ _ ⟩∎
     cast-Var (refl _) (rename-Var x y z)  ∎)
    _

  -- A fusion lemma for cast-Var.

  cast-Var-cast-Var :
    {x : Var s₁} {eq₁ : [ s₁ ] ≡ [ s₂ ]} {eq₂ : [ s₂ ] ≡ [ s₃ ]} →
    cast-Var eq₂ (cast-Var eq₁ x) ≡ cast-Var (trans eq₁ eq₂) x
  cast-Var-cast-Var = subst-subst _ _ _ _

  -- The proof given to cast-Var can be replaced.

  cast-Var-irrelevance :
    {x : Var s₁} {eq₁ eq₂ : [ s₁ ] ≡ [ s₂ ]} →
    cast-Var eq₁ x ≡ cast-Var eq₂ x
  cast-Var-irrelevance =
    cong (λ eq → cast-Var eq _) (H-level-Erased 2 Sort-set _ _)

  -- Renamings can sometimes be reordered in a certain way.

  module _
    {x₁ y₁ : Var s₁} {x₂ y₂ : Var s₂}
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

    rename-Var-swap :
      {z : Var s} →
      rename-Var x₁ y₁ (rename-Var x₂ y₂ z) ≡
      rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)
    rename-Var-swap {z = z} =
      lemma ((_ , x₁) ≟∃V (_ , z))
            ((_ , x₂) ≟∃V (_ , z))
            ((_ , x₂) ≟∃V (_ , y₁))
            ((_ , x₁) ≟∃V (_ , y₂))
      where
      lemma :
        Dec (_≡_ {A = ∃Var} (_ , x₁) (_ , z)) →
        Dec (_≡_ {A = ∃Var} (_ , x₂) (_ , z)) →
        Dec (_≡_ {A = ∃Var} (_ , x₂) (_ , y₁)) →
        Dec (_≡_ {A = ∃Var} (_ , x₁) (_ , y₂)) →
        rename-Var x₁ y₁ (rename-Var x₂ y₂ z) ≡
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)
      lemma (no x₁≢z) (no x₂≢z) _ _ =
        rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≢ x₂≢z ⟩
        rename-Var x₁ y₁ z                                        ≡⟨ rename-Var-≢ x₁≢z ⟩
        z                                                         ≡⟨ sym $ rename-Var-≢ x₂≢z ⟩
        rename-Var x₂ (rename-Var x₁ y₁ y₂) z                     ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≢ x₁≢z ⟩∎
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

      lemma (no x₁≢z) (yes x₂≡z) _ _ =
        rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≡ x₂≡z ⟩
        rename-Var x₁ y₁ (cast-Var _ y₂)                          ≡⟨ rename-Var-cast-Var ⟩
        cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ sym $ rename-Var-≡ x₂≡z ⟩
        rename-Var x₂ (rename-Var x₁ y₁ y₂) z                     ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≢ x₁≢z ⟩∎
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

      lemma (yes x₁≡z) (yes x₂≡z) (yes x₂≡y₁) _ =
        rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≡ x₂≡z ⟩
        rename-Var x₁ y₁ (cast-Var _ y₂)                          ≡⟨ rename-Var-cast-Var ⟩
        cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ cast-Var-irrelevance ⟩
        cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ sym cast-Var-cast-Var ⟩
        cast-Var _ (cast-Var _ (rename-Var x₁ y₁ y₂))             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≡ x₂≡y₁ ⟩
        cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

      lemma (yes x₁≡z) (yes x₂≡z) (no x₂≢y₁) (yes x₁≡y₂) =
        rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≡ x₂≡z ⟩
        rename-Var x₁ y₁ (cast-Var _ y₂)                          ≡⟨ rename-Var-cast-Var ⟩
        cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ cong (cast-Var _) $ rename-Var-≡ x₁≡y₂ ⟩
        cast-Var _ (cast-Var _ y₁)                                ≡⟨ cast-Var-cast-Var ⟩
        cast-Var _ y₁                                             ≡⟨ cast-Var-irrelevance ⟩
        cast-Var _ y₁                                             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≢ x₂≢y₁ ⟩
        cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

      lemma (yes x₁≡z) (yes x₂≡z) (no x₂≢y₁) (no x₁≢y₂) =
        case hyp of λ where
          (inj₁ hyp) → ⊥-elim $ hyp
                         (inj₁ (trans x₂≡z (sym x₁≡z) , x₂≢y₁) , x₁≢y₂)
          (inj₂ hyp) →
            rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≡ x₂≡z ⟩
            rename-Var x₁ y₁ (cast-Var _ y₂)                          ≡⟨ rename-Var-cast-Var ⟩
            cast-Var _ (rename-Var x₁ y₁ y₂)                          ≡⟨ cong (cast-Var _) $ rename-Var-≢ x₁≢y₂ ⟩
            cast-Var _ y₂                                             ≡⟨ cong (cast-Var _) $ sym $ proj₂ (Σ-≡,≡←≡ hyp) ⟩
            cast-Var _ (cast-Var _ y₁)                                ≡⟨ cast-Var-cast-Var ⟩
            cast-Var _ y₁                                             ≡⟨ cast-Var-irrelevance ⟩
            cast-Var _ y₁                                             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≢ x₂≢y₁ ⟩
            cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
            rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
            rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

      lemma (yes x₁≡z) (no x₂≢z) (no x₂≢y₁) _ =
        rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≢ x₂≢z ⟩
        rename-Var x₁ y₁ z                                        ≡⟨ rename-Var-≡ x₁≡z ⟩
        cast-Var _ y₁                                             ≡⟨ sym $ cong (cast-Var _) $ rename-Var-≢ x₂≢y₁ ⟩
        cast-Var _ (rename-Var x₂ (rename-Var x₁ y₁ y₂) y₁)       ≡⟨ sym rename-Var-cast-Var ⟩
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (cast-Var _ y₁)       ≡⟨ sym $ cong (rename-Var _ _) $ rename-Var-≡ x₁≡z ⟩∎
        rename-Var x₂ (rename-Var x₁ y₁ y₂) (rename-Var x₁ y₁ z)  ∎

      lemma (yes x₁≡z) (no x₂≢z) (yes x₂≡y₁) (yes x₁≡y₂) =
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

      lemma (yes x₁≡z) (no x₂≢z) (yes x₂≡y₁) (no x₁≢y₂) =
        case hyp of λ where
          (inj₁ hyp) → ⊥-elim $ hyp
                         (inj₂ (x₂≡y₁ , x₂≢z ∘ flip trans x₁≡z) , x₁≢y₂)
          (inj₂ hyp) →
            rename-Var x₁ y₁ (rename-Var x₂ y₂ z)                     ≡⟨ cong (rename-Var _ _) $ rename-Var-≢ x₂≢z ⟩
            rename-Var x₁ y₁ z                                        ≡⟨ rename-Var-≡ x₁≡z ⟩
            cast-Var _ y₁                                             ≡⟨ cast-Var-irrelevance ⟩
            cast-Var _ y₁                                             ≡⟨ sym cast-Var-cast-Var ⟩
            cast-Var _ (cast-Var _ y₁)                                ≡⟨ cong (cast-Var _) $ proj₂ (Σ-≡,≡←≡ hyp) ⟩
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

  ----------------------------------------------------------------------
  -- Free variables

  -- These functions return sets containing exactly the free
  -- variables.
  --
  -- Note that this code is not intended to be used at run-time.

  free-Var : Var s → Vars
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

  module _ {x y : Var s} where

    mutual

      free-rename-⊆-Tm :
        ∀ (tˢ : Tmˢ s′) {t} →
        free-Tm tˢ (rename-Tm x y tˢ t) ⊆
        (_ , y) ∷ del (_ , x) (free-Tm tˢ t)
      free-rename-⊆-Tm var {t = z} p =
        p ∈ singleton (_ , rename-Var x y z)                 ↔⟨ ∥∥↔ ∃Var-set F.∘ from-isomorphism ∈singleton≃ ⟩

        p ≡ (_ , rename-Var x y z)                           ↔⟨ ≡,rename-Var≃′ ⟩

        p ≡ (_ , y) × (_ , x) ≡ (_ , z) ⊎
        p ≢ (_ , x) × p ≡ (_ , z)                            ↝⟨ ∣_∣ ∘ [ inj₁ ∘ proj₁ , inj₂ ∘ Σ-map id ≡→∈∷ ]′ ⟩

        p ≡ (_ , y) ∥⊎∥ p ≢ (_ , x) × p ∈ singleton (_ , z)  ↔⟨ F.id ∥⊎∥-cong inverse (∈delete≃ merely-equal?-∃Var) ⟩

        p ≡ (_ , y) ∥⊎∥ p ∈ del (_ , x) (singleton (_ , z))  ↔⟨ inverse ∈∷≃ ⟩□

        p ∈ (_ , y) ∷ del (_ , x) (singleton (_ , z))        □

      free-rename-⊆-Tm (op o asˢ) = free-rename-⊆-Args asˢ

      free-rename-⊆-Args :
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
        (p ≡ (_ , y) ∥⊎∥ p ∈ del (_ , x) (free-Args asˢ as))          ↔⟨ (∥⊎∥-idempotent ∃Var-set ∥⊎∥-cong F.id) F.∘
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

      free-rename-⊆-Arg :
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
          p ≡ (_ , z) × ¬ (_ , x) ≢ (_ , z)  ↝⟨ Σ-map id (λ eq → case (_ ≟∃V _) of [ id , ⊥-elim ∘ eq ]′) ⟩
          p ≡ (_ , z) × (_ , x) ≡ (_ , z)    ↝⟨ (uncurry λ eq₁ eq₂ → trans eq₁ (sym eq₂)) ⟩
          p ≡ (_ , x)                        ↝⟨ proj₁ (_≃_.to (∈delete≃ {z = free-Arg aˢ a} merely-equal?-∃Var) p∈) ⟩□
          ⊥                                  □

    mutual

      ⊆-free-rename-Tm :
        ∀ (tˢ : Tmˢ s′) {t} →
        free-Tm tˢ t ⊆
        (_ , x) ∷ (_ , y) ∷ free-Tm tˢ (rename-Tm x y tˢ t)
      ⊆-free-rename-Tm var {t = z} p =
        p ∈ singleton (_ , z)                                           ↔⟨ ∈singleton≃ ⟩

        ∥ p ≡ (_ , z) ∥                                                 ↝⟨ (Trunc.rec ∥⊎∥-propositional λ p≡z → case p ≟∃V (_ , x) of
                                                                            [ ∣inj₁∣ , ∣inj₂∣ ∘ ∣inj₂∣ ∘ ∣inj₂∣ ∘ (_, p≡z) ]′) ⟩
        p ≡ (_ , x) ∥⊎∥ p ≡ (_ , y) ∥⊎∥
        (p ≡ (_ , y) × (_ , x) ≡ (_ , z) ∥⊎∥
         p ≢ (_ , x) × p ≡ (_ , z))                                     ↔⟨ inverse $ F.id ∥⊎∥-cong F.id ∥⊎∥-cong ∥∥-cong ≡,rename-Var≃′ ⟩

        p ≡ (_ , x) ∥⊎∥ p ≡ (_ , y) ∥⊎∥ ∥ p ≡ (_ , rename-Var x y z) ∥  ↔⟨ inverse $ (F.id ∥⊎∥-cong (F.id ∥⊎∥-cong ∈singleton≃) F.∘ ∈∷≃) F.∘ ∈∷≃ ⟩□

        p ∈ (_ , x) ∷ (_ , y) ∷ singleton (_ , rename-Var x y z)        □

      ⊆-free-rename-Tm (op o asˢ) = ⊆-free-rename-Args asˢ

      ⊆-free-rename-Args :
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

      ⊆-free-rename-Arg :
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
                                                        [ (λ p≡y _ → ∣inj₂∣ (∣inj₁∣ p≡y))
                                                        , (λ p≢y → uncurry λ p≢z → id ∥⊎∥-cong id ∥⊎∥-cong (lemma p≢y p≢z ,_))
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

  module _ (x : Var s) where

    Free-in-var′ : Var s′ → Proposition ℓ
    Free-in-var′ y =
        _≡_ {A = ∃Var} (_ , x) (_ , y)
      , ∃Var-set

    mutual

      Free-in-term′ :
        ∀ (tˢ : Tmˢ s′) t →
        @0 Wf-tm ((_ , x) ∷ xs) tˢ t → Proposition ℓ
      Free-in-term′ var y _ = Free-in-var′ y

      Free-in-term′ (op o asˢ) as wf =
        Free-in-arguments′ asˢ as wf

      Free-in-arguments′ :
        ∀ (asˢ : Argsˢ vs) as →
        @0 Wf-args ((_ , x) ∷ xs) asˢ as → Proposition ℓ
      Free-in-arguments′ nil _ _ = ⊥ , ⊥-propositional

      Free-in-arguments′ (cons aˢ asˢ) (a , as) (wf , wfs) =
          (proj₁ (Free-in-argument′ aˢ a wf) ∥⊎∥
           proj₁ (Free-in-arguments′ asˢ as wfs))
        , ∥⊎∥-propositional

      Free-in-argument′ :
        ∀ (aˢ : Argˢ v) a →
        @0 Wf-arg ((_ , x) ∷ xs) aˢ a → Proposition ℓ
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
        Π : (A : Type ℓ) → (A → Proposition ℓ) → Proposition ℓ
        Π A B =
            (∀ x → proj₁ (B x))
          , Π-closure ext 1 λ x →
            proj₂ (B x)

    Free-in-variable : Variable ((_ , x) ∷ xs) s′ → Type ℓ
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
  -- free in a term is propositional.

  module _ {x : Var s} where

    Free-in-variable-propositional :
      (y : Variable ((_ , x) ∷ xs) s′) →
      Is-proposition (Free-in-variable x y)
    Free-in-variable-propositional (y , _) =
      proj₂ (Free-in-var′ _ y)

    Free-in-term-propositional :
      (t : Term ((_ , x) ∷ xs) s′) →
      Is-proposition (Free-in-term x t)
    Free-in-term-propositional (t , tˢ , [ wf ]) =
      proj₂ (Free-in-term′ _ t tˢ wf)

    Free-in-arguments-propositional :
      (as : Arguments ((_ , x) ∷ xs) vs) →
      Is-proposition (Free-in-arguments x as)
    Free-in-arguments-propositional (as , asˢ , [ wfs ]) =
      proj₂ (Free-in-arguments′ _ as asˢ wfs)

    Free-in-argument-propositional :
      (a : Argument ((_ , x) ∷ xs) v) →
      Is-proposition (Free-in-argument x a)
    Free-in-argument-propositional (a , aˢ , [ wf ]) =
      proj₂ (Free-in-argument′ _ a aˢ wf)

  -- Variables that are free according to the alternative definition
  -- are in the set of free variables.

  Free-free-Var :
    {x : Var s} {y : Var s′}
    (@0 wf : Wf-var ((_ , x) ∷ xs) y) →
    Free-in-variable x (y , [ wf ]) → (_ , x) ∈ free-Var y
  Free-free-Var _ = ≡→∈singleton

  mutual

    Free-free-Tm :
      ∀ {x : Var s} {xs}
      (tˢ : Tmˢ s′) {t} (@0 wf : Wf-tm ((_ , x) ∷ xs) tˢ t) →
      Free-in-term x (tˢ , t , [ wf ]) → (_ , x) ∈ free-Tm tˢ t
    Free-free-Tm var        = Free-free-Var
    Free-free-Tm (op o asˢ) = Free-free-Args asˢ

    Free-free-Args :
      ∀ {x : Var s} {xs}
      (asˢ : Argsˢ vs) {as} (@0 wf : Wf-args ((_ , x) ∷ xs) asˢ as) →
      Free-in-arguments x (asˢ , as , [ wf ]) →
      (_ , x) ∈ free-Args asˢ as
    Free-free-Args {x = x} (cons aˢ asˢ) {as = a , as} (wf , wfs) =
      Free-in-argument x (aˢ , a , [ wf ]) ∥⊎∥
      Free-in-arguments x (asˢ , as , [ wfs ])                ↝⟨ Free-free-Arg aˢ wf ∥⊎∥-cong Free-free-Args asˢ wfs ⟩

      (_ , x) ∈ free-Arg aˢ a ∥⊎∥ (_ , x) ∈ free-Args asˢ as  ↔⟨ inverse ∈∪≃ ⟩□

      (_ , x) ∈ free-Arg aˢ a ∪ free-Args asˢ as              □

    Free-free-Arg :
      ∀ {x : Var s} {xs}
      (aˢ : Argˢ v) {a} (@0 wf : Wf-arg ((_ , x) ∷ xs) aˢ a) →
      Free-in-argument x (aˢ , a , [ wf ]) → (_ , x) ∈ free-Arg aˢ a
    Free-free-Arg (nil tˢ) = Free-free-Tm tˢ

    Free-free-Arg {x = x} {xs = xs} (cons aˢ) {a = y , a} wf =
      let xxs              = (_ , x) ∷ xs
          x₁ ,         x₁∉ = fresh xxs
          x₂ , x₂≢x₁ , x₂∉ =                                       $⟨ fresh ((_ , x₁) ∷ xxs) ⟩
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
  -- the alternative definition.

  free-Free-Var :
    {x : Var s′} {y : Var s}
    (@0 wf : Wf-var ((_ , x) ∷ xs) y) →
    (_ , x) ∈ free-Var y → Free-in-variable x (y , [ wf ])
  free-Free-Var {x = x} {y = y} _ =
    (_ , x) ∈ singleton (_ , y)  ↔⟨ ∈singleton≃ ⟩
    ∥ (_ , x) ≡ (_ , y) ∥        ↔⟨ ∥∥↔ ∃Var-set ⟩□
    (_ , x) ≡ (_ , y)            □

  mutual

    free-Free-Tm :
      ∀ {x : Var s′} {xs}
      (tˢ : Tmˢ s) {t} (@0 wf : Wf-tm ((_ , x) ∷ xs) tˢ t) →
      (_ , x) ∈ free-Tm tˢ t → Free-in-term x (tˢ , t , [ wf ])
    free-Free-Tm var        = free-Free-Var
    free-Free-Tm (op o asˢ) = free-Free-Args asˢ

    free-Free-Args :
      ∀ {x : Var s′} {xs}
      (asˢ : Argsˢ vs) {as} (@0 wf : Wf-args ((_ , x) ∷ xs) asˢ as) →
      (_ , x) ∈ free-Args asˢ as →
      Free-in-arguments x (asˢ , as , [ wf ])
    free-Free-Args
      {x = x} (cons aˢ asˢ) {as = a , as} (wf , wfs) =

      (_ , x) ∈ free-Arg aˢ a ∪ free-Args asˢ as              ↔⟨ ∈∪≃ ⟩

      (_ , x) ∈ free-Arg aˢ a ∥⊎∥ (_ , x) ∈ free-Args asˢ as  ↝⟨ free-Free-Arg aˢ wf ∥⊎∥-cong free-Free-Args asˢ wfs ⟩□

      Free-in-argument x (aˢ , a , [ wf ]) ∥⊎∥
      Free-in-arguments x (asˢ , as , [ wfs ])                □

    free-Free-Arg :
      ∀ {x : Var s′} {xs}
      (aˢ : Argˢ v) {a} (@0 wf : Wf-arg ((_ , x) ∷ xs) aˢ a) →
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
            x₁ ,         x₁∉ = fresh (xs ∪ fs)
            x₂ , x₂≢x₁ , x₂∉ =                                           $⟨ fresh ((_ , x₁) ∷ xs ∪ fs) ⟩
              (∃ λ x₂ → ¬ (_ , x₂) ∈ (_ , x₁) ∷ xs ∪ fs)                 ↝⟨ (∃-cong λ _ → →-cong₁ ext ∈∷≃) ⟩
              (∃ λ x₂ → ¬ ((_ , x₂) ≡ (_ , x₁) ∥⊎∥ (_ , x₂) ∈ xs ∪ fs))  ↝⟨ (∃-cong λ _ → Π∥⊎∥↔Π×Π λ _ → ⊥-propositional) ⟩□
              (∃ λ x₂ → (_ , x₂) ≢ (_ , x₁) × ¬ (_ , x₂) ∈ xs ∪ fs)      □
        in
        y ∈ free-Arg aˢ a                                            ↝⟨ (λ y∈ _ z∉ → (λ y≡z → z∉ (subst (_∈ _) y≡z y∈))
                                                                                   , ⊆-free-rename-Arg aˢ _ y∈) ⟩
        (∀ z → ¬ (_ , z) ∈ free-Arg aˢ a →
         y ≢ (_ , z) ×
         y ∈ (_ , x) ∷ (_ , z) ∷ free-Arg aˢ (rename-Arg x z aˢ a))  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → uncurry λ y≢z →
                                                                         to-implication (∈≢∷≃ y≢z F.∘ ∈≢∷≃ y≢x)) ⟩
        (∀ z → ¬ (_ , z) ∈ free-Arg aˢ a →
         y ∈ free-Arg aˢ (rename-Arg x z aˢ a))                      ↝⟨ (λ hyp → free-⊆-Arg aˢ (wf x₁ (x₁∉ ∘ ∈→∈∪ˡ)) y (hyp x₁ (x₁∉ ∘ ∈→∈∪ʳ xs))
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
  … | no x≢z =                $⟨ z∈ ⟩
      (_ , z) ∈ (_ , x) ∷ xs  ↔⟨ ∈≢∷≃ (x≢z ∘ sym) ⟩
      (_ , z) ∈ xs            ↝⟨ ∈→∈∷ ⟩□
      (_ , z) ∈ (_ , y) ∷ xs  □

  … | yes x≡z =
    ≡→∈∷ $ Σ-≡,≡→≡
      (sym (cong proj₁ x≡z))
      (cast-Var (sym (cong proj₁ x≡z)) (cast-Var (cong proj₁ x≡z) y)  ≡⟨ subst-sym-subst _ ⟩∎
       y                                                              ∎)

  @0 rename-Wf-tm :
    ∀ (tˢ : Tmˢ s) {t} →
    Wf-tm ((_ , x) ∷ xs) tˢ t →
    Wf-tm ((_ , y) ∷ xs) tˢ (rename-Tm x y tˢ t)
  rename-Wf-tm {x = x} {xs = xs} {y = y} tˢ {t = t} wf =             $⟨ wf-free-Tm tˢ ⟩
    Wf-tm (free-Tm tˢ (rename-Tm x y tˢ t)) tˢ (rename-Tm x y tˢ t)  ↝⟨ weaken-Wf-tm (⊆∷delete→⊆∷→⊆∷ (free-rename-⊆-Tm tˢ) (free-⊆-Tm tˢ wf)) tˢ ⟩□
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

  module _ {ys} (x : Var s) (t : Term ys s) where

    -- Substitution for variables.

    subst-Variable : Variable ((_ , x) ∷ xs) s′ → Term (xs ∪ ys) s′
    subst-Variable {xs = xs} (y , [ y∈x∷xs ]) =
      case (_ , y) ≟∃V (_ , x) of λ where
        (no y≢x)  → var-wf y (∈→∈∪ˡ (_≃_.to (∈≢∷≃ y≢x) y∈x∷xs))
        (yes y≡x) →
          subst (λ ([ s ] , _) → Term (xs ∪ ys) s) (sym y≡x) $
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
          (inj₁ x≡y) →
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
          (inj₂ x≢y) →
            -- Otherwise, rename the bound variable to something fresh
            -- and keep substituting.
            let z , z∉             = fresh ((_ , x) ∷ xs ∪ ys)
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
