------------------------------------------------------------------------
-- Abstract binding trees, based on Harper's "Practical Foundations
-- for Programming Languages"
------------------------------------------------------------------------

-- Operators are not indexed by symbolic parameters.

{-# OPTIONS --cubical --safe #-}

open import Equality

module Abstract-binding-tree
  {e⁺} (eq-J : ∀ {a p} → Equality-with-J a p e⁺) where

private
  open module D = Derived-definitions-and-properties eq-J

open import Logical-equivalence using (_⇔_; Dec-map)
open import Prelude

import Bijection eq-J as Bijection
open import Equality.Decidable-UIP eq-J
open import Equality.Decision-procedures eq-J
open import Equality.Path.Isomorphisms eq-J
open import Equivalence eq-J as Eq using (_≃_)
open import Erased.Cubical eq-J as E
open import Finite-subset.Listed eq-J as L
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J
open import H-level.Closure eq-J
open import H-level.Truncation.Propositional eq-J as Trunc
open import List eq-J hiding (tail)

------------------------------------------------------------------------
-- Signatures

private
 module Dummy where

  -- Signatures for abstract binding trees.

  record Signature ℓ : Set (lsuc ℓ) where
    infix 4 _≟S_ _≟O_ _≟∃V_

    field
      -- A set of sorts with decidable equality.
      Sort : Set ℓ
      _≟S_ : Decidable-equality Sort

    -- Valences.

    Valence : Set ℓ
    Valence = List Sort × Sort

    field
      -- Codomain-indexed operators with decidable equality and
      -- domains.
      Op     : @0 Sort → Set ℓ
      _≟O_   : ∀ {@0 s} → Decidable-equality (Op s)
      domain : ∀ {@0 s} → Op s → List Valence

      -- A sort-indexed type of variables with decidable equality.
      Var : @0 Sort → Set ℓ

    -- Non-indexed variables

    ∃Var : Set ℓ
    ∃Var = ∃ λ (s : Erased Sort) → Var (erased s)

    field
      -- Decidable equality for non-indexed variables.
      _≟∃V_ : Decidable-equality ∃Var

    -- Arities.

    Arity : Set ℓ
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
      @0 A                   : Set ℓ
      @0 wf wfs x x′ y x₁ x₂ : A
      @0 eq eq₁ eq₂          : x ≡ y
      @0 s s′                : Sort
      @0 ss                  : List Sort
      @0 v v₁ v₂             : Valence
      @0 vs vs′ vs₁ vs₂      : List Valence
      @0 o                   : Op s

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

    data Tmˢ (@0 s : Sort) : Set ℓ where
      var : Tmˢ s
      op  : (o : Op s) → Argsˢ (domain o) → Tmˢ s

    -- Sequences of arguments.

    data Argsˢ : @0 List Valence → Set ℓ where
      nil  : Argsˢ []
      cons : Argˢ v → Argsˢ vs → Argsˢ (v ∷ vs)

    -- Arguments.

    data Argˢ : @0 Valence → Set ℓ where
      nil  : Tmˢ s → Argˢ ([] , s)
      cons : Argˢ (ss , s′) → Argˢ (s ∷ ss , s′)

  ----------------------------------------------------------------------
  -- Raw terms

  -- Raw (possibly ill-scoped) terms.

  mutual

    Tm : Tmˢ s → Set ℓ
    Tm {s = s} var       = Var s
    Tm         (op o as) = Args as

    Args : Argsˢ vs → Set ℓ
    Args nil         = ↑ _ ⊤
    Args (cons a as) = Arg a × Args as

    Arg : Argˢ v → Set ℓ
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

  -- Finite subsets of variables.

  Vars : Set ℓ
  Vars = Finite-subset-of ∃Var

  private
    variable
      @0 xs : Vars

  -- Predicates for well-formed variables, terms and arguments.

  Wf-var : Vars → Var s → Set ℓ
  Wf-var xs x = (_ , x) ∈ xs

  mutual

    Wf-tm : Vars → (tˢ : Tmˢ s) → Tm tˢ → Set ℓ
    Wf-tm xs var        = Wf-var xs
    Wf-tm xs (op o asˢ) = Wf-args xs asˢ

    Wf-args : Vars → (asˢ : Argsˢ vs) → Args asˢ → Set ℓ
    Wf-args _  nil           _        = ↑ _ ⊤
    Wf-args xs (cons aˢ asˢ) (a , as) =
      Wf-arg xs aˢ a × Wf-args xs asˢ as

    Wf-arg : Vars → (aˢ : Argˢ v) → Arg aˢ → Set ℓ
    Wf-arg xs (nil tˢ)  t       = Wf-tm xs tˢ t
    Wf-arg xs (cons aˢ) (x , a) =
      ∀ y → ¬ (_ , y) ∈ xs →
      Wf-arg ((_ , y) ∷ xs) aˢ (rename-Arg x y aˢ a)

  -- Well-formed variables.

  Variable : @0 Vars → @0 Sort → Set ℓ
  Variable xs s = ∃ λ (x : Var s) → Erased (Wf-var xs x)

  -- Well-formed terms.

  Term : @0 Vars → @0 Sort → Set ℓ
  Term xs s =
    ∃ λ (tˢ : Tmˢ s) → ∃ λ (t : Tm tˢ) → Erased (Wf-tm xs tˢ t)

  -- Well-formed sequences of arguments.

  Arguments : @0 Vars → @0 List Valence → Set ℓ
  Arguments xs vs =
    ∃ λ (asˢ : Argsˢ vs) → ∃ λ (as : Args asˢ) →
    Erased (Wf-args xs asˢ as)

  -- Well-formed arguments.

  Argument : @0 Vars → @0 Valence → Set ℓ
  Argument xs v =
    ∃ λ (aˢ : Argˢ v) → ∃ λ (a : Arg aˢ) → Erased (Wf-arg xs aˢ a)

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
    RHS : Erased (List Valence) → Set ℓ
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
    lemma₁ {as = as} = D.elim¹ _
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
     (∃ λ (([ s ] , [ ss , s′ ] , _) :
           Erased Sort × ∃ λ v → Argˢ (erased v)) →
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
    RHS : Erased Valence → Set ℓ
    RHS [ v ] =
      (∃ λ (([ s ] , _) : ∃ λ s → Tmˢ (erased s)) →
         Erased (([] , s) ≡ v)) ⊎
      (∃ λ (([ s ] , [ ss , s′ ] , _) :
            Erased Sort × ∃ λ v → Argˢ (erased v)) →
       Erased ((s ∷ ss , s′) ≡ v))

    to : Argˢ v → RHS [ v ]
    to (nil t)          = inj₁ ((_ , t) , [ refl _ ])
    to (cons {s = s} a) = inj₂ (([ s ] , _ , a) , [ refl _ ])

    from : RHS [ v ] → Argˢ v
    from (inj₁ ((_ , t) , [ eq ])) =
      subst (λ v → Argˢ (erased v)) ([]-cong [ eq ]) (nil t)
    from (inj₂ (([ s ] , _ , a) , [ eq ])) =
      subst (λ v → Argˢ (erased v)) ([]-cong [ eq ]) (cons {s = s} a)

    lemma₁ :
      ∀ {v₁ v₂ a} (eq : v₁ ≡ v₂) →
      to (subst (λ v → Argˢ (erased v)) eq a) ≡
      subst RHS eq (to a)
    lemma₁ {a = a} = D.elim¹ _
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

    to∘from (inj₂ (([ s ] , [ ss , s′ ] , a) , [ eq ])) =
      to (subst (λ v → Argˢ (erased v))
                ([]-cong [ eq ])
                (cons {s = s} a))                            ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to (cons {s = s} a))       ≡⟨⟩

      subst RHS ([]-cong [ eq ])
            (inj₂ (([ s ] , _ , a) , [ refl _ ]))            ≡⟨ push-subst-inj₂ _ _ ⟩

      inj₂ (subst _
                  ([]-cong [ eq ])
                  (([ s ] , _ , a) , [ refl _ ]))            ≡⟨ cong inj₂ (push-subst-pair-× _ _) ⟩

      inj₂ ( ([ s ] , _ , a)
           , subst (λ ([ v ]) → Erased ((s ∷ ss , s′) ≡ v))
                   ([]-cong [ eq ])
                   [ refl _ ]
           )                                                 ≡⟨ cong (λ eq → inj₂ (([ s ] , _ , a) , eq)) $
                                                                H-level-Erased 1 Valence-set _ _ ⟩∎
      inj₂ (([ s ] , _ , a) , [ eq ])                        ∎

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
