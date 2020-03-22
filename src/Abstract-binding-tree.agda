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
open import Finite-subset.Listed eq-J
open import Function-universe eq-J as F hiding (_∘_)
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
  -- Raw terms

  mutual

    -- Raw (possibly ill-scoped) terms.

    data Tm : @0 Sort → Set ℓ where
      var : Var s → Tm s
      op  : (o : Op s) → Args (domain o) → Tm s

    -- Sequences of raw arguments.

    data Args : @0 List Valence → Set ℓ where
      nil  : Args []
      cons : Arg v → Args vs → Args (v ∷ vs)

    -- Raw arguments.

    data Arg : @0 Valence → Set ℓ where
      nil  : Tm s → Arg ([] , s)
      cons : Var s → Arg (ss , s′) → Arg (s ∷ ss , s′)

  module _ (x y : Var s) where

    mutual

      -- The term rename t is t with each (free or bound) occurrence
      -- of x replaced by y.

      rename : Tm s′ → Tm s′
      rename (var z)   = var (rename-Var z)
      rename (op o as) = op o (rename-Args as)

      rename-Var : Var s′ → Var s′
      rename-Var z = case (_ , x) ≟∃V (_ , z) of λ where
        (no _)    → z
        (yes x≡z) → subst (λ ([ s ] , _) → Var s) x≡z y

      rename-Args : Args vs → Args vs
      rename-Args nil         = nil
      rename-Args (cons a as) = cons (rename-Arg a) (rename-Args as)

      rename-Arg : Arg (ss , s′) → Arg (ss , s′)
      rename-Arg (nil t)       = nil (rename t)
      rename-Arg (cons z rest) = cons (rename-Var z) (rename-Arg rest)

  ----------------------------------------------------------------------
  -- Well-formed terms

  -- A finite subset of variables.

  Vars : Set ℓ
  Vars = Finite-subset-of ∃Var

  private
    variable
      @0 t t₁ t₂                  : Tm s
      @0 a a′ a₁ a₂ a′₁ a′₂       : Arg v
      @0 as as′ as₁ as₂ as′₁ as′₂ : Args vs
      @0 xs                       : Vars

  -- Predicates for well-formed terms and arguments.

  mutual

    data Wf-tm (xs : Vars) : Tm s → Set ℓ where
      var : (_ , x) ∈ xs → Wf-tm xs (var x)
      op  : Wf-args xs as → Wf-tm xs (op o as)

    data Wf-args (xs : Vars) : Args vs → Set ℓ where
      nil  : Wf-args xs nil
      cons : Wf-arg xs a → Wf-args xs as → Wf-args xs (cons a as)

    data Wf-arg (xs : Vars) : Arg v → Set ℓ where
      nil  : Wf-tm xs t → Wf-arg xs (nil t)
      cons : ((y : Var s) → ¬ (_ , y) ∈ xs →
              Wf-arg ((_ , y) ∷ xs) (rename-Arg x y a)) →
             Wf-arg xs (cons x a)

  -- Well-formed terms.

  Term : @0 Vars → @0 Sort → Set ℓ
  Term xs s = ∃ λ (t : Tm s) → Erased (Wf-tm xs t)

  -- Well-formed sequences of arguments.

  Arguments : @0 Vars → @0 List Valence → Set ℓ
  Arguments xs vs = ∃ λ (as : Args vs) → Erased (Wf-args xs as)

  -- Well-formed arguments.

  Argument : @0 Vars → @0 Valence → Set ℓ
  Argument xs v = ∃ λ (a : Arg v) → Erased (Wf-arg xs a)

  ----------------------------------------------------------------------
  -- Equality is decidable for terms

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

  -- Rearrangement lemmas for Tm, Args and Arg.

  Tm≃ : Tm s ≃ (Var s ⊎ ∃ λ (o : Op s) → Args (domain o))
  Tm≃ = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = λ where
                   (var s)   → inj₁ s
                   (op o as) → inj₂ (o , as)
        ; from = λ where
                   (inj₁ s)        → var s
                   (inj₂ (o , as)) → op o as
        }
      ; right-inverse-of = λ where
          (inj₁ _) → refl _
          (inj₂ _) → refl _
      }
    ; left-inverse-of = λ where
        (var _)  → refl _
        (op _ _) → refl _
    })

  Args≃ :
    Args vs ≃
    (Erased ([] ≡ vs) ⊎
     (∃ λ ((([ v ] , _) , [ vs′ ] , _) :
           (∃ λ v → Arg (erased v)) ×
           (∃ λ vs′ → Args (erased vs′))) →
        Erased (v ∷ vs′ ≡ vs)))
  Args≃ = Eq.↔⇒≃ (record
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
            (∃ λ v → Arg (erased v)) ×
            (∃ λ vs′ → Args (erased vs′))) →
         Erased (v ∷ vs′ ≡ vs)))

    to : Args vs → RHS [ vs ]
    to nil         = inj₁ [ refl _ ]
    to (cons a as) = inj₂ (((_ , a) , _ , as) , [ refl _ ])

    from : RHS [ vs ] → Args vs
    from (inj₁ [ eq ]) =
      subst (λ vs → Args (erased vs)) ([]-cong [ eq ]) nil
    from (inj₂ (((_ , a) , _ , as) , [ eq ])) =
      subst (λ vs → Args (erased vs)) ([]-cong [ eq ]) (cons a as)

    lemma₁ :
      ∀ {vs₁ vs₂ as} (eq : vs₁ ≡ vs₂) →
      to (subst (λ vs → Args (erased vs)) eq as) ≡
      subst RHS eq (to as)
    lemma₁ {as = as} = D.elim¹ _
      (to (subst (λ vs → Args (erased vs)) (refl _) as)  ≡⟨ cong to $ subst-refl _ _ ⟩
       to as                                             ≡⟨ sym $ subst-refl _ _ ⟩∎
       subst RHS (refl _) (to as)                        ∎)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ [ eq ]) =
      to (subst (λ vs → Args (erased vs)) ([]-cong [ eq ]) nil)         ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to nil)                               ≡⟨⟩

      subst RHS ([]-cong [ eq ]) (inj₁ [ refl _ ])                      ≡⟨ push-subst-inj₁ _ _ ⟩

      inj₁ (subst (λ vs → Erased ([] ≡ erased vs))
                  ([]-cong [ eq ]) [ refl _ ])                          ≡⟨ cong inj₁ $ H-level-Erased 1 (H-level-List 0 Valence-set) _ _ ⟩∎

      inj₁ [ eq ]                                                       ∎

    to∘from (inj₂ ((([ v ] , a) , [ vs′ ] , as) , [ eq ])) =
      to (subst (λ vs → Args (erased vs)) ([]-cong [ eq ]) (cons a as))  ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to (cons a as))                        ≡⟨⟩

      subst RHS ([]-cong [ eq ])
            (inj₂ (((_ , a) , _ , as) , [ refl _ ]))                     ≡⟨ push-subst-inj₂ _ _ ⟩

      inj₂ (subst _
                  ([]-cong [ eq ])
                  (((_ , a) , _ , as) , [ refl _ ]))                     ≡⟨ cong inj₂ (push-subst-pair-× _ _) ⟩

      inj₂ ( ((_ , a) , _ , as)
           , subst (λ ([ vs ]) → Erased (v ∷ vs′ ≡ vs))
                   ([]-cong [ eq ])
                   [ refl _ ]
           )                                                             ≡⟨ cong (λ eq → inj₂ (((_ , a) , _ , as) , eq)) $
                                                                            H-level-Erased 1 (H-level-List 0 Valence-set) _ _ ⟩∎
      inj₂ (((_ , a) , _ , as) , [ eq ])                                 ∎

    lemma₂ :
      {as : Args vs} →
      subst (λ vs → Args (erased vs)) ([]-cong [ refl _ ]) as ≡ as
    lemma₂ {as = as} =
      subst (λ vs → Args (erased vs)) ([]-cong [ refl _ ]) as  ≡⟨ cong (λ eq → subst (λ vs → Args (erased vs)) eq _) []-cong-[refl] ⟩
      subst (λ vs → Args (erased vs)) (refl _) as              ≡⟨ subst-refl _ _ ⟩∎
      as                                                       ∎

    from∘to : ∀ x → from (to x) ≡ x
    from∘to nil        = lemma₂
    from∘to (cons _ _) = lemma₂

  Arg≃ :
    Arg v ≃
    ((∃ λ (([ s ] , _) : ∃ λ s → Tm (erased s)) →
        Erased (([] , s) ≡ v)) ⊎
     (∃ λ ((([ s ] , _) , [ ss , s′ ] , _) :
           ∃Var × ∃ λ v → Arg (erased v)) →
      Erased ((s ∷ ss , s′) ≡ v)))
  Arg≃ = Eq.↔⇒≃ (record
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
      (∃ λ (([ s ] , _) : ∃ λ s → Tm (erased s)) →
         Erased (([] , s) ≡ v)) ⊎
      (∃ λ ((([ s ] , _) , [ ss , s′ ] , _) :
            ∃Var × ∃ λ v → Arg (erased v)) →
       Erased ((s ∷ ss , s′) ≡ v))

    to : Arg v → RHS [ v ]
    to (nil t)    = inj₁ ((_ , t) , [ refl _ ])
    to (cons x a) = inj₂ (((_ , x) , _ , a) , [ refl _ ])

    from : RHS [ v ] → Arg v
    from (inj₁ ((_ , t) , [ eq ])) =
      subst (λ v → Arg (erased v)) ([]-cong [ eq ]) (nil t)
    from (inj₂ (((_ , x) , _ , a) , [ eq ])) =
      subst (λ v → Arg (erased v)) ([]-cong [ eq ]) (cons x a)

    lemma₁ :
      ∀ {v₁ v₂ a} (eq : v₁ ≡ v₂) →
      to (subst (λ v → Arg (erased v)) eq a) ≡
      subst RHS eq (to a)
    lemma₁ {a = a} = D.elim¹ _
      (to (subst (λ v → Arg (erased v)) (refl _) a)  ≡⟨ cong to $ subst-refl _ _ ⟩
       to a                                          ≡⟨ sym $ subst-refl _ _ ⟩∎
       subst RHS (refl _) (to a)                     ∎)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ (([ s ] , t) , [ eq ])) =
      to (subst (λ v → Arg (erased v)) ([]-cong [ eq ]) (nil t))      ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to (nil t))                         ≡⟨⟩

      subst RHS ([]-cong [ eq ]) (inj₁ ((_ , t) , [ refl _ ]))        ≡⟨ push-subst-inj₁ _ _ ⟩

      inj₁ (subst (λ v → ∃ λ (([ s ] , _) : ∃ λ s → Tm (erased s)) →
                           Erased (([] , s) ≡ erased v))
                  ([]-cong [ eq ])
                  ((_ , t) , [ refl _ ]))                             ≡⟨ cong inj₁ $ push-subst-pair-× _ _ ⟩

      inj₁ ( (_ , t)
           , subst (λ v → Erased (([] , s) ≡ erased v))
                   ([]-cong [ eq ])
                   [ refl _ ]
           )                                                          ≡⟨ cong (λ eq → inj₁ ((_ , t) , eq)) $
                                                                         H-level-Erased 1 Valence-set _ _ ⟩∎
      inj₁ ((_ , t) , [ eq ])                                         ∎

    to∘from (inj₂ ((([ s ] , x) , [ ss , s′ ] , a) , [ eq ])) =
      to (subst (λ v → Arg (erased v)) ([]-cong [ eq ]) (cons x a))  ≡⟨ lemma₁ _ ⟩

      subst RHS ([]-cong [ eq ]) (to (cons x a))                     ≡⟨⟩

      subst RHS ([]-cong [ eq ])
            (inj₂ (((_ , x) , _ , a) , [ refl _ ]))                  ≡⟨ push-subst-inj₂ _ _ ⟩

      inj₂ (subst _
                  ([]-cong [ eq ])
                  (((_ , x) , _ , a) , [ refl _ ]))                  ≡⟨ cong inj₂ (push-subst-pair-× _ _) ⟩

      inj₂ ( ((_ , x) , _ , a)
           , subst (λ ([ v ]) → Erased ((s ∷ ss , s′) ≡ v))
                   ([]-cong [ eq ])
                   [ refl _ ]
           )                                                         ≡⟨ cong (λ eq → inj₂ (((_ , x) , _ , a) , eq)) $
                                                                        H-level-Erased 1 Valence-set _ _ ⟩∎
      inj₂ (((_ , x) , _ , a) , [ eq ])                              ∎

    lemma₂ :
      {a : Arg v} →
      subst (λ v → Arg (erased v)) ([]-cong [ refl _ ]) a ≡ a
    lemma₂ {a = a} =
      subst (λ v → Arg (erased v)) ([]-cong [ refl _ ]) a  ≡⟨ cong (λ eq → subst (λ v → Arg (erased v)) eq _) []-cong-[refl] ⟩
      subst (λ v → Arg (erased v)) (refl _) a              ≡⟨ subst-refl _ _ ⟩∎
      a                                                    ∎

    from∘to : ∀ x → from (to x) ≡ x
    from∘to (nil _)    = lemma₂
    from∘to (cons _ _) = lemma₂

  -- Equality is decidable for Var, Tm, Args and Arg.

  infix 4 _≟V_ _≟Tm_ _≟Args_ _≟Arg_

  _≟V_ : Decidable-equality (Var s)
  _≟V_ {s = s} x₁ x₂ =                                   $⟨ _ ≟∃V _ ⟩

    Dec (([ s ] , x₁) ≡ ([ s ] , x₂))                    ↝⟨ Dec-map $ from-isomorphism $ inverse Bijection.Σ-≡,≡↔≡ ⟩

    Dec (∃ λ (eq : [ s ] ≡ [ s ]) →
           subst (λ s → Var (erased s)) eq x₁ ≡ x₂)      ↝⟨ Dec-map $ from-isomorphism $ drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                            propositional⇒inhabited⇒contractible (H-level-Erased 2 Sort-set) (refl _) ⟩

    Dec (subst (λ s → Var (erased s)) _ x₁ ≡ x₂)         ↝⟨ ≡⇒↝ _ $ cong (λ eq → Dec (subst _ eq _ ≡ _)) $ H-level-Erased 2 Sort-set _ _ ⟩

    Dec (subst (λ s → Var (erased s)) (refl _) x₁ ≡ x₂)  ↝⟨ ≡⇒↝ _ $ cong (λ x → Dec (x ≡ _)) $ subst-refl _ _ ⟩□

    Dec (x₁ ≡ x₂)                                        □

  mutual

    _≟Tm_ : Decidable-equality (Tm s)
    var x₁ ≟Tm var x₂ =      $⟨ _ ≟V _ ⟩
      Dec (x₁ ≡ x₂)          ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ from-isomorphism Bijection.≡↔inj₁≡inj₁ ⟩□
      Dec (var x₁ ≡ var x₂)  □

    var _ ≟Tm op _ _ =      $⟨ no (λ ()) ⟩
      Dec ⊥                 ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (var _ ≡ op _ _)  □

    op _ _ ≟Tm var _ =      $⟨ no (λ ()) ⟩
      Dec ⊥                 ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (op _ _ ≡ var _)  □

    op o₁ as₁ ≟Tm op o₂ as₂ =        $⟨ Σ.decidable⇒dec⇒dec _≟O_ (λ _ → _ ≟Args as₂) ⟩
      Dec ((o₁ , as₁) ≡ (o₂ , as₂))  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□
      Dec (op o₁ as₁ ≡ op o₂ as₂)    □

    _≟Args_ : Decidable-equality (Args vs)
    nil ≟Args nil =                  $⟨ yes (refl _) ⟩
      Dec ([ refl _ ] ≡ [ refl _ ])  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Args≃) F.∘ from-isomorphism Bijection.≡↔inj₁≡inj₁ ⟩□
      Dec (nil ≡ nil)                □

    cons a₁ as₁ ≟Args cons a₂ as₂ =                      $⟨ ×.dec⇒dec⇒dec
                                                              (Σ.set⇒dec⇒dec⇒dec
                                                                 (H-level-Erased 2 (×-closure 2 (H-level-List 0 Sort-set) Sort-set))
                                                                 (yes (refl _))
                                                                 (λ _ → _ ≟Arg a₂))
                                                              (Σ.set⇒dec⇒dec⇒dec
                                                                 (H-level-Erased 2 (H-level-List 0 Valence-set))
                                                                 (yes (refl _))
                                                                 (λ _ → _ ≟Args as₂)) ⟩

      Dec (((_ , a₁) , _ , as₁) ≡ ((_ , a₂) , _ , as₂))  ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                            H-level-Erased 1 (H-level-List 0 Valence-set) ⟩
      Dec ((((_ , a₁) , _ , as₁) , [ refl _ ]) ≡
           (((_ , a₂) , _ , as₂) , [ refl _ ]))          ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Args≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□

      Dec (cons a₁ as₁ ≡ cons a₂ as₂)                    □

    _≟Arg_ : Decidable-equality (Arg v)
    nil t₁ ≟Arg nil t₂ =                                       $⟨ Σ.set⇒dec⇒dec⇒dec
                                                                    (H-level-Erased 2 Sort-set)
                                                                    (yes (refl _))
                                                                    (λ _ → _ ≟Tm t₂) ⟩
      Dec ((_ , t₁) ≡ (_ , t₂))                                ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                                  H-level-Erased 1 Valence-set ⟩
      Dec (((_ , t₁) , [ refl _ ]) ≡ ((_ , t₂) , [ refl _ ]))  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Arg≃) F.∘
                                                                            from-isomorphism Bijection.≡↔inj₁≡inj₁ ⟩□
      Dec (nil t₁ ≡ nil t₂)                                    □

    cons x₁ a₁ ≟Arg cons x₂ a₂ =                       $⟨ ×.dec⇒dec⇒dec
                                                           (_ ≟∃V _)
                                                           (Σ.set⇒dec⇒dec⇒dec
                                                              (H-level-Erased 2 Valence-set)
                                                              (yes (refl _))
                                                              (λ _ → _ ≟Arg a₂)) ⟩

      Dec (((_ , x₁) , _ , a₁) ≡ ((_ , x₂) , _ , a₂))  ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                          H-level-Erased 1 Valence-set ⟩
      Dec ((((_ , x₁) , _ , a₁) , [ refl _ ]) ≡
           (((_ , x₂) , _ , a₂) , [ refl _ ]))         ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Arg≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□

      Dec (cons x₁ a₁ ≡ cons x₂ a₂)                    □

  -- Tm, Args and Arg are sets (pointwise).

  Tm-set : Is-set (Tm s)
  Tm-set = decidable⇒set _≟Tm_

  Args-set : Is-set (Args vs)
  Args-set = decidable⇒set _≟Args_

  Arg-set : Is-set (Arg v)
  Arg-set = decidable⇒set _≟Arg_

  ----------------------------------------------------------------------
  -- The Wf predicates are propositional

  mutual

    -- Wf-tm is propositional.

    @0 Wf-tm-propositional :
      (t : Tm s) → Is-proposition (Wf-tm xs t)
    Wf-tm-propositional {xs = xs} (var x) (var p₁) (var p₂) =
      cong var (∈-propositional p₁ p₂)
    Wf-tm-propositional (op o as) (op wfs₁) (op wfs₂) =
      cong op (Wf-args-propositional as wfs₁ wfs₂)

    -- Wf-args is propositional.

    @0 Wf-args-propositional :
      (as : Args vs) → Is-proposition (Wf-args xs as)
    Wf-args-propositional nil nil nil = refl _

    Wf-args-propositional (cons a as) (cons wf₁ wfs₁) (cons wf₂ wfs₂) =
      cong₂ cons
        (Wf-arg-propositional a wf₁ wf₂)
        (Wf-args-propositional as wfs₁ wfs₂)

    -- Wf-arg is propositional.

    @0 Wf-arg-propositional :
      (a : Arg v) → Is-proposition (Wf-arg xs a)
    Wf-arg-propositional (nil t) (nil wf₁) (nil wf₂) =
      cong nil (Wf-tm-propositional t wf₁ wf₂)

    Wf-arg-propositional (cons x a) (cons wf₁) (cons wf₂) =
      cong cons
        (⟨ext⟩ λ y → ⟨ext⟩ λ y∉xs →
           Wf-arg-propositional
             (rename-Arg x y a)
             (wf₁ y y∉xs) (wf₂ y y∉xs))

  ----------------------------------------------------------------------
  -- Some (at the time of writing unused) rearrangement lemmas

  -- Rearrangement lemmas for Wf-tm, Wf-args and Wf-arg.

  @0 Wf-tm≃ :
    Wf-tm xs t ≃
    ((∃ λ ((x , _) : ∃ λ x → (_ , x) ∈ xs) → var x ≡ t) ⊎
     (∃ λ (((o , as) , _) :
           ∃ λ ((_ , as) : ∃ λ o → Args (domain o)) → Wf-args xs as) →
        op o as ≡ t))
  Wf-tm≃ {xs = xs} = Eq.↔⇒≃ (record
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
    RHS : Tm s → Set ℓ
    RHS t =
      (∃ λ ((x , _) : ∃ λ x → (_ , x) ∈ xs) → var x ≡ t) ⊎
      (∃ λ (((o , as) , _) :
            ∃ λ ((_ , as) : ∃ λ o → Args (domain o)) → Wf-args xs as) →
         op o as ≡ t)

    to : Wf-tm xs t → RHS t
    to (var p)  = inj₁ ((_ , p) , refl _)
    to (op wfs) = inj₂ ((_ , wfs) , refl _)

    from : RHS t → Wf-tm xs t
    from (inj₁ ((_ , p) , eq))   = subst (Wf-tm _) eq (var p)
    from (inj₂ ((_ , wfs) , eq)) = subst (Wf-tm _) eq (op wfs)

    lemma :
      (eq : t₁ ≡ t₂) →
      to (subst (Wf-tm xs) eq wf) ≡
      subst RHS eq (to wf)
    lemma {wf = wf} = D.elim¹ _
      (to (subst (Wf-tm xs) (refl _) wf)  ≡⟨ cong to $ subst-refl _ _ ⟩
       to wf                              ≡⟨ sym $ subst-refl _ _ ⟩∎
       subst RHS (refl _) (to wf)         ∎)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ ((_ , p) , eq)) =
      to (subst (Wf-tm xs) eq (var p))        ≡⟨ lemma _ ⟩
      subst RHS eq (to (var p))               ≡⟨⟩
      subst RHS eq (inj₁ ((_ , p) , refl _))  ≡⟨ push-subst-inj₁ _ _ ⟩
      inj₁ (subst _ eq ((_ , p) , refl _))    ≡⟨ cong inj₁ $ push-subst-pair-× _ _ ⟩
      inj₁ ((_ , p) , _)                      ≡⟨ cong (λ eq → inj₁ ((_ , p) , eq)) $ Tm-set _ _ ⟩∎
      inj₁ ((_ , p) , eq)                     ∎
    to∘from (inj₂ ((_ , wfs) , eq)) =
      to (subst (Wf-tm xs) eq (op wfs))         ≡⟨ lemma _ ⟩
      subst RHS eq (to (op wfs))                ≡⟨⟩
      subst RHS eq (inj₂ ((_ , wfs) , refl _))  ≡⟨ push-subst-inj₂ _ _ ⟩
      inj₂ (subst _ eq ((_ , wfs) , refl _))    ≡⟨ cong inj₂ $ push-subst-pair-× _ _ ⟩
      inj₂ ((_ , wfs) , _)                      ≡⟨ cong (λ eq → inj₂ ((_ , wfs) , eq)) $ Tm-set _ _ ⟩∎
      inj₂ ((_ , wfs) , eq)                     ∎

    from∘to : ∀ x → from (to x) ≡ x
    from∘to (var _) = subst-refl _ _
    from∘to (op _)  = subst-refl _ _

  @0 Wf-args≃ :
    Wf-args xs as ≃
    (_≡_ {A = ∃ λ vs → Args vs} (_ , nil) (_ , as) ⊎
     (∃ λ ((((_ , a) , _) , ((_ , as′) , _)) :
           (∃ λ ((_ , a) : ∃ λ v → Arg (erased v)) →
              Wf-arg xs a) ×
           (∃ λ ((_ , as′) : ∃ λ vs → Args (erased vs)) →
              Wf-args xs as′)) →
        _≡_ {A = ∃ λ vs → Args vs} (_ , cons a as′) (_ , as)))
  Wf-args≃ {xs = xs} = Eq.↔⇒≃ (record
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
    RHS : Args vs → Set ℓ
    RHS {vs = vs} as =
      _≡_ {A = ∃ λ vs → Args vs} ([] , nil) (vs , as) ⊎
      (∃ λ (((([ v ] , a) , _) , (([ vs′ ] , as′) , _)) :
            (∃ λ ((_ , a) : ∃ λ v → Arg (erased v)) →
               Wf-arg xs a) ×
            (∃ λ ((_ , as′) : ∃ λ vs → Args (erased vs)) →
               Wf-args xs as′)) →
         _≡_ {A = ∃ λ vs → Args vs} (v ∷ vs′ , cons a as′) (vs , as))

    to : Wf-args xs as → RHS as
    to nil           = inj₁ (refl _)
    to (cons wf wfs) = inj₂ (((_ , wf) , (_ , wfs)) , refl _)

    from : RHS as → Wf-args xs as
    from (inj₁ eq) =
      subst (λ (_ , as) → Wf-args xs as) eq nil
    from (inj₂ (((_ , wf) , (_ , wfs)) , eq)) =
      subst (λ (_ , as) → Wf-args xs as) eq (cons wf wfs)

    lemma :
      (eq : _≡_ {A = ∃ λ vs → Args vs} (vs₁ , as₁) (vs₂ , as₂)) →
      to (subst (λ (_ , as) → Wf-args xs as) eq wfs) ≡
      subst (λ (_ , as) → RHS as) eq (to wfs)
    lemma {wfs = wfs} = D.elim¹ _
      (to (subst (λ ((_ , as) : ∃ λ vs → Args vs) → Wf-args xs as)
                 (refl _) wfs)                                      ≡⟨ cong to $ subst-refl _ _ ⟩

       to wfs                                                       ≡⟨ sym $ subst-refl _ _ ⟩∎

       subst (λ ((_ , as) : ∃ λ vs → Args vs) → RHS as)
             (refl _) (to wfs)                                      ∎)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ eq) =
      to (subst (λ (_ , as) → Wf-args xs as) eq nil)  ≡⟨ lemma _ ⟩
      subst (λ (_ , as) → RHS as) eq (to nil)         ≡⟨⟩
      subst (λ (_ , as) → RHS as) eq (inj₁ (refl _))  ≡⟨ push-subst-inj₁ _ _ ⟩
      inj₁ (subst _ eq (refl _))                      ≡⟨ cong inj₁ (Σ-closure 2 (H-level-List 0 Valence-set) (λ _ → Args-set) _ _) ⟩∎
      inj₁ eq                                         ∎

    to∘from (inj₂ (((_ , wf) , (_ , wfs)) , eq)) =
      to (subst (λ (_ , as) → Wf-args xs as) eq (cons wf wfs))  ≡⟨ lemma _ ⟩

      subst (λ (_ , as) → RHS as) eq (to (cons wf wfs))         ≡⟨⟩

      subst (λ (_ , as) → RHS as) eq
        (inj₂ (((_ , wf) , (_ , wfs)) , refl _))                ≡⟨ push-subst-inj₂ _ _ ⟩

      inj₂ (subst _ eq (((_ , wf) , (_ , wfs)) , refl _))       ≡⟨ cong inj₂ $ push-subst-pair-× _ _ ⟩

      inj₂ (((_ , wf) , (_ , wfs)) , _)                         ≡⟨ cong (λ eq → inj₂ (((_ , wf) , (_ , wfs)) , eq)) $
                                                                   Σ-closure 2 (H-level-List 0 Valence-set) (λ _ → Args-set) _ _ ⟩∎
      inj₂ (((_ , wf) , (_ , wfs)) , eq)                        ∎

    from∘to : ∀ x → from (to x) ≡ x
    from∘to nil        = subst-refl _ _
    from∘to (cons _ _) = subst-refl _ _

  @0 Wf-arg≃ :
    Wf-arg xs a ≃
    ((∃ λ (((_ , t) , _) :
           ∃ λ ((_ , t) : ∃ λ s → Tm (erased s)) →
             Wf-tm xs t) →
        _≡_ {A = ∃ λ v → Arg v} (_ , nil t) (_ , a)) ⊎
     (∃ λ ((((_ , x) , _ , a′) , _) :
           ∃ λ ((([ s ] , x) , _ , a′) :
                ∃Var × (∃ λ v → Arg (erased v))) →
             ((y : Var s) → ¬ (_ , y) ∈ xs →
              Wf-arg ((_ , y) ∷ xs) (rename-Arg x y a′))) →
        _≡_ {A = ∃ λ v → Arg v} (_ , cons x a′) (_ , a)))
  Wf-arg≃ {xs = xs} = Eq.↔⇒≃ (record
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
    RHS : Arg v → Set ℓ
    RHS = _

    to : Wf-arg xs a → RHS a
    to (nil wf)  = inj₁ ((_ , wf) , refl _)
    to (cons wf) = inj₂ ((_ , wf) , refl _)

    from : RHS a → Wf-arg xs a
    from (inj₁ ((_ , wf) , eq)) =
      subst (λ (_ , a) → Wf-arg xs a) eq (nil wf)
    from (inj₂ ((_ , wf) , eq)) =
      subst (λ (_ , a) → Wf-arg xs a) eq (cons wf)

    lemma :
      (eq : _≡_ {A = ∃ λ v → Arg v} (v₁ , a₁) (v₂ , a₂)) →
      to (subst (λ (_ , a) → Wf-arg xs a) eq wf) ≡
      subst (λ (_ , a) → RHS a) eq (to wf)
    lemma {wf = wf} = D.elim¹ _
      (to (subst (λ ((_ , a) : ∃ λ v → Arg v) → Wf-arg xs a)
                 (refl _) wf)                                        ≡⟨ cong to $ subst-refl _ _ ⟩

       to wf                                                         ≡⟨ sym $ subst-refl _ _ ⟩∎

       subst (λ ((_ , a) : ∃ λ v → Arg v) → RHS a) (refl _) (to wf)  ∎)

    to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ ((_ , wf) , eq)) =
      to (subst (λ (_ , a) → Wf-arg xs a) eq (nil wf))         ≡⟨ lemma _ ⟩
      subst (λ (_ , a) → RHS a) eq (to (nil wf))               ≡⟨⟩
      subst (λ (_ , a) → RHS a) eq (inj₁ ((_ , wf) , refl _))  ≡⟨ push-subst-inj₁ _ _ ⟩
      inj₁ (subst _ eq ((_ , wf) , refl _))                    ≡⟨ cong inj₁ $ push-subst-pair-× _ _ ⟩
      inj₁ ((_ , wf) , _)                                      ≡⟨ cong (λ eq → inj₁ ((_ , wf) , eq)) $
                                                                  Σ-closure 2 Valence-set (λ _ → Arg-set) _ _ ⟩∎
      inj₁ ((_ , wf) , eq)                                     ∎

    to∘from (inj₂ ((_ , wf) , eq)) =
      to (subst (λ (_ , a) → Wf-arg xs a) eq (cons wf))        ≡⟨ lemma _ ⟩
      subst (λ (_ , a) → RHS a) eq (to (cons wf))              ≡⟨⟩
      subst (λ (_ , a) → RHS a) eq (inj₂ ((_ , wf) , refl _))  ≡⟨ push-subst-inj₂ _ _ ⟩
      inj₂ (subst _ eq ((_ , wf) , refl _))                    ≡⟨ cong inj₂ $ push-subst-pair-× _ _ ⟩
      inj₂ ((_ , wf) , _)                                      ≡⟨ cong (λ eq → inj₂ ((_ , wf) , eq)) $
                                                                  Σ-closure 2 Valence-set (λ _ → Arg-set) _ _ ⟩∎
      inj₂ ((_ , wf) , eq)                                     ∎

    from∘to : ∀ x → from (to x) ≡ x
    from∘to (nil _)  = subst-refl _ _
    from∘to (cons _) = subst-refl _ _
