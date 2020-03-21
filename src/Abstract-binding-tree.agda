------------------------------------------------------------------------
-- Abstract binding trees, based on Harper's "Practical Foundations
-- for Programming Languages"
------------------------------------------------------------------------

-- Operators are not indexed by symbolic parameters.

{-# OPTIONS --cubical --safe #-}

open import Equality

module Abstract-binding-tree
  {e⁺} (eq-J : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq-J

open import Logical-equivalence using (Dec-map)
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
    infix 4 _≟S_ _≟O_ _≟V_

    field
      -- A set of sorts with decidable equality.
      Sort : Set ℓ
      _≟S_ : Decidable-equality Sort

    -- Valences.

    Valence : Set ℓ
    Valence = List Sort × Sort

    -- Arities.

    Arity : Set ℓ
    Arity = List Valence × Sort

    field
      -- Operators with decidable equality and arities.
      Op    : Set ℓ
      _≟O_  : Decidable-equality Op
      arity : Op → Arity

      -- A sort-indexed type of variables with decidable equality.
      Var  : Sort → Set ℓ
      _≟V_ : ∀ {s} → Decidable-equality (Var s)

    -- An operator's argument valences.

    domain : Op → List Valence
    domain = proj₁ ∘ arity

    -- An operator's target sort.

    codomain : Op → Sort
    codomain = proj₂ ∘ arity

open Dummy public using (Signature) hiding (module Signature)

-- Definitions depending on a signature. Defined in a separate module
-- to avoid problems with record modules.

module Signature {ℓ} (sig : Signature ℓ) where

  open Dummy.Signature sig public

  private
    variable
      @0 A            : Set ℓ
      @0 x x′ y x₁ x₂ : A
      @0 eq eq₁ eq₂   : x ≡ y
      @0 s s′         : Sort
      @0 ss           : List Sort
      @0 v            : Valence
      @0 vs vs′       : List Valence
      @0 o            : Op

  ----------------------------------------------------------------------
  -- Raw terms

  mutual

    -- Raw (possibly ill-scoped) terms.

    data Tm (@0 s : Sort) : Set ℓ where
      var : ∀ {s′} → Var s′ → @0 s′ ≡ s → Tm s
      op  : (o : Op) → Args (domain o) → @0 codomain o ≡ s → Tm s

    -- Sequences of raw arguments.
    --
    -- TODO: When Cubical Agda gets proper support for inductive
    -- families, replace this data type with an inductive family.

    data Args (@0 vs : List Valence) : Set ℓ where
      nil  : @0 [] ≡ vs → Args vs
      cons : Arg v → Args vs′ → @0 v ∷ vs′ ≡ vs → Args vs

    -- Raw arguments.
    --
    -- TODO: See Args.

    data Arg (@0 v : Valence) : Set ℓ where
      nil  : Tm s → @0 ([] , s) ≡ v → Arg v
      cons : ∀ {s} → Var s → Arg (ss , s′) →
             @0 (s ∷ ss , s′) ≡ v → Arg v

  module _ {s} (x y : Var s) where

    mutual

      -- The term rename t is t with each (free or bound) occurrence
      -- of x replaced by y.

      rename : Tm s′ → Tm s′
      rename (var z eq)   = var (rename-Var z) eq
      rename (op o as eq) = op o (rename-Args as) eq

      rename-Var : ∀ {s′} → Var s′ → Var s′
      rename-Var {s′ = s′} z = case s ≟S s′ of λ where
        (no _)     → z
        (yes s≡s′) →
          let cast = subst Var s≡s′ in
          if   cast x ≟V z
          then cast y
          else z

      rename-Args : Args vs → Args vs
      rename-Args (nil eq)       = nil eq
      rename-Args (cons a as eq) =
        cons (rename-Arg a) (rename-Args as) eq

      rename-Arg : Arg (ss , s′) → Arg (ss , s′)
      rename-Arg (nil t eq)       = nil (rename t) eq
      rename-Arg (cons z rest eq) =
        cons (rename-Var z) (rename-Arg rest) eq

  ----------------------------------------------------------------------
  -- Well-formed terms

  -- Finite subsets of variables of each sort.

  Vars : Set ℓ
  Vars = {s : Sort} → Finite-subset-of (Var s)

  private
    variable
      @0 t t₁ t₂                  : Tm s
      @0 a a′ a₁ a₂ a′₁ a′₂       : Arg v
      @0 as as′ as₁ as₂ as′₁ as′₂ : Args vs
      @0 xs                       : Vars

  -- Extends one subset with a potentially new element.

  snoc : ∀ {s′} → Vars → Var s′ → Vars
  snoc {s′ = s′} xs x {s = s} = case s′ ≟S s of λ where
    (yes s′≡s) → subst Var s′≡s x ∷ xs
    (no  _)    → xs

  -- Predicates for well-formed terms and arguments.

  mutual

    data Wf-tm (xs : Vars) (t : Tm s) : Set ℓ where
      var : x ∈ xs → var x eq ≡ t → Wf-tm xs t
      op  : Wf-args xs as → op o as eq ≡ t → Wf-tm xs t

    data Wf-args (xs : Vars) (as : Args vs) : Set ℓ where
      nil  : nil eq ≡ as → Wf-args xs as
      cons : Wf-arg xs a → Wf-args xs as′ →
             cons a as′ eq ≡ as → Wf-args xs as

    data Wf-arg (xs : Vars) (a : Arg v) : Set ℓ where
      nil  : Wf-tm xs t → nil t eq ≡ a → Wf-arg xs a
      cons : ((y : Var s) → ¬ y ∈ xs →
              Wf-arg (snoc xs y) (rename-Arg x y a′)) →
             cons {s = s} x a′ eq ≡ a →
             Wf-arg xs a

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

  Tm≃ :
    Tm s ≃
    ((∃ λ ((s′ , _) : ∃ λ s′ → Var s′) → Erased (s′ ≡ s)) ⊎
     (∃ λ ((o , _) : ∃ λ (o : Op) → Args (domain o)) →
        Erased (codomain o ≡ s)))
  Tm≃ = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = λ where
                   (var s eq)   → inj₁ ((_ , s) , [ eq ])
                   (op o as eq) → inj₂ ((o , as) , [ eq ])
        ; from = λ where
                   (inj₁ ((_ , s) , [ eq ]))  → var s eq
                   (inj₂ ((o , as) , [ eq ])) → op o as eq
        }
      ; right-inverse-of = λ where
          (inj₁ _) → refl _
          (inj₂ _) → refl _
      }
    ; left-inverse-of = λ where
        (var _ _)  → refl _
        (op _ _ _) → refl _
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
        { to   = λ where
                   (nil eq)       → inj₁ [ eq ]
                   (cons a as eq) → inj₂ (((_ , a) , _ , as) , [ eq ])
        ; from = λ where
                   (inj₁ [ eq ])                        → nil eq
                   (inj₂ (((_ , a) , _ , as) , [ eq ])) → cons a as eq
        }
      ; right-inverse-of = λ where
          (inj₁ _) → refl _
          (inj₂ _) → refl _
      }
    ; left-inverse-of = λ where
        (nil _)      → refl _
        (cons _ _ _) → refl _
    })

  Arg≃ :
    Arg v ≃
    ((∃ λ (([ s ] , _) : ∃ λ s → Tm (erased s)) →
        Erased (([] , s) ≡ v)) ⊎
     (∃ λ (((s , _) , [ ss , s′ ] , _) :
           ∃ Var × ∃ λ v → Arg (erased v)) →
      Erased ((s ∷ ss , s′) ≡ v)))
  Arg≃ = Eq.↔⇒≃ (record
    { surjection = record
      { logical-equivalence = record
        { to   = λ where
                   (nil t eq)    → inj₁ ((_ , t) , [ eq ])
                   (cons x a eq) → inj₂ (((_ , x) , _ , a) , [ eq ])
        ; from = λ where
                   (inj₁ ((_ , t) , [ eq ]))           → nil t eq
                   (inj₂ (((_ , x) , _ , a) , [ eq ])) → cons x a eq
        }
      ; right-inverse-of = λ where
          (inj₁ _) → refl _
          (inj₂ _) → refl _
      }
    ; left-inverse-of = λ where
        (nil _ _)    → refl _
        (cons _ _ _) → refl _
    })

  -- Equality is decidable for Tm, Args and Arg.

  mutual

    infix 4 _≟Tm_ _≟Args_ _≟Arg_

    _≟Tm_ : Decidable-equality (Tm s)
    var {s′ = s′₁} x₁ eq₁ ≟Tm var {s′ = s′₂} x₂ eq₂ =    $⟨ Σ.Dec._≟_ _≟S_ _≟V_ _ _ ⟩
      Dec ((_ , x₁) ≡ (_ , x₂))                          ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                            H-level-Erased 1 Sort-set ⟩
      Dec (((_ , x₁) , [ eq₁ ]) ≡ ((_ , x₂) , [ eq₂ ]))  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ from-isomorphism Bijection.≡↔inj₁≡inj₁ ⟩□
      Dec (var x₁ eq₁ ≡ var x₂ eq₂)                      □

    var _ _ ≟Tm op _ _ _ =      $⟨ no (λ ()) ⟩
      Dec ⊥                     ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (var _ _ ≡ op _ _ _)  □

    op _ _ _ ≟Tm var _ _ =      $⟨ no (λ ()) ⟩
      Dec ⊥                     ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (op _ _ _ ≡ var _ _)  □

    op o₁ as₁ eq₁ ≟Tm op o₂ as₂ eq₂ =                        $⟨ Σ.decidable⇒dec⇒dec _≟O_ (λ _ → _ ≟Args as₂) ⟩
      Dec ((o₁ , as₁) ≡ (o₂ , as₂))                          ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                                H-level-Erased 1 Sort-set ⟩
      Dec (((o₁ , as₁) , [ eq₁ ]) ≡ ((o₂ , as₂) , [ eq₂ ]))  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘
                                                                          from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□
      Dec (op o₁ as₁ eq₁ ≡ op o₂ as₂ eq₂)                    □

    _≟Args_ : Decidable-equality (Args vs)
    nil eq₁ ≟Args nil eq₂ =    $⟨ yes (H-level-Erased 1 (H-level-List 0 Valence-set) _ _) ⟩
      Dec ([ eq₁ ] ≡ [ eq₂ ])  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Args≃) F.∘ from-isomorphism Bijection.≡↔inj₁≡inj₁ ⟩□
      Dec (nil eq₁ ≡ nil eq₂)  □

    nil _ ≟Args cons _ _ _ =    $⟨ no (λ ()) ⟩
      Dec ⊥                     ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Args≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (nil _ ≡ cons _ _ _)  □

    cons _ _ _ ≟Args nil _ =    $⟨ no (λ ()) ⟩
      Dec ⊥                     ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Args≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (cons _ _ _ ≡ nil _)  □

    cons a₁ as₁ eq₁ ≟Args cons a₂ as₂ eq₂ =              $⟨ (let eq = [ trans eq₁ (sym eq₂) ] in
                                                             ×.dec⇒dec⇒dec
                                                               (Σ.set⇒dec⇒dec⇒dec
                                                                  (H-level-Erased 2 (×-closure 2 (H-level-List 0 Sort-set) Sort-set))
                                                                  (yes ([]-cong (E.map List.cancel-∷-head eq)))
                                                                  (λ _ → _ ≟Arg a₂))
                                                               (Σ.set⇒dec⇒dec⇒dec
                                                                  (H-level-Erased 2 (H-level-List 0 Valence-set))
                                                                  (yes ([]-cong (E.map List.cancel-∷-tail eq)))
                                                                  (λ _ → _ ≟Args as₂))) ⟩

      Dec (((_ , a₁) , _ , as₁) ≡ ((_ , a₂) , _ , as₂))  ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                            H-level-Erased 1 (H-level-List 0 Valence-set) ⟩
      Dec ((((_ , a₁) , _ , as₁) , [ eq₁ ]) ≡
           (((_ , a₂) , _ , as₂) , [ eq₂ ]))             ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Args≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□

      Dec (cons a₁ as₁ eq₁ ≡ cons a₂ as₂ eq₂)            □

    _≟Arg_ : Decidable-equality (Arg v)
    nil t₁ eq₁ ≟Arg nil t₂ eq₂ =                         $⟨ Σ.set⇒dec⇒dec⇒dec
                                                              (H-level-Erased 2 Sort-set)
                                                              (yes ([]-cong [ cong proj₂ (trans eq₁ (sym eq₂)) ]))
                                                              (λ _ → _ ≟Tm t₂) ⟩
      Dec ((_ , t₁) ≡ (_ , t₂))                          ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                            H-level-Erased 1 Valence-set ⟩
      Dec (((_ , t₁) , [ eq₁ ]) ≡ ((_ , t₂) , [ eq₂ ]))  ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Arg≃) F.∘ from-isomorphism Bijection.≡↔inj₁≡inj₁ ⟩□
      Dec (nil t₁ eq₁ ≡ nil t₂ eq₂)                      □

    nil _ _ ≟Arg cons _ _ _ =     $⟨ no (λ ()) ⟩
      Dec ⊥                       ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Arg≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (nil _ _ ≡ cons _ _ _)  □

    cons _ _ _ ≟Arg nil _ _ =     $⟨ no (λ ()) ⟩
      Dec ⊥                       ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Arg≃) F.∘ from-isomorphism (inverse Bijection.≡↔⊎) ⟩□
      Dec (cons _ _ _ ≡ nil _ _)  □

    cons x₁ a₁ eq₁ ≟Arg cons x₂ a₂ eq₂ =               $⟨ ×.dec⇒dec⇒dec
                                                           (Σ.Dec._≟_ _≟S_ _≟V_ _ _)
                                                           (Σ.set⇒dec⇒dec⇒dec
                                                              (H-level-Erased 2 Valence-set)
                                                              (yes ([]-cong [ (let eq = trans eq₁ (sym eq₂) in
                                                                               cong₂ _,_ (List.cancel-∷-tail (cong proj₁ eq))
                                                                                         (cong proj₂ eq))
                                                                            ]))
                                                              (λ _ → _ ≟Arg a₂)) ⟩

      Dec (((_ , x₁) , _ , a₁) ≡ ((_ , x₂) , _ , a₂))  ↝⟨ Dec-map $ from-isomorphism $ ignore-propositional-component $
                                                          H-level-Erased 1 Valence-set ⟩
      Dec ((((_ , x₁) , _ , a₁) , [ eq₁ ]) ≡
           (((_ , x₂) , _ , a₂) , [ eq₂ ]))            ↝⟨ Dec-map $ from-isomorphism (Eq.≃-≡ Arg≃) F.∘ from-isomorphism Bijection.≡↔inj₂≡inj₂ ⟩□

      Dec (cons x₁ a₁ eq₁ ≡ cons x₂ a₂ eq₂)            □

  -- Tm, Args and Arg are sets (pointwise).

  Tm-set : Is-set (Tm s)
  Tm-set = decidable⇒set _≟Tm_

  Args-set : Is-set (Args vs)
  Args-set = decidable⇒set _≟Args_

  Arg-set : Is-set (Arg v)
  Arg-set = decidable⇒set _≟Arg_

  ----------------------------------------------------------------------
  -- The Wf predicates are propositional

  -- Rearrangement lemmas for Wf-tm, Wf-args and Wf-arg.

  @0 Wf-tm≃ :
    Wf-tm xs t ≃
    ((∃ λ (((_ , x) , _) : ∃ λ ((_ , x) : ∃ λ s → Var s) → x ∈ xs) →
        ∃ λ eq → var x eq ≡ t) ⊎
     (∃ λ (((o , as) , _) :
           ∃ λ ((_ , as) : ∃ λ o → Args (domain o)) → Wf-args xs as) →
        ∃ λ eq → op o as eq ≡ t))
  Wf-tm≃ = Eq.↔⇒≃ (record
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
    @0 to : Wf-tm _ _ → _
    to (var p eq)  = inj₁ ((_ , p) , _ , eq)
    to (op wfs eq) = inj₂ ((_ , wfs) , _ , eq)

    @0 from : _ ⊎ _ → _
    from (inj₁ ((_ , p) , _ , eq))   = var p eq
    from (inj₂ ((_ , wfs) , _ , eq)) = op wfs eq

    @0 to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ _) = refl _
    to∘from (inj₂ _) = refl _

    @0 from∘to : ∀ x → from (to x) ≡ x
    from∘to (var _ _) = refl _
    from∘to (op _ _)  = refl _

  @0 Wf-args≃ :
    Wf-args xs as ≃
    ((∃ λ eq → nil eq ≡ as) ⊎
     (∃ λ ((((_ , a) , _) , ((_ , as′) , _)) :
           (∃ λ ((_ , a) : ∃ λ v → Arg (erased v)) →
              Wf-arg xs a) ×
           (∃ λ ((_ , as′) : ∃ λ vs → Args (erased vs)) →
              Wf-args xs as′)) →
        ∃ λ eq → cons a as′ eq ≡ as))
  Wf-args≃ = Eq.↔⇒≃ (record
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
    @0 to : Wf-args _ _ → _
    to (nil eq)         = inj₁ (_ , eq)
    to (cons wf wfs eq) = inj₂ (((_ , wf) , (_ , wfs)) , _ , eq)

    @0 from : _ ⊎ _ → _
    from (inj₁ (_ , eq))                          = nil eq
    from (inj₂ (((_ , wf) , (_ , wfs)) , _ , eq)) = cons wf wfs eq

    @0 to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ _) = refl _
    to∘from (inj₂ _) = refl _

    @0 from∘to : ∀ x → from (to x) ≡ x
    from∘to (nil _)      = refl _
    from∘to (cons _ _ _) = refl _

  @0 Wf-arg≃ :
    Wf-arg xs a ≃
    ((∃ λ (((_ , t) , _) :
           ∃ λ ((_ , t) : ∃ λ s → Tm (erased s)) →
             Wf-tm xs t) →
        ∃ λ eq → nil t eq ≡ a) ⊎
     (∃ λ ((((_ , x) , _ , a′) , _) :
           ∃ λ (((s , x) , _ , a′) :
                (∃ Var) × (∃ λ v → Arg (erased v))) →
             ((y : Var s) →
              ¬ y ∈ xs → Wf-arg (snoc xs y) (rename-Arg x y a′))) →
        ∃ λ eq → cons x a′ eq ≡ a))
  Wf-arg≃ = Eq.↔⇒≃ (record
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
    @0 to : Wf-arg _ _ → _
    to (nil wf eq)  = inj₁ ((_ , wf) , _ , eq)
    to (cons wf eq) = inj₂ ((_ , wf) , _ , eq)

    @0 from : _ ⊎ _ → _
    from (inj₁ ((_ , wf) , _ , eq)) = nil wf eq
    from (inj₂ ((_ , wf) , _ , eq)) = cons wf eq

    @0 to∘from : ∀ x → to (from x) ≡ x
    to∘from (inj₁ _) = refl _
    to∘from (inj₂ _) = refl _

    @0 from∘to : ∀ x → from (to x) ≡ x
    from∘to (nil _ _)  = refl _
    from∘to (cons _ _) = refl _

  -- The Wf predicates are propositional.

  mutual

    @0 Wf-tm-propositional :
      (t : Tm s) → Is-proposition (Wf-tm xs t)
    Wf-tm-propositional
      {xs = xs} (var x eq)
      (var {x = x₁} p₁ eq₁)
      (var {x = x₂} p₂ eq₂) =
                                                   $⟨ ∈-propositional xs _ _ ⟩
      _ ≡ p₂                                       ↝⟨ lemma ,_ ⦂ (_ → _) ⟩
      (∃ λ _ → _ ≡ p₂)                             ↔⟨ Bijection.Σ-≡,≡↔≡ ⟩
      (_ , p₁) ≡ (_ , p₂)                          ↔⟨ ignore-propositional-component (Σ-closure 1 Sort-set λ _ → Tm-set) ⟩
      ((_ , p₁) , _ , eq₁) ≡ ((_ , p₂) , _ , eq₂)  ↔⟨ from-isomorphism (Eq.≃-≡ Wf-tm≃) F.∘ Bijection.≡↔inj₁≡inj₁ ⟩□
      var p₁ eq₁ ≡ var p₂ eq₂                      □
      where
      lemma =                            $⟨ trans eq₁ (sym eq₂) ⟩
        var x₁ _ ≡ var x₂ _              ↝⟨ inverse $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ Bijection.≡↔inj₁≡inj₁ ⟩
        ((_ , x₁) , _) ≡ ((_ , x₂) , _)  ↝⟨ inverse $ ignore-propositional-component (H-level-Erased 1 Sort-set) ⟩□
        (_ , x₁) ≡ (_ , x₂)              □

    Wf-tm-propositional
      (op o as eq)
      (op {o = o₁} {as = as₁} wfs₁ eq₁)
      (op {o = o₂} {as = as₂} wfs₂ eq₂) =
                                                       $⟨ Wf-args-propositional _ _ wfs₂ ⟩
      _ ≡ wfs₂                                         ↝⟨ lemma ,_ ⦂ (_ → _) ⟩
      (∃ λ _ → _ ≡ wfs₂)                               ↔⟨ Bijection.Σ-≡,≡↔≡ ⟩
      (_ , wfs₁) ≡ (_ , wfs₂)                          ↔⟨ ignore-propositional-component (Σ-closure 1 Sort-set λ _ → Tm-set) ⟩
      ((_ , wfs₁) , _ , eq₁) ≡ ((_ , wfs₂) , _ , eq₂)  ↔⟨ from-isomorphism (Eq.≃-≡ Wf-tm≃) F.∘ Bijection.≡↔inj₂≡inj₂ ⟩□
      op wfs₁ eq₁ ≡ op wfs₂ eq₂                        □
      where
      lemma =                                $⟨ trans eq₁ (sym eq₂) ⟩
        op o₁ as₁ _ ≡ op o₂ as₂ _            ↝⟨ inverse $ from-isomorphism (Eq.≃-≡ Tm≃) F.∘ Bijection.≡↔inj₂≡inj₂ ⟩
        ((o₁ , as₁) , _) ≡ ((o₂ , as₂) , _)  ↝⟨ inverse $ ignore-propositional-component (H-level-Erased 1 Sort-set) ⟩□
        (o₁ , as₁) ≡ (o₂ , as₂)              □

    Wf-tm-propositional (var _ _) (op _ eq₁) _ =
                          $⟨ eq₁ ⟩
      op _ _ _ ≡ var _ _  ↔⟨ inverse $ Eq.≃-≡ Tm≃ ⟩
      inj₂ _ ≡ inj₁ _     ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym ⟩□
      _                   □

    Wf-tm-propositional (var _ _) _ (op _ eq₂) =
                          $⟨ eq₂ ⟩
      op _ _ _ ≡ var _ _  ↔⟨ inverse $ Eq.≃-≡ Tm≃ ⟩
      inj₂ _ ≡ inj₁ _     ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym ⟩□
      _                   □

    Wf-tm-propositional (op _ _ _) (var _ eq₁) _ =
                          $⟨ eq₁ ⟩
      var _ _ ≡ op _ _ _  ↔⟨ inverse $ Eq.≃-≡ Tm≃ ⟩
      inj₁ _ ≡ inj₂ _     ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ⟩□
      _                   □

    Wf-tm-propositional (op _ _ _) _ (var _ eq₂) =
                          $⟨ eq₂ ⟩
      var _ _ ≡ op _ _ _  ↔⟨ inverse $ Eq.≃-≡ Tm≃ ⟩
      inj₁ _ ≡ inj₂ _     ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ⟩□
      _                   □

    @0 Wf-args-propositional :
      (as : Args vs) → Is-proposition (Wf-args xs as)
    Wf-args-propositional (nil eq) (nil eq₁) (nil eq₂) =
                             $⟨ Σ-closure 1 (H-level-List 0 Valence-set) (λ _ → Args-set) _ _ ⟩
      (_ , eq₁) ≡ (_ , eq₂)  ↝⟨ from-isomorphism (Eq.≃-≡ Wf-args≃) F.∘ Bijection.≡↔inj₁≡inj₁ ⟩□
      nil eq₁ ≡ nil eq₂      □

    Wf-args-propositional
      (cons a as eq)
      (cons {a = a₁} {as′ = as₁} wf₁ wfs₁ eq₁)
      (cons {a = a₂} {as′ = as₂} wf₂ wfs₂ eq₂) =
                                                           $⟨ Wf-arg-propositional _ _ wf₂ , Wf-args-propositional _ _ wfs₂ ⟩
      _ ≡ wf₂ × _ ≡ wfs₂                                   ↝⟨ Σ-map (proj₁ lemma ,_) (proj₂ lemma ,_) ⟩

      (∃ λ _ → _ ≡ wf₂) × (∃ λ _ → _ ≡ wfs₂)               ↔⟨ Bijection.Σ-≡,≡↔≡ ×-cong Bijection.Σ-≡,≡↔≡ ⟩

      (_ , wf₁) ≡ (_ , wf₂) × (_ , wfs₁) ≡ (_ , wfs₂)      ↔⟨ ≡×≡↔≡ ⟩

      ((_ , wf₁) , (_ , wfs₁)) ≡ ((_ , wf₂) , (_ , wfs₂))  ↔⟨ ignore-propositional-component $
                                                              Σ-closure 1 (H-level-List 0 Valence-set) (λ _ → Args-set) ⟩
      (((_ , wf₁) , (_ , wfs₁)) , _ , eq₁) ≡
      (((_ , wf₂) , (_ , wfs₂)) , _ , eq₂)                 ↔⟨ from-isomorphism (Eq.≃-≡ Wf-args≃) F.∘ Bijection.≡↔inj₂≡inj₂ ⟩□

      cons wf₁ wfs₁ eq₁ ≡ cons wf₂ wfs₂ eq₂                □
      where
      lemma =                                                        $⟨ trans eq₁ (sym eq₂) ⟩
        cons a₁ as₁ _ ≡ cons a₂ as₂ _                                ↝⟨ inverse $ from-isomorphism (Eq.≃-≡ Args≃) F.∘ Bijection.≡↔inj₂≡inj₂ ⟩
        (((_ , a₁) , (_ , as₁)) , _) ≡ (((_ , a₂) , (_ , as₂)) , _)  ↝⟨ inverse $ ignore-propositional-component $
                                                                        H-level-Erased 1 (H-level-List 0 Valence-set) ⟩
        ((_ , a₁) , (_ , as₁)) ≡ ((_ , a₂) , (_ , as₂))              ↝⟨ inverse ≡×≡↔≡ ⟩□
        (_ , a₁) ≡ (_ , a₂) × (_ , as₁) ≡ (_ , as₂)                  □

    Wf-args-propositional (nil _) (cons _ _ eq₁) _ =
                          $⟨ eq₁ ⟩
      cons _ _ _ ≡ nil _  ↔⟨ inverse $ Eq.≃-≡ Args≃ ⟩
      inj₂ _ ≡ inj₁ _     ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym ⟩□
      _                   □

    Wf-args-propositional (nil _) _ (cons _ _ eq₂) =
                          $⟨ eq₂ ⟩
      cons _ _ _ ≡ nil _  ↔⟨ inverse $ Eq.≃-≡ Args≃ ⟩
      inj₂ _ ≡ inj₁ _     ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym ⟩□
      _                   □

    Wf-args-propositional (cons _ _ _) (nil eq₁) _ =
                          $⟨ eq₁ ⟩
      nil _ ≡ cons _ _ _  ↔⟨ inverse $ Eq.≃-≡ Args≃ ⟩
      inj₁ _ ≡ inj₂ _     ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ⟩□
      _                   □

    Wf-args-propositional (cons _ _ _) _ (nil eq₂) =
                          $⟨ eq₂ ⟩
      nil _ ≡ cons _ _ _  ↔⟨ inverse $ Eq.≃-≡ Args≃ ⟩
      inj₁ _ ≡ inj₂ _     ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ⟩□
      _                   □

    @0 Wf-arg-propositional :
      (a : Arg v) → Is-proposition (Wf-arg xs a)
    Wf-arg-propositional
      {xs = xs} (nil t eq)
      (nil {t = t₁} wf₁ eq₁)
      (nil {t = t₂} wf₂ eq₂) =
                                                                   $⟨ Wf-tm-propositional _ _ wf₂ ⟩
      _ ≡ wf₂                                                      ↝⟨ lemma ,_ ⦂ (_ → _) ⟩
      (∃ λ (eq : (_ , t₁) ≡ (_ , t₂)) → _ ≡ wf₂)                   ↔⟨ Bijection.Σ-≡,≡↔≡ ⟩
      ((_ , t₁) , wf₁) ≡ ((_ , t₂) , wf₂)                          ↔⟨ ignore-propositional-component (Σ-closure 1 Valence-set λ _ → Arg-set) ⟩
      (((_ , t₁) , wf₁) , _ , eq₁) ≡ (((_ , t₂) , wf₂) , _ , eq₂)  ↔⟨ from-isomorphism (Eq.≃-≡ Wf-arg≃) F.∘ Bijection.≡↔inj₁≡inj₁ ⟩□
      nil wf₁ eq₁ ≡ nil wf₂ eq₂                                    □
      where
      lemma =                            $⟨ trans eq₁ (sym eq₂) ⟩
        nil t₁ _ ≡ nil t₂ _              ↝⟨ inverse $ from-isomorphism (Eq.≃-≡ Arg≃) F.∘ Bijection.≡↔inj₁≡inj₁ ⟩
        ((_ , t₁) , _) ≡ ((_ , t₂) , _)  ↝⟨ inverse $ ignore-propositional-component (H-level-Erased 1 Valence-set) ⟩□
        (_ , t₁) ≡ (_ , t₂)              □

    Wf-arg-propositional
      (cons x a eq)
      (cons {x = x₁} {a′ = a₁} wf₁ eq₁)
      (cons {x = x₂} {a′ = a₂} wf₂ eq₂) =
                                                     $⟨ (λ y y∉xs → Wf-arg-propositional _ _ (wf₂ y y∉xs)) ⟩
      (∀ y y∉xs → _ ≡ wf₂ y y∉xs)                    ↔⟨ Eq.extensionality-isomorphism ext F.∘ ∀-cong ext (λ _ → Eq.extensionality-isomorphism ext) ⟩
      _ ≡ wf₂                                        ↝⟨ lemma ,_ ⦂ (_ → _) ⟩
      (∃ λ _ → _ ≡ wf₂)                              ↔⟨ Bijection.Σ-≡,≡↔≡ ⟩
      (_ , wf₁) ≡ (_ , wf₂)                          ↔⟨ ignore-propositional-component (Σ-closure 1 Valence-set λ _ → Arg-set) ⟩
      ((_ , wf₁) , _ , eq₁) ≡ ((_ , wf₂) , _ , eq₂)  ↔⟨ from-isomorphism (Eq.≃-≡ Wf-arg≃) F.∘ Bijection.≡↔inj₂≡inj₂ ⟩□
      cons wf₁ eq₁ ≡ cons wf₂ eq₂                    □
      where
      lemma =                                                  $⟨ trans eq₁ (sym eq₂) ⟩
        cons x₁ a₁ _ ≡ cons x₂ a₂ _                            ↝⟨ inverse $ from-isomorphism (Eq.≃-≡ Arg≃) F.∘ Bijection.≡↔inj₂≡inj₂ ⟩
        (((_ , x₁) , _ , a₁) , _) ≡ (((_ , x₂) , _ , a₂) , _)  ↝⟨ inverse $ ignore-propositional-component (H-level-Erased 1 Valence-set) ⟩□
        ((_ , x₁) , _ , a₁) ≡ ((_ , x₂) , _ , a₂)              □

    Wf-arg-propositional (nil _ _) (cons _ eq₁) _ =
                            $⟨ eq₁ ⟩
      cons _ _ _ ≡ nil _ _  ↔⟨ inverse $ Eq.≃-≡ Arg≃ ⟩
      inj₂ _ ≡ inj₁ _       ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym ⟩□
      _                     □

    Wf-arg-propositional (nil _ _) _ (cons _ eq₂) =
                            $⟨ eq₂ ⟩
      cons _ _ _ ≡ nil _ _  ↔⟨ inverse $ Eq.≃-≡ Arg≃ ⟩
      inj₂ _ ≡ inj₁ _       ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ∘ sym ⟩□
      _                     □

    Wf-arg-propositional (cons _ _ _) (nil _ eq₁) _ =
                            $⟨ eq₁ ⟩
      nil _ _ ≡ cons _ _ _  ↔⟨ inverse $ Eq.≃-≡ Arg≃ ⟩
      inj₁ _ ≡ inj₂ _       ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ⟩□
      _                     □

    Wf-arg-propositional (cons _ _ _) _ (nil _ eq₂) =
                            $⟨ eq₂ ⟩
      nil _ _ ≡ cons _ _ _  ↔⟨ inverse $ Eq.≃-≡ Arg≃ ⟩
      inj₁ _ ≡ inj₂ _       ↝⟨ ⊥-elim ∘ ⊎.inj₁≢inj₂ ⟩□
      _                     □
