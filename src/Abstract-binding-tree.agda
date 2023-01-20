------------------------------------------------------------------------
-- Abstract binding trees, based on Harper's "Practical Foundations
-- for Programming Languages"
------------------------------------------------------------------------

-- Operators are not indexed by symbolic parameters.

-- TODO: Define α-equivalence, prove that key operations respect
-- α-equivalence.

{-# OPTIONS --erased-cubical --safe #-}

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
open import Finite-subset.Listed equality-with-paths as L
open import Finite-subset.Listed.Membership.Erased equality-with-paths
  hiding (fresh)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc
open import List equality-with-J using (H-level-List)

private
  variable
    p : Level

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
              ∃ λ (x : Var s) → Erased ((_ , x) ∉ xs)

    -- Arities.

    Arity : Type ℓ
    Arity = List Valence × Sort

    -- An operator's arity.

    arity : ∀ {s} → Op s → Arity
    arity {s} o = domain o , s

open Dummy public using (Signature) hiding (module Signature)

-- Definitions depending on a signature. Defined in a separate module
-- to avoid problems with record modules.

module Signature {ℓ} (sig : Signature ℓ) where

  open Dummy.Signature sig public

  private
    variable
      @0 A                        : Type ℓ
      @0 s s′ s₁ s₂ s₃ wf wf₁ wf₂ : A
      @0 ss                       : List Sort
      @0 v                        : Valence
      @0 vs                       : List Valence
      @0 o                        : Op s
      @0 x y z                    : Var s
      @0 dom fs xs ys             : Finite-subset-of A

  ----------------------------------------------------------------------
  -- Variants of some functions from the signature

  -- A variant of fresh that does not return an erased proof.

  fresh-not-erased :
    ∀ {s} (xs : Vars) → ∃ λ (x : Var s) → (_ , x) ∉ xs
  fresh-not-erased =
    Σ-map id Stable-¬ ∘ fresh

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
  -- Some decision procedures

  -- "Erased mere equality" is decidable for Var s.

  merely-equal?-Var : (x y : Var s) → Dec-Erased ∥ x ≡ y ∥
  merely-equal?-Var x y with x ≟V y
  … | yes [ x≡y ] = yes [ ∣ x≡y ∣ ]
  … | no  [ x≢y ] = no  [ x≢y ∘ Trunc.rec Var-set id ]

  -- "Erased mere equality" is decidable for ∃Var.

  merely-equal?-∃Var : (x y : ∃Var) → Dec-Erased ∥ x ≡ y ∥
  merely-equal?-∃Var x y with x ≟∃V y
  … | yes [ x≡y ] = yes [ ∣ x≡y ∣ ]
  … | no  [ x≢y ] = no  [ x≢y ∘ Trunc.rec ∃Var-set id ]

  private

    -- An instance of delete.

    del : ∃Var → Vars → Vars
    del = delete merely-equal?-∃Var

    -- An instance of minus.

    infixl 5 _∖_

    _∖_ :
      Finite-subset-of (Var s) → Finite-subset-of (Var s) →
      Finite-subset-of (Var s)
    _∖_ = minus merely-equal?-Var

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
    Tm {s} var       = Var s
    Tm     (op o as) = Args as

    Args : Argsˢ vs → Type ℓ
    Args nil         = ↑ _ ⊤
    Args (cons a as) = Arg a × Args as

    Arg : Argˢ v → Type ℓ
    Arg (nil t)      = Tm t
    Arg (cons {s} a) = Var s × Arg a

  ----------------------------------------------------------------------
  -- Casting variables

  -- A cast lemma.

  cast-Var : @0 s ≡ s′ → Var s → Var s′
  cast-Var = substᴱ Var

  -- Attempts to cast a variable to a given sort.

  maybe-cast-∃Var : ∀ s → ∃Var → Maybe (Var s)
  maybe-cast-∃Var s (s′ , x) with s′ ≟S s
  … | yes [ s′≡s ] = just (cast-Var s′≡s x)
  … | no  _        = nothing

  abstract

    -- When no arguments are erased one can express cast-Var in a
    -- different way.

    cast-Var-not-erased :
      ∀ {s s′} {s≡s′ : s ≡ s′} {x} →
      cast-Var s≡s′ x ≡ subst (λ s → Var s) s≡s′ x
    cast-Var-not-erased {s≡s′} {x} =
      substᴱ Var s≡s′ x           ≡⟨ substᴱ≡subst ⟩∎
      subst (λ s → Var s) s≡s′ x  ∎

    -- If eq has type s₁ ≡ s₂, then s₁ paired up with x (as an element
    -- of ∃Var) is equal to s₂ paired up with cast-Var eq x (if none
    -- of these inputs are erased).

    ≡,cast-Var :
      ∀ {s₁ s₂ x} {eq : s₁ ≡ s₂} →
      _≡_ {A = ∃Var} (s₁ , x) (s₂ , cast-Var eq x)
    ≡,cast-Var {s₁} {s₂} {x} {eq} =
      Σ-≡,≡→≡ eq
        (subst (λ s → Var s) eq x  ≡⟨ sym cast-Var-not-erased ⟩∎
         cast-Var eq x             ∎)

    -- A "computation rule".

    cast-Var-refl :
      ∀ {@0 s} {x : Var s} →
      cast-Var (refl s) x ≡ x
    cast-Var-refl {x} =
      substᴱ Var (refl _) x  ≡⟨ substᴱ-refl ⟩∎
      x                      ∎

    -- A fusion lemma for cast-Var.

    cast-Var-cast-Var :
      {x : Var s₁} {@0 eq₁ : s₁ ≡ s₂} {@0 eq₂ : s₂ ≡ s₃} →
      cast-Var eq₂ (cast-Var eq₁ x) ≡ cast-Var (trans eq₁ eq₂) x
    cast-Var-cast-Var {x} {eq₁} {eq₂} =
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
    cast-Var-Σ-≡,≡←≡ {x₁} {x₂} eq =
      cast-Var (proj₁ (Σ-≡,≡←≡ eq)) x₁             ≡⟨ cast-Var-not-erased ⟩
      subst (λ s → Var s) (proj₁ (Σ-≡,≡←≡ eq)) x₁  ≡⟨ proj₂ (Σ-≡,≡←≡ eq) ⟩∎
      x₂                                           ∎

    -- An equality between a casted variable and another variable can
    -- be expressed in terms of an equality between elements of ∃Var.
    -- (In erased contexts.)

    @0 ≡cast-Var≃ :
      {s≡s′ : s ≡ s′} →
      (cast-Var s≡s′ x ≡ y) ≃ _≡_ {A = ∃Var} (s , x) (s′ , y)
    ≡cast-Var≃ {s} {s′} {x} {y} {s≡s′} =
      cast-Var s≡s′ x ≡ y                                     ↝⟨ ≡⇒↝ _ $ cong (_≡ _) cast-Var-not-erased ⟩
      subst (λ s → Var s) s≡s′ x ≡ y                          ↔⟨ inverse $ drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                                 propositional⇒inhabited⇒contractible Sort-set s≡s′ ⟩
      (∃ λ (s≡s′ : s ≡ s′) → subst (λ s → Var s) s≡s′ x ≡ y)  ↔⟨ Bijection.Σ-≡,≡↔≡ ⟩□
      (s , x) ≡ (s′ , y)                                      □

    -- Equality between pairs in ∃Var can be "simplified" when the
    -- sorts are equal. (In erased contexts.)

    @0 ≡→,≡,≃ :
      _≡_ {A = ∃Var} (s , x) (s , y) ≃ (x ≡ y)
    ≡→,≡,≃ {s} {x} {y} =
      (s , x) ≡ (s , y)        ↝⟨ inverse ≡cast-Var≃ ⟩
      cast-Var (refl _) x ≡ y  ↝⟨ ≡⇒↝ _ $ cong (_≡ _) cast-Var-refl ⟩□
      x ≡ y                    □

    -- Equality between pairs in ∃Var can be "simplified" when the
    -- sorts are not equal.

    ≢→,≡,≃ :
      ∀ {s₁ s₂ x y} →
      s₁ ≢ s₂ →
      _≡_ {A = ∃Var} (s₁ , x) (s₂ , y) ≃ ⊥₀
    ≢→,≡,≃ {s₁} {s₂} {x} {y} s₁≢s₂ =
      (s₁ , x) ≡ (s₂ , y)                                        ↔⟨ inverse Bijection.Σ-≡,≡↔≡ ⟩
      (∃ λ (s₁≡s₂ : s₁ ≡ s₂) → subst (λ s → Var s) s₁≡s₂ x ≡ y)  ↝⟨ Σ-cong-contra (Bijection.⊥↔uninhabited s₁≢s₂) (λ _ → F.id) ⟩
      (∃ λ (p : ⊥₀) → subst (λ s → Var s) (⊥-elim p) x ≡ y)      ↔⟨ Σ-left-zero ⟩□
      ⊥                                                          □

  ----------------------------------------------------------------------
  -- A small universe

  -- The universe.

  data Term-kind : Type where
    var tm args arg : Term-kind

  private
    variable
      k : Term-kind

  -- A variable skeleton is just an unerased sort.

  data Varˢ : @0 Sort → Type ℓ where
    var : ∀ {s} → Varˢ s

  -- For each kind of term there is a kind of sort, a kind of
  -- skeleton, and a kind of data.

  Sort-kind : Term-kind → Type ℓ
  Sort-kind var  = Sort
  Sort-kind tm   = Sort
  Sort-kind args = List Valence
  Sort-kind arg  = Valence

  Skeleton : (k : Term-kind) → @0 Sort-kind k → Type ℓ
  Skeleton var  = Varˢ
  Skeleton tm   = Tmˢ
  Skeleton args = Argsˢ
  Skeleton arg  = Argˢ

  Data : Skeleton k s → Type ℓ
  Data {k = var} {s} = λ _ → Var s
  Data {k = tm}      = Tm
  Data {k = args}    = Args
  Data {k = arg}     = Arg

  -- Term-kind is equivalent to Fin 4.

  Term-kind≃Fin-4 : Term-kind ≃ Fin 4
  Term-kind≃Fin-4 = Eq.↔→≃ to from to∘from from∘to
    where
    to : Term-kind → Fin 4
    to var  = fzero
    to tm   = fsuc fzero
    to args = fsuc (fsuc fzero)
    to arg  = fsuc (fsuc (fsuc fzero))

    from : Fin 4 → Term-kind
    from fzero                      = var
    from (fsuc fzero)               = tm
    from (fsuc (fsuc fzero))        = args
    from (fsuc (fsuc (fsuc fzero))) = arg

    to∘from : ∀ i → to (from i) ≡ i
    to∘from fzero                      = refl _
    to∘from (fsuc fzero)               = refl _
    to∘from (fsuc (fsuc fzero))        = refl _
    to∘from (fsuc (fsuc (fsuc fzero))) = refl _

    from∘to : ∀ k → from (to k) ≡ k
    from∘to var  = refl _
    from∘to tm   = refl _
    from∘to args = refl _
    from∘to arg  = refl _

  ----------------------------------------------------------------------
  -- Computing the set of free variables

  -- These functions return sets containing exactly the free
  -- variables.
  --
  -- Note that this code is not intended to be used at run-time.

  private

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

  free : (tˢ : Skeleton k s) → Data tˢ → Vars
  free {k = var}  = λ { var → free-Var }
  free {k = tm}   = free-Tm
  free {k = args} = free-Args
  free {k = arg}  = free-Arg

  ----------------------------------------------------------------------
  -- Set restriction

  -- Restricts a set to variables with the given sort.

  restrict-to-sort :
    ∀ s → Vars → Finite-subset-of (Var s)
  restrict-to-sort = map-Maybe ∘ maybe-cast-∃Var

  abstract

    -- A lemma characterising restrict-to-sort (in erased contexts).

    @0 ∈restrict-to-sort≃ :
      (x ∈ restrict-to-sort s xs) ≃ ((s , x) ∈ xs)
    ∈restrict-to-sort≃ {s} {x} {xs} =
      x ∈ restrict-to-sort s xs                            ↝⟨ ∈map-Maybe≃ ⟩
      ∥ (∃ λ y → y ∈ xs × maybe-cast-∃Var s y ≡ just x) ∥  ↝⟨ ∥∥-cong (∃-cong λ _ → ∃-cong λ _ → lemma) ⟩
      ∥ (∃ λ y → y ∈ xs × y ≡ (s , x)) ∥                   ↝⟨ ∥∥-cong (∃-cong λ _ → ×-cong₁ λ eq → ≡⇒↝ _ $ cong (_∈ _) eq) ⟩
      ∥ (∃ λ y → (s , x) ∈ xs × y ≡ (s , x)) ∥             ↔⟨ (×-cong₁ λ _ → ∥∥↔ ∈-propositional) F.∘
                                                              inverse ∥∥×∥∥↔∥×∥ F.∘
                                                              ∥∥-cong ∃-comm ⟩
      (s , x) ∈ xs × ∥ (∃ λ y → y ≡ (s , x)) ∥             ↔⟨ (drop-⊤-right λ _ →
                                                               _⇔_.to contractible⇔↔⊤ $
                                                               propositional⇒inhabited⇒contractible
                                                                 truncation-is-proposition
                                                                 ∣ _ , refl _ ∣) ⟩□
      (s , x) ∈ xs                                         □
      where
      lemma :
        (maybe-cast-∃Var s (s′ , y) ≡ just x) ≃
        _≡_ {A = ∃Var} (s′ , y) (s , x)
      lemma {s′} {y} with s′ ≟S s
      … | yes [ s′≡s ] =
        just (cast-Var s′≡s y) ≡ just x  ↔⟨ inverse Bijection.≡↔inj₂≡inj₂ ⟩
        cast-Var s′≡s y ≡ x              ↝⟨ ≡cast-Var≃ ⟩□
        (s′ , y) ≡ (s , x)               □
      … | no [ s′≢s ] =
        nothing ≡ just x    ↔⟨ Bijection.≡↔⊎ ⟩
        ⊥                   ↔⟨ ⊥↔⊥ ⟩
        ⊥                   ↝⟨ inverse $ ≢→,≡,≃ s′≢s ⟩
        (s′ , y) ≡ (s , x)  □

    -- A kind of extensionality.

    @0 ≃∈restrict-to-sort :
      ((s , x) ∈ xs) ≃
      (∀ s′ (s≡s′ : s ≡ s′) → cast-Var s≡s′ x ∈ restrict-to-sort s′ xs)
    ≃∈restrict-to-sort {s} {x} {xs} =
      (s , x) ∈ xs                                                       ↝⟨ inverse ∈restrict-to-sort≃ ⟩
      x ∈ restrict-to-sort s xs                                          ↝⟨ ≡⇒↝ _ $ cong (_∈ _) $ sym cast-Var-refl ⟩
      cast-Var (refl _) x ∈ restrict-to-sort s xs                        ↝⟨ ∀-intro _ ext ⟩□
      (∀ s′ (s≡s′ : s ≡ s′) → cast-Var s≡s′ x ∈ restrict-to-sort s′ xs)  □

    -- The function restrict-to-sort s is monotone with respect to _⊆_
    -- (in erased contexts).

    @0 restrict-to-sort-cong :
      xs ⊆ ys → restrict-to-sort s xs ⊆ restrict-to-sort s ys
    restrict-to-sort-cong {xs} {ys} {s} xs⊆ys = λ z →
      z ∈ restrict-to-sort s xs  ↔⟨ ∈restrict-to-sort≃ ⟩
      (s , z) ∈ xs               ↝⟨ xs⊆ys _ ⟩
      (s , z) ∈ ys               ↔⟨ inverse ∈restrict-to-sort≃ ⟩□
      z ∈ restrict-to-sort s ys  □

    -- A lemma that allows one to replace the sort with an equal one
    -- in an expression of the form z ∈ restrict-to-sort s xs.

    sort-can-be-replaced-in-∈-restrict-to-sort :
      ∀ {s s′ s≡s′ z} xs →
      (z ∈ restrict-to-sort s xs) ≃
      (cast-Var s≡s′ z ∈ restrict-to-sort s′ xs)
    sort-can-be-replaced-in-∈-restrict-to-sort {s} {s≡s′} {z} xs =
      elim¹
        (λ {s′} s≡s′ →
           (z ∈ restrict-to-sort s xs) ≃
           (cast-Var s≡s′ z ∈ restrict-to-sort s′ xs))
        (≡⇒↝ _ $ cong (_∈ _) (sym cast-Var-refl))
        s≡s′

    -- The function restrict-to-sort commutes with _∪_ (in erased
    -- contexts).

    @0 restrict-to-sort-∪ :
      ∀ xs →
      restrict-to-sort s (xs ∪ ys) ≡
      restrict-to-sort s xs ∪ restrict-to-sort s ys
    restrict-to-sort-∪ {s} {ys} xs =
      _≃_.from extensionality λ x →
        x ∈ restrict-to-sort s (xs ∪ ys)                   ↔⟨ ∈∪≃ F.∘
                                                              ∈restrict-to-sort≃ ⟩
        (s , x) ∈ xs ∥⊎∥ (s , x) ∈ ys                      ↔⟨ inverse $
                                                              (∈restrict-to-sort≃
                                                                 ∥⊎∥-cong
                                                               ∈restrict-to-sort≃) F.∘
                                                              ∈∪≃ ⟩□
        x ∈ restrict-to-sort s xs ∪ restrict-to-sort s ys  □

  ----------------------------------------------------------------------
  -- Renamings

  -- Renamings.
  --
  -- A renaming for the sort s maps the variables to be renamed to the
  -- corresponding "new" variables in Var s.
  --
  -- Every new variable must be in the set fs (the idea is that this
  -- set should be a superset of the set of free variables of the
  -- resulting term), and dom must be the renaming's domain.
  --
  -- TODO: It may make sense to replace this function type with an
  -- efficient data structure.

  Renaming :
    (@0 dom fs : Finite-subset-of (Var s)) → Type ℓ
  Renaming {s} dom fs =
    (x : Var s) →
    (∃ λ (y : Var s) → Erased (x ∈ dom × y ∈ fs))
      ⊎
    Erased (x ∉ dom)

  -- An empty renaming.

  empty-renaming :
    (@0 fs : Finite-subset-of (Var s)) →
    Renaming [] fs
  empty-renaming _ = λ _ → inj₂ [ (λ ()) ]

  -- Adds the mapping x ↦ y to the renaming.

  extend-renaming :
    (x y : Var s) →
    Renaming dom fs →
    Renaming (x ∷ dom) (y ∷ fs)
  extend-renaming {dom} x y ρ z with z ≟V x
  … | yes ([ z≡x ]) =
    inj₁
      ( y
      , [ ≡→∈∷ z≡x
        , ≡→∈∷ (refl _)
        ]
      )
  … | no [ z≢x ] =
    ⊎-map
      (Σ-map id (E.map (Σ-map ∈→∈∷ ∈→∈∷)))
      (E.map (_∘
         (z ∈ x ∷ dom        ↔⟨ ∈∷≃ ⟩
          z ≡ x ∥⊎∥ z ∈ dom  ↔⟨ drop-⊥-left-∥⊎∥ ∈-propositional z≢x ⟩□
          z ∈ dom            □))) $
    ρ z

  -- A renaming for a single variable.

  singleton-renaming :
    (x y : Var s)
    (@0 fs : Finite-subset-of (Var s)) →
    Renaming (singleton x) (y ∷ fs)
  singleton-renaming x y fs =
    extend-renaming x y (empty-renaming fs)

  ----------------------------------------------------------------------
  -- An implementation of renaming

  private

    -- Capture-avoiding renaming for variables.

    rename-Var :
      ∀ {s s′} {@0 dom fs} (x : Var s′)
      (ρ : Renaming dom fs) →
      @0 restrict-to-sort s (free-Var x) ∖ dom ⊆ fs →
      ∃ λ (x′ : Var s′) →
        Erased (restrict-to-sort s (free-Var x′) ⊆ fs
                  ×
                restrict-to-sort s (free-Var x) ⊆
                dom ∪ restrict-to-sort s (free-Var x′)
                  ×
                ∀ s′ → s′ ≢ s →
                restrict-to-sort s′ (free-Var x′) ≡
                restrict-to-sort s′ (free-Var x))
    rename-Var {s} {s′} {dom} {fs} x ρ ⊆free with s ≟S s′
    … | no [ s≢s′ ] =
        x
      , [ (λ y →
             y ∈ restrict-to-sort s (free-Var x)  ↔⟨ from-isomorphism (∥∥↔ ∃Var-set) F.∘
                                                     ∈singleton≃ F.∘
                                                     ∈restrict-to-sort≃ ⟩
             (s , y) ≡ (s′ , x)                   ↝⟨ cong proj₁ ⟩
             s ≡ s′                               ↝⟨ s≢s′ ⟩
             ⊥                                    ↝⟨ ⊥-elim ⟩□
             y ∈ fs                               □)
        , (λ y →
             y ∈ restrict-to-sort s (free-Var x)        ↝⟨ ∈→∈∪ʳ dom ⟩□
             y ∈ dom ∪ restrict-to-sort s (free-Var x)  □)
        , (λ _ _ → refl _)
        ]
    … | yes [ s≡s′ ] with ρ (cast-Var (sym s≡s′) x)
    …   | inj₂ [ x∉domain ] =
        x
      , [ (λ y →
             y ∈ restrict-to-sort s (free-Var x)            ↝⟨ (λ hyp →
                                                                    hyp
                                                                  , _≃_.to
                                                                      (from-isomorphism ≡-comm F.∘
                                                                       inverse ≡cast-Var≃ F.∘
                                                                       from-isomorphism ≡-comm F.∘
                                                                       from-isomorphism (∥∥↔ ∃Var-set) F.∘
                                                                       ∈singleton≃ F.∘
                                                                       ∈restrict-to-sort≃)
                                                                      hyp) ⟩
             y ∈ restrict-to-sort s (free-Var x) ×
             y ≡ cast-Var (sym s≡s′) x                      ↝⟨ Σ-map id (λ y≡x → subst (_∉ _) (sym y≡x) x∉domain) ⟩

             y ∈ restrict-to-sort s (free-Var x) × y ∉ dom  ↔⟨ inverse ∈minus≃ ⟩

             y ∈ restrict-to-sort s (free-Var x) ∖ dom      ↝⟨ ⊆free _ ⟩□

             y ∈ fs                                         □)
        , (λ y →
             y ∈ restrict-to-sort s (free-Var x)        ↝⟨ ∈→∈∪ʳ dom ⟩□
             y ∈ dom ∪ restrict-to-sort s (free-Var x)  □)
        , (λ _ _ → refl _)
        ]
    …   | inj₁ (y , [ x∈dom , y∈free ]) =
        cast-Var s≡s′ y
      , [ (λ z →
             z ∈ restrict-to-sort s (free-Var (cast-Var s≡s′ y))  ↔⟨ from-isomorphism (∥∥↔ ∃Var-set) F.∘
                                                                     ∈singleton≃ F.∘
                                                                     ∈restrict-to-sort≃ ⟩
             (s , z) ≡ (s′ , cast-Var s≡s′ y)                     ↝⟨ ≡⇒↝ _ $ cong (_ ≡_) $ sym ≡,cast-Var ⟩
             (s , z) ≡ (s , y)                                    ↔⟨ ≡→,≡,≃ ⟩
             z ≡ y                                                ↝⟨ (λ z≡y → subst (_∈ _) (sym z≡y) y∈free) ⟩□
             z ∈ fs                                               □)
        , (λ z →
             z ∈ restrict-to-sort s (free-Var x)                        ↔⟨ from-isomorphism ≡-comm F.∘
                                                                           inverse ≡cast-Var≃ F.∘
                                                                           from-isomorphism ≡-comm F.∘
                                                                           from-isomorphism (∥∥↔ ∃Var-set) F.∘
                                                                           ∈singleton≃ F.∘
                                                                           ∈restrict-to-sort≃ ⟩

             z ≡ cast-Var (sym s≡s′) x                                  ↝⟨ (λ z≡x → subst (_∈ _) (sym z≡x) x∈dom) ⟩

             z ∈ dom                                                    ↝⟨ ∈→∈∪ˡ ⟩□

             z ∈ dom ∪ restrict-to-sort s (free-Var (cast-Var s≡s′ y))  □)
        , (λ s″ s″≢s → _≃_.from extensionality λ z →
             z ∈ restrict-to-sort s″ (singleton (s′ , cast-Var s≡s′ y))  ↔⟨ from-isomorphism (∥∥↔ ∃Var-set) F.∘
                                                                            ∈singleton≃ F.∘
                                                                            ∈restrict-to-sort≃ ⟩
             (s″ , z) ≡ (s′ , cast-Var s≡s′ y)                           ↔⟨ ≢→,≡,≃ (subst (_ ≢_) s≡s′ s″≢s) ⟩
             ⊥                                                           ↔⟨ inverse $ ≢→,≡,≃ (subst (_ ≢_) s≡s′ s″≢s) ⟩
             (s″ , z) ≡ (s′ , x)                                         ↔⟨ inverse $
                                                                            from-isomorphism (∥∥↔ ∃Var-set) F.∘
                                                                            ∈singleton≃ F.∘
                                                                            ∈restrict-to-sort≃ ⟩□
             z ∈ restrict-to-sort s″ ((s′ , x) ∷ [])                     □)
        ]

  private
   mutual

    -- Capture-avoiding renaming for terms.

    rename-Tm :
      ∀ {s} {@0 dom} {fs} (tˢ : Tmˢ s′) (t : Tm tˢ)
      (ρ : Renaming dom fs) →
      @0 restrict-to-sort s (free-Tm tˢ t) ∖ dom ⊆ fs →
      ∃ λ (t′ : Tm tˢ) →
        Erased (restrict-to-sort s (free-Tm tˢ t′) ⊆ fs
                  ×
                restrict-to-sort s (free-Tm tˢ t) ⊆
                dom ∪ restrict-to-sort s (free-Tm tˢ t′)
                  ×
                ∀ s′ → s′ ≢ s →
                restrict-to-sort s′ (free-Tm tˢ t′) ≡
                restrict-to-sort s′ (free-Tm tˢ t))
    rename-Tm var        = rename-Var
    rename-Tm (op _ asˢ) = rename-Args asˢ

    -- Capture-avoiding renaming for sequences of arguments.

    rename-Args :
      ∀ {s} {@0 dom} {fs} (asˢ : Argsˢ vs) (as : Args asˢ)
      (ρ : Renaming dom fs) →
      @0 restrict-to-sort s (free-Args asˢ as) ∖ dom ⊆ fs →
      ∃ λ (as′ : Args asˢ) →
        Erased (restrict-to-sort s (free-Args asˢ as′) ⊆ fs
                  ×
                restrict-to-sort s (free-Args asˢ as) ⊆
                dom ∪ restrict-to-sort s (free-Args asˢ as′)
                  ×
                ∀ s′ → s′ ≢ s →
                restrict-to-sort s′ (free-Args asˢ as′) ≡
                restrict-to-sort s′ (free-Args asˢ as))
    rename-Args nil _ _ _ =
        _
      , [ (λ _ ())
        , (λ _ ())
        , (λ _ _ → refl _)
        ]
    rename-Args {s} {dom} {fs} (cons aˢ asˢ) (a , as) ρ ⊆free =
      Σ-zip _,_
        (λ {a′ as′} ([ ⊆free₁ , ⊆dom₁ , ≡free₁ ])
                    ([ ⊆free₂ , ⊆dom₂ , ≡free₂ ]) →
           [ (λ x →
                x ∈ restrict-to-sort s
                      (free-Arg aˢ a′ ∪ free-Args asˢ as′)   ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $ restrict-to-sort-∪ (free-Arg aˢ a′) ⟩

                x ∈ restrict-to-sort s (free-Arg aˢ a′) ∪
                    restrict-to-sort s (free-Args asˢ as′)   ↝⟨ ∪-cong-⊆ ⊆free₁ ⊆free₂ _ ⟩

                x ∈ fs ∪ fs                                  ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $ idem _ ⟩□

                x ∈ fs                                       □)
           , (λ x →
                x ∈ restrict-to-sort s
                      (free-Arg aˢ a ∪ free-Args asˢ as)                ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $
                                                                           restrict-to-sort-∪ (free-Arg aˢ a) ⟩
                x ∈ restrict-to-sort s (free-Arg aˢ a) ∪
                    restrict-to-sort s (free-Args asˢ as)               ↝⟨ ∪-cong-⊆ ⊆dom₁ ⊆dom₂ _ ⟩

                x ∈ (dom ∪ restrict-to-sort s (free-Arg aˢ a′)) ∪
                    (dom ∪ restrict-to-sort s (free-Args asˢ as′))      ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) (

                    (dom ∪ restrict-to-sort s (free-Arg aˢ a′)) ∪
                    (dom ∪ restrict-to-sort s (free-Args asˢ as′))           ≡⟨ sym $
                                                                                L.assoc dom ⟩
                    dom ∪
                    (restrict-to-sort s (free-Arg aˢ a′) ∪
                       (dom ∪ restrict-to-sort s (free-Args asˢ as′)))       ≡⟨ cong (dom ∪_) $
                                                                                L.assoc (restrict-to-sort s (free-Arg aˢ a′)) ⟩
                    dom ∪
                    ((restrict-to-sort s (free-Arg aˢ a′) ∪ dom) ∪
                     restrict-to-sort s (free-Args asˢ as′))                 ≡⟨ cong (λ xs → dom ∪ (xs ∪ _)) $ sym $
                                                                                L.comm dom ⟩
                    dom ∪
                    ((dom ∪ restrict-to-sort s (free-Arg aˢ a′)) ∪
                     restrict-to-sort s (free-Args asˢ as′))                 ≡⟨ cong (dom ∪_) $ sym $
                                                                                L.assoc dom ⟩
                    dom ∪
                    (dom ∪
                     (restrict-to-sort s (free-Arg aˢ a′) ∪
                      restrict-to-sort s (free-Args asˢ as′)))               ≡⟨ L.assoc dom ⟩

                    (dom ∪ dom) ∪
                    (restrict-to-sort s (free-Arg aˢ a′) ∪
                     restrict-to-sort s (free-Args asˢ as′))                 ≡⟨ cong (_∪ _) $
                                                                                idem dom ⟩
                    dom ∪
                    (restrict-to-sort s (free-Arg aˢ a′) ∪
                     restrict-to-sort s (free-Args asˢ as′))                 ≡⟨ cong (dom ∪_) $ sym $
                                                                                restrict-to-sort-∪ (free-Arg aˢ a′) ⟩∎
                    dom ∪ restrict-to-sort s
                            (free-Arg aˢ a′ ∪ free-Args asˢ as′)             ∎) ⟩□

                x ∈ dom ∪ restrict-to-sort s
                            (free-Arg aˢ a′ ∪ free-Args asˢ as′)        □)
           , (λ s′ s′≢s → _≃_.from extensionality λ x →
                x ∈ restrict-to-sort s′ (free-Arg aˢ a′ ∪ free-Args asˢ as′)  ↔⟨ inverse (∈restrict-to-sort≃ ∥⊎∥-cong ∈restrict-to-sort≃) F.∘
                                                                                 ∈∪≃ {y = free-Arg aˢ a′} F.∘
                                                                                 ∈restrict-to-sort≃ ⟩
                x ∈ restrict-to-sort s′ (free-Arg aˢ a′) ∥⊎∥
                x ∈ restrict-to-sort s′ (free-Args asˢ as′)                   ↝⟨ ≡⇒↝ _ $ cong₂ (λ y z → x ∈ y ∥⊎∥ x ∈ z)
                                                                                   (≡free₁ s′ s′≢s)
                                                                                   (≡free₂ s′ s′≢s) ⟩
                x ∈ restrict-to-sort s′ (free-Arg aˢ a) ∥⊎∥
                x ∈ restrict-to-sort s′ (free-Args asˢ as)                    ↔⟨ inverse $
                                                                                 inverse (∈restrict-to-sort≃ ∥⊎∥-cong ∈restrict-to-sort≃) F.∘
                                                                                 ∈∪≃ {y = free-Arg aˢ a} F.∘
                                                                                 ∈restrict-to-sort≃ ⟩□
                x ∈ restrict-to-sort s′ (free-Arg aˢ a ∪ free-Args asˢ as)    □)
           ])
        (rename-Arg aˢ a ρ
           (λ x →
              x ∈ restrict-to-sort s (free-Arg aˢ a) ∖ dom    ↝⟨ minus-cong-⊆
                                                                   (restrict-to-sort-cong λ _ → ∈→∈∪ˡ {y = free-Arg aˢ a})
                                                                   (⊆-refl {x = dom}) _ ⟩
              x ∈ restrict-to-sort s
                    (free-Arg aˢ a ∪ free-Args asˢ as) ∖ dom  ↝⟨ ⊆free _ ⟩□

              x ∈ fs                                          □))
        (rename-Args asˢ as ρ
           (λ x →
              x ∈ restrict-to-sort s (free-Args asˢ as) ∖ dom  ↝⟨ minus-cong-⊆
                                                                    (restrict-to-sort-cong λ _ → ∈→∈∪ʳ (free-Arg aˢ a))
                                                                    (⊆-refl {x = dom}) _ ⟩
              x ∈ restrict-to-sort s
                    (free-Arg aˢ a ∪ free-Args asˢ as) ∖ dom   ↝⟨ ⊆free _ ⟩□

              x ∈ fs                                           □))

    -- Capture-avoiding renaming for arguments.

    rename-Arg :
      ∀ {s} {@0 dom} {fs} (aˢ : Argˢ v) (a : Arg aˢ)
      (ρ : Renaming dom fs) →
      @0 restrict-to-sort s (free-Arg aˢ a) ∖ dom ⊆ fs →
      ∃ λ (a′ : Arg aˢ) →
        Erased (restrict-to-sort s (free-Arg aˢ a′) ⊆ fs
                  ×
                restrict-to-sort s (free-Arg aˢ a) ⊆
                dom ∪ restrict-to-sort s (free-Arg aˢ a′)
                  ×
                ∀ s′ → s′ ≢ s →
                restrict-to-sort s′ (free-Arg aˢ a′) ≡
                restrict-to-sort s′ (free-Arg aˢ a))
    rename-Arg (nil tˢ) = rename-Tm tˢ

    rename-Arg {s} {dom} {fs} (cons {s = s′} aˢ) (x , a) ρ ⊆free
      with s ≟S s′
    … | no [ s≢s′ ] =
      -- The bound variable does not have the same sort as the
      -- ones to be renamed. Continue recursively.
      Σ-map
        (x ,_)
        (λ {a′} → E.map (Σ-map
           (λ ⊆free y →
              y ∈ restrict-to-sort s (del (s′ , x) (free-Arg aˢ a′))  ↔⟨ ∈delete≃ merely-equal?-∃Var F.∘
                                                                         ∈restrict-to-sort≃ ⟩
              (s , y) ≢ (s′ , x) × (s , y) ∈ free-Arg aˢ a′           ↝⟨ proj₂ ⟩
              (s , y) ∈ free-Arg aˢ a′                                ↔⟨ inverse ∈restrict-to-sort≃ ⟩
              y ∈ restrict-to-sort s (free-Arg aˢ a′)                 ↝⟨ ⊆free _ ⟩□
              y ∈ fs                                                  □)
           (Σ-map
              (λ ⊆dom y →
                 y ∈ restrict-to-sort s (del (s′ , x) (free-Arg aˢ a))  ↔⟨ (∃-cong λ _ → inverse $ ∈restrict-to-sort≃ {xs = free-Arg aˢ a}) F.∘
                                                                           ∈delete≃ merely-equal?-∃Var F.∘
                                                                           ∈restrict-to-sort≃ ⟩
                 (s , y) ≢ (s′ , x) ×
                 y ∈ restrict-to-sort s (free-Arg aˢ a)                 ↝⟨ Σ-map id (⊆dom _) ⟩

                 (s , y) ≢ (s′ , x) ×
                 y ∈ dom ∪ restrict-to-sort s (free-Arg aˢ a′)          ↔⟨ (∃-cong λ _ →
                                                                            (F.id ∥⊎∥-cong ∈restrict-to-sort≃) F.∘
                                                                            ∈∪≃) ⟩
                 (s , y) ≢ (s′ , x) ×
                 (y ∈ dom ∥⊎∥ (s , y) ∈ free-Arg aˢ a′)                 ↝⟨ (uncurry λ y≢x → id ∥⊎∥-cong y≢x ,_) ⟩

                 y ∈ dom ∥⊎∥
                 (s , y) ≢ (s′ , x) × (s , y) ∈ free-Arg aˢ a′          ↔⟨ inverse $
                                                                           (F.id
                                                                              ∥⊎∥-cong
                                                                            (∈delete≃ merely-equal?-∃Var F.∘
                                                                             ∈restrict-to-sort≃)) F.∘
                                                                           ∈∪≃ ⟩□
                 y ∈ dom ∪ restrict-to-sort s
                             (del (s′ , x) (free-Arg aˢ a′))            □)
              (λ ≡free s″ s″≢s → _≃_.from extensionality λ z →
                 z ∈ restrict-to-sort s″ (del (s′ , x) (free-Arg aˢ a′))  ↔⟨ (∃-cong λ _ → inverse $ ∈restrict-to-sort≃ {xs = free-Arg aˢ a′}) F.∘
                                                                             ∈delete≃ merely-equal?-∃Var F.∘
                                                                             ∈restrict-to-sort≃ ⟩
                 (s″ , z) ≢ (s′ , x) ×
                 z ∈ restrict-to-sort s″ (free-Arg aˢ a′)                 ↝⟨ (∃-cong λ _ → ≡⇒↝ _ $ cong (_ ∈_) $ ≡free s″ s″≢s) ⟩

                 (s″ , z) ≢ (s′ , x) ×
                 z ∈ restrict-to-sort s″ (free-Arg aˢ a)                  ↔⟨ inverse $
                                                                             (∃-cong λ _ → inverse $ ∈restrict-to-sort≃ {xs = free-Arg aˢ a}) F.∘
                                                                             ∈delete≃ merely-equal?-∃Var F.∘
                                                                             ∈restrict-to-sort≃ ⟩□
                 z ∈ restrict-to-sort s″ (del (s′ , x) (free-Arg aˢ a))   □))))
        (rename-Arg aˢ a ρ
           (λ y →
              y ∈ restrict-to-sort s (free-Arg aˢ a) ∖ dom      ↔⟨ (∈restrict-to-sort≃ ×-cong F.id) F.∘
                                                                   ∈minus≃ ⟩

              (s , y) ∈ free-Arg aˢ a × y ∉ dom                 ↝⟨ Σ-map (s≢s′ ∘ cong proj₁ ,_) id ⟩

              ((s , y) ≢ (s′ , x) × (s , y) ∈ free-Arg aˢ a) ×
              y ∉ dom                                           ↔⟨ inverse $
                                                                   (×-cong₁ λ _ → ∈delete≃ merely-equal?-∃Var) F.∘
                                                                   (∈restrict-to-sort≃ ×-cong F.id) F.∘
                                                                   ∈minus≃ ⟩
              y ∈ restrict-to-sort s
                    (del (s′ , x) (free-Arg aˢ a)) ∖ dom        ↝⟨ ⊆free _ ⟩□

              y ∈ fs                                            □))
    … | yes [ s≡s′ ] =
      -- The bound variable has the same sort as the ones to be
      -- renamed. Extend the renaming with a mapping from the bound
      -- variable to a fresh one, and continue recursively.
      Σ-map
        (x′ ,_)
        (λ {a′} → E.map (Σ-map
           (λ ⊆x′∷free y →
              y ∈ restrict-to-sort s (del (s′ , x′) (free-Arg aˢ a′))  ↔⟨ (∃-cong λ _ → inverse $
                                                                           ∈restrict-to-sort≃ {xs = free-Arg aˢ a′}) F.∘
                                                                          ∈delete≃ merely-equal?-∃Var F.∘
                                                                          ∈restrict-to-sort≃ ⟩
              (s , y) ≢ (s′ , x′) ×
              y ∈ restrict-to-sort s (free-Arg aˢ a′)                  ↝⟨ Σ-map id (⊆x′∷free _) ⟩

              (s , y) ≢ (s′ , x′) ×
              y ∈ cast-Var (sym s≡s′) x′ ∷ fs                          ↔⟨ (¬-cong ext (
                                                                           from-isomorphism ≡-comm F.∘
                                                                           inverse ≡cast-Var≃ F.∘
                                                                           from-isomorphism ≡-comm))
                                                                            ×-cong
                                                                          ∈∷≃ ⟩
              y ≢ cast-Var (sym s≡s′) x′ ×
              (y ≡ cast-Var (sym s≡s′) x′ ∥⊎∥ y ∈ fs)                  ↔⟨ (∃-cong λ y≢x → drop-⊥-left-∥⊎∥ ∈-propositional y≢x) ⟩

              y ≢ cast-Var (sym s≡s′) x′ × y ∈ fs                      ↝⟨ proj₂ ⟩□

              y ∈ fs                                                   □)
           (Σ-map
              (λ ⊆x∷dom y y∈ →
                 let lemma : y ∉ dom → y ∈ fs
                     lemma =
                       y ∉ dom                                     ↝⟨ _≃_.from ∈minus≃ ∘ (y∈ ,_)  ⟩

                       y ∈ restrict-to-sort s
                             (del (s′ , x) (free-Arg aˢ a)) ∖ dom  ↝⟨ ⊆free _ ⟩□

                       y ∈ fs                                      □
                 in                                                     $⟨ y∈ ⟩
                 y ∈ restrict-to-sort s (del (s′ , x) (free-Arg aˢ a))  ↔⟨ (∃-cong λ _ → inverse $ ∈restrict-to-sort≃ {xs = free-Arg aˢ a}) F.∘
                                                                           ∈delete≃ merely-equal?-∃Var F.∘
                                                                           ∈restrict-to-sort≃ ⟩
                 (s , y) ≢ (s′ , x) ×
                 y ∈ restrict-to-sort s (free-Arg aˢ a)                 ↝⟨ Σ-map id (⊆x∷dom _) ⟩

                 (s , y) ≢ (s′ , x) ×
                 y ∈ cast-Var (sym s≡s′) x ∷ dom ∪
                     restrict-to-sort s (free-Arg aˢ a′)                ↔⟨ (∃-cong λ _ →
                                                                            (F.id
                                                                               ∥⊎∥-cong
                                                                             ((F.id ∥⊎∥-cong ∈restrict-to-sort≃) F.∘
                                                                              ∈∪≃)) F.∘
                                                                            ∈∷≃) ⟩
                 (s , y) ≢ (s′ , x) ×
                 (y ≡ cast-Var (sym s≡s′) x ∥⊎∥ y ∈ dom ∥⊎∥
                  (s , y) ∈ free-Arg aˢ a′)                             ↔⟨ (∃-cong λ y≢x → drop-⊥-left-∥⊎∥ ∥⊎∥-propositional $
                                                                            y≢x ∘ sym ∘ _≃_.to ≡cast-Var≃ ∘ sym) ⟩
                 (s , y) ≢ (s′ , x) ×
                 (y ∈ dom ∥⊎∥ (s , y) ∈ free-Arg aˢ a′)                 ↔⟨ (∃-cong λ _ →
                                                                            ∥⊎∥≃∥⊎∥¬× $ Dec→Dec-∥∥ $
                                                                            member? (ΠΠ-Dec-Erased→ΠΠ-Dec-Erased-∥∥ _≟V_) y dom) ⟩
                 (s , y) ≢ (s′ , x) ×
                 (y ∈ dom ∥⊎∥ y ∉ dom × (s , y) ∈ free-Arg aˢ a′)       ↝⟨ (uncurry λ y≢x → id ∥⊎∥-cong ×-cong₁ λ _ →

                     y ∉ dom                                                  ↝⟨ _≃_.from ∈minus≃ ∘ (y∈ ,_)  ⟩

                     y ∈ restrict-to-sort s
                           (del (s′ , x) (free-Arg aˢ a)) ∖ dom               ↝⟨ ⊆free _ ⟩

                     y ∈ fs                                                   ↝⟨ ∈→∈map ⟩

                     (s , y) ∈ L.map (s ,_) fs                                ↝⟨ (λ y∈ →

                         (s , y) ≡ (s′ , x′)                                        ↝⟨ (λ y≡x′ → subst (_∈ _) y≡x′ y∈) ⟩
                         (s′ , x′) ∈ L.map (s ,_) fs                                ↝⟨ erased (proj₂ (fresh (L.map (s ,_) fs))) ⟩□
                         ⊥                                                          □) ⟩□

                     (s , y) ≢ (s′ , x′)                                      □) ⟩

                 y ∈ dom ∥⊎∥
                 (s , y) ≢ (s′ , x′) × (s , y) ∈ free-Arg aˢ a′         ↔⟨ inverse $
                                                                           (F.id
                                                                              ∥⊎∥-cong
                                                                            (∈delete≃ merely-equal?-∃Var F.∘
                                                                             ∈restrict-to-sort≃)) F.∘
                                                                           ∈∪≃ ⟩□
                 y ∈ dom ∪ restrict-to-sort s
                             (del (s′ , x′) (free-Arg aˢ a′))           □)
              (λ ≡free s″ s″≢s → _≃_.from extensionality λ z →
                 z ∈ restrict-to-sort s″
                       (del (s′ , x′) (free-Arg aˢ a′))                  ↔⟨ (∃-cong λ _ → inverse $ ∈restrict-to-sort≃ {xs = free-Arg aˢ a′}) F.∘
                                                                            ∈delete≃ merely-equal?-∃Var F.∘
                                                                            ∈restrict-to-sort≃ ⟩
                 (s″ , z) ≢ (s′ , x′) ×
                 z ∈ restrict-to-sort s″ (free-Arg aˢ a′)                ↔⟨ (×-cong₁ λ _ → ¬-cong ext (
                                                                             ≢→,≡,≃ $ s″≢s ∘ subst (_ ≡_) (sym s≡s′))) ⟩

                 ¬ ⊥ × z ∈ restrict-to-sort s″ (free-Arg aˢ a′)          ↝⟨ (∃-cong λ _ → ≡⇒↝ _ $ cong (_ ∈_) $ ≡free s″ s″≢s) ⟩

                 ¬ ⊥ × z ∈ restrict-to-sort s″ (free-Arg aˢ a)           ↔⟨ (inverse $ ×-cong₁ λ _ → ¬-cong ext (
                                                                             ≢→,≡,≃ $ s″≢s ∘ subst (_ ≡_) (sym s≡s′))) ⟩
                 (s″ , z) ≢ (s′ , x) ×
                 z ∈ restrict-to-sort s″ (free-Arg aˢ a)                 ↔⟨ inverse $
                                                                            (∃-cong λ _ → inverse $ ∈restrict-to-sort≃ {xs = free-Arg aˢ a}) F.∘
                                                                            ∈delete≃ merely-equal?-∃Var F.∘
                                                                            ∈restrict-to-sort≃ ⟩□
                 z ∈ restrict-to-sort s″ (del (s′ , x) (free-Arg aˢ a))  □))))
        (rename-Arg aˢ a
           (extend-renaming
              (cast-Var (sym s≡s′) x)
              (cast-Var (sym s≡s′) x′)
              ρ)
           (λ y →
              y ∈ restrict-to-sort s (free-Arg aˢ a) ∖
                    (cast-Var (sym s≡s′) x ∷ dom)         ↔⟨ (∈restrict-to-sort≃
                                                                ×-cong
                                                              ¬⊎↔¬×¬ ext F.∘
                                                              from-isomorphism ¬∥∥↔¬ F.∘
                                                              ¬-cong ext ∈∷≃) F.∘
                                                             ∈minus≃ {_≟_ = merely-equal?-Var} ⟩
              (s , y) ∈ free-Arg aˢ a ×
              y ≢ cast-Var (sym s≡s′) x × y ∉ dom         ↔⟨ inverse $
                                                             from-isomorphism (inverse Σ-assoc) F.∘
                                                             (×-cong₁ λ _ →
                                                                ((∃-cong λ _ → ¬-cong ext (
                                                                  from-isomorphism ≡-comm F.∘
                                                                  inverse ≡cast-Var≃ F.∘
                                                                  from-isomorphism ≡-comm)) F.∘
                                                                 from-isomorphism ×-comm) F.∘
                                                                ∈delete≃ merely-equal?-∃Var F.∘
                                                                ∈restrict-to-sort≃) F.∘
                                                             ∈minus≃ ⟩
              y ∈ restrict-to-sort s
                    (del (s′ , x) (free-Arg aˢ a)) ∖ dom  ↝⟨ ⊆free _ ⟩

              y ∈ fs                                      ↝⟨ ∣inj₂∣ ⟩

              y ≡ cast-Var (sym s≡s′) x′ ∥⊎∥ y ∈ fs       ↔⟨ inverse ∈∷≃ ⟩□

              y ∈ cast-Var (sym s≡s′) x′ ∷ fs             □))
      where
      -- TODO: Perhaps it would make sense to avoid the use of L.map
      -- below.
      x′ = proj₁ (fresh (L.map (s ,_) fs))

  -- Capture-avoiding renaming of free variables.
  --
  -- Bound variables are renamed to variables that are fresh with
  -- respect to the set fs.
  --
  -- Note that this function renames every bound variable of the given
  -- sort.

  rename :
    ∀ {s} {@0 dom} {fs} (tˢ : Skeleton k s′) (t : Data tˢ)
    (ρ : Renaming dom fs) →
    @0 restrict-to-sort s (free tˢ t) ∖ dom ⊆ fs →
    ∃ λ (t′ : Data tˢ) →
      Erased (restrict-to-sort s (free tˢ t′) ⊆ fs
                ×
              restrict-to-sort s (free tˢ t) ⊆
              dom ∪ restrict-to-sort s (free tˢ t′)
                ×
              ∀ s′ → s′ ≢ s →
              restrict-to-sort s′ (free tˢ t′) ≡
              restrict-to-sort s′ (free tˢ t))
  rename {k = var}  = λ { var → rename-Var }
  rename {k = tm}   = rename-Tm
  rename {k = args} = rename-Args
  rename {k = arg}  = rename-Arg

  ----------------------------------------------------------------------
  -- A special case of the implementation of renaming above

  -- Capture-avoiding renaming of x to y.
  --
  -- Note that this function is not intended to be used at runtime. It
  -- uses free to compute the set of free variables.

  rename₁ :
    ∀ {s} (x y : Var s) (tˢ : Skeleton k s′) → Data tˢ → Data tˢ
  rename₁ x y tˢ t =
    proj₁ $
    rename tˢ t
      (singleton-renaming x y
         (restrict-to-sort _ (free tˢ t) ∖ singleton x))
      (λ _ → ∈→∈∷)

  -- If x is renamed to y in a, then the free variables of the result
  -- are a subset of the free variables of a, minus x, plus y.

  @0 free-rename₁⊆ :
    {x y : Var s} (tˢ : Skeleton k s′) {t : Data tˢ} →
    free tˢ (rename₁ x y tˢ t) ⊆
    (_ , y) ∷ del (_ , x) (free tˢ t)
  free-rename₁⊆ {s} {x} {y} tˢ {t} (s′ , z) =
    (s′ , z) ∈ free tˢ (rename₁ x y tˢ t)                          ↔⟨ ≃∈restrict-to-sort ⟩

    (∀ s″ (s′≡s″ : s′ ≡ s″) →
       cast-Var s′≡s″ z ∈
         restrict-to-sort s″ (free tˢ (rename₁ x y tˢ t)))         ↝⟨ (∀-cong _ λ s″ → ∀-cong _ λ s′≡s″ →
                                                                       lemma s″ s′≡s″ (s″ ≟S s)) ⟩
    (∀ s″ (s′≡s″ : s′ ≡ s″) →
       cast-Var s′≡s″ z ∈
         restrict-to-sort s″ ((s , y) ∷ del (s , x) (free tˢ t)))  ↔⟨ inverse ≃∈restrict-to-sort ⟩□

    (s′ , z) ∈ (s , y) ∷ del (s , x) (free tˢ t)                   □
    where
    lemma :
      ∀ s″ (s′≡s″ : s′ ≡ s″) → Dec-Erased (s″ ≡ s) → _ ∈ _ → _ ∈ _
    lemma s″ s′≡s″ (no [ s″≢s ]) =
      cast-Var s′≡s″ z ∈
        restrict-to-sort s″ (free tˢ (rename₁ x y tˢ t))         ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $
                                                                    proj₂ (proj₂ $ erased $ proj₂ $ rename tˢ _ _ _) s″ s″≢s ⟩

      cast-Var s′≡s″ z ∈ restrict-to-sort s″ (free tˢ t)         ↔⟨ ∈restrict-to-sort≃ ⟩

      z′ ∈ free tˢ t                                             ↝⟨ s″≢s ∘ cong proj₁ ,_ ⟩

      z′ ≢ (s , x) × z′ ∈ free tˢ t                              ↝⟨ ∣inj₂∣ ⟩

      z′ ≡ (s , y) ∥⊎∥ z′ ≢ (s , x) × z′ ∈ free tˢ t             ↔⟨ inverse $
                                                                    (F.id ∥⊎∥-cong ∈delete≃ merely-equal?-∃Var) F.∘
                                                                    ∈∷≃ F.∘
                                                                    ∈restrict-to-sort≃ ⟩□
      cast-Var s′≡s″ z ∈
        restrict-to-sort s″ ((s , y) ∷ del (s , x) (free tˢ t))  □
      where
      z′ = s″ , cast-Var s′≡s″ z

    lemma s″ s′≡s″ (yes [ s″≡s ]) =
      cast-Var s′≡s″ z ∈
        restrict-to-sort s″ (free tˢ (rename₁ x y tˢ t))           ↔⟨ sort-can-be-replaced-in-∈-restrict-to-sort
                                                                        (free tˢ (rename₁ x y tˢ t)) ⟩

      z′ ∈ restrict-to-sort s (free tˢ (rename₁ x y tˢ t))         ↝⟨ proj₁ (erased $ proj₂ $ rename tˢ _ _ _) _ ⟩

      z′ ∈ y ∷ (restrict-to-sort s (free tˢ t) ∖ singleton x)      ↔⟨ (F.id
                                                                         ∥⊎∥-cong
                                                                       ((∈restrict-to-sort≃
                                                                           ×-cong
                                                                         (from-isomorphism ¬∥∥↔¬ F.∘
                                                                          ¬-cong ext ∈singleton≃)) F.∘
                                                                        ∈minus≃ {_≟_ = merely-equal?-Var})) F.∘
                                                                      ∈∷≃ ⟩

      z′ ≡ y ∥⊎∥ (s , z′) ∈ free tˢ t × z′ ≢ x                     ↔⟨ inverse $
                                                                      ≡→,≡,≃
                                                                        ∥⊎∥-cong
                                                                      (∃-cong λ _ → ¬-cong ext ≡→,≡,≃) ⟩
      (s , z′) ≡ (s , y) ∥⊎∥
      (s , z′) ∈ free tˢ t × (s , z′) ≢ (s , x)                    ↔⟨ inverse $
                                                                      (F.id ∥⊎∥-cong (from-isomorphism ×-comm F.∘
                                                                                      ∈delete≃ merely-equal?-∃Var)) F.∘
                                                                      ∈∷≃ F.∘
                                                                      ∈restrict-to-sort≃ ⟩

      z′ ∈ restrict-to-sort s ((s , y) ∷ del (s , x) (free tˢ t))  ↔⟨ inverse $
                                                                      sort-can-be-replaced-in-∈-restrict-to-sort
                                                                        ((s , y) ∷ del (s , x) (free tˢ t)) ⟩□
      cast-Var s′≡s″ z ∈
        restrict-to-sort s″ ((s , y) ∷ del (s , x) (free tˢ t))    □
      where
      z′ = cast-Var s″≡s $ cast-Var s′≡s″ z

  -- If x is renamed to y in t, then the free variables of t are a
  -- subset of the free variables of the result plus x.

  @0 ⊆free-rename₁ :
    {x y : Var s} (tˢ : Skeleton k s′) {t : Data tˢ} →
    free tˢ t ⊆ (_ , x) ∷ free tˢ (rename₁ x y tˢ t)
  ⊆free-rename₁ {s} {x} {y} tˢ {t} (s′ , z) =
    (s′ , z) ∈ free tˢ t                                    ↔⟨ ≃∈restrict-to-sort ⟩

    (∀ s″ (s′≡s″ : s′ ≡ s″) →
       cast-Var s′≡s″ z ∈ restrict-to-sort s″ (free tˢ t))  ↝⟨ (∀-cong _ λ s″ → ∀-cong _ λ s′≡s″ →
                                                                lemma s″ s′≡s″ (s″ ≟S s)) ⟩
    (∀ s″ (s′≡s″ : s′ ≡ s″) →
       cast-Var s′≡s″ z ∈
         restrict-to-sort s″
           ((s , x) ∷ free tˢ (rename₁ x y tˢ t)))          ↔⟨ inverse ≃∈restrict-to-sort ⟩□

    (s′ , z) ∈ (s , x) ∷ free tˢ (rename₁ x y tˢ t)         □
    where
    lemma :
      ∀ s″ (s′≡s″ : s′ ≡ s″) → Dec-Erased (s″ ≡ s) → _ ∈ _ → _ ∈ _
    lemma s″ s′≡s″ (no [ s″≢s ]) =
      cast-Var s′≡s″ z ∈ restrict-to-sort s″ (free tˢ t)            ↝⟨ ≡⇒↝ _ $ cong (_ ∈_) $ sym $
                                                                       proj₂ (proj₂ $ erased $ proj₂ $ rename tˢ _ _ _) s″ s″≢s ⟩
      cast-Var s′≡s″ z ∈
        restrict-to-sort s″ (free tˢ (rename₁ x y tˢ t))            ↝⟨ restrict-to-sort-cong
                                                                         {xs = free tˢ (rename₁ x y tˢ t)}
                                                                         (λ _ → ∈→∈∷) _ ⟩□
      cast-Var s′≡s″ z ∈
        restrict-to-sort s″ ((s , x) ∷ free tˢ (rename₁ x y tˢ t))  □

    lemma s″ s′≡s″ (yes [ s″≡s ]) =
      cast-Var s′≡s″ z ∈ restrict-to-sort s″ (free tˢ t)              ↔⟨ sort-can-be-replaced-in-∈-restrict-to-sort (free tˢ t) ⟩

      z′ ∈ restrict-to-sort s (free tˢ t)                             ↝⟨ proj₁
                                                                           (proj₂ $ erased $ proj₂ $
                                                                            rename tˢ _
                                                                              (singleton-renaming x y
                                                                                 (restrict-to-sort _ (free tˢ t) ∖ singleton x))
                                                                              (λ _ → ∈→∈∷))
                                                                            _ ⟩

      z′ ∈ x ∷ restrict-to-sort s (free tˢ (rename₁ x y tˢ t))        ↔⟨ inverse ∈∷≃ F.∘
                                                                         (inverse ≡→,≡,≃ ∥⊎∥-cong ∈restrict-to-sort≃) F.∘
                                                                         ∈∷≃ ⟩

      (s , z′) ∈ (s , x) ∷ free tˢ (rename₁ x y tˢ t)                 ↔⟨ inverse ∈restrict-to-sort≃ ⟩

      z′ ∈ restrict-to-sort s ((s , x) ∷ free tˢ (rename₁ x y tˢ t))  ↔⟨ inverse $
                                                                         sort-can-be-replaced-in-∈-restrict-to-sort
                                                                           ((s , x) ∷ free tˢ (rename₁ x y tˢ t)) ⟩□
      cast-Var s′≡s″ z ∈
        restrict-to-sort s″ ((s , x) ∷ free tˢ (rename₁ x y tˢ t))    □
      where
      z′ = cast-Var s″≡s $ cast-Var s′≡s″ z

  ----------------------------------------------------------------------
  -- Well-formed terms

  -- Predicates for well-formed variables, terms and arguments.

  mutual

    Wf : Vars → (tˢ : Skeleton k s) → Data tˢ → Type ℓ
    Wf {k = var}  = λ { xs var → Wf-var xs }
    Wf {k = tm}   = Wf-tm
    Wf {k = args} = Wf-args
    Wf {k = arg}  = Wf-arg

    private

      Wf-var : ∀ {s} → Vars → Var s → Type ℓ
      Wf-var xs x = (_ , x) ∈ xs

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
        ∀ y → (_ , y) ∉ xs →
        Wf-arg ((_ , y) ∷ xs) aˢ (rename₁ x y aˢ a)

  -- Well-formed terms.

  Term[_] : (k : Term-kind) → @0 Vars → @0 Sort-kind k → Type ℓ
  Term[ k ] xs s =
    ∃ λ (tˢ : Skeleton k s) →
    ∃ λ (t : Data tˢ) →
      Erased (Wf xs tˢ t)

  Term : @0 Vars → @0 Sort → Type ℓ
  Term = Term[ tm ]

  pattern var-wf x wf        = var , x , [ wf ]
  pattern op-wf o asˢ as wfs = op o asˢ , as , [ wfs ]

  pattern nil-wfs =
    Argsˢ.nil , lift tt , [ lift tt ]
  pattern cons-wfs aˢ asˢ a as wf wfs =
    Argsˢ.cons aˢ asˢ , (a , as) , [ wf , wfs ]

  pattern nil-wf tˢ t wf    = Argˢ.nil tˢ , t , [ wf ]
  pattern cons-wf aˢ x a wf = Argˢ.cons aˢ , (x , a) , [ wf ]

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
  -- Alternative definitions of Tm/Args/Arg/Data and Term[_]

  -- The following four definitions are indexed by /erased/ skeletons.

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

  Data′ : @0 Skeleton k s → Type ℓ
  Data′ {k = var} {s} = λ _ → Var s
  Data′ {k = tm}      = Tm′
  Data′ {k = args}    = Args′
  Data′ {k = arg}     = Arg′

  -- Lemmas used by Tm′≃Tm, Args′≃Args and Arg′≃Arg below.

  private

    module ′≃ where

      mutual

        to-Tm : {tˢ : Tmˢ s} → Tm′ tˢ → Tm tˢ
        to-Tm {tˢ = var}    (var x) = x
        to-Tm {tˢ = op _ _} (op as) = to-Args as

        to-Args : {asˢ : Argsˢ vs} → Args′ asˢ → Args asˢ
        to-Args {asˢ = nil}      nil         = _
        to-Args {asˢ = cons _ _} (cons a as) = to-Arg a , to-Args as

        to-Arg : {aˢ : Argˢ v} → Arg′ aˢ → Arg aˢ
        to-Arg {aˢ = nil _}  (nil t)    = to-Tm t
        to-Arg {aˢ = cons _} (cons x a) = x , to-Arg a

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
        from-to-Args {asˢ = nil}      nil         = refl _
        from-to-Args {asˢ = cons _ _} (cons a as) =
          cong₂ cons (from-to-Arg a) (from-to-Args as)

        from-to-Arg :
          {aˢ : Argˢ v} (a : Arg′ aˢ) → from-Arg aˢ (to-Arg a) ≡ a
        from-to-Arg {aˢ = nil _}  (nil t)    = cong nil (from-to-Tm _ t)
        from-to-Arg {aˢ = cons _} (cons x a) =
          cong (cons x) (from-to-Arg a)

  -- The alternative definitions of Tm, Args, Arg and Data are
  -- pointwise equivalent to the original ones.

  Tm′≃Tm : {tˢ : Tmˢ s} → Tm′ tˢ ≃ Tm tˢ
  Tm′≃Tm {tˢ} = Eq.↔→≃
    to-Tm
    (from-Tm _)
    (to-from-Tm tˢ)
    (from-to-Tm _)
    where
    open ′≃

  Args′≃Args : {asˢ : Argsˢ vs} → Args′ asˢ ≃ Args asˢ
  Args′≃Args {asˢ} = Eq.↔→≃
    to-Args
    (from-Args _)
    (to-from-Args asˢ)
    from-to-Args
    where
    open ′≃

  Arg′≃Arg : {aˢ : Argˢ v} → Arg′ aˢ ≃ Arg aˢ
  Arg′≃Arg {aˢ} = Eq.↔→≃
    to-Arg
    (from-Arg _)
    (to-from-Arg aˢ)
    from-to-Arg
    where
    open ′≃

  Data′≃Data : ∀ k {@0 s} {tˢ : Skeleton k s} → Data′ tˢ ≃ Data tˢ
  Data′≃Data var  = F.id
  Data′≃Data tm   = Tm′≃Tm
  Data′≃Data args = Args′≃Args
  Data′≃Data arg  = Arg′≃Arg

  -- The following alternative definition of Term[_] uses Data′
  -- instead of Data.

  Term[_]′ :
    (k : Term-kind) →
    @0 Vars → @0 Sort-kind k → Type ℓ
  Term[ k ]′ xs s =
    ∃ λ (tˢ : Skeleton k s) →
    ∃ λ (t : Data′ tˢ) →
      Erased (Wf xs tˢ (_≃_.to (Data′≃Data k) t))

  -- This alternative definition is also pointwise equivalent to the
  -- original one.

  Term′≃Term : Term[ k ]′ xs s ≃ Term[ k ] xs s
  Term′≃Term {k} = ∃-cong λ _ → Σ-cong (Data′≃Data k) λ _ → F.id

  ----------------------------------------------------------------------
  -- Decision procedures for equality

  -- Erased equality is decidable for Term-kind.
  --
  -- This decision procedure is not optimised.

  infix 4 _≟Term-kind_

  _≟Term-kind_ : Decidable-erased-equality Term-kind
  _≟Term-kind_ =                         $⟨ Fin._≟_ ⟩
    Decidable-equality (Fin 4)           ↝⟨ Decidable-equality→Decidable-erased-equality ⟩
    Decidable-erased-equality (Fin 4)    ↝⟨ Decidable-erased-equality-map (_≃_.surjection $ inverse Term-kind≃Fin-4) ⟩□
    Decidable-erased-equality Term-kind  □

  -- Erased equality is decidable for Skeleton k s.

  infix 4 _≟ˢ_ _≟Tmˢ_ _≟Argsˢ_ _≟Argˢ_

  mutual

    _≟ˢ_ : Decidable-erased-equality (Skeleton k s)
    _≟ˢ_ {k = var}  = _≟Varˢ_
    _≟ˢ_ {k = tm}   = _≟Tmˢ_
    _≟ˢ_ {k = args} = _≟Argsˢ_
    _≟ˢ_ {k = arg}  = _≟Argˢ_

    private

      _≟Varˢ_ : Decidable-erased-equality (Varˢ s)
      var ≟Varˢ var = yes [ refl _ ]

      _≟Tmˢ_ : Decidable-erased-equality (Tmˢ s)
      var ≟Tmˢ var = yes [ refl _ ]

      var ≟Tmˢ op _ _ =            $⟨ no [ (λ ()) ] ⟩
        Dec-Erased ⊥               ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘
                                                      from-isomorphism (inverse Bijection.≡↔⊎)) ⟩□
        Dec-Erased (var ≡ op _ _)  □

      op _ _ ≟Tmˢ var =            $⟨ no [ (λ ()) ] ⟩
        Dec-Erased ⊥               ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘
                                                      from-isomorphism (inverse Bijection.≡↔⊎)) ⟩□
        Dec-Erased (op _ _ ≡ var)  □

      op o₁ as₁ ≟Tmˢ op o₂ as₂ =              $⟨ decidable-erased⇒dec-erased⇒Σ-dec-erased _≟O_ (λ _ → _ ≟Argsˢ as₂) ⟩
        Dec-Erased ((o₁ , as₁) ≡ (o₂ , as₂))  ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Tmˢ≃) F.∘
                                                                 from-isomorphism Bijection.≡↔inj₂≡inj₂) ⟩□
        Dec-Erased (op o₁ as₁ ≡ op o₂ as₂)    □

      _≟Argsˢ_ : Decidable-erased-equality (Argsˢ vs)
      nil ≟Argsˢ nil =                        $⟨ yes [ refl _ ] ⟩
        Dec-Erased ([ refl _ ] ≡ [ refl _ ])  ↝⟨ Dec-Erased-map (from-isomorphism (Eq.≃-≡ Argsˢ≃) F.∘
                                                                 from-isomorphism Bijection.≡↔inj₁≡inj₁) ⟩□
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
                                                                     from-isomorphism (Eq.≃-≡ Argsˢ≃) F.∘
                                                                     from-isomorphism Bijection.≡↔inj₂≡inj₂) ⟩□
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

  -- Erased equality is decidable for Data tˢ.

  mutual

    equal?-Data :
      (tˢ : Skeleton k s) → Decidable-erased-equality (Data tˢ)
    equal?-Data {k = var}  = λ _ → _≟V_
    equal?-Data {k = tm}   = equal?-Tm
    equal?-Data {k = args} = equal?-Args
    equal?-Data {k = arg}  = equal?-Arg

    private

      equal?-Tm : (tˢ : Tmˢ s) → Decidable-erased-equality (Tm tˢ)
      equal?-Tm var        x₁  x₂  = x₁ ≟V x₂
      equal?-Tm (op o asˢ) as₁ as₂ = equal?-Args asˢ as₁ as₂

      equal?-Args :
        (asˢ : Argsˢ vs) → Decidable-erased-equality (Args asˢ)
      equal?-Args nil           _          _          = yes [ refl _ ]
      equal?-Args (cons aˢ asˢ) (a₁ , as₁) (a₂ , as₂) =
        dec-erased⇒dec-erased⇒×-dec-erased
          (equal?-Arg aˢ a₁ a₂)
          (equal?-Args asˢ as₁ as₂)

      equal?-Arg : (aˢ : Argˢ v) → Decidable-erased-equality (Arg aˢ)
      equal?-Arg (nil tˢ)  t₁        t₂        = equal?-Tm tˢ t₁ t₂
      equal?-Arg (cons aˢ) (x₁ , a₁) (x₂ , a₂) =
        dec-erased⇒dec-erased⇒×-dec-erased
          (x₁ ≟V x₂)
          (equal?-Arg aˢ a₁ a₂)

  -- Erased equality is decidable for Data′ tˢ.
  --
  -- (Presumably it is possible to prove this without converting to
  -- Data, and in that case the sort and skeleton arguments can
  -- perhaps be erased.)

  equal?-Data′ :
    ∀ k {s} {tˢ : Skeleton k s} →
    Decidable-erased-equality (Data′ tˢ)
  equal?-Data′ k {tˢ} t₁ t₂ =                                         $⟨ equal?-Data tˢ _ _ ⟩
    Dec-Erased (_≃_.to (Data′≃Data k) t₁ ≡ _≃_.to (Data′≃Data k) t₂)  ↝⟨ Dec-Erased-map (from-equivalence (Eq.≃-≡ (Data′≃Data k))) ⟩□
    Dec-Erased (t₁ ≡ t₂)                                              □

  -- The Wf predicate is propositional.

  mutual

    @0 Wf-propositional :
      ∀ {s} (tˢ : Skeleton k s) {t : Data tˢ} →
      Is-proposition (Wf xs tˢ t)
    Wf-propositional {k = var}  var = ∈-propositional
    Wf-propositional {k = tm}       = Wf-tm-propositional
    Wf-propositional {k = args}     = Wf-args-propositional
    Wf-propositional {k = arg}      = Wf-arg-propositional

    private

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

  -- Erased equality is decidable for Term[_]′.

  infix 4 _≟Term′_

  _≟Term′_ : ∀ {s} → Decidable-erased-equality (Term[ k ]′ xs s)
  _≟Term′_ {k} =
    decidable-erased⇒decidable-erased⇒Σ-decidable-erased
      _≟ˢ_
      λ {tˢ} →
        decidable-erased⇒decidable-erased⇒Σ-decidable-erased
          (equal?-Data′ k)
          λ _ _ → yes [ []-cong [ Wf-propositional tˢ _ _ ] ]

  -- Erased equality is decidable for Term[_].
  --
  -- TODO: Is it possible to prove this without converting to
  -- Term[_]′?

  infix 4 _≟Term_

  _≟Term_ : ∀ {s} → Decidable-erased-equality (Term[ k ] xs s)
  _≟Term_ {k} {xs} {s} =                         $⟨ _≟Term′_ ⟩
    Decidable-erased-equality (Term[ k ]′ xs s)  ↝⟨ Decidable-erased-equality-map (_≃_.surjection Term′≃Term) ⟩□
    Decidable-erased-equality (Term[ k ] xs s)   □

  -- Skeleton, Data, Data′, Term[_] and Term[_]′ are sets (pointwise,
  -- in erased contexts).

  @0 Skeleton-set : Is-set (Skeleton k s)
  Skeleton-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟ˢ_

  @0 Data-set : (tˢ : Skeleton k s) → Is-set (Data tˢ)
  Data-set tˢ =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ (equal?-Data tˢ)

  @0 Data′-set : ∀ k {s} {tˢ : Skeleton k s} → Is-set (Data′ tˢ)
  Data′-set k =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ (equal?-Data′ k)

  @0 Term-set : Is-set (Term[ k ] xs s)
  Term-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Term_

  @0 Term′-set : Is-set (Term[ k ]′ xs s)
  Term′-set =
    decidable⇒set $
    Decidable-erased-equality≃Decidable-equality _ _≟Term′_

  ----------------------------------------------------------------------
  -- A lemma

  -- Changing the well-formedness proof does not actually change
  -- anything.

  @0 Wf-proof-irrelevant :
    ∀ {tˢ : Skeleton k s} {t : Data tˢ} {wf₁ wf₂} →
    _≡_ {A = Term[ k ] xs s} (tˢ , t , [ wf₁ ]) (tˢ , t , [ wf₂ ])
  Wf-proof-irrelevant {tˢ} =
    cong (λ wf → tˢ , _ , [ wf ]) (Wf-propositional tˢ _ _)

  ----------------------------------------------------------------------
  -- An elimination principle for well-formed terms ("structural
  -- induction modulo fresh renaming")

  -- The eliminator's arguments.

  record Wf-elim
           (P : ∀ k {@0 xs s} → Term[ k ] xs s → Type p) :
           Type (ℓ ⊔ p) where
    no-eta-equality
    field
      varʳ : ∀ {s} (x : Var s) (@0 x∈ : (_ , x) ∈ xs) →
             P var (var-wf x x∈)

      varʳ′ : ∀ {s} (x : Var s) (@0 wf : Wf xs Varˢ.var x) →
              P var (var-wf x wf) →
              P tm (var-wf x wf)
      opʳ   : ∀ (o : Op s) asˢ as (@0 wfs : Wf xs asˢ as) →
              P args (asˢ , as , [ wfs ]) →
              P tm (op-wf o asˢ as wfs)

      nilʳ  : P args {xs = xs} nil-wfs
      consʳ : ∀ aˢ a asˢ as
              (@0 wf : Wf {s = v} xs aˢ a)
              (@0 wfs : Wf {s = vs} xs asˢ as) →
              P arg (aˢ , a , [ wf ]) →
              P args (asˢ , as , [ wfs ]) →
              P args (cons-wfs aˢ asˢ a as wf wfs)

      nilʳ′  : ∀ tˢ t (@0 wf : Wf {s = s} xs tˢ t) →
               P tm (tˢ , t , [ wf ]) →
               P arg (nil-wf tˢ t wf)
      consʳ′ : ∀ {@0 xs : Vars} {s}
               (aˢ : Argˢ v) (x : Var s) a (@0 wf) →
               (∀ y (@0 y∉ : (_ , y) ∉ xs) →
                P arg (aˢ , rename₁ x y aˢ a , [ wf y y∉ ])) →
               P arg (cons-wf aˢ x a wf)

  -- The eliminator.

  -- TODO: Can one implement a more efficient eliminator that does not
  -- use rename₁, and that merges all the renamings into one?

  module _
    {P : ∀ k {@0 xs s} → Term[ k ] xs s → Type p}
    (e : Wf-elim P)
    where

    open Wf-elim

    mutual

      wf-elim : ∀ {xs} (t : Term[ k ] xs s) → P k t
      wf-elim {k = var} (var , x , [ wf ]) =
        wf-elim-Var x wf
      wf-elim {k = tm} (tˢ , t , [ wf ]) =
        wf-elim-Term tˢ t wf
      wf-elim {k = args} (asˢ , as , [ wfs ]) =
        wf-elim-Arguments asˢ as wfs
      wf-elim {k = arg} (aˢ , a , [ wf ]) =
        wf-elim-Argument aˢ a wf

      private

        wf-elim-Var :
          ∀ {xs s} (x : Var s) (@0 wf : Wf xs Varˢ.var x) →
          P var (var , x , [ wf ])
        wf-elim-Var x wf = e .varʳ x wf

        wf-elim-Term :
          ∀ {xs} (tˢ : Tmˢ s) (t : Tm tˢ) (@0 wf : Wf-tm xs tˢ t) →
          P tm (tˢ , t , [ wf ])
        wf-elim-Term var x wf =
          e .varʳ′ x wf (wf-elim-Var x wf)
        wf-elim-Term (op o asˢ) as wfs =
          e .opʳ o asˢ as wfs (wf-elim-Arguments asˢ as wfs)

        wf-elim-Arguments :
          ∀ {xs} (asˢ : Argsˢ vs) (as : Args asˢ)
          (@0 wfs : Wf-args xs asˢ as) →
          P args (asˢ , as , [ wfs ])
        wf-elim-Arguments nil _ _ = e .nilʳ

        wf-elim-Arguments (cons aˢ asˢ) (a , as) (wf , wfs) =
          e .consʳ aˢ a asˢ as wf wfs
            (wf-elim-Argument aˢ a wf)
            (wf-elim-Arguments asˢ as wfs)

        wf-elim-Argument :
          ∀ {xs} (aˢ : Argˢ v) (a : Arg aˢ) (@0 wf : Wf-arg xs aˢ a) →
          P arg (aˢ , a , [ wf ])
        wf-elim-Argument (nil tˢ) t wf =
          e .nilʳ′ tˢ t wf (wf-elim-Term tˢ t wf)

        wf-elim-Argument (cons aˢ) (x , a) wf =
          e .consʳ′ aˢ x a wf λ y y∉ →
            wf-elim-Argument aˢ (rename₁ x y aˢ a) (wf y y∉)

  ----------------------------------------------------------------------
  -- Free variables

  -- An alternative definition of what it means for a variable to be
  -- free in a term.
  --
  -- This definition is based on Harper's.

  module _ {s} (x : Var s) where

    private

      Free-in-var :
        ∀ {s′} → Var s′ →
        ∃ λ (A : Type ℓ) → Erased (Is-proposition A)
      Free-in-var y =
          _≡_ {A = ∃Var} (_ , x) (_ , y)
        , [ ∃Var-set ]

      mutual

        Free-in-term :
          ∀ {xs} (tˢ : Tmˢ s′) t →
          @0 Wf ((_ , x) ∷ xs) tˢ t →
          ∃ λ (A : Type ℓ) → Erased (Is-proposition A)
        Free-in-term var y _ = Free-in-var y

        Free-in-term (op o asˢ) as wf =
          Free-in-arguments asˢ as wf

        Free-in-arguments :
          ∀ {xs} (asˢ : Argsˢ vs) as →
          @0 Wf ((_ , x) ∷ xs) asˢ as →
          ∃ λ (A : Type ℓ) → Erased (Is-proposition A)
        Free-in-arguments nil _ _ = ⊥ , [ ⊥-propositional ]

        Free-in-arguments (cons aˢ asˢ) (a , as) (wf , wfs) =
            (proj₁ (Free-in-argument aˢ a wf) ∥⊎∥
             proj₁ (Free-in-arguments asˢ as wfs))
          , [ ∥⊎∥-propositional ]

        Free-in-argument :
          ∀ {xs} (aˢ : Argˢ v) a →
          @0 Wf ((_ , x) ∷ xs) aˢ a →
          ∃ λ (A : Type ℓ) → Erased (Is-proposition A)
        Free-in-argument (nil tˢ) t wf = Free-in-term tˢ t wf

        Free-in-argument {xs} (cons aˢ) (y , a) wf =
          Π _ λ z → Π (Erased ((_ , z) ∉ (_ , x) ∷ xs)) λ ([ z∉ ]) →
          Free-in-argument
            aˢ
            (rename₁ y z aˢ a)
            (subst (λ xs′ → Wf xs′ aˢ (rename₁ y z aˢ a))
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

    -- A predicate that holds if x is free in the term.

    Free-in : ∀ {xs} → Term[ k ] ((_ , x) ∷ xs) s′ → Type ℓ
    Free-in {k = var} (var , y , [ wf ]) =
      proj₁ (Free-in-var y)
    Free-in {k = tm} (tˢ , t , [ wf ]) =
      proj₁ (Free-in-term tˢ t wf)
    Free-in {k = args} (asˢ , as , [ wfs ]) =
      proj₁ (Free-in-arguments asˢ as wfs)
    Free-in {k = arg} (aˢ , a , [ wf ]) =
      proj₁ (Free-in-argument aˢ a wf)

    abstract

      -- The alternative definition of what it means for a variable to
      -- be free is propositional (in erased contexts).

      @0 Free-in-propositional :
        (t : Term[ k ] ((_ , x) ∷ xs) s′) →
        Is-proposition (Free-in t)
      Free-in-propositional {k = var} (var , y , [ wf ]) =
        erased (proj₂ (Free-in-var y))
      Free-in-propositional {k = tm} (tˢ , t , [ wf ]) =
        erased (proj₂ (Free-in-term tˢ t wf))
      Free-in-propositional {k = args} (asˢ , as , [ wfs ]) =
        erased (proj₂ (Free-in-arguments asˢ as wfs))
      Free-in-propositional {k = arg} (aˢ , a , [ wf ]) =
        erased (proj₂ (Free-in-argument aˢ a wf))

  abstract

    mutual

      -- Variables that are free according to the alternative
      -- definition are in the set of free variables (in erased
      -- contexts).

      @0 Free-free :
        ∀ (tˢ : Skeleton k s′) {t} (wf : Wf ((s , x) ∷ xs) tˢ t) →
        Free-in x (tˢ , t , [ wf ]) → (s , x) ∈ free tˢ t
      Free-free {k = var}  = λ yˢ wf → Free-free-Var yˢ wf
      Free-free {k = tm}   = Free-free-Tm
      Free-free {k = args} = Free-free-Args
      Free-free {k = arg}  = Free-free-Arg

      private

        @0 Free-free-Var :
          ∀ {s} {x : Var s} (yˢ : Varˢ s′) {y : Var s′}
          (@0 wf : Wf ((_ , x) ∷ xs) yˢ y) →
          Free-in x (yˢ , y , [ wf ]) → (_ , x) ∈ free yˢ y
        Free-free-Var var _ = ≡→∈singleton

        @0 Free-free-Tm :
          ∀ (tˢ : Tmˢ s′) {t} (wf : Wf ((_ , x) ∷ xs) tˢ t) →
          Free-in x (tˢ , t , [ wf ]) → (_ , x) ∈ free tˢ t
        Free-free-Tm var        wf  = Free-free-Var var wf
        Free-free-Tm (op o asˢ) wfs = Free-free-Args asˢ wfs

        @0 Free-free-Args :
          ∀ (asˢ : Argsˢ vs) {as} (wfs : Wf ((_ , x) ∷ xs) asˢ as) →
          Free-in x (asˢ , as , [ wfs ]) →
          (_ , x) ∈ free asˢ as
        Free-free-Args {x} (cons aˢ asˢ) {as = a , as} (wf , wfs) =
          Free-in x (aˢ , a , [ wf ]) ∥⊎∥ Free-in x (asˢ , as , [ wfs ])  ↝⟨ Free-free-Arg aˢ wf ∥⊎∥-cong Free-free-Args asˢ wfs ⟩
          (_ , x) ∈ free aˢ a ∥⊎∥ (_ , x) ∈ free asˢ as                   ↔⟨ inverse ∈∪≃ ⟩□
          (_ , x) ∈ free aˢ a ∪ free asˢ as                               □

        @0 Free-free-Arg :
          ∀ (aˢ : Argˢ v) {a} (wf : Wf ((_ , x) ∷ xs) aˢ a) →
          Free-in x (aˢ , a , [ wf ]) → (_ , x) ∈ free aˢ a
        Free-free-Arg (nil tˢ) = Free-free-Tm tˢ

        Free-free-Arg {x} {xs} (cons {s} aˢ) {a = y , a} wf =
          let xxs              = (_ , x) ∷ xs
              x₁ ,         x₁∉ = fresh-not-erased xxs
              x₂ , x₂≢x₁ , x₂∉ =                                       $⟨ fresh-not-erased ((_ , x₁) ∷ xxs) ⟩
                (∃ λ x₂ → (_ , x₂) ∉ (_ , x₁) ∷ xxs)                   ↝⟨ (∃-cong λ _ → →-cong₁ ext ∈∷≃) ⟩
                (∃ λ x₂ → ¬ ((_ , x₂) ≡ (_ , x₁) ∥⊎∥ (_ , x₂) ∈ xxs))  ↝⟨ (∃-cong λ _ → Π∥⊎∥↔Π×Π λ _ → ⊥-propositional) ⟩□
                (∃ λ x₂ → (_ , x₂) ≢ (_ , x₁) × (_ , x₂) ∉ xxs)        □
          in
          (∀ z (z∉ : Erased ((_ , z) ∉ (_ , x) ∷ xs)) →
           Free-in x
             ( aˢ
             , rename₁ y z aˢ a
             , [ subst (λ xs → Wf xs aˢ (rename₁ y z aˢ a))
                       swap
                       (wf z (erased z∉)) ]
             ))                                                   ↝⟨ (λ hyp z z∉ → Free-free-Arg
                                                                                     aˢ
                                                                                     (subst (λ xs → Wf xs aˢ (rename₁ y z aˢ a))
                                                                                            swap
                                                                                            (wf z z∉))
                                                                                     (hyp z [ z∉ ])) ⟩
          (∀ z → (_ , z) ∉ (_ , x) ∷ xs →
           (_ , x) ∈ free aˢ (rename₁ y z aˢ a))                  ↝⟨ (λ hyp z z∉ → free-rename₁⊆ aˢ _ (hyp z z∉)) ⦂ (_ → _) ⟩

          (∀ z → (_ , z) ∉ (_ , x) ∷ xs →
           (_ , x) ∈ (_ , z) ∷ fs′)                               ↝⟨ (λ hyp → hyp x₁ x₁∉ , hyp x₂ x₂∉) ⟩

          (_ , x) ∈ (_ , x₁) ∷ fs′ ×
          (_ , x) ∈ (_ , x₂) ∷ fs′                                ↔⟨ ∈∷≃ ×-cong ∈∷≃ ⟩

          ((_ , x) ≡ (_ , x₁) ∥⊎∥ (_ , x) ∈ fs′) ×
          ((_ , x) ≡ (_ , x₂) ∥⊎∥ (_ , x) ∈ fs′)                  ↔⟨ (Σ-∥⊎∥-distrib-right (λ _ → ∃Var-set) ∥⊎∥-cong F.id) F.∘
                                                                     Σ-∥⊎∥-distrib-left ∥⊎∥-propositional ⟩
          ((_ , x) ≡ (_ , x₁) × (_ , x) ≡ (_ , x₂) ∥⊎∥
           (_ , x) ∈ fs′ × (_ , x) ≡ (_ , x₂)) ∥⊎∥
          ((_ , x) ≡ (_ , x₁) ∥⊎∥ (_ , x) ∈ fs′) × (_ , x) ∈ fs′  ↝⟨ ((λ (y≡x₁ , y≡x₂) → x₂≢x₁ (trans (sym y≡x₂) y≡x₁)) ∥⊎∥-cong proj₁)
                                                                       ∥⊎∥-cong
                                                                     proj₂ ⟩

          (⊥ ∥⊎∥ (_ , x) ∈ fs′) ∥⊎∥ (_ , x) ∈ fs′                 ↔⟨ ∥⊎∥-idempotent ∈-propositional F.∘
                                                                     (∥⊎∥-left-identity ∈-propositional ∥⊎∥-cong F.id) ⟩□
          (_ , x) ∈ fs′                                           □
          where
          fs′ : Vars
          fs′ = del (_ , y) (free aˢ a)

    mutual

      -- Every member of the set of free variables is free according
      -- to the alternative definition (in erased contexts).

      @0 free-Free :
        ∀ (tˢ : Skeleton k s) {t} (wf : Wf ((s′ , x) ∷ xs) tˢ t) →
        (s′ , x) ∈ free tˢ t → Free-in x (tˢ , t , [ wf ])
      free-Free {k = var}  = free-Free-Var
      free-Free {k = tm}   = free-Free-Tm
      free-Free {k = args} = free-Free-Args
      free-Free {k = arg}  = free-Free-Arg

      private

        @0 free-Free-Var :
          ∀ (yˢ : Varˢ s) {y} (wf : Wf ((_ , x) ∷ xs) yˢ y) →
          (_ , x) ∈ free yˢ y → Free-in x (yˢ , y , [ wf ])
        free-Free-Var {x} var {y} _ =
          (_ , x) ∈ singleton (_ , y)  ↔⟨ ∈singleton≃ ⟩
          ∥ (_ , x) ≡ (_ , y) ∥        ↔⟨ ∥∥↔ ∃Var-set ⟩□
          (_ , x) ≡ (_ , y)            □

        @0 free-Free-Tm :
          ∀ (tˢ : Tmˢ s) {t} (wf : Wf-tm ((_ , x) ∷ xs) tˢ t) →
          (_ , x) ∈ free tˢ t → Free-in x (tˢ , t , [ wf ])
        free-Free-Tm var        = free-Free-Var var
        free-Free-Tm (op o asˢ) = free-Free-Args asˢ

        @0 free-Free-Args :
          ∀ (asˢ : Argsˢ vs) {as} (wf : Wf ((_ , x) ∷ xs) asˢ as) →
          (_ , x) ∈ free asˢ as → Free-in x (asˢ , as , [ wf ])
        free-Free-Args {x} (cons aˢ asˢ) {as = a , as} (wf , wfs) =
          (_ , x) ∈ free aˢ a ∪ free asˢ as                               ↔⟨ ∈∪≃ ⟩
          (_ , x) ∈ free aˢ a ∥⊎∥ (_ , x) ∈ free asˢ as                   ↝⟨ free-Free-Arg aˢ wf
                                                                               ∥⊎∥-cong
                                                                             free-Free-Args asˢ wfs ⟩□
          Free-in x (aˢ , a , [ wf ]) ∥⊎∥ Free-in x (asˢ , as , [ wfs ])  □

        @0 free-Free-Arg :
          ∀ (aˢ : Argˢ v) {a} (wf : Wf ((_ , x) ∷ xs) aˢ a) →
          (_ , x) ∈ free aˢ a → Free-in x (aˢ , a , [ wf ])
        free-Free-Arg (nil tˢ) = free-Free-Tm tˢ

        free-Free-Arg {x} {xs} (cons aˢ) {a = y , a} wf =
          (_ , x) ∈ del (_ , y) (free aˢ a)                       ↔⟨ ∈delete≃ merely-equal?-∃Var ⟩

          (_ , x) ≢ (_ , y) × (_ , x) ∈ free aˢ a                 ↝⟨ Σ-map id (λ x∈ _ → ⊆free-rename₁ aˢ _ x∈) ⟩

          (_ , x) ≢ (_ , y) ×
          (∀ z → (_ , x) ∈ (_ , y) ∷ free aˢ (rename₁ y z aˢ a))  ↔⟨ (∃-cong λ x≢y → ∀-cong ext λ z →
                                                                      drop-⊥-left-∥⊎∥ ∈-propositional x≢y F.∘
                                                                      from-equivalence ∈∷≃) ⟩
          (_ , x) ≢ (_ , y) ×
          (∀ z → (_ , x) ∈ free aˢ (rename₁ y z aˢ a))            ↝⟨ proj₂ ⟩

          (∀ z → (_ , x) ∈ free aˢ (rename₁ y z aˢ a))            ↝⟨ (λ hyp z _ → hyp z) ⟩

          (∀ z → (_ , z) ∉ (_ , x) ∷ xs →
                 (_ , x) ∈ free aˢ (rename₁ y z aˢ a))            ↝⟨ (λ x∈ z z∉ →
                                                                        free-Free-Arg aˢ
                                                                          (subst (λ xs → Wf xs aˢ (rename₁ y z aˢ a))
                                                                                 swap
                                                                                 (wf z (erased z∉)))
                                                                          (x∈ z (Stable-¬ z∉))) ⟩□
          (∀ z (z∉ : Erased ((_ , z) ∉ (_ , x) ∷ xs)) →
           Free-in x
             ( aˢ
             , rename₁ y z aˢ a
             , [ subst (λ xs → Wf xs aˢ (rename₁ y z aˢ a))
                       swap
                       (wf z (erased z∉))
               ]
             ))                                                   □

  ----------------------------------------------------------------------
  -- Lemmas related to the Wf predicate

  abstract

    -- Weakening of the Wf predicate.

    mutual

      @0 weaken-Wf :
        xs ⊆ ys → ∀ (tˢ : Skeleton k s) {t} →
        Wf xs tˢ t → Wf ys tˢ t
      weaken-Wf {k = var}  = weaken-Wf-var
      weaken-Wf {k = tm}   = weaken-Wf-tm
      weaken-Wf {k = args} = weaken-Wf-args
      weaken-Wf {k = arg}  = weaken-Wf-arg

      private

        @0 weaken-Wf-var :
          xs ⊆ ys → ∀ (xˢ : Varˢ s) {x} →
          Wf xs xˢ x → Wf ys xˢ x
        weaken-Wf-var xs⊆ys var = xs⊆ys _

        @0 weaken-Wf-tm :
          xs ⊆ ys → ∀ (tˢ : Tmˢ s) {t} →
          Wf xs tˢ t → Wf ys tˢ t
        weaken-Wf-tm xs⊆ys var        = weaken-Wf-var xs⊆ys var
        weaken-Wf-tm xs⊆ys (op o asˢ) = weaken-Wf-args xs⊆ys asˢ

        @0 weaken-Wf-args :
          xs ⊆ ys → ∀ (asˢ : Argsˢ vs) {as} →
          Wf xs asˢ as → Wf ys asˢ as
        weaken-Wf-args xs⊆ys nil           = id
        weaken-Wf-args xs⊆ys (cons aˢ asˢ) =
          Σ-map (weaken-Wf-arg xs⊆ys aˢ)
                (weaken-Wf-args xs⊆ys asˢ)

        @0 weaken-Wf-arg :
          xs ⊆ ys → ∀ (aˢ : Argˢ v) {a} →
          Wf xs aˢ a → Wf ys aˢ a
        weaken-Wf-arg xs⊆ys (nil tˢ)  = weaken-Wf-tm xs⊆ys tˢ
        weaken-Wf-arg xs⊆ys (cons aˢ) =
          λ wf y y∉ys →
            weaken-Wf-arg (∷-cong-⊆ xs⊆ys) aˢ (wf y (y∉ys ∘ xs⊆ys _))

    -- A term is well-formed for its set of free variables.

    mutual

      @0 wf-free :
        ∀ (tˢ : Skeleton k s) {t} → Wf (free tˢ t) tˢ t
      wf-free {k = var}  = wf-free-Var
      wf-free {k = tm}   = wf-free-Tm
      wf-free {k = args} = wf-free-Args
      wf-free {k = arg}  = wf-free-Arg

      private

        @0 wf-free-Var :
          ∀ (xˢ : Varˢ s) {x} → Wf (free xˢ x) xˢ x
        wf-free-Var var = ≡→∈∷ (refl _)

        @0 wf-free-Tm :
          ∀ (tˢ : Tmˢ s) {t} → Wf (free tˢ t) tˢ t
        wf-free-Tm var        = wf-free-Var var
        wf-free-Tm (op o asˢ) = wf-free-Args asˢ

        @0 wf-free-Args :
          ∀ (asˢ : Argsˢ vs) {as} → Wf (free asˢ as) asˢ as
        wf-free-Args nil           = _
        wf-free-Args (cons aˢ asˢ) =
            weaken-Wf-arg (λ _ → ∈→∈∪ˡ) aˢ (wf-free-Arg aˢ)
          , weaken-Wf-args (λ _ → ∈→∈∪ʳ (free-Arg aˢ _))
                           asˢ (wf-free-Args asˢ)

        @0 wf-free-Arg :
          ∀ (aˢ : Argˢ v) {a : Arg aˢ} → Wf (free aˢ a) aˢ a
        wf-free-Arg (nil tˢ)              = wf-free-Tm tˢ
        wf-free-Arg (cons aˢ) {a = x , a} = λ y y∉ →
                                                      $⟨ wf-free-Arg aˢ ⟩
          Wf-arg (free aˢ (rename₁ x y aˢ a))
            aˢ (rename₁ x y aˢ a)                     ↝⟨ weaken-Wf (free-rename₁⊆ aˢ) aˢ ⟩□

          Wf-arg ((_ , y) ∷ del (_ , x) (free aˢ a))
            aˢ (rename₁ x y aˢ a)                     □

    -- If a term is well-formed with respect to a set of variables xs,
    -- then xs is a superset of the term's set of free variables.

    mutual

      @0 free-⊆ :
        ∀ (tˢ : Skeleton k s) {t} → Wf xs tˢ t → free tˢ t ⊆ xs
      free-⊆ {k = var}  = free-⊆-Var
      free-⊆ {k = tm}   = free-⊆-Tm
      free-⊆ {k = args} = free-⊆-Args
      free-⊆ {k = arg}  = free-⊆-Arg

      private

        @0 free-⊆-Var :
          ∀ (xˢ : Varˢ s) {x} → Wf xs xˢ x → free xˢ x ⊆ xs
        free-⊆-Var {xs} var {x} wf y =
          y ∈ singleton (_ , x)  ↔⟨ ∈singleton≃ ⟩
          ∥ y ≡ (_ , x) ∥        ↔⟨ ∥∥↔ ∃Var-set ⟩
          y ≡ (_ , x)            ↝⟨ (λ eq → subst (_∈ xs) (sym eq) wf) ⟩□
          y ∈ xs                 □

        @0 free-⊆-Tm :
          ∀ (tˢ : Tmˢ s) {t} → Wf xs tˢ t → free tˢ t ⊆ xs
        free-⊆-Tm var        = free-⊆-Var var
        free-⊆-Tm (op o asˢ) = free-⊆-Args asˢ

        @0 free-⊆-Args :
          ∀ (asˢ : Argsˢ vs) {as} → Wf xs asˢ as → free asˢ as ⊆ xs
        free-⊆-Args      nil           _          _ = λ ()
        free-⊆-Args {xs} (cons aˢ asˢ) (wf , wfs) y =
          y ∈ free aˢ _ ∪ free asˢ _        ↔⟨ ∈∪≃ ⟩
          y ∈ free aˢ _ ∥⊎∥ y ∈ free asˢ _  ↝⟨ free-⊆-Arg aˢ wf y ∥⊎∥-cong free-⊆-Args asˢ wfs y ⟩
          y ∈ xs ∥⊎∥ y ∈ xs                 ↔⟨ ∥⊎∥-idempotent ∈-propositional ⟩□
          y ∈ xs                            □

        @0 free-⊆-Arg :
          ∀ (aˢ : Argˢ v) {a} → Wf xs aˢ a → free aˢ a ⊆ xs
        free-⊆-Arg (nil tˢ) = free-⊆-Tm tˢ

        free-⊆-Arg {xs} (cons {s} aˢ) {a = x , a} wf y =
          y ∈ del (_ , x) (free aˢ a)  ↔⟨ ∈delete≃ merely-equal?-∃Var ⟩
          y ≢ (_ , x) × y ∈ free aˢ a  ↝⟨ uncurry lemma ⟩□
          y ∈ xs                       □
          where
          lemma : y ≢ (_ , x) → y ∈ free aˢ a → y ∈ xs
          lemma y≢x =
            let x₁ ,         x₁∉ = fresh-not-erased xs
                x₂ , x₂≢x₁ , x₂∉ =                                $⟨ fresh-not-erased ((_ , x₁) ∷ xs) ⟩
                  (∃ λ x₂ → (_ , x₂) ∉ (_ , x₁) ∷ xs)             ↝⟨ (∃-cong λ _ → →-cong₁ ext ∈∷≃) ⟩
                  (∃ λ x₂ →
                     ¬ ((_ , x₂) ≡ (_ , x₁) ∥⊎∥ (_ , x₂) ∈ xs))   ↝⟨ (∃-cong λ _ → Π∥⊎∥↔Π×Π λ _ → ⊥-propositional) ⟩□
                  (∃ λ x₂ → (_ , x₂) ≢ (_ , x₁) × (_ , x₂) ∉ xs)  □
            in
            y ∈ free aˢ a                                                ↝⟨ (λ y∈ _ → ⊆free-rename₁ aˢ _ y∈) ⟩

            (∀ z → y ∈ (_ , x) ∷ free aˢ (rename₁ x z aˢ a))             ↝⟨ (∀-cong _ λ _ → to-implication (∈≢∷≃ y≢x)) ⟩

            (∀ z → y ∈ free aˢ (rename₁ x z aˢ a))                       ↝⟨ (λ hyp →
                                                                                 free-⊆-Arg aˢ (wf x₁ x₁∉) y (hyp x₁)
                                                                               , free-⊆-Arg aˢ (wf x₂ x₂∉) y (hyp x₂)) ⟩

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

    -- Strengthening of the Wf predicate.

    @0 strengthen-Wf :
      ∀ (tˢ : Skeleton k s) {t} →
      (_ , x) ∉ free tˢ t →
      Wf ((_ , x) ∷ xs) tˢ t → Wf xs tˢ t
    strengthen-Wf {x} {xs} tˢ {t} x∉ =
      Wf ((_ , x) ∷ xs) tˢ t                ↝⟨ free-⊆ tˢ ⟩
      free tˢ t ⊆ (_ , x) ∷ xs              ↝⟨ ∉→⊆∷→⊆ x∉ ⟩
      free tˢ t ⊆ xs                        ↝⟨ _, wf-free tˢ ⟩
      free tˢ t ⊆ xs × Wf (free tˢ t) tˢ t  ↝⟨ (λ (sub , wf) → weaken-Wf sub tˢ wf) ⟩□
      Wf xs tˢ t                            □
      where
      ∉→⊆∷→⊆ :
        {x : ∃Var} {xs ys : Vars} →
        x ∉ xs → xs ⊆ x ∷ ys → xs ⊆ ys
      ∉→⊆∷→⊆ {x} {xs} {ys} x∉ xs⊆x∷ys z =
        z ∈ xs              ↝⟨ (λ z∈ → x∉ ∘ flip (subst (_∈ _)) z∈ , z∈) ⟩
        z ≢ x × z ∈ xs      ↝⟨ Σ-map id (xs⊆x∷ys _) ⟩
        z ≢ x × z ∈ x ∷ ys  ↔⟨ ∃-cong ∈≢∷≃ ⟩
        z ≢ x × z ∈ ys      ↝⟨ proj₂ ⟩□
        z ∈ ys              □

    -- Renaming preserves well-formedness.

    @0 rename₁-Wf :
      ∀ (tˢ : Skeleton k s) {t} →
      Wf ((_ , x) ∷ xs) tˢ t →
      Wf ((_ , y) ∷ xs) tˢ (rename₁ x y tˢ t)
    rename₁-Wf {x} {xs} {y} tˢ {t} wf =
                                                             $⟨ wf-free tˢ ⟩
      Wf (free tˢ (rename₁ x y tˢ t)) tˢ (rename₁ x y tˢ t)  ↝⟨ weaken-Wf
                                                                  (⊆∷delete→⊆∷→⊆∷
                                                                     (free-rename₁⊆ tˢ)
                                                                     (free-⊆ tˢ wf))
                                                                  tˢ ⟩□
      Wf ((_ , y) ∷ xs)               tˢ (rename₁ x y tˢ t)  □
      where
      ⊆∷delete→⊆∷→⊆∷ :
        ∀ {x y : ∃Var} {xs ys zs} →
        xs ⊆ x ∷ del y ys →
        ys ⊆ y ∷ zs →
        xs ⊆ x ∷ zs
      ⊆∷delete→⊆∷→⊆∷ {x} {y} {xs} {ys} {zs} xs⊆ ys⊆ z =
        z ∈ xs                        ↝⟨ xs⊆ z ⟩
        z ∈ x ∷ del y ys              ↔⟨ (F.id ∥⊎∥-cong ∈delete≃ merely-equal?-∃Var) F.∘ ∈∷≃ ⟩
        z ≡ x ∥⊎∥ z ≢ y × z ∈ ys      ↝⟨ id ∥⊎∥-cong id ×-cong ys⊆ z ⟩
        z ≡ x ∥⊎∥ z ≢ y × z ∈ y ∷ zs  ↔⟨ (F.id ∥⊎∥-cong ∃-cong λ z≢y → ∈≢∷≃ z≢y) ⟩
        z ≡ x ∥⊎∥ z ≢ y × z ∈ zs      ↝⟨ id ∥⊎∥-cong proj₂ ⟩
        z ≡ x ∥⊎∥ z ∈ zs              ↔⟨ inverse ∈∷≃ ⟩□
        z ∈ x ∷ zs                    □

    -- If one renames with a fresh variable, and the renamed thing is
    -- well-formed (with respect to a certain set of variables), then
    -- the original thing is also well-formed (with respect to a
    -- certain set of variables).

    @0 renamee-Wf :
      ∀ (tˢ : Skeleton k s) {t} →
      (_ , y) ∉ free tˢ t →
      Wf ((_ , y) ∷ xs) tˢ (rename₁ x y tˢ t) →
      Wf ((_ , x) ∷ xs) tˢ t
    renamee-Wf {y} {xs} {x} tˢ {t} y∉a =
      Wf ((_ , y) ∷ xs) tˢ (rename₁ x y tˢ t)    ↝⟨ free-⊆ tˢ ⟩
      free tˢ (rename₁ x y tˢ t) ⊆ (_ , y) ∷ xs  ↝⟨ ∉→⊆∷∷→⊆∷→⊆∷ y∉a (⊆free-rename₁ tˢ) ⟩
      free tˢ t ⊆ (_ , x) ∷ xs                   ↝⟨ (λ wf → weaken-Wf wf tˢ (wf-free tˢ)) ⟩□
      Wf ((_ , x) ∷ xs) tˢ t                     □
      where
      ∉→⊆∷∷→⊆∷→⊆∷ :
        ∀ {x y : ∃Var} {xs ys zs} →
        y ∉ xs →
        xs ⊆ x ∷ ys →
        ys ⊆ y ∷ zs →
        xs ⊆ x ∷ zs
      ∉→⊆∷∷→⊆∷→⊆∷ {x} {y} {xs} {ys} {zs} y∉xs xs⊆x∷y∷ys ys⊆y∷zs = λ z →
        z ∈ xs                                ↝⟨ (λ z∈xs → (λ z≡y → y∉xs (subst (_∈ _) z≡y z∈xs))
                                                         , xs⊆x∷y∷ys z z∈xs) ⟩

        z ≢ y × z ∈ x ∷ ys                    ↔⟨ (∃-cong λ _ → ∈∷≃) ⟩

        z ≢ y × (z ≡ x ∥⊎∥ z ∈ ys)            ↝⟨ (∃-cong λ _ → F.id ∥⊎∥-cong ys⊆y∷zs z) ⟩

        z ≢ y × (z ≡ x ∥⊎∥ z ∈ y ∷ zs)        ↔⟨ (∃-cong λ _ → F.id ∥⊎∥-cong ∈∷≃) ⟩

        z ≢ y × (z ≡ x ∥⊎∥ z ≡ y ∥⊎∥ z ∈ zs)  ↔⟨ (∃-cong λ z≢y → F.id ∥⊎∥-cong (
                                                  drop-⊥-left-∥⊎∥ ∈-propositional z≢y)) ⟩

        z ≢ y × (z ≡ x ∥⊎∥ z ∈ zs)            ↝⟨ proj₂ ⟩

        z ≡ x ∥⊎∥ z ∈ zs                      ↔⟨ inverse ∈∷≃ ⟩□

        z ∈ x ∷ zs                            □

    -- If the "body of a lambda" is well-formed for all fresh
    -- variables, then it is well-formed for the bound variable.

    @0 body-Wf :
      ∀ (tˢ : Skeleton k s′) {t} →
      (∀ (y : Var s) →
       (_ , y) ∉ xs →
       Wf ((_ , y) ∷ xs) tˢ (rename₁ x y tˢ t)) →
      Wf ((_ , x) ∷ xs) tˢ t
    body-Wf {xs} tˢ {t} wf =
      let y , [ y-fresh ] = fresh (xs ∪ free tˢ t)
          y∉xs            = y-fresh ∘ ∈→∈∪ˡ
          y∉t             = y-fresh ∘ ∈→∈∪ʳ xs
      in
      renamee-Wf tˢ y∉t (wf y y∉xs)

  ----------------------------------------------------------------------
  -- Weakening, casting and strengthening

  -- Weakening.

  weaken : @0 xs ⊆ ys → Term[ k ] xs s → Term[ k ] ys s
  weaken xs⊆ys (tˢ , t , [ wf ]) =
    tˢ , t , [ weaken-Wf xs⊆ys tˢ wf ]

  -- Casting.

  cast :
    @0 xs ≡ ys → Term[ k ] xs s → Term[ k ] ys s
  cast eq = weaken (subst (_ ⊆_) eq ⊆-refl)

  -- Strengthening.

  strengthen :
    (t : Term[ k ] ((s′ , x) ∷ xs) s) →
    @0 ¬ Free-in x t →
    Term[ k ] xs s
  strengthen (tˢ , t , [ wf ]) ¬free =
    tˢ , t , [ strengthen-Wf tˢ (¬free ∘ free-Free tˢ wf) wf ]

  ----------------------------------------------------------------------
  -- Substitution

  -- The function subst-Term maps variables to terms. Other kinds of
  -- terms are preserved.

  var-to-tm : Term-kind → Term-kind
  var-to-tm var = tm
  var-to-tm k   = k

  -- The kind of sort corresponding to var-to-tm k is the same as that
  -- for k.

  var-to-tm-for-sorts : ∀ k → Sort-kind k → Sort-kind (var-to-tm k)
  var-to-tm-for-sorts var  = id
  var-to-tm-for-sorts tm   = id
  var-to-tm-for-sorts args = id
  var-to-tm-for-sorts arg  = id

  -- Capture-avoiding substitution. The term subst-Term x t′ t is the
  -- result of substituting t′ for x in t.

  syntax subst-Term x t′ t = t [ x ← t′ ]

  subst-Term :
    ∀ {xs s}
    (x : Var s) → Term xs s →
    Term[ k ] ((_ , x) ∷ xs) s′ →
    Term[ var-to-tm k ] xs (var-to-tm-for-sorts k s′)
  subst-Term {s} x t t′ = wf-elim e t′ (refl _) t
    where
    e : Wf-elim
          (λ k {xs = xs′} {s = s′} _ →
             ∀ {xs} → @0 xs′ ≡ (_ , x) ∷ xs →
             Term xs s →
             Term[ var-to-tm k ] xs (var-to-tm-for-sorts k s′))
    e .Wf-elim.varʳ {xs = xs′} y y∈xs′ {xs} xs′≡x∷xs t =
      case (_ , y) ≟∃V (_ , x) of λ where
        (yes [ y≡x ]) →
          substᴱ (λ p → Term xs (proj₁ p)) (sym y≡x) t
        (no [ y≢x ]) →
          var-wf y
            (                        $⟨ y∈xs′ ⟩
             (_ , y) ∈ xs′           ↝⟨ subst (_ ∈_) xs′≡x∷xs ⟩
             (_ , y) ∈ (_ , x) ∷ xs  ↔⟨ ∈≢∷≃ y≢x ⟩□
             (_ , y) ∈ xs            □)

    e .Wf-elim.varʳ′ _ _ hyp eq t = hyp eq t

    e .Wf-elim.opʳ o _ _ _ hyp eq t = Σ-map (op o) id (hyp eq t)

    e .Wf-elim.nilʳ = λ _ _ → nil-wfs

    e .Wf-elim.consʳ _ _ _ _ _ _ hyp hyps eq t =
      Σ-zip cons (Σ-zip _,_ λ ([ wf ]) ([ wfs ]) → [ (wf , wfs) ])
        (hyp eq t) (hyps eq t)

    e .Wf-elim.nilʳ′ _ _ _ hyp eq t = Σ-map nil id (hyp eq t)

    e .Wf-elim.consʳ′ {xs = xs′} aˢ y a wf hyp {xs} eq t =
      case (_ , x) ≟∃V (_ , y) of λ where
        (inj₁ [ x≡y ]) →
          -- If the bound variable matches x, keep the original
          -- term (with a new well-formedness proof).
          cons-wf aˢ y a
            (                                           $⟨ wf ⟩
             Wf xs′ (Argˢ.cons aˢ) (y , a)              ↝⟨ subst (λ xs → Wf xs (Argˢ.cons aˢ) _) eq ⟩
             Wf ((_ , x) ∷ xs) (Argˢ.cons aˢ) (y , a)   ↝⟨ strengthen-Wf (Argˢ.cons aˢ) (
               (_ , x) ∈ del (_ , y) (free aˢ a)             ↔⟨ ∈delete≃ merely-equal?-∃Var ⟩
               (_ , x) ≢ (_ , y) × (_ , x) ∈ free aˢ a       ↝⟨ (_$ x≡y) ∘ proj₁ ⟩□
               ⊥                                             □) ⟩□
             Wf xs (Argˢ.cons aˢ) (y , a)               □)
        (inj₂ [ x≢y ]) →
          -- Otherwise, rename the bound variable to something fresh
          -- and keep substituting.
          let z , [ z∉ ]         = fresh ((_ , x) ∷ xs)
              aˢ′ , a′ , [ wf′ ] =
                hyp z (z∉ ∘ subst (_ ∈_) eq)
                  ((_ , z) ∷ xs′           ≡⟨ cong (_ ∷_) eq ⟩
                   (_ , z) ∷ (_ , x) ∷ xs  ≡⟨ swap ⟩∎
                   (_ , x) ∷ (_ , z) ∷ xs  ∎)
                  (weaken
                     (λ u →
                        u ∈ xs            ↝⟨ ∈→∈∷ ⟩□
                        u ∈ (_ , z) ∷ xs  □)
                     t)
          in
          cons-wf aˢ′ z a′
            (λ p _ →                                       $⟨ wf′ ⟩
               Wf ((_ , z) ∷ xs) aˢ′ a′                    ↝⟨ rename₁-Wf aˢ′ ⟩□
               Wf ((_ , p) ∷ xs) aˢ′ (rename₁ z p aˢ′ a′)  □)
