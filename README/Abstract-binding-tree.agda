------------------------------------------------------------------------
-- An example of how Abstract-binding-tree can be used
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module README.Abstract-binding-tree where

open import Dec
open import Equality.Path
open import Prelude as P hiding (swap; [_,_]; type-signature)

open import Abstract-binding-tree equality-with-paths
open import Bijection equality-with-J using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Equivalence equality-with-J using (_≃_)
open import Erased.Cubical equality-with-paths
open import Finite-subset.Listed equality-with-paths as L
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc
import Nat equality-with-J as Nat

-- Sorts: expressions and statements.

Sort : Type
Sort = Bool

pattern expr = true
pattern stmt = false

-- Constructors: lambda, application and print.

data Constructor : @0 Sort → Type where
  ec : Bool → Constructor expr
  sc : ⊤ → Constructor stmt

pattern lam   = ec true
pattern app   = ec false
pattern print = sc tt

-- Erased equality of constructors is decidable.

_≟O_ : ∀ {@0 s} → Decidable-erased-equality (Constructor s)
ec x  ≟O ec y  = Dec-Erased-map
                   (record { to   = cong ec
                           ; from = cong (λ { (ec x) → x })
                           })
                   (Decidable-equality→Decidable-erased-equality
                      Bool._≟_ x y)
print ≟O print = yes [ refl ]

-- Variables are natural numbers.

Var : @0 Sort → Type
Var _ = ℕ

-- A signature.

sig : Signature lzero
sig .Signature.Sort         = Sort
sig .Signature.Op           = Constructor
sig .Signature.domain lam   = (expr ∷ [] , expr) ∷ []
sig .Signature.domain app   = ([] , expr) ∷ ([] , expr) ∷ []
sig .Signature.domain print = ([] , expr) ∷ []
sig .Signature.Var          = Var
sig .Signature._≟O_         = _≟O_
sig .Signature._≟S_         =
  Decidable-equality→Decidable-erased-equality Bool._≟_
sig .Signature._≟V_ =
  Decidable-equality→Decidable-erased-equality Nat._≟_
sig .Signature.fresh {s = s} xs =
  Σ-map id (λ {n} ([ ub ]) → [ (λ n∈ → Nat.<-irreflexive (ub n n∈)) ])
    (L.elim e xs)
  where
  P : @0 Finite-subset-of (∃ λ s → Var s) → @0 ℕ → Type
  P xs m = Erased (∀ n → (s , n) ∈ xs → n Nat.< m)

  prop : ∀ {xs m} → Is-proposition (P xs m)
  prop =
    H-level-Erased 1 (
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ≤-propositional)

  ∷-max-suc :
    ∀ {xs n} {x@(_ , m) : ∃ λ s → Var s} →
    P xs n →
    P (x ∷ xs) (Nat.max (suc m) n)
  ∷-max-suc {xs = xs} {n = n} {x = x@(_ , m)} [ ub ] =
    [ (λ o →
         (_ , o) ∈ x ∷ xs              ↔⟨ ∈∷≃ ⟩
         (_ , o) ≡ x ∥⊎∥ (_ , o) ∈ xs  ↝⟨ Nat.≤-refl′ ∘ cong suc ∘ cong proj₂ ∥⊎∥-cong ub o ⟩
         o Nat.< suc m ∥⊎∥ o Nat.< n   ↝⟨ Trunc.rec ≤-propositional
                                            P.[ flip Nat.≤-trans (Nat.ˡ≤max _ n)
                                              , flip Nat.≤-trans (Nat.ʳ≤max (suc m) _)
                                              ] ⟩□
         o Nat.< Nat.max (suc m) n     □)
    ]

  e : L.Elim (λ xs → ∃ λ m → P xs m)
  e .[]ʳ =
    0 , [ (λ _ ()) ]

  e .∷ʳ (_ , m) (n , ub) =
    Nat.max (suc m) n , ∷-max-suc ub

  e .dropʳ {y = y} x@(_ , m) (n , ub) =
    to-implication (ignore-propositional-component prop)
      (proj₁ (subst (λ xs → ∃ λ m → P xs m)
                    (drop {x = x} {y = y})
                    ( Nat.max (suc m) (Nat.max (suc m) n)
                    , ∷-max-suc (∷-max-suc ub)
                    ))                                     ≡⟨ cong proj₁ $
                                                              push-subst-pair-× {y≡z = drop {x = x} {y = y}} _
                                                                (λ (xs , m) → P xs m)
                                                                {p = _ , ∷-max-suc (∷-max-suc ub)} ⟩

       Nat.max (suc m) (Nat.max (suc m) n)                 ≡⟨ Nat.max-assoc (suc m) {n = suc m} {o = n} ⟩

       Nat.max (Nat.max (suc m) (suc m)) n                 ≡⟨ cong (λ m → Nat.max m n) $ Nat.max-idempotent (suc m) ⟩∎

       Nat.max (suc m) n                                   ∎)

  e .swapʳ {z = z} x@(_ , m) y@(_ , n) (o , ub) =
    to-implication (ignore-propositional-component prop)
      (proj₁ (subst (λ xs → ∃ λ m → P xs m)
                    (swap {x = x} {y = y} {z = z})
                    ( Nat.max (suc m) (Nat.max (suc n) o)
                    , ∷-max-suc (∷-max-suc ub)
                    ))                                     ≡⟨ cong proj₁ $
                                                              push-subst-pair-× {y≡z = swap {x = x} {y = y} {z = z}} _
                                                                (λ (xs , m) → P xs m)
                                                                {p = _ , ∷-max-suc (∷-max-suc ub)} ⟩

       Nat.max (suc m) (Nat.max (suc n) o)                 ≡⟨ Nat.max-assoc (suc m) {n = suc n} {o = o} ⟩

       Nat.max (Nat.max (suc m) (suc n)) o                 ≡⟨ cong (λ m → Nat.max m o) $ Nat.max-comm (suc m) (suc n) ⟩

       Nat.max (Nat.max (suc n) (suc m)) o                 ≡⟨ sym $ Nat.max-assoc (suc n) {n = suc m} {o = o} ⟩∎

       Nat.max (suc n) (Nat.max (suc m) o)                 ∎)

  e .is-setʳ _ =
    Σ-closure 2 ℕ-set λ _ →
    mono₁ 1 prop

open Signature sig public hiding (Sort; Var; _≟O_)

private
  variable
    @0 s  : Sort
    @0 xs : Vars
    @0 A  : Type
    @0 x  : A

-- Pattern synonyms.

pattern varᵖ x wf = var , x , [ wf ]

pattern lamˢᵖ tˢ =
  op lam (cons (cons (nil tˢ)) nil)
pattern lamᵖ x tˢ t wf =
    lamˢᵖ tˢ
  , ((x , t) , lift tt)
  , [ wf , lift tt ]

pattern appˢᵖ t₁ˢ t₂ˢ =
  op app (cons (nil t₁ˢ) (cons (nil t₂ˢ) nil))
pattern appᵖ t₁ˢ t₂ˢ t₁ t₂ wf₁ wf₂ =
    appˢᵖ t₁ˢ t₂ˢ
  , (t₁ , t₂ , lift tt)
  , [ wf₁ , wf₂ , lift tt ]

pattern printˢᵖ tˢ =
  op print (cons (nil tˢ) nil)
pattern printᵖ tˢ t wf =
    printˢᵖ tˢ
  , (t , lift tt)
  , [ wf , lift tt ]

-- Some (more or less) smart constructors.

varˢ : ∀ {s} (x : Var s) → Term ((s , x) ∷ xs) s
varˢ x = varᵖ x (≡→∈∷ refl)

lamˢ :
  (x : Var expr) →
  Term ((expr , x) ∷ xs) expr →
  Term xs expr
lamˢ x (tˢ , t , [ wf ]) =
  lamᵖ x tˢ t (λ _ _ → rename-Wf-tm tˢ wf)

appˢ : Term xs expr → Term xs expr → Term xs expr
appˢ (t₁ˢ , t₁ , [ wf₁ ]) (t₂ˢ , t₂ , [ wf₂ ]) =
  appᵖ t₁ˢ t₂ˢ t₁ t₂ wf₁ wf₂

printˢ : Term xs expr → Term xs stmt
printˢ (tˢ , t , [ wf ]) = printᵖ tˢ t wf

-- A representation of "λ x. x".

λx→x : Term [] expr
λx→x = lamˢ 0 (varˢ 0)

-- A representation of "print (λ x y. x y)".

print[λxy→xy] : Term [] stmt
print[λxy→xy] =
  printˢ $ lamˢ 0 $ lamˢ 1 $
  appˢ (weaken-Term lemma (varˢ 0)) (varˢ 1)
  where
  @0 lemma : _
  lemma =
    from-⊎ $
    subset?
      (decidable-equality→decidable-mere-equality
         (Decidable-erased-equality≃Decidable-equality _ _≟∃V_))
      ((expr , 0) ∷ [])
      ((expr , 1) ∷ (expr , 0) ∷ [])

-- An interpreter that uses fuel.

eval : ∀ {xs} → ℕ → Term xs s → Term xs s
eval zero    t = t
eval (suc n) t = eval′ t
  where
  eval′ : ∀ {xs} → Term xs s → Term xs s
  eval′ t@(varᵖ _ _)     = t
  eval′ t@(lamᵖ _ _ _ _) = t
  eval′ (printᵖ tˢ t wf) = printˢ (eval′ (tˢ , t , [ wf ]))
  eval′ {xs = xs} (appᵖ t₁ˢ t₂ˢ t₁ t₂ wf₁ wf₂)
    with eval′ (t₁ˢ , t₁ , [ wf₁ ])
       | eval′ (t₂ˢ , t₂ , [ wf₂ ])
  … | lamᵖ x t₁ˢ′ t₁′ wf₁′ | t₂′ =
    cast-Term (idem xs) $
    eval n (subst-Term x t₂′
              ( t₁ˢ′
              , t₁′
              , [ body-Wf-tm t₁ˢ′ wf₁′ ]
              ))
  … | t₁′ | t₂′ = appˢ t₁′ t₂′

-- Simple types.

infixr 6 _⇨_

data Ty : Type where
  base : Ty
  _⇨_  : Ty → Ty → Ty

-- Contexts.

Ctxt : Vars → Type
Ctxt xs = Block "Ctxt" → ∀ x → x ∈ xs → Ty

private
  variable
    @0 σ : Ty
    @0 Γ : Ctxt xs

-- Extends a context with a new variable. If the variable already
-- exists in the context, then the old binding is removed.

infixl 5 _,_⦂_

_,_⦂_ : ∀ {xs} → Ctxt xs → ∀ x → Ty → Ctxt (x ∷ xs)
(Γ , x ⦂ σ) ⊠ y y∈x∷xs =
  case y ≟∃V x of λ where
    (yes y≡x) → σ
    (no  y≢x) → Γ ⊠ y (_≃_.to (∈≢∷≃ (Stable-¬ _ y≢x)) y∈x∷xs)

-- A type system.

infix 4 _⊢_⦂_

data _⊢_⦂_ : Ctxt xs → Term xs s → Ty → Type where
  ⊢var   : ∀ {s x xs} {Γ : Ctxt ((s , x) ∷ xs)} {t σ} →
           t ≡ varˢ x →
           σ ≡ Γ ⊠ (s , x) (≡→∈∷ refl) →
           Γ ⊢ t ⦂ σ
  ⊢lam   : ∀ {xs} {Γ : Ctxt xs} {x t t′ σ τ} →
           Γ , (_ , x) ⦂ σ ⊢ t ⦂ τ →
           t′ ≡ lamˢ x t →
           Γ ⊢ t′ ⦂ σ ⇨ τ
  ⊢app   : ∀ {xs} {Γ : Ctxt xs} {t₁ t₂ t′ σ τ} →
           Γ ⊢ t₁ ⦂ σ ⇨ τ →
           Γ ⊢ t₂ ⦂ σ →
           t′ ≡ appˢ t₁ t₂ →
           Γ ⊢ t′ ⦂ τ
  ⊢print : ∀ {xs} {Γ : Ctxt xs} {t t′ σ} →
           Γ ⊢ t ⦂ σ →
           t′ ≡ printˢ t →
           Γ ⊢ t′ ⦂ σ
