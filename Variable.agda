------------------------------------------------------------------------
-- Contexts, variables, environments, etc.
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

module Variable where

open import Prelude

-- Contexts. To avoid having to write boring expressions like
--
--   ε ▻ _ ▻ _ ▻ _
--
-- (where ε denotes the empty context) in cases where the context
-- length cannot be inferred (but the context elements can be),
-- contexts are indexed by their length, and defined in such a way
-- that we get η-equality. Then it suffices to give the length as a
-- natural number, for which a compact notation exists. Note also that
-- Ctxt is "constructor-headed", i.e. of a certain syntactic form;
-- Agda can infer more things automatically for constructor-headed
-- functions.

Ctxt : ∀ {a} (A : Set a) → ℕ → Set a
Ctxt A zero    = ⊤
Ctxt A (suc n) = Σ (Ctxt A n) λ _ → A

-- Snoc.

infixl 5 _▻_

_▻_ : ∀ {n a} {A : Set a} → Ctxt A n → A → Ctxt A (suc n)
_▻_ = _,_

-- Variables.

infix 4 _∋_

data _∋_ {a} {A : Set a} : ∀ {n} → Ctxt A n → A → Set a where
  zero : ∀ {n} {Γ : Ctxt A n} {x} → Γ ▻ x ∋ x
  suc  : ∀ {n} {Γ : Ctxt A n} {x y} (y∈Γ : Γ ∋ y) → Γ ▻ x ∋ y

-- Environments.

Env : ∀ {n a ℓ} {A : Set a} (⟦_⟧ : A → Set ℓ) → Ctxt A n → Set ℓ
Env {zero}  ⟦_⟧ _       = ⊤
Env {suc n} ⟦_⟧ (Γ , X) = Env ⟦_⟧ Γ × ⟦ X ⟧

-- Map and lookup functions.

map : ∀ {a ℓ ℓ′} {A : Set a} {⟦_⟧ : A → Set ℓ} {⟦_⟧′ : A → Set ℓ′} →
      (∀ {x} → ⟦ x ⟧ → ⟦ x ⟧′) →
      ∀ {n} (Γ : Ctxt A n) → Env ⟦_⟧ Γ → Env ⟦_⟧′ Γ
map f {n = zero}  _       _       = _
map f {n = suc n} (Γ , X) (ρ , x) = (map f Γ ρ , f x)

lookup : ∀ {a ℓ n} {A : Set a} {Γ : Ctxt A n} {⟦_⟧ : A → Set ℓ} {X : A} →
         Γ ∋ X → Env ⟦_⟧ Γ → ⟦ X ⟧
lookup zero    = proj₂
lookup (suc x) = lookup x ∘ proj₁

-- All possible variables for a given context.

allVars : ∀ {n} {a} {A : Set a} (Γ : Ctxt A n) → Env (λ x → Γ ∋ x) Γ
allVars {zero}  _       = _
allVars {suc n} (Γ , X) = (map suc Γ (allVars Γ) , zero)

-- N-ary functions.

infixr 4 [_]_⇒_

[_]_⇒_ : ∀ {a ℓ} {A : Set a} → (A → Set ℓ) →
         ∀ {n} → Ctxt A n → Set ℓ → Set ℓ
[_]_⇒_ ⟦_⟧ {zero}  _       B = B
[_]_⇒_ ⟦_⟧ {suc n} (Γ , X) B = [ ⟦_⟧ ] Γ ⇒ (⟦ X ⟧ → B)

-- (Un)currying.

curry : ∀ {a ℓ} {A : Set a} {B} {⟦_⟧ : A → Set ℓ} →
        ∀ {n} (Γ : Ctxt A n) → (Env ⟦_⟧ Γ → B) → [ ⟦_⟧ ] Γ ⇒ B
curry {n = zero}  _       f = f _
curry {n = suc n} (Γ , X) f = curry Γ (λ ρ x → f (ρ , x))

uncurry : ∀ {a ℓ} {A : Set a} {B} {⟦_⟧ : A → Set ℓ} →
          ∀ {n} (Γ : Ctxt A n) → [ ⟦_⟧ ] Γ ⇒ B → (Env ⟦_⟧ Γ → B)
uncurry {n = zero}  _       f _       = f
uncurry {n = suc n} (Γ , X) f (ρ , x) = uncurry Γ f ρ x
