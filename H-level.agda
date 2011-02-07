------------------------------------------------------------------------
-- H-levels
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

module H-level where

open import Equality
import Equality.Decidable-UIP as DUIP
import Equality.Groupoid as EG
private module G {A : Set} = EG.Groupoid (EG.groupoid A)
import Equality.Tactic as Tactic; open Tactic.Eq
open import Equivalence hiding (id; _∘_)
open import Prelude
open import Surjection hiding (id; _∘_)

------------------------------------------------------------------------
-- H-levels

-- H-levels ("homotopy levels").

H-level : ℕ → Set → Set
H-level zero    A = Contractible A
H-level (suc n) A = (x y : A) → H-level n (x ≡ y)

-- Some named levels.

Propositional : Set → Set
Propositional = H-level 1

Is-set : Set → Set
Is-set = H-level 2

------------------------------------------------------------------------
-- General properties

abstract

  -- H-level is upwards closed in its first argument.

  mono₁ : ∀ {A} n → H-level n A → H-level (1 + n) A
  mono₁ (suc n) h x y = mono₁ n (h x y)
  mono₁ zero    h x y = (trivial x y , irr)
    where
    trivial : ∀ x y → x ≡ y
    trivial x y =
      x        ≡⟨ sym $ proj₂ h x ⟩
      proj₁ h  ≡⟨ proj₂ h y ⟩∎
      y        ∎

    irr : ∀ {x y} (x≡y : x ≡ y) → trivial x y ≡ x≡y
    irr = elim (λ {x y} x≡y → trivial x y ≡ x≡y)
               (λ x → G.right-inverse (proj₂ h x))

  mono : ∀ {A m n} → m ≤ n → H-level m A → H-level n A
  mono ≤-refl               = id
  mono (≤-step {n = n} m≤n) = mono₁ n ∘ mono m≤n

  -- If something is contractible given the assumption that it is
  -- inhabited, then it is propositional.

  [inhabited⇒contractible]⇒propositional :
    {A : Set} → (A → Contractible A) → Propositional A
  [inhabited⇒contractible]⇒propositional h x = mono₁ 0 (h x) x

  -- If something has h-level (1 + n) given the assumption that it is
  -- inhabited, then it has h-level (1 + n)

  [inhabited⇒+]⇒+ :
    ∀ {A} n → (A → H-level (1 + n) A) → H-level (1 + n) A
  [inhabited⇒+]⇒+ n h x = h x x

  -- Being propositional is equivalent to having at most one element.

  propositional⇔irrelevant :
    {A : Set} → Propositional A ⇔ Proof-irrelevant A
  propositional⇔irrelevant {A} = equivalent ⇒ ⇐
    where
    ⇒ : Propositional A → Proof-irrelevant A
    ⇒ h x y = proj₁ (h x y)

    ⇐ : Proof-irrelevant A → Propositional A
    ⇐ irr = [inhabited⇒contractible]⇒propositional (λ x → (x , irr x))

  -- Being a set is equivalent to having unique identity proofs. Note
  -- that this means that, assuming that Agda is consistent, I cannot
  -- prove (inside Agda) that there is any type whose minimal h-level
  -- is at least three.

  set⇔UIP : {A : Set} → Is-set A ⇔ Uniqueness-of-identity-proofs A
  set⇔UIP {A} = equivalent ⇒ ⇐
    where
    ⇒ : Is-set A → Uniqueness-of-identity-proofs A
    ⇒ h {x} {y} x≡y x≡y′ = proj₁ (h x y x≡y x≡y′)

    ⇐ : Uniqueness-of-identity-proofs A → Is-set A
    ⇐ UIP x y =
      [inhabited⇒contractible]⇒propositional (λ x≡y → (x≡y , UIP x≡y))

  -- Types with decidable equality are sets.

  decidable⇒set : {A : Set} → Decidable (_≡_ {A = A}) → Is-set A
  decidable⇒set dec = _⇔_.from set⇔UIP (DUIP.decidable⇒UIP dec)

-- H-level n respects surjections.

respects-surjection :
  ∀ {A B} → A ↠ B → ∀ n → H-level n A → H-level n B
respects-surjection A↠B zero (x , irr) = (to x , irr′)
  where
  open _↠_ A↠B

  abstract
    irr′ = λ y →
      to x         ≡⟨ cong to (irr (from y)) ⟩
      to (from y)  ≡⟨ right-inverse-of y ⟩∎
      y            ∎

respects-surjection A↠B (suc n) h = rs
  where
  abstract
    open _↠_ A↠B

    to′ : ∀ {x y} → from x ≡ from y → x ≡ y
    to′ {x} {y} = λ from-x≡from-y →
      x            ≡⟨ sym $ right-inverse-of x ⟩
      to (from x)  ≡⟨ cong to from-x≡from-y ⟩
      to (from y)  ≡⟨ right-inverse-of y ⟩∎
      y            ∎

    from′ : ∀ {x y} → x ≡ y → from x ≡ from y
    from′ {x} {y} = λ x≡y →
      from x  ≡⟨ cong from x≡y ⟩∎
      from y  ∎

    surj : ∀ {x y} → (from x ≡ from y) ↠ (x ≡ y)
    surj = record
      { equivalence = record
        { to   = to′
        ; from = from′
        }
      ; right-inverse-of = elim (λ x≡y → to′ (from′ x≡y) ≡ x≡y) (λ x →
          let riox = right-inverse-of x in
          (trans (sym riox) $
           trans (cong to $ cong from $ refl x) $
           riox)                                   ≡⟨ Tactic.prove (Trans (Sym (Lift riox)) $
                                                                    Trans (Cong to (Cong from Refl))
                                                                          (Lift riox))
                                                                   (Trans (Sym (Lift riox)) (Lift riox))
                                                                   (refl _) ⟩
          trans (sym riox) riox                    ≡⟨ G.right-inverse _ ⟩∎
          refl x                                   ∎)
      }

    rs = λ x y → respects-surjection surj n (h (from x) (from y))
