------------------------------------------------------------------------
-- H-levels
------------------------------------------------------------------------

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

module H-level where

open import Data.Nat
open import Data.Product as Prod
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalent; module Equivalent)
open import Function.Surjection using (module Surjection)
open import Relation.Binary using (Decidable)

open import Equality-without-K as Eq
import Equality-without-K.Decidable-UIP as DUIP
import Equality-without-K.Groupoid as EG
private module G {A : Set} = EG.Groupoid (EG.groupoid {A = A})
import Equality-without-K.Tactic as Tactic; open Tactic.Eq

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
  irr =
    Eq.elim
      (λ {x y} x≡y → trivial x y ≡ x≡y)
      (λ x → G.right-inverse (proj₂ h x))

mono : ∀ {A m n} → m ≤′ n → H-level m A → H-level n A
mono ≤′-refl               = id
mono (≤′-step {n = n} m≤n) = mono₁ n ∘ mono m≤n

-- If something is contractible given the assumption that it is
-- inhabited, then it is propositional.

[inhabited⇒contractible]⇒propositional :
  {A : Set} → (A → Contractible A) → Propositional A
[inhabited⇒contractible]⇒propositional h x = mono₁ 0 (h x) x

-- If something has h-level (1 + n) given the assumption that it is
-- inhabited, then it has h-level (1 + n)

[inhabited⇒+]⇒+ : ∀ {A} n → (A → H-level (1 + n) A) → H-level (1 + n) A
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
-- prove (inside Agda) that there is any type whose minimal h-level is
-- at least three.

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
decidable⇒set dec = Equivalent.from set⇔UIP ⟨$⟩ DUIP.decidable⇒UIP dec

-- H-level n respects surjections.

respects-surjection :
  ∀ {A B} → A ↠ B → ∀ n → H-level n A → H-level n B
respects-surjection A↠B zero h =
  Prod.map (_⟨$⟩_ to)
           (λ {x} triv y →
              to ⟨$⟩ x             ≡⟨ Eq.cong (_⟨$⟩_ to) (triv (from ⟨$⟩ y)) ⟩
              to ⟨$⟩ (from ⟨$⟩ y)  ≡⟨ right-inverse-of y ⟩∎
              y                    ∎)
           h
  where open Surjection A↠B
respects-surjection A↠B (suc n) h = λ x y →
  let surj : (from ⟨$⟩ x ≡ from ⟨$⟩ y) ↠ (x ≡ y)
      surj = record
        { to         = Eq.→-to-⟶ to′
        ; surjective = record
          { from             = Eq.→-to-⟶ from′
          ; right-inverse-of = Eq.elim (λ x≡y → to′ (from′ x≡y) ≡ x≡y) (λ x →
              let riox = right-inverse-of x in
              (trans (sym riox) $
               trans (Eq.cong (_⟨$⟩_ to)   $
                      Eq.cong (_⟨$⟩_ from) $ refl x) $
               riox)                                    ≡⟨ Tactic.prove (Trans (Sym (Lift riox))
                                                                               (Trans (Cong (_⟨$⟩_ to) (Cong (_⟨$⟩_ from) Refl))
                                                                                      (Lift riox)))
                                                                        (Trans (Sym (Lift riox)) (Lift riox))
                                                                        (refl _) ⟩
              trans (sym riox) riox                     ≡⟨ G.right-inverse _ ⟩∎
              refl x                                    ∎)
          }
        }
  in respects-surjection surj n (h (from ⟨$⟩ x) (from ⟨$⟩ y))
  where
  open Surjection A↠B

  to′ : ∀ {x y} → from ⟨$⟩ x ≡ from ⟨$⟩ y → x ≡ y
  to′ {x} {y} = λ from-x≡from-y →
    x                    ≡⟨ sym $ right-inverse-of x ⟩
    to ⟨$⟩ (from ⟨$⟩ x)  ≡⟨ Eq.cong (_⟨$⟩_ to) from-x≡from-y ⟩
    to ⟨$⟩ (from ⟨$⟩ y)  ≡⟨ right-inverse-of y ⟩∎
    y                    ∎

  from′ : ∀ {x y} → x ≡ y → from ⟨$⟩ x ≡ from ⟨$⟩ y
  from′ {x} {y} = λ x≡y →
    from ⟨$⟩ x  ≡⟨ Eq.cong (_⟨$⟩_ from) x≡y ⟩∎
    from ⟨$⟩ y  ∎
