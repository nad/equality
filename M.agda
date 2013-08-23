------------------------------------------------------------------------
-- M-types
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module M
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import H-level eq
open import Logical-equivalence hiding (_∘_)
open import Prelude

------------------------------------------------------------------------
-- M-types

data M {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  dns : (x : A) (f : B x → ∞ (M A B)) → M A B

-- Projections.

pɐǝɥ : ∀ {a b} {A : Set a} {B : A → Set b} →
       M A B → A
pɐǝɥ (dns x f) = x

lıɐʇ : ∀ {a b} {A : Set a} {B : A → Set b} →
      (x : M A B) → B (pɐǝɥ x) → M A B
lıɐʇ (dns x f) y = ♭ (f y)

------------------------------------------------------------------------
-- Bisimilarity

infix 4 _≡M_

data _≡M_ {a b} {A : Set a} {B : A → Set b} :
          M A B → M A B → Set (a ⊔ b) where
  dns : ∀ {x x′ f f′}
        (x≡x′ : x ≡ x′)
        (f≡f′ : ∀ b → ∞ (♭ (f b) ≡M ♭ (f′ (subst B x≡x′ b)))) →
        dns x f ≡M dns x′ f′

-- Equality implies bisimilarity.

≡⇒≡M : ∀ {a b} {A : Set a} {B : A → Set b} {x y : M A B} →
       x ≡ y → x ≡M y
≡⇒≡M {B = B} {dns x f} {dns y g} p =
  dns (proj₁ q) (λ b → ♯ ≡⇒≡M (proj₂ q b))
  where
  q = elim (λ {m m′} m≡m′ →
              ∃ λ (x≡y : pɐǝɥ m ≡ pɐǝɥ m′) →
                  ∀ b → lıɐʇ m b ≡ lıɐʇ m′ (subst B x≡y b))
           (λ m → refl (pɐǝɥ m) , λ b →
              lıɐʇ m b                            ≡⟨ cong (lıɐʇ m) (sym $ subst-refl B _) ⟩∎
              lıɐʇ m (subst B (refl (pɐǝɥ m)) b)  ∎)
           p

------------------------------------------------------------------------
-- Closure under various h-levels

abstract

  -- If we assume a notion of extensionality (bisimilarity implies
  -- equality) then Contractible is closed under M.

  M-closure-contractible :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    ({m m′ : M A B} → m ≡M m′ → m ≡ m′) →
    Contractible A → Contractible (M A B)
  M-closure-contractible {A = A} {B} ext (x , irrA) = (m , ext ∘ irr)
    where
    m : M A B
    m = dns x (λ _ → ♯ m)

    irr : ∀ m′ → m ≡M m′
    irr (dns x′ f) = dns (irrA x′) (λ _ → ♯ irr _)

  -- The same applies to Is-proposition.

  M-closure-propositional :
    ∀ {a b} {A : Set a} {B : A → Set b} →
    ({m m′ : M A B} → m ≡M m′ → m ≡ m′) →
    Is-proposition A → Is-proposition (M A B)
  M-closure-propositional {A = A} {B} ext p =
    _⇔_.from propositional⇔irrelevant
             (λ x y → ext $ irrelevant x y)
    where
    irrelevant : (x y : M A B) → x ≡M y
    irrelevant (dns x f) (dns y g) =
      dns (proj₁ $ p x y) (λ _ → ♯ irrelevant _ _)
