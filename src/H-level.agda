------------------------------------------------------------------------
-- H-levels
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module H-level
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence hiding (id; _∘_)
open import Nat eq
open import Prelude
open import Surjection eq hiding (id; _∘_)

private
  variable
    a ℓ : Level
    m n : ℕ
    A B : Type a

------------------------------------------------------------------------
-- H-levels

-- H-levels ("homotopy levels").

H-level : ℕ → Type ℓ → Type ℓ
H-level zero          A = Contractible A
H-level (suc zero)    A = Is-proposition A
H-level (suc (suc n)) A = {x y : A} → H-level (suc n) (x ≡ y)

private

  -- Note that H-level 2 is a synonym for Is-set.

  H-level-2≡Is-set : H-level 2 A ≡ Is-set A
  H-level-2≡Is-set = refl _

-- For-iterated-equality n P A means that P holds for (equalities
-- over)^n A.

For-iterated-equality : ℕ → (Type ℓ → Type ℓ) → (Type ℓ → Type ℓ)
For-iterated-equality zero    P A = P A
For-iterated-equality (suc n) P A =
  (x y : A) → For-iterated-equality n P (x ≡ y)

-- An alternative definition of h-levels.
--
-- In some cases this definition, with only two cases, is easier to
-- use. In other cases the definition above, which is less complicated
-- for positive h-levels, is easier to use.

H-level′ : ℕ → Type ℓ → Type ℓ
H-level′ = flip For-iterated-equality Contractible

-- Propositions are propositional types.

Proposition : (ℓ : Level) → Type (lsuc ℓ)
Proposition _ = ∃ Is-proposition

-- Types that are sets.

Set : (ℓ : Level) → Type (lsuc ℓ)
Set _ = ∃ Is-set

-- The underlying type.

⌞_⌟ : Set ℓ → Type ℓ
⌞ A ⌟ = proj₁ A

------------------------------------------------------------------------
-- General properties

-- H-level′ is upwards closed in its first argument.

mono₁′ : ∀ n → H-level′ n A → H-level′ (1 + n) A
mono₁′     (suc n) h x y = mono₁′ n (h x y)
mono₁′ {A} zero    h x y = trivial x y , irr
  where
  trivial : (x y : A) → x ≡ y
  trivial x y =
    x        ≡⟨ sym $ proj₂ h x ⟩
    proj₁ h  ≡⟨ proj₂ h y ⟩∎
    y        ∎

  irr : (x≡y : x ≡ y) → trivial x y ≡ x≡y
  irr = elim (λ {x y} x≡y → trivial x y ≡ x≡y)
             (λ x → trans-symˡ (proj₂ h x))

-- H-level and H-level′ are pointwise logically equivalent.

H-level⇔H-level′ : H-level n A ⇔ H-level′ n A
H-level⇔H-level′ = record { to = to _; from = from _ }
  where
  to : ∀ n → H-level n A → H-level′ n A
  to zero          h = h
  to (suc zero)    h = λ x → mono₁′ 0 (x , h x) x
  to (suc (suc n)) h = λ x y → to (suc n) h

  from : ∀ n → H-level′ n A → H-level n A
  from zero          h         = h
  from (suc zero)    h x y     = proj₁ (h x y)
  from (suc (suc n)) h {x} {y} = from (suc n) (h x y)

-- If A has h-level 1 + n, then the types of equality proofs between
-- elements of type A have h-level n.

+⇒≡ : {x y : A} → H-level (suc n) A → H-level n (x ≡ y)
+⇒≡ h = _⇔_.from H-level⇔H-level′ $ _⇔_.to H-level⇔H-level′ h _ _

-- H-level is upwards closed in its first argument.

mono₁ : ∀ n → H-level n A → H-level (1 + n) A
mono₁ n =
  _⇔_.from H-level⇔H-level′ ∘
  mono₁′ n ∘
  _⇔_.to H-level⇔H-level′

opaque

  mono : m ≤ n → H-level m A → H-level n A
  mono (≤-refl′ eq)     = subst (λ n → H-level n _) eq
  mono (≤-step′ m≤n eq) =
    subst (λ n → H-level n _) eq ∘
    mono₁ _ ∘
    mono m≤n

  -- If A has h-level n, then the types of equality proofs between
  -- elements of type A also have h-level n.

  ⇒≡ : {x y : A} → ∀ n → H-level n A → H-level n (x ≡ y)
  ⇒≡ _ = +⇒≡ ∘ mono₁ _

  -- If something is contractible given the assumption that it is
  -- inhabited, then it is propositional.

  [inhabited⇒contractible]⇒propositional :
    (A → Contractible A) → Is-proposition A
  [inhabited⇒contractible]⇒propositional h x = mono₁ 0 (h x) x

  -- If something has h-level (1 + n) given the assumption that it is
  -- inhabited, then it has h-level (1 + n).

  [inhabited⇒+]⇒+ : ∀ n → (A → H-level (1 + n) A) → H-level (1 + n) A
  [inhabited⇒+]⇒+ n h =
    _⇔_.from H-level⇔H-level′ λ x → _⇔_.to H-level⇔H-level′ (h x) x

  -- An alternative characterisation of sets and higher h-levels.
  --
  -- This is Theorem 7.2.7 from the HoTT book.

  2+⇔∀1+≡ :
    ∀ n → H-level (2 + n) A ⇔ ((x : A) → H-level (1 + n) (x ≡ x))
  2+⇔∀1+≡ n = record
    { to   = λ h _ → h
    ; from = λ h → [inhabited⇒+]⇒+ _
                     (elim (λ {x y} _ → H-level (1 + n) (x ≡ y)) h)
    }

-- If a propositional type is inhabited, then it is contractible.

propositional⇒inhabited⇒contractible :
  {@0 A : Type a} →
  Is-proposition A → A → Contractible A
propositional⇒inhabited⇒contractible p x = (x , p x)

-- H-level′ n respects (split) surjections.

respects-surjection′ :
  A ↠ B → ∀ n → H-level′ n A → H-level′ n B
respects-surjection′ A↠B zero (x , irr) = (to x , irr′)
  where
  open _↠_ A↠B

  irr′ : ∀ y → to x ≡ y
  irr′ = λ y →
    to x         ≡⟨ cong to (irr (from y)) ⟩
    to (from y)  ≡⟨ right-inverse-of y ⟩∎
    y            ∎

respects-surjection′ A↠B (suc n) h = λ x y →
  respects-surjection′ (↠-≡ A↠B) n (h (from x) (from y))
  where open _↠_ A↠B

-- H-level n respects (split) surjections.

respects-surjection :
  A ↠ B → ∀ n → H-level n A → H-level n B
respects-surjection A↠B n =
  _⇔_.from H-level⇔H-level′ ∘
  respects-surjection′ A↠B n ∘
  _⇔_.to H-level⇔H-level′
