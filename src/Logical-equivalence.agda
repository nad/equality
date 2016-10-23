------------------------------------------------------------------------
-- Logical equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Logical-equivalence where

open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- Logical equivalence

-- A ⇔ B means that A and B are logically equivalent.

infix 0 _⇔_

record _⇔_ {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    to   : From → To
    from : To → From

------------------------------------------------------------------------
-- Equivalence relation

-- _⇔_ is an equivalence relation.

id : ∀ {a} {A : Set a} → A ⇔ A
id = record
  { to   = P.id
  ; from = P.id
  }

inverse : ∀ {a b} {A : Set a} {B : Set b} → A ⇔ B → B ⇔ A
inverse A⇔B = record
  { to               = from
  ; from             = to
  } where open _⇔_ A⇔B

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ⇔ C → A ⇔ B → A ⇔ C
f ∘ g = record
  { to   = to   f ⊚ to   g
  ; from = from g ⊚ from f
  } where open _⇔_

-- "Equational" reasoning combinators.

infix  -1 finally-⇔
infixr -2 step-⇔

-- For an explanation of why step-⇔ is defined in this way, see
-- Equality.step-≡.

step-⇔ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         B ⇔ C → A ⇔ B → A ⇔ C
step-⇔ _ = _∘_

syntax step-⇔ A B⇔C A⇔B = A ⇔⟨ A⇔B ⟩ B⇔C

finally-⇔ : ∀ {a b} (A : Set a) (B : Set b) → A ⇔ B → A ⇔ B
finally-⇔ _ _ A⇔B = A⇔B

syntax finally-⇔ A B A⇔B = A ⇔⟨ A⇔B ⟩□ B □

------------------------------------------------------------------------
-- A lemma

-- Dec preserves logical equivalences.

Dec-preserves : {A B : Set} → A ⇔ B → Dec A ⇔ Dec B
Dec-preserves A⇔B = record
  { to   = lemma A⇔B
  ; from = lemma (inverse A⇔B)
  }
  where
  lemma : {A B : Set} → A ⇔ B → Dec A → Dec B
  lemma A⇔B = ⊎-map to (λ ¬A → ¬A ⊚ from)
    where open _⇔_ A⇔B
