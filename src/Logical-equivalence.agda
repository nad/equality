------------------------------------------------------------------------
-- Logical equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Logical-equivalence where

open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

------------------------------------------------------------------------
-- Logical equivalence

-- A ⇔ B means that A and B are logically equivalent.

infix 0 _⇔_

record _⇔_ {f t} (From : Type f) (To : Type t) : Type (f ⊔ t) where
  field
    to   : From → To
    from : To → From

------------------------------------------------------------------------
-- Equivalence relation

-- _⇔_ is an equivalence relation.

id : ∀ {a} {A : Type a} → A ⇔ A
id = record
  { to   = P.id
  ; from = P.id
  }

inverse : ∀ {a b} {A : Type a} {B : Type b} → A ⇔ B → B ⇔ A
inverse A⇔B = record
  { to               = from
  ; from             = to
  } where open _⇔_ A⇔B

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
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

step-⇔ : ∀ {a b c} (A : Type a) {B : Type b} {C : Type c} →
         B ⇔ C → A ⇔ B → A ⇔ C
step-⇔ _ = _∘_

syntax step-⇔ A B⇔C A⇔B = A ⇔⟨ A⇔B ⟩ B⇔C

finally-⇔ : ∀ {a b} (A : Type a) (B : Type b) → A ⇔ B → A ⇔ B
finally-⇔ _ _ A⇔B = A⇔B

syntax finally-⇔ A B A⇔B = A ⇔⟨ A⇔B ⟩□ B □

------------------------------------------------------------------------
-- Some lemmas

-- A map function for Dec.

Dec-map :
  ∀ {a b} {A : Type a} {B : Type b} →
  A ⇔ B → Dec A → Dec B
Dec-map A⇔B = ⊎-map to (_⊚ from)
  where
  open _⇔_ A⇔B

-- Dec preserves logical equivalences.

Dec-preserves :
  ∀ {a b} {A : Type a} {B : Type b} →
  A ⇔ B → Dec A ⇔ Dec B
Dec-preserves A⇔B = record
  { to   = Dec-map A⇔B
  ; from = Dec-map (inverse A⇔B)
  }
