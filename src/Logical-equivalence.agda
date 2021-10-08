------------------------------------------------------------------------
-- Logical equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Logical-equivalence where

open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

private
  variable
    a b      : Level
    @0 A B C : Type a

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

id : A ⇔ A
id = record
  { to   = P.id
  ; from = P.id
  }

inverse : A ⇔ B → B ⇔ A
inverse A⇔B ._⇔_.to   = let record { from = from } = A⇔B in from
inverse A⇔B ._⇔_.from = let record { to   = to   } = A⇔B in to

infixr 9 _∘_

_∘_ : B ⇔ C → A ⇔ B → A ⇔ C
(f ∘ g) ._⇔_.to =
  let record { to = f-to } = f
      record { to = g-to } = g
  in f-to ⊚ g-to
(f ∘ g) ._⇔_.from =
  let record { from = f-from } = f
      record { from = g-from } = g
  in g-from ⊚ f-from

-- "Equational" reasoning combinators.

infix  -1 finally-⇔
infixr -2 step-⇔

-- For an explanation of why step-⇔ is defined in this way, see
-- Equality.step-≡.

step-⇔ : (@0 A : Type a) → B ⇔ C → A ⇔ B → A ⇔ C
step-⇔ _ = _∘_

syntax step-⇔ A B⇔C A⇔B = A ⇔⟨ A⇔B ⟩ B⇔C

finally-⇔ : (@0 A : Type a) (@0 B : Type b) → A ⇔ B → A ⇔ B
finally-⇔ _ _ A⇔B = A⇔B

syntax finally-⇔ A B A⇔B = A ⇔⟨ A⇔B ⟩□ B □
