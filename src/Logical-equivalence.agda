------------------------------------------------------------------------
-- Logical equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Logical-equivalence where

open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

private
  variable
    a b p      : Level
    @0 A B C D : Type a
    @0 P Q     : A → Type p

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

------------------------------------------------------------------------
-- Preservation lemmas

-- Note that all of the type arguments of these lemmas are erased.

-- _⊎_ preserves logical equivalences.

infixr 2 _×-cong_

_×-cong_ : A ⇔ C → B ⇔ D → A × B ⇔ C × D
A⇔C ×-cong B⇔D =
  let record { to = to₁; from = from₁ } = A⇔C
      record { to = to₂; from = from₂ } = B⇔D
  in
  record
    { to   = Σ-map to₁   to₂
    ; from = Σ-map from₁ from₂
    }

-- ∃ preserves logical equivalences.

∃-cong : (∀ x → P x ⇔ Q x) → ∃ P ⇔ ∃ Q
∃-cong P⇔Q = record
  { to   = λ (x , y) → x , let record { to   = to   } = P⇔Q x in to   y
  ; from = λ (x , y) → x , let record { from = from } = P⇔Q x in from y
  }

-- _⊎_ preserves logical equivalences.

infixr 1 _⊎-cong_

_⊎-cong_ : A ⇔ C → B ⇔ D → A ⊎ B ⇔ C ⊎ D
A⇔C ⊎-cong B⇔D =
  let record { to = to₁; from = from₁ } = A⇔C
      record { to = to₂; from = from₂ } = B⇔D
  in
  record
    { to   = ⊎-map to₁   to₂
    ; from = ⊎-map from₁ from₂
    }

-- The non-dependent function space preserves logical equivalences.

→-cong : A ⇔ C → B ⇔ D → (A → B) ⇔ (C → D)
→-cong A⇔C B⇔D =
  let record { to = to₁; from = from₁ } = A⇔C
      record { to = to₂; from = from₂ } = B⇔D
  in
  record
    { to   = (to₂   ⊚_) ⊚ (_⊚ from₁)
    ; from = (from₂ ⊚_) ⊚ (_⊚ to₁)
    }

-- Π preserves logical equivalences in its second argument.

∀-cong :
  ((x : A) → P x ⇔ Q x) →
  ((x : A) → P x) ⇔ ((x : A) → Q x)
∀-cong P⇔Q = record
  { to   = λ f x → let record { to   = to   } = P⇔Q x in to   (f x)
  ; from = λ f x → let record { from = from } = P⇔Q x in from (f x)
  }

-- The implicit variant of Π preserves logical equivalences in its
-- second argument.

implicit-∀-cong :
  ({x : A} → P x ⇔ Q x) →
  ({x : A} → P x) ⇔ ({x : A} → Q x)
implicit-∀-cong P⇔Q = record
  { to   = λ f → let record { to   = to   } = P⇔Q in to   f
  ; from = λ f → let record { from = from } = P⇔Q in from f
  }

-- ↑ preserves logical equivalences.

↑-cong : B ⇔ C → ↑ a B ⇔ ↑ a C
↑-cong B⇔C =
  let record { to = to; from = from } = B⇔C in
  record
    { to   = λ (lift x) → lift (to   x)
    ; from = λ (lift x) → lift (from x)
    }

-- _⇔_ preserves logical equivalences.

⇔-cong : A ⇔ B → C ⇔ D → (A ⇔ C) ⇔ (B ⇔ D)
⇔-cong {A = A} {B = B} {C = C} {D = D} A⇔B C⇔D = record
  { to   = λ A⇔C →
             B  ⇔⟨ inverse A⇔B ⟩
             A  ⇔⟨ A⇔C ⟩
             C  ⇔⟨ C⇔D ⟩□
             D  □
  ; from = λ B⇔D →
             A  ⇔⟨ A⇔B ⟩
             B  ⇔⟨ B⇔D ⟩
             D  ⇔⟨ inverse C⇔D ⟩□
             C  □
  }
