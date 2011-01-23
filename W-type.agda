------------------------------------------------------------------------
-- W-types
------------------------------------------------------------------------

module W-type where

open import Relation.Nullary

-- The family of W-types.

data W (A : Set) (B : A → Set) : Set where
  sup : (x : A) (f : B x → W A B) → W A B

-- Projections.

head : ∀ {A B} → W A B → A
head (sup x f) = x

tail : ∀ {A B} → (x : W A B) → B (head x) → W A B
tail (sup x f) = f

-- If B is always inhabited, then W A B is empty.

empty : ∀ {A B} → (∀ x → B x) → ¬ W A B
empty b (sup x f) = empty b (f (b x))
