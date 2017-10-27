------------------------------------------------------------------------
-- Definitions related to sizes
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Size where

open import Prelude

------------------------------------------------------------------------
-- Size elimination

-- A trick is used to implement size elimination. This trick was
-- suggested to me by Andrea Vezzosi.

-- A data type wrapping Size<_.
--
-- If this wrapper is removed from the definition of elim below, then
-- that definition is rejected.

data [Size<_] (i : Size) : Set where
  box : Size< i → [Size< i ]

-- A projection.

unbox : ∀ {i} → [Size< i ] → Size< i
unbox (box j) = j

-- Size elimination.

elim :
  ∀ {p}
  (P : Size → Set p) →
  (∀ i → ((j : [Size< i ]) → P (unbox j)) → P i) →
  ∀ i → P i
elim P f i = f i λ { (box j) → elim P f j }
