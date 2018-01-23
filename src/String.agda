------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module String where

open import Prelude

------------------------------------------------------------------------
-- The String type

open import Agda.Builtin.String public using (String)

------------------------------------------------------------------------
-- Helper code used below

private

  -- A variant of Maybe that matches the Haskell Maybe type.

  data HMaybe (A : Set) : Set where
    Nothing : HMaybe A
    Just    : A → HMaybe A

  {-# COMPILE GHC HMaybe = data Maybe (Nothing | Just) #-}

  -- A conversion function.

  hmaybe-to-maybe : ∀ {A} → HMaybe A → Maybe A
  hmaybe-to-maybe Nothing  = nothing
  hmaybe-to-maybe (Just x) = just x

------------------------------------------------------------------------
-- Operations on strings

-- Implemented using the FFI. These operations do not compute at
-- compile-time, and are only supported by the GHC backend.

{-# FOREIGN GHC
  import qualified Data.Text
  #-}

mutual

  -- Tries to parse the given string as a natural number. Accepts
  -- whatever the Haskell Read instance for Integer accepts, except
  -- for negative numbers.

  parseℕ : String → Maybe ℕ
  parseℕ = hmaybe-to-maybe ∘ parseℕ′

  private
    postulate
      parseℕ′ : String → HMaybe ℕ

{-# COMPILE GHC parseℕ′ =
  \s -> case reads (Data.Text.unpack s) of
          { [(x, "")] | x >= 0 -> Just (x :: Integer)
          ; _                  -> Nothing
          }
  #-}

-- Turns natural numbers into strings.

postulate
  prettyℕ : ℕ → String

{-# COMPILE GHC prettyℕ =
  \n -> Data.Text.pack (show (n :: Integer))
  #-}
