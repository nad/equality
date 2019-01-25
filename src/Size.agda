------------------------------------------------------------------------
-- Support for sized types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Size where

open import Agda.Builtin.Size public
  using (Size; Size<_; ∞)
  renaming (SizeU to Size-universe; ↑_ to ssuc)
