------------------------------------------------------------------------
-- Support for sized types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Prelude.Size where

open import Agda.Builtin.Size public
  using (Size; Size<_; ∞)
  renaming (SizeUniv to Size-universe; ↑_ to ssuc)
