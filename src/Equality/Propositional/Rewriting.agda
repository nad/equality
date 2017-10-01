------------------------------------------------------------------------
-- Support for using propositional equality with the rewriting
-- machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Equality.Propositional.Rewriting where

open import Equality.Propositional

{-# BUILTIN REWRITE _≡_ #-}
