------------------------------------------------------------------------
-- Modules that can (perhaps) not be type-checked in safe mode
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Unsafe where

-- Support for using propositional equality with the rewriting
-- machinery.

import Equality.Propositional.Rewriting

-- IO.

import IO

-- Strings.

import String
