------------------------------------------------------------------------
-- Modules that can (perhaps) not be type-checked in safe mode
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Unsafe where

-- Strings.

import String

-- IO.

import IO-monad
