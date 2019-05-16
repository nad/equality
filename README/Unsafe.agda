------------------------------------------------------------------------
-- Modules that can (perhaps) not be type-checked in safe mode
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Unsafe where

-- IO.

import IO-monad

-- Strings.

import String
