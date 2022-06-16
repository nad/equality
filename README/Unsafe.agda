------------------------------------------------------------------------
-- Modules that can (perhaps) not be type-checked in safe mode, and
-- do not use --sized-types
------------------------------------------------------------------------

{-# OPTIONS --without-K --irrelevant-projections #-}

module README.Unsafe where

-- Strings.

import String

-- IO.

import IO-monad

-- Squashing using irrelevance (with irrelevant projections).

import Squash.Irrelevance
