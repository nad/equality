------------------------------------------------------------------------
-- Safe modules that use --sized-types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module README.Safe.Sized-types where

-- Support for sized types.

import Prelude.Size

-- Some results that could not be placed in Function-universe because
-- they make use of --sized-types.

import Function-universe.Size

-- Conatural numbers.

import Conat

-- Colists.

import Colist

-- M-types.

import M
