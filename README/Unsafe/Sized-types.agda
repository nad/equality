------------------------------------------------------------------------
-- Modules that are not safe because they use --sized-types
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module README.Unsafe.Sized-types where

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
