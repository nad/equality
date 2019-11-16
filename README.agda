------------------------------------------------------------------------
-- Experiments related to equality
--
-- Nils Anders Danielsson
--
-- Some files have been developed in collaboration with others, see
-- the individual files.
------------------------------------------------------------------------

{-# OPTIONS --cubical --with-K --prop #-}

module README where

-- "Safe" code that does not use --with-K.

import README.Safe

-- "Safe" code that uses --with-K.

import README.Safe.With-K

-- Code related to the paper "Logical properties of a modality for
-- erasure". This code uses both --cubical and --with-K, but not at
-- the same time, except in the module README.Erased, which for that
-- reason cannot use --safe.

import README.Erased

-- Code which might depend on potentially unsafe features.

import README.Unsafe
