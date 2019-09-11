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

-- Code which might depend on potentially unsafe features.

import README.Unsafe
