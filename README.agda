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

-- "Safe" code that uses --without-K.

import README.Safe.Without-K

-- "Safe" code that uses --cubical.

import README.Safe.Cubical

-- "Safe" code that uses --cubical and --guardedness.

import README.Safe.Cubical.Guardedness

-- "Safe" code that uses --cubical and --prop.

import README.Safe.Cubical.Prop

-- "Safe" code that uses --with-K.

import README.Safe.With-K

-- Code which might depend on potentially unsafe features (other than
-- --sized-types).

import README.Unsafe

-- Code which is "safe", except for the use of --sized-types.

import README.Unsafe.Sized-types

-- Code related to the paper "Logical properties of a modality for
-- erasure". This code uses both --cubical and --with-K, but not at
-- the same time, except in the module README.Erased, which for that
-- reason cannot use --safe.

import README.Erased
