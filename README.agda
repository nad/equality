------------------------------------------------------------------------
-- Experiments related to equality
--
-- Nils Anders Danielsson
--
-- Some files have been developed in collaboration with others, see
-- the individual files.
------------------------------------------------------------------------

{-# OPTIONS --cubical --with-K --guardedness --sized-types --prop #-}

module README where

-- "Safe" code that uses --cubical-compatible.

import README.Safe.Cubical-compatible

-- "Safe" code that uses --cubical-compatible and --erased-matches.

import README.Safe.Cubical-compatible.Erased-matches

-- "Safe" code that uses --cubical-compatible and --prop.

import README.Safe.Cubical-compatible.Prop

-- "Safe" code that uses --cubical-compatible, --prop and
-- --erased-matches.

import README.Safe.Cubical-compatible.Prop.Erased-matches

-- "Safe" code that uses --erased-cubical.

import README.Safe.Cubical.Erased

-- "Safe" code that uses --erased-cubical and --guardedness.

import README.Safe.Cubical.Erased.Guardedness

-- "Safe" code that uses --erased-cubical and --prop.

import README.Safe.Cubical.Erased.Prop

-- "Safe" code that uses --cubical.

import README.Safe.Cubical

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
