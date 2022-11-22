------------------------------------------------------------------------
-- Safe modules that use --cubical-compatible and --erased-matches
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --erased-matches #-}

module README.Safe.Cubical-compatible.Erased-matches where

-- Results related to accessibility that are implemented using
-- --erased-matches.

import Accessibility.Erased-matches

-- Some results that hold for a modality, implemented using
-- --erased-matches.

import Modality.Erased-matches

-- Results related to Erased that are implemented using
-- --erased-matches.

import Erased.Erased-matches
