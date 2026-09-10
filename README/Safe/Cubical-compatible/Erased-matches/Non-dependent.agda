------------------------------------------------------------------------
-- Safe modules that use --cubical-compatible and
-- --erased-matches=non-dependent
------------------------------------------------------------------------

{-# OPTIONS
      --safe --cubical-compatible --erased-matches=non-dependent #-}

module README.Safe.Cubical-compatible.Erased-matches.Non-dependent where

-- Results related to accessibility that are implemented using
-- --erased-matches=non-dependent.

import Accessibility.Erased-matches

-- Some results that hold for a modality, implemented using
-- --erased-matches=non-dependent.

import Modality.Erased-matches

-- Results related to Erased that are implemented using
-- --erased-matches=non-dependent.

import Erased.Erased-matches
