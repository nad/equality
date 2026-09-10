------------------------------------------------------------------------
-- Safe modules that use --with-K and --erased-matches=unrestricted
------------------------------------------------------------------------

{-# OPTIONS --safe --with-K --erased-matches=unrestricted #-}

module README.Safe.With-K where

-- Some theory of Erased, developed using the K rule, propositional
-- equality and --erased-matches=unrestricted.

import Erased.With-K

-- Erased univalence is incompatible with certain features.

import Univalence-axiom.Incompatible
