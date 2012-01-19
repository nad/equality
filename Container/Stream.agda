------------------------------------------------------------------------
-- The stream container
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container.Stream where

open import Container
open import Prelude

-- Streams.

Stream : Container lzero
Stream = ⊤ ▷ const ℕ
