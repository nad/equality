------------------------------------------------------------------------
-- IO
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module IO where

open import Equality.Propositional
open import Prelude
open import String

open import Monad equality-with-J

------------------------------------------------------------------------
-- The IO type former

open import Agda.Builtin.IO public using (IO)

------------------------------------------------------------------------
-- The IO monad

postulate
  returnIO : ∀ {a} {A : Set a} → A → IO A
  bindIO   : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC returnIO = \_ _ -> return    #-}
{-# COMPILE GHC bindIO   = \_ _ _ _ -> (>>=) #-}

instance

  io-monad : ∀ {ℓ} → Raw-monad (IO {a = ℓ})
  Raw-monad.return io-monad = returnIO
  Raw-monad._>>=_  io-monad = bindIO

------------------------------------------------------------------------
-- Some IO primitives

-- Note that some commands may raise exceptions when executed.

postulate
  putStr      : String → IO ⊤
  putStrLn    : String → IO ⊤
  exitFailure : IO ⊤
  getArgs     : IO (List String)

{-# FOREIGN GHC
  import qualified Data.Text
  import qualified Data.Text.IO
  import qualified System.Environment
  import qualified System.Exit
#-}

{-# COMPILE GHC putStr      = Data.Text.IO.putStr #-}
{-# COMPILE GHC putStrLn    = Data.Text.IO.putStrLn #-}
{-# COMPILE GHC exitFailure = System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs     = fmap (map Data.Text.pack)
                                System.Environment.getArgs #-}
