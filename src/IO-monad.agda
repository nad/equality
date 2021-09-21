------------------------------------------------------------------------
-- IO
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module IO-monad where

open import Monad.Raw
open import Prelude
open import String

------------------------------------------------------------------------
-- The IO type former

open import Agda.Builtin.IO public using (IO)

------------------------------------------------------------------------
-- The IO monad

postulate
  returnIO : ∀ {a} {A : Type a} → A → IO A
  bindIO   : ∀ {a b} {A : Type a} {B : Type b} →
             IO A → (A → IO B) → IO B

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

-- Note that the GHC code below ignores potential problems. For
-- instance, putStr could raise an exception.

{-# COMPILE GHC putStr      = Data.Text.IO.putStr #-}
{-# COMPILE GHC putStrLn    = Data.Text.IO.putStrLn #-}
{-# COMPILE GHC exitFailure = System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs     = fmap (map Data.Text.pack)
                                System.Environment.getArgs #-}
