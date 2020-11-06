------------------------------------------------------------------------
-- The reader monad transformer
------------------------------------------------------------------------

-- The interface is based on that used by the "mtl" package on
-- Hackage.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Monad.Reader
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open Derived-definitions-and-properties eq
open import Monad eq

-- The reader monad transformer, defined using a wrapper type to make
-- instance resolution easier.

record ReaderT {s} (S : Type s)
               (M : Type s → Type s)
               (A : Type s) : Type s where
  constructor wrap
  field
    run : S → M A

open ReaderT public

instance

  -- ReaderT is a "raw monad" transformer.

  raw-monad-transformer :
    ∀ {s} {S : Type s} →
    Raw-monad-transformer (ReaderT S)
  run (Raw-monad.return (Raw-monad-transformer.transform
                           raw-monad-transformer) x) =
    λ _ → return x
  run (Raw-monad._>>=_ (Raw-monad-transformer.transform
                          raw-monad-transformer) x f) =
    λ s → run x s >>= λ x → run (f x) s

  run (Raw-monad-transformer.liftʳ raw-monad-transformer m) =
    λ _ → m

  transform : ∀ {s} {S : Type s} {M} ⦃ is-raw-monad : Raw-monad M ⦄ →
              Raw-monad (ReaderT S M)
  transform = Raw-monad-transformer.transform raw-monad-transformer

-- ReaderT is a monad transformer (assuming extensionality).

monad-transformer :
  ∀ {s} {S : Type s} →
  Extensionality s s →
  Monad-transformer (ReaderT S)
Monad.raw-monad (Monad-transformer.transform (monad-transformer _)) =
  Raw-monad-transformer.transform raw-monad-transformer

Monad.left-identity (Monad-transformer.transform
                       (monad-transformer ext)) x f =
  cong wrap (apply-ext ext λ s →
    (return x >>= λ x → run (f x) s)  ≡⟨ left-identity _ _ ⟩∎
    run (f x) s                       ∎)

Monad.right-identity (Monad-transformer.transform
                        (monad-transformer ext)) x =
  cong wrap (apply-ext ext λ s →
    run x s >>= return  ≡⟨ right-identity _ ⟩∎
    run x s             ∎)

Monad.associativity (Monad-transformer.transform
                       (monad-transformer ext)) x f g =
  cong wrap (apply-ext ext λ s →
    (run x s >>= λ x → run (f x) s >>= λ x → run (g x) s)    ≡⟨ associativity _ _ _ ⟩∎
    ((run x s >>= λ x → run (f x) s) >>= λ x → run (g x) s)  ∎)

Monad-transformer.liftᵐ (monad-transformer _) = liftʳ

Monad-transformer.lift-return (monad-transformer ext) x =
  cong wrap (apply-ext ext λ _ →
    return x  ∎)

Monad-transformer.lift->>= (monad-transformer ext) x f =
  cong wrap (apply-ext ext λ _ →
    x >>= f  ∎)

-- Returns the "state".

ask : ∀ {s} {S : Type s} {M} ⦃ is-monad : Raw-monad M ⦄ →
      ReaderT S M S
run ask = return

-- Modifies the "state" in a given computation.

local : ∀ {s} {S : Type s} {M A} ⦃ is-monad : Raw-monad M ⦄ →
        (S → S) → ReaderT S M A → ReaderT S M A
run (local f m) = run m ∘ f
