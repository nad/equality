------------------------------------------------------------------------
-- The state monad transformer
------------------------------------------------------------------------

-- The interface is based on that used by the "mtl" package on
-- Hackage.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Monad.State
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open Derived-definitions-and-properties eq
open import Monad eq

-- The state monad transformer, defined using a wrapper type to make
-- instance resolution easier.

record StateT {s} (S : Type s)
              (M : Type s → Type s)
              (A : Type s) : Type s where
  constructor wrap
  field
    run : S → M (A × S)

open StateT public

instance

  -- StateT is a "raw monad" transformer.

  raw-monad-transformer :
    ∀ {s} {S : Type s} →
    Raw-monad-transformer (StateT S)
  run (Raw-monad.return (Raw-monad-transformer.transform
                           raw-monad-transformer) x) =
    λ s → return (x , s)
  run (Raw-monad._>>=_ (Raw-monad-transformer.transform
                          raw-monad-transformer) x f) =
    λ s → run x s >>= λ { (x , s) → run (f x) s }

  run (Raw-monad-transformer.liftʳ raw-monad-transformer m) =
    λ s → map (_, s) m

  transform : ∀ {s} {S : Type s} {M} ⦃ is-raw-monad : Raw-monad M ⦄ →
              Raw-monad (StateT S M)
  transform = Raw-monad-transformer.transform raw-monad-transformer

-- StateT is a monad transformer (assuming extensionality).

monad-transformer :
  ∀ {s} {S : Type s} →
  Extensionality s s →
  Monad-transformer (StateT S)
Monad.raw-monad (Monad-transformer.transform (monad-transformer _)) =
  Raw-monad-transformer.transform raw-monad-transformer

Monad.left-identity (Monad-transformer.transform
                       (monad-transformer ext)) x f =
  cong wrap (apply-ext ext λ s →
    (return (x , s) >>= λ { (x , s) → run (f x) s })  ≡⟨ left-identity _ _ ⟩∎
    run (f x) s                                       ∎)

Monad.right-identity (Monad-transformer.transform
                        (monad-transformer ext)) x =
  cong wrap (apply-ext ext λ s →
    run x s >>= (λ { (x , s) → return (x , s) })  ≡⟨ right-identity _ ⟩∎
    run x s                                       ∎)

Monad.associativity (Monad-transformer.transform
                       (monad-transformer ext)) x f g =
  cong wrap (apply-ext ext λ s →
    (run x s >>= λ { (x , s) →
     run (f x) s >>= λ { (x , s) →
     run (g x) s } })                                             ≡⟨ associativity _ _ _ ⟩∎

    ((run x s >>= λ { (x , s) → run (f x) s }) >>= λ { (x , s) →
     run (g x) s })                                               ∎)

Monad-transformer.liftᵐ (monad-transformer _) = liftʳ

Monad-transformer.lift-return (monad-transformer ext) x =
  cong wrap (apply-ext ext λ s →
    map (_, s) (return x)  ≡⟨ map-return _ _ ⟩∎
    return (x , s)         ∎)

Monad-transformer.lift->>= (monad-transformer ext) x f =
  cong wrap (apply-ext ext λ s →
    map (_, s) (x >>= f)                                 ≡⟨ map->>= _ _ _ ⟩
    (x >>= λ x → map (_, s) (f x))                       ≡⟨ sym $ >>=-map ext _ _ _ ⟩∎
    (map (_, s) x >>= λ { (x , s) → map (_, s) (f x) })  ∎)

-- Returns the state.

get : ∀ {s} {S : Type s} {M} ⦃ is-monad : Raw-monad M ⦄ →
      StateT S M S
run get = λ s → return (s , s)

-- Types the state.

set : ∀ {s} {S : Type s} {M} ⦃ is-monad : Raw-monad M ⦄ →
      S → StateT S M (↑ _ ⊤)
run (set s) = λ _ → return (_ , s)

-- Modifies the state.

modify :
  ∀ {s} {S : Type s} {M} ⦃ is-monad : Raw-monad M ⦄ →
  (S → S) → StateT S M (↑ _ ⊤)
modify f = get >>= set ∘ f
