------------------------------------------------------------------------
-- Some definitions related to and properties of the Maybe type
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Maybe
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Monad eq

-- A dependent eliminator.

maybe : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
maybe j n (just x) = j x
maybe j n nothing  = n

instance

  -- The maybe monad.

  monad : ∀ {ℓ} → Monad (Maybe {a = ℓ})
  Raw-monad.return (Monad.raw-monad monad) x  = just x
  Raw-monad._>>=_ (Monad.raw-monad monad) x f = maybe f nothing x
  Monad.left-identity monad x f               = refl (f x)
  Monad.right-identity monad nothing          = refl nothing
  Monad.right-identity monad (just x)         = refl (just x)
  Monad.associativity monad nothing f g       = refl nothing
  Monad.associativity monad (just x) f g      = refl (f x >>= g)

-- The maybe monad transformer.

record MaybeT {d c} (M : Set d → Set c) (A : Set d) : Set c where
  constructor wrap
  field
    run : M (Maybe A)

open MaybeT public

-- MaybeT id is pointwise isomorphic to Maybe.

MaybeT-id↔Maybe : ∀ {a} {A : Set a} → MaybeT id A ↔ Maybe A
MaybeT-id↔Maybe = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ x → run x
      ; from = wrap
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

instance

  -- MaybeT is a "raw monad" transformer.

  raw-monad-transformer :
    ∀ {d c} → Raw-monad-transformer (MaybeT {d = d} {c = c})
  run (Raw-monad.return raw-monad-transformer x)   = return (just x)
  run (Raw-monad._>>=_  raw-monad-transformer x f) =
    run x >>= maybe (run ∘ f) (return nothing)

-- MaybeT is a monad transformer (assuming extensionality).

monad-transformer :
  ∀ {d c} →
  Extensionality d c →
  Monad-transformer (MaybeT {d = d} {c = c})

Monad.raw-monad     (monad-transformer _)     = raw-monad-transformer

Monad.left-identity (monad-transformer _) x f = cong wrap
  (return (just x) >>= maybe (run ∘ f) (return nothing)  ≡⟨ left-identity (just x) (maybe (run ∘ f) (return nothing)) ⟩∎
   run (f x)                                             ∎)

Monad.right-identity (monad-transformer ext) x = cong wrap
  (run x >>= maybe (return ∘ just) (return nothing)  ≡⟨ cong (run x >>=_) (ext (maybe (λ _ → refl _) (refl _))) ⟩
   run x >>= return                                  ≡⟨ right-identity _ ⟩∎
   run x                                             ∎)

Monad.associativity (monad-transformer ext) x f g = cong wrap (
  run x >>=
    (maybe (λ x → run (f x) >>= maybe (run ∘ g) (return nothing))
           (return nothing))                                       ≡⟨ cong (run x >>=_) (ext (maybe (λ _ → refl _) (

    return nothing                                                      ≡⟨ sym $ left-identity _ _ ⟩∎
    return nothing >>= maybe (run ∘ g) (return nothing)                 ∎))) ⟩

  run x >>= (λ x → maybe (run ∘ f) (return nothing) x >>=
                   maybe (run ∘ g) (return nothing))               ≡⟨ associativity _ _ _ ⟩∎

  (run x >>= maybe (run ∘ f) (return nothing)) >>=
    maybe (run ∘ g) (return nothing)                               ∎)

-- Failure.

fail : ∀ {d c} {M : Set d → Set c} ⦃ is-monad : Raw-monad M ⦄ {A} →
       MaybeT M A
fail = wrap (return nothing)
