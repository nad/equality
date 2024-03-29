------------------------------------------------------------------------
-- Some definitions related to and properties of the Maybe type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Maybe
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Extensionality eq
open import Monad eq

-- A dependent eliminator.

maybe : ∀ {a b} {A : Type a} {B : Maybe A → Type b} →
        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
maybe j n (just x) = j x
maybe j n nothing  = n

-- Is the value just something?

is-just : ∀ {a} {A : Type a} → Maybe A → Bool
is-just = maybe (const true) false

-- Is the value nothing?

is-nothing : ∀ {a} {A : Type a} → Maybe A → Bool
is-nothing = not ∘ is-just

-- Is-just x is a proposition that is inhabited iff x is
-- just something.

Is-just : ∀ {a} {A : Type a} → Maybe A → Type
Is-just = T ∘ is-just

-- Is-nothing x is a proposition that is inhabited iff x is nothing.

Is-nothing : ∀ {a} {A : Type a} → Maybe A → Type
Is-nothing = T ∘ is-nothing

-- Is-just and Is-nothing are mutually exclusive.

not-both-just-and-nothing :
  ∀ {a} {A : Type a} (x : Maybe A) →
  Is-just x → Is-nothing x → ⊥₀
not-both-just-and-nothing (just _) _  ()
not-both-just-and-nothing nothing  () _

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∀ {a b} {A : Type a} {B : Type b} →
         Maybe A → (A → Maybe B) → Maybe B
x >>=′ f = maybe f nothing x

instance

  -- The maybe monad.

  raw-monad : ∀ {ℓ} → Raw-monad (Maybe {a = ℓ})
  Raw-monad.return raw-monad x = just x
  Raw-monad._>>=_ raw-monad    = _>>=′_

  monad : ∀ {ℓ} → Monad (Maybe {a = ℓ})
  Monad.raw-monad      monad              = raw-monad
  Monad.left-identity  monad x f          = refl (f x)
  Monad.right-identity monad nothing      = refl nothing
  Monad.right-identity monad (just x)     = refl (just x)
  Monad.associativity  monad nothing f g  = refl nothing
  Monad.associativity  monad (just x) f g = refl (f x >>= g)

-- The maybe monad transformer.

record MaybeT {d c} (M : Type d → Type c) (A : Type d) : Type c where
  constructor wrap
  field
    run : M (Maybe A)

open MaybeT public

-- Failure.

fail : ∀ {d c} {M : Type d → Type c} ⦃ is-monad : Raw-monad M ⦄ {A} →
       MaybeT M A
run fail = return nothing

-- MaybeT id is pointwise isomorphic to Maybe.

MaybeT-id↔Maybe : ∀ {a} {A : Type a} → MaybeT id A ↔ Maybe A
MaybeT-id↔Maybe = record
  { surjection = record
    { logical-equivalence = record { to = run; from = wrap }
    ; right-inverse-of    = refl
    }
  ; left-inverse-of = refl
  }

instance

  -- MaybeT is a "raw monad" transformer.

  raw-monad-transformer :
    ∀ {d c} → Raw-monad-transformer (MaybeT {d = d} {c = c})

  run (Raw-monad.return (Raw-monad-transformer.transform
                           raw-monad-transformer) x) =
    return (just x)

  run (Raw-monad._>>=_ (Raw-monad-transformer.transform
                          raw-monad-transformer) x f) =
    run x >>= maybe (run ∘ f) (return nothing)

  run (Raw-monad-transformer.liftʳ raw-monad-transformer m) =
    map just m

  transform :
    ∀ {d c} {M : Type d → Type c} ⦃ is-raw-monad : Raw-monad M ⦄ →
    Raw-monad (MaybeT M)
  transform = Raw-monad-transformer.transform raw-monad-transformer

-- MaybeT is a monad transformer (assuming extensionality).

monad-transformer :
  ∀ {d c} →
  Extensionality d c →
  Monad-transformer (MaybeT {d = d} {c = c})

Monad.raw-monad (Monad-transformer.transform (monad-transformer _)) =
  Raw-monad-transformer.transform raw-monad-transformer

Monad.left-identity
  (Monad-transformer.transform (monad-transformer _)) x f = cong wrap (
    return (just x) >>= maybe (run ∘ f) (return nothing)  ≡⟨ left-identity (just x) (maybe (run ∘ f) (return nothing)) ⟩∎
    run (f x)                                             ∎)

Monad.right-identity
  (Monad-transformer.transform (monad-transformer ext)) x = cong wrap (
    run x >>= maybe (return ∘ just) (return nothing)  ≡⟨ cong (run x >>=_) (apply-ext ext (maybe (λ _ → refl _) (refl _))) ⟩
    run x >>= return                                  ≡⟨ right-identity _ ⟩∎
    run x                                             ∎)

Monad.associativity
  (Monad-transformer.transform (monad-transformer ext)) x f g = cong wrap (
    run x >>=
      (maybe (λ x → run (f x) >>= maybe (run ∘ g) (return nothing))
             (return nothing))                                       ≡⟨ cong (run x >>=_) (apply-ext ext (maybe (λ _ → refl _) (

      return nothing                                                      ≡⟨ sym $ left-identity _ _ ⟩∎
      return nothing >>= maybe (run ∘ g) (return nothing)                 ∎))) ⟩

    run x >>= (λ x → maybe (run ∘ f) (return nothing) x >>=
                     maybe (run ∘ g) (return nothing))               ≡⟨ associativity _ _ _ ⟩∎

    (run x >>= maybe (run ∘ f) (return nothing)) >>=
      maybe (run ∘ g) (return nothing)                               ∎)

Monad-transformer.liftᵐ (monad-transformer _) = liftʳ

Monad-transformer.lift-return (monad-transformer _) x = cong wrap (
  map just (return x)  ≡⟨ map-return just x ⟩∎
  return (just x)      ∎)

Monad-transformer.lift->>= (monad-transformer ext) x f = cong wrap (
  map just (x >>= f)                                    ≡⟨ map->>= _ _ _ ⟩
  x >>= map just ∘ f                                    ≡⟨ sym $ >>=-map ext _ _ _ ⟩∎
  map just x >>= maybe (map just ∘ f) (return nothing)  ∎)
