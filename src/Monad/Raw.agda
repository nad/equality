------------------------------------------------------------------------
-- Raw monads
------------------------------------------------------------------------

-- Note that this module is not parametrised by an axiomatisation of
-- equality. This module is reexported from Monad.

{-# OPTIONS --cubical-compatible --safe #-}

module Monad.Raw where

open import Prelude

-- Raw monads.

record Raw-monad {d c} (M : Type d → Type c) : Type (lsuc d ⊔ c) where
  constructor mk
  infixl 6 _⟨$⟩_ _⊛_
  infixl 5 _>>=_ _>>_
  infixr 5 _=<<_
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B

  -- Variants of _>>=_.

  _>>_ : ∀ {A B} → M A → M B → M B
  x >> y = x >>= const y

  _=<<_ : ∀ {A B} → (A → M B) → M A → M B
  _=<<_ = flip _>>=_

  -- A map function.

  map : ∀ {A B} → (A → B) → M A → M B
  map f x = x >>= return ∘ f

  -- A synonym.

  _⟨$⟩_ : ∀ {A B} → (A → B) → M A → M B
  _⟨$⟩_ = map

  -- Applicative functor application.

  _⊛_ : ∀ {A B} → M (A → B) → M A → M B
  f ⊛ x = f >>= λ f → x >>= λ x → return (f x)

  -- The sequence function (for lists).

  sequence : ∀ {A} → List (M A) → M (List A)
  sequence []       = return []
  sequence (x ∷ xs) = _∷_ ⟨$⟩ x ⊛ sequence xs

open Raw-monad ⦃ … ⦄ public

-- Raw monad transformers.

record Raw-monad-transformer
         {d c₁ c₂} (F : (Type d → Type c₁) → (Type d → Type c₂)) :
         Type (lsuc (c₁ ⊔ d) ⊔ c₂) where
  constructor mk
  field
    transform : ∀ {M}   ⦃ is-raw-monad : Raw-monad M ⦄ → Raw-monad (F M)
    liftʳ     : ∀ {M A} ⦃ is-raw-monad : Raw-monad M ⦄ → M A → F M A

open Raw-monad-transformer ⦃ … ⦄ public using (liftʳ)
