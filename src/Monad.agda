------------------------------------------------------------------------
-- Monads
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Monad
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Function-universe eq using (inverse)

------------------------------------------------------------------------
-- Basic definitions

-- Raw monads.

record Raw-monad {d c} (M : Set d → Set c) : Set (lsuc d ⊔ c) where
  constructor mk-raw-monad
  infixl 5 _>>=_
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B

open Raw-monad ⦃ … ⦄ public

-- Monads.

record Monad {d c} (M : Set d → Set c) : Set (lsuc d ⊔ c) where
  constructor mk-monad
  field
    instance
      ⦃ raw-monad ⦄ : Raw-monad M

    left-identity  : ∀ {A B} (x : A) (f : A → M B) →
                     return x >>= f ≡ f x
    right-identity : ∀ {A} (x : M A) →
                     x >>= return ≡ x
    associativity  : ∀ {A B C} →
                     (x : M A) (f : A → M B) (g : B → M C) →
                     x >>= (λ x → f x >>= g) ≡ x >>= f >>= g

open Monad ⦃ … ⦄ public

-- Monad transformers.

Raw-monad-transformer :
  ∀ {d c} → ((Set d → Set c) → (Set d → Set c)) → Set (lsuc (c ⊔ d))
Raw-monad-transformer F =
  ∀ {M} ⦃ is-raw-monad : Raw-monad M ⦄ → Raw-monad (F M)

Monad-transformer :
  ∀ {d c} → ((Set d → Set c) → (Set d → Set c)) → Set (lsuc (c ⊔ d))
Monad-transformer F = ∀ {M} ⦃ is-monad : Monad M ⦄ → Monad (F M)

------------------------------------------------------------------------
-- Preservation lemmas

-- If F and G are pointwise logically equivalent, then Raw-monad F and
-- Raw-monad G are logically equivalent.

⇔→raw⇔raw : ∀ {a f g} {F : Set a → Set f} {G : Set a → Set g} →
            (∀ x → F x ⇔ G x) → Raw-monad F ⇔ Raw-monad G
⇔→raw⇔raw {a} = λ F⇔G → record
  { to   = to F⇔G
  ; from = to (inverse ∘ F⇔G)
  }
  where
  to : ∀ {f g} {F : Set a → Set f} {G : Set a → Set g} →
       (∀ x → F x ⇔ G x) → Raw-monad F → Raw-monad G
  Raw-monad.return (to F⇔G F-monad) x =
    _⇔_.to (F⇔G _) (F.return x)
    where
    module F = Raw-monad F-monad

  Raw-monad._>>=_ (to F⇔G F-monad) x f =
    _⇔_.to (F⇔G _) (_⇔_.from (F⇔G _) x F.>>= λ x →
                    _⇔_.from (F⇔G _) (f x))
    where
    module F = Raw-monad F-monad

-- If F and G are pointwise isomorphic, then Raw-monad F and
-- Raw-monad G are isomorphic (assuming extensionality).

↔→raw↔raw : ∀ {a f g} →
            Extensionality (lsuc a ⊔ f ⊔ g) (lsuc a ⊔ f ⊔ g) →
            {F : Set a → Set f} {G : Set a → Set g} →
            (∀ x → F x ↔ G x) → Raw-monad F ↔ Raw-monad G
↔→raw↔raw {a} = λ {f g} ext F↔G → record
  { surjection = record
    { logical-equivalence = ⇔→raw⇔raw (_↔_.logical-equivalence ∘ F↔G)
    ; right-inverse-of    = to∘to (lower-extensionality f f ext)
                                  (inverse ∘ F↔G)
    }
  ; left-inverse-of = to∘to (lower-extensionality g g ext) F↔G
  }
  where
  to∘to :
    ∀ {f g} {F : Set a → Set f} {G : Set a → Set g} →
    Extensionality (lsuc a ⊔ f) (lsuc a ⊔ f) →
    (F↔G : ∀ x → F x ↔ G x) (F-monad : Raw-monad F) →
    let eq = ⇔→raw⇔raw (_↔_.logical-equivalence ∘ F↔G) in
    _⇔_.from eq (_⇔_.to eq F-monad) ≡ F-monad
  to∘to {f} ext F↔G (mk-raw-monad return _>>=_) = cong₂ mk-raw-monad
    (implicit-extensionality (lower-extensionality f (lsuc a) ext) λ _ →
     lower-extensionality _ (lsuc a) ext λ x →

       _↔_.from (F↔G _) (_↔_.to (F↔G _) (return x))  ≡⟨ _↔_.left-inverse-of (F↔G _) _ ⟩∎
       return x                                      ∎)

    (implicit-extensionality (lower-extensionality f lzero    ext) λ _ →
     implicit-extensionality (lower-extensionality f (lsuc a) ext) λ _ →
     lower-extensionality (lsuc a) (lsuc a) ext λ x →
     lower-extensionality (lsuc a) (lsuc a) ext λ f →

       _↔_.from (F↔G _) (_↔_.to (F↔G _)
         (_↔_.from (F↔G _) (_↔_.to (F↔G _) x) >>= λ x →
          _↔_.from (F↔G _) (_↔_.to (F↔G _) (f x))))      ≡⟨ _↔_.left-inverse-of (F↔G _) _ ⟩

       (_↔_.from (F↔G _) (_↔_.to (F↔G _) x) >>= λ x →
        _↔_.from (F↔G _) (_↔_.to (F↔G _) (f x)))         ≡⟨ cong₂ _>>=_ (_↔_.left-inverse-of (F↔G _) _)
                                                                        (lower-extensionality _ (lsuc a) ext λ _ →
                                                                         _↔_.left-inverse-of (F↔G _) _) ⟩∎
       x >>= f                                           ∎)

-- If F and G are pointwise isomorphic, then Monad F and Monad G are
-- logically equivalent (assuming extensionality).

↔→⇔ : ∀ {a f g} →
      Extensionality a (f ⊔ g) →
      {F : Set a → Set f} {G : Set a → Set g} →
      (∀ x → F x ↔ G x) → Monad F ⇔ Monad G
↔→⇔ {a} = λ {f g} ext F↔G → record
  { to   = to (lower-extensionality lzero g ext) F↔G
  ; from = to (lower-extensionality lzero f ext) (inverse ∘ F↔G)
  }
  where
  to : ∀ {f g} {F : Set a → Set f} {G : Set a → Set g} →
       Extensionality a f →
       (∀ x → F x ↔ G x) → Monad F → Monad G
  Monad.raw-monad (to ext F↔G F-monad) =
    _⇔_.to (⇔→raw⇔raw (_↔_.logical-equivalence ∘ F↔G)) F.raw-monad
    where
    module F = Monad F-monad

  Monad.left-identity (to ext F↔G F-monad) x f =
    _↔_.to (F↔G _)
      (_↔_.from (F↔G _) (_↔_.to (F↔G _) (FR.return x)) FR.>>= λ x →
       _↔_.from (F↔G _) (f x))                                        ≡⟨ cong (λ y → _↔_.to (F↔G _) (y FR.>>= _)) (_↔_.left-inverse-of (F↔G _) _) ⟩

    _↔_.to (F↔G _) (FR.return x FR.>>= λ x → _↔_.from (F↔G _) (f x))  ≡⟨ cong (_↔_.to (F↔G _)) (FM.left-identity _ _) ⟩

    _↔_.to (F↔G _) (_↔_.from (F↔G _) (f x))                           ≡⟨ _↔_.right-inverse-of (F↔G _) _ ⟩∎

    f x                                                               ∎
    where
    module FM = Monad F-monad
    module FR = Raw-monad FM.raw-monad

  Monad.right-identity (to ext F↔G F-monad) x =
    _↔_.to (F↔G _) (_↔_.from (F↔G _) x FR.>>= λ x →
                    _↔_.from (F↔G _) (_↔_.to (F↔G _) (FR.return x)))  ≡⟨ cong (λ g → _↔_.to (F↔G _) (_ FR.>>= g))
                                                                              (ext λ _ → _↔_.left-inverse-of (F↔G _) _) ⟩
    _↔_.to (F↔G _) (_↔_.from (F↔G _) x FR.>>= FR.return)              ≡⟨ cong (_↔_.to (F↔G _)) (FM.right-identity _) ⟩

    _↔_.to (F↔G _) (_↔_.from (F↔G _) x)                               ≡⟨ _↔_.right-inverse-of (F↔G _) _ ⟩∎

    x                                                                 ∎
    where
    module FM = Monad F-monad
    module FR = Raw-monad FM.raw-monad

  Monad.associativity (to ext F↔G F-monad) x f g =
    _↔_.to (F↔G _)
      (_↔_.from (F↔G _) x FR.>>= λ x →
       _↔_.from (F↔G _) (_↔_.to (F↔G _)
         (_↔_.from (F↔G _) (f x) FR.>>= λ x → _↔_.from (F↔G _) (g x))))  ≡⟨ cong (λ g → _↔_.to (F↔G _) (_↔_.from (F↔G _) x FR.>>= g))
                                                                                 (ext λ _ → _↔_.left-inverse-of (F↔G _) _) ⟩
    _↔_.to (F↔G _)
      (_↔_.from (F↔G _) x FR.>>= λ x →
       _↔_.from (F↔G _) (f x) FR.>>= λ x → _↔_.from (F↔G _) (g x))       ≡⟨ cong (_↔_.to (F↔G _)) (FM.associativity _ _ _) ⟩

    _↔_.to (F↔G _)
      ((_↔_.from (F↔G _) x FR.>>= λ x →
        _↔_.from (F↔G _) (f x)) FR.>>= λ x →
       _↔_.from (F↔G _) (g x))                                           ≡⟨ cong (λ y → _↔_.to (F↔G _) (y FR.>>= _))
                                                                                 (sym $ _↔_.left-inverse-of (F↔G _) _) ⟩∎
    _↔_.to (F↔G _)
      (_↔_.from (F↔G _) (_↔_.to (F↔G _)
         (_↔_.from (F↔G _) x FR.>>= λ x →
          _↔_.from (F↔G _) (f x))) FR.>>= λ x →
       _↔_.from (F↔G _) (g x))                                           ∎
    where
    module FM = Monad F-monad
    module FR = Raw-monad FM.raw-monad

------------------------------------------------------------------------
-- Identity monads

-- The identity monad.

identity-monad : ∀ {ℓ} → Monad {d = ℓ} id
Raw-monad.return (Monad.raw-monad identity-monad) x   = x
Raw-monad._>>=_  (Monad.raw-monad identity-monad) x f = f x
Monad.left-identity  identity-monad x f               = refl (f x)
Monad.right-identity identity-monad x                 = refl x
Monad.associativity  identity-monad x f g             = refl (g (f x))

-- The identity monad, defined using a wrapper type to make instance
-- resolution easier.

record Id {a} (A : Set a) : Set a where
  constructor wrap
  field
    run : A

open Id public

instance

  identity-monad′ : ∀ {ℓ} → Monad {d = ℓ} Id
  run (Raw-monad.return (Monad.raw-monad identity-monad′) x)   = x
  run (Raw-monad._>>=_  (Monad.raw-monad identity-monad′) x f) = run (f (run x))
  Monad.left-identity  identity-monad′ x f   = cong wrap (refl (run (f x)))
  Monad.right-identity identity-monad′ x     = cong wrap (refl (run x))
  Monad.associativity  identity-monad′ x f g = cong wrap (refl (run (g (run (f (run x))))))