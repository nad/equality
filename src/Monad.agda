------------------------------------------------------------------------
-- Monads
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Monad
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Extensionality eq
open import Function-universe eq using (inverse)

------------------------------------------------------------------------
-- Basic definitions

-- Raw monads and raw monad transformers.

open import Monad.Raw public

-- Monads.

record Monad {d c} (M : Type d → Type c) : Type (lsuc d ⊔ c) where
  constructor mk
  field
    ⦃ raw-monad ⦄  : Raw-monad M

    left-identity  : ∀ {A B} (x : A) (f : A → M B) →
                     return x >>= f ≡ f x
    right-identity : ∀ {A} (x : M A) →
                     x >>= return ≡ x
    associativity  : ∀ {A B C} →
                     (x : M A) (f : A → M B) (g : B → M C) →
                     x >>= (λ x → f x >>= g) ≡ x >>= f >>= g

  -- Monads are functors.

  map-id : ∀ {A} (x : M A) → map id x ≡ x
  map-id x =
    x >>= return ∘ id  ≡⟨⟩
    x >>= return       ≡⟨ right-identity _ ⟩∎
    x                  ∎

  map-∘ : Extensionality d c →
          ∀ {A B C} (f : B → C) (g : A → B) (x : M A) →
          map (f ∘ g) x ≡ map f (map g x)
  map-∘ ext f g x =
    x >>= return ∘ (f ∘ g)                     ≡⟨ cong (x >>=_) (apply-ext ext λ _ → sym $ left-identity _ _) ⟩
    x >>= (λ x → return (g x) >>= return ∘ f)  ≡⟨ associativity _ _ _ ⟩∎
    (x >>= return ∘ g) >>= return ∘ f          ∎

  -- More lemmas.

  map-return : ∀ {A B} (f : A → B) (x : A) →
               map {M = M} f (return x) ≡ return (f x)
  map-return f x =
    return x >>= return ∘ f  ≡⟨ left-identity _ _ ⟩∎
    return (f x)             ∎

  map->>= : ∀ {A B C} (f : B → C) (x : M A) (g : A → M B) →
            map f (x >>= g) ≡ x >>= map f ∘ g
  map->>= f x g =
    x >>= g >>= return ∘ f            ≡⟨ sym $ associativity _ _ _ ⟩
    x >>= (λ x → g x >>= return ∘ f)  ≡⟨⟩
    x >>= (λ x → map f (g x))         ≡⟨ refl _ ⟩∎
    x >>= map f ∘ g                   ∎

  >>=-map : Extensionality d c →
            ∀ {A B C} (f : A → B) (x : M A) (g : B → M C) →
            map f x >>= g ≡ x >>= g ∘ f
  >>=-map ext f x g =
    (x >>= return ∘ f) >>= g          ≡⟨ sym $ associativity _ _ _ ⟩
    x >>= (λ x → return (f x) >>= g)  ≡⟨ cong (x >>=_) (apply-ext ext λ _ → left-identity _ _) ⟩∎
    x >>= g ∘ f                       ∎

open Monad ⦃ … ⦄ public hiding (raw-monad)

-- Monad transformers.

record Monad-transformer
         {d c₁ c₂} (F : (Type d → Type c₁) → (Type d → Type c₂)) :
         Type (lsuc (c₁ ⊔ d) ⊔ c₂) where
  constructor mk
  field
    transform : ∀ {M}   ⦃ is-monad : Monad M ⦄ → Monad (F M)
    liftᵐ     : ∀ {M A} ⦃ is-monad : Monad M ⦄ → M A → F M A

    lift-return :
      ∀ {M A} ⦃ is-monad : Monad M ⦄ (x : A) →
      let module M = Raw-monad (Monad.raw-monad transform) in
      liftᵐ {M = M} (return x) ≡ M.return x

    lift->>= :
      ∀ {M A B} ⦃ is-monad : Monad M ⦄
      (x : M A) (f : A → M B) →
      let module M = Raw-monad (Monad.raw-monad transform) in
      liftᵐ (x >>= f) ≡ liftᵐ x M.>>= liftᵐ ∘ f

open Monad-transformer ⦃ … ⦄ public using (liftᵐ; lift-return; lift->>=)

------------------------------------------------------------------------
-- Preservation lemmas

-- If F and G are pointwise logically equivalent, then Raw-monad F and
-- Raw-monad G are logically equivalent.

⇔→raw⇔raw : ∀ {a f g} {F : Type a → Type f} {G : Type a → Type g} →
            (∀ x → F x ⇔ G x) → Raw-monad F ⇔ Raw-monad G
⇔→raw⇔raw {a} = λ F⇔G → record
  { to   = to F⇔G
  ; from = to (inverse ∘ F⇔G)
  }
  where
  to : ∀ {f g} {F : Type a → Type f} {G : Type a → Type g} →
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
            {F : Type a → Type f} {G : Type a → Type g} →
            (∀ x → F x ↔ G x) → Raw-monad F ↔ Raw-monad G
↔→raw↔raw {a} {f} {g} = λ ext F↔G → record
  { surjection = record
    { logical-equivalence = ⇔→raw⇔raw (_↔_.logical-equivalence ∘ F↔G)
    ; right-inverse-of    = to∘to (lower-extensionality f f ext)
                                  (inverse ∘ F↔G)
    }
  ; left-inverse-of = to∘to (lower-extensionality g g ext) F↔G
  }
  where
  to∘to :
    ∀ {f g} {F : Type a → Type f} {G : Type a → Type g} →
    Extensionality (lsuc a ⊔ f) (lsuc a ⊔ f) →
    (F↔G : ∀ x → F x ↔ G x) (F-monad : Raw-monad F) →
    let eq = ⇔→raw⇔raw (_↔_.logical-equivalence ∘ F↔G) in
    _⇔_.from eq (_⇔_.to eq F-monad) ≡ F-monad
  to∘to {f} ext F↔G (mk return _>>=_) = cong₂ mk
    (implicit-extensionality (lower-extensionality f (lsuc a) ext) λ _ →
     apply-ext (lower-extensionality _ (lsuc a) ext) λ x →

       _↔_.from (F↔G _) (_↔_.to (F↔G _) (return x))  ≡⟨ _↔_.left-inverse-of (F↔G _) _ ⟩∎
       return x                                      ∎)

    (implicit-extensionality (lower-extensionality f lzero    ext) λ _ →
     implicit-extensionality (lower-extensionality f (lsuc a) ext) λ _ →
     apply-ext (lower-extensionality (lsuc a) (lsuc a) ext) λ x →
     apply-ext (lower-extensionality (lsuc a) (lsuc a) ext) λ f →

       _↔_.from (F↔G _) (_↔_.to (F↔G _)
         (_↔_.from (F↔G _) (_↔_.to (F↔G _) x) >>= λ x →
          _↔_.from (F↔G _) (_↔_.to (F↔G _) (f x))))      ≡⟨ _↔_.left-inverse-of (F↔G _) _ ⟩

       (_↔_.from (F↔G _) (_↔_.to (F↔G _) x) >>= λ x →
        _↔_.from (F↔G _) (_↔_.to (F↔G _) (f x)))         ≡⟨ cong₂ _>>=_ (_↔_.left-inverse-of (F↔G _) _)
                                                                        (apply-ext (lower-extensionality _ (lsuc a) ext) λ _ →
                                                                         _↔_.left-inverse-of (F↔G _) _) ⟩∎
       x >>= f                                           ∎)

-- If F and G are pointwise isomorphic, then Monad F and Monad G are
-- logically equivalent (assuming extensionality).

↔→⇔ : ∀ {a f g} →
      Extensionality a (f ⊔ g) →
      {F : Type a → Type f} {G : Type a → Type g} →
      (∀ x → F x ↔ G x) → Monad F ⇔ Monad G
↔→⇔ {a} {f} {g} = λ ext F↔G → record
  { to   = to (lower-extensionality lzero g ext) F↔G
  ; from = to (lower-extensionality lzero f ext) (inverse ∘ F↔G)
  }
  where
  to : ∀ {f g} {F : Type a → Type f} {G : Type a → Type g} →
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
                                                                              (apply-ext ext λ _ → _↔_.left-inverse-of (F↔G _) _) ⟩
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
                                                                                 (apply-ext ext λ _ → _↔_.left-inverse-of (F↔G _) _) ⟩
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

record Id {a} (A : Type a) : Type a where
  constructor wrap
  field
    run : A

open Id public

instance

  Id-raw-monad : ∀ {ℓ} → Raw-monad {d = ℓ} Id
  run (Raw-monad.return Id-raw-monad x)   = x
  run (Raw-monad._>>=_  Id-raw-monad x f) = run (f (run x))

  Id-monad : ∀ {ℓ} → Monad {d = ℓ} Id
  Monad.raw-monad      Id-monad       = Id-raw-monad
  Monad.left-identity  Id-monad x f   = cong wrap (refl (run (f x)))
  Monad.right-identity Id-monad x     = cong wrap (refl (run x))
  Monad.associativity  Id-monad x f g = cong wrap (refl (run (g (run (f (run x))))))
