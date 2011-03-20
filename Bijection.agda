------------------------------------------------------------------------
-- Bijections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Bijection
  {reflexive} (eq : Equality-with-J reflexive) where

open Derived-definitions-and-properties eq
import Equivalence
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
private
  module Surjection where
    import Surjection; open Surjection eq public
open Surjection using (_↠_; module _↠_)

infix 0 _↔_

------------------------------------------------------------------------
-- Bijections

record _↔_ (From To : Set) : Set where
  field
    surjection : From ↠ To

  open _↠_ surjection

  field
    left-inverse-of : ∀ x → from (to x) ≡ x

  open _↠_ surjection public

------------------------------------------------------------------------
-- Equivalence

-- _↔_ is an equivalence relation.

id : ∀ {A} → A ↔ A
id = record
  { surjection      = Surjection.id
  ; left-inverse-of = refl
  }

inverse : ∀ {A B} → A ↔ B → B ↔ A
inverse A↔B = record
  { surjection = record
    { equivalence      = Equivalence.inverse equivalence
    ; right-inverse-of = left-inverse-of
    }
  ; left-inverse-of = right-inverse-of
  } where open _↔_ A↔B

infixr 9 _∘_

_∘_ : ∀ {A B C} → B ↔ C → A ↔ B → A ↔ C
f ∘ g = record
  { surjection      = Surjection._∘_ (surjection f) (surjection g)
  ; left-inverse-of = from∘to
  }
  where
  open _↔_

  abstract
    from∘to = λ x →
      from g (from f (to f (to g x)))  ≡⟨ cong (from g) (left-inverse-of f (to g x)) ⟩
      from g (to g x)                  ≡⟨ left-inverse-of g x ⟩∎
      x                                ∎

-- "Equational" reasoning combinators.

infix  0 finally-↔
infixr 0 _↔⟨_⟩_

_↔⟨_⟩_ : ∀ A {B C} → A ↔ B → B ↔ C → A ↔ C
_ ↔⟨ A↔B ⟩ B↔C = B↔C ∘ A↔B

finally-↔ : ∀ A B → A ↔ B → A ↔ B
finally-↔ _ _ A↔B = A↔B

syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩∎ B ∎

------------------------------------------------------------------------
-- A lemma related to ⊤

-- Contractible sets are isomorphic to ⊤.

contractible↔⊤ : {A : Set} → Contractible A → A ↔ ⊤
contractible↔⊤ c = record
  { surjection = record
    { equivalence = record
      { to   = const tt
      ; from = const $ proj₁ c
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = proj₂ c
  }

------------------------------------------------------------------------
-- _⊎_ is a commutative monoid

-- _⊎_ preserves bijections.

infixr 1 _⊎-cong_

_⊎-cong_ : {A₁ A₂ B₁ B₂ : Set} →
           A₁ ↔ A₂ → B₁ ↔ B₂ → (A₁ ⊎ B₁) ↔ (A₂ ⊎ B₂)
A₁↔A₂ ⊎-cong B₁↔B₂ = record
  { surjection = record
    { equivalence = record
      { to   = [ inj₁ ⊚ to   A₁↔A₂ , inj₂ ⊚ to   B₁↔B₂ ]
      ; from = [ inj₁ ⊚ from A₁↔A₂ , inj₂ ⊚ from B₁↔B₂ ]
      }
    ; right-inverse-of =
        [ cong inj₁ ⊚ right-inverse-of A₁↔A₂
        , cong inj₂ ⊚ right-inverse-of B₁↔B₂
        ]
    }
  ; left-inverse-of =
      [ cong inj₁ ⊚ left-inverse-of A₁↔A₂
      , cong inj₂ ⊚ left-inverse-of B₁↔B₂
      ]
  } where open _↔_

-- _⊎_ is commutative.

⊎-comm : {A B : Set} → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm = record
  { surjection = record
    { equivalence = record
      { to   = [ inj₂ , inj₁ ]
      ; from = [ inj₂ , inj₁ ]
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
  }

-- _⊎_ is associative.

⊎-assoc : {A B C : Set} → (A ⊎ (B ⊎ C)) ↔ ((A ⊎ B) ⊎ C)
⊎-assoc = record
  { surjection = record
    { equivalence = record
      { to   = [ inj₁ ⊚ inj₁ , [ inj₁ ⊚ inj₂ , inj₂ ] ]
      ; from = [ [ inj₁ , inj₂ ⊚ inj₁ ] , inj₂ ⊚ inj₂ ]
      }
    ; right-inverse-of =
        [ [ refl ⊚ inj₁ ⊚ inj₁ , refl ⊚ inj₁ ⊚ inj₂ ] , refl ⊚ inj₂ ]
    }
  ; left-inverse-of =
      [ refl ⊚ inj₁ , [ refl ⊚ inj₂ ⊚ inj₁ , refl ⊚ inj₂ ⊚ inj₂ ] ]
  }

-- ⊥ is a left and right identity of _⊎_.

⊎-left-identity : {A : Set} → ⊥ ⊎ A ↔ A
⊎-left-identity = record
  { surjection = record
    { equivalence = record
      { to   = [ (λ ()) , P.id ]
      ; from = inj₂
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = [ (λ ()) , refl ⊚ inj₂ ]
  }

⊎-right-identity : {A : Set} → A ⊎ ⊥ ↔ A
⊎-right-identity {A} =
  A ⊎ ⊥  ↔⟨ ⊎-comm ⟩
  ⊥ ⊎ A  ↔⟨ ⊎-left-identity ⟩∎
  A      ∎

------------------------------------------------------------------------
-- _×_ is a commutative monoid with a zero

-- _×_ preserves bijections.

infixr 1 _×-cong_

_×-cong_ : {A₁ A₂ B₁ B₂ : Set} →
           A₁ ↔ A₂ → B₁ ↔ B₂ → (A₁ × B₁) ↔ (A₂ × B₂)
A₁↔A₂ ×-cong B₁↔B₂ = record
  { surjection = record
    { equivalence = record
      { to   = Σ-map (to   A₁↔A₂) (to   B₁↔B₂)
      ; from = Σ-map (from A₁↔A₂) (from B₁↔B₂)
      }
    ; right-inverse-of = uncurry λ x y →
        cong₂ _,_ (right-inverse-of A₁↔A₂ x) (right-inverse-of B₁↔B₂ y)
    }
  ; left-inverse-of = uncurry λ x y →
      cong₂ _,_ (left-inverse-of A₁↔A₂ x) (left-inverse-of B₁↔B₂ y)
  } where open _↔_

-- _×_ is commutative.

×-comm : {A B : Set} → (A × B) ↔ (B × A)
×-comm = record
  { surjection = record
    { equivalence = record
      { to   = uncurry λ x y → (y , x)
      ; from = uncurry λ x y → (y , x)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- _×_ is associative.

×-assoc : {A B C : Set} → (A × (B × C)) ↔ ((A × B) × C)
×-assoc = record
  { surjection = record
    { equivalence = record
      { to   = uncurry λ x → uncurry λ y z → ((x , y) , z)
      ; from = uncurry (flip λ z → uncurry λ x y → (x , (y , z)))
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- ⊤ is a left and right identity of _×_ and Σ.

Σ-left-identity : {A : ⊤ → Set} → Σ ⊤ A ↔ A tt
Σ-left-identity = record
  { surjection = record
    { equivalence = record
      { to   = proj₂
      ; from = λ x → (tt , x)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

×-left-identity : {A : Set} → ⊤ × A ↔ A
×-left-identity = Σ-left-identity

×-right-identity : {A : Set} → A × ⊤ ↔ A
×-right-identity {A} =
  A × ⊤  ↔⟨ ×-comm ⟩
  ⊤ × A  ↔⟨ ×-left-identity ⟩∎
  A      ∎

-- ⊥ is a left and right zero of _×_ and Σ.

Σ-left-zero : {A : ⊥ → Set} → Σ ⊥ A ↔ ⊥
Σ-left-zero = record
  { surjection = record
    { equivalence = record
      { to   = proj₁
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = ⊥-elim ⊚ proj₁
  }

×-left-zero : {A : Set} → ⊥ × A ↔ ⊥
×-left-zero = Σ-left-zero

×-right-zero : {A : Set} → A × ⊥ ↔ ⊥
×-right-zero {A} =
  A × ⊥  ↔⟨ ×-comm ⟩
  ⊥ × A  ↔⟨ ×-left-zero ⟩∎
  ⊥      ∎

------------------------------------------------------------------------
-- Some lemmas related to ∃

-- See also Σ-left-zero and Σ-right-zero above.

-- ∃ preserves surjections.
--
-- For a more general property, see Weak-equivalence.Σ-preserves.

∃-cong : ∀ {A : Set} {B₁ B₂ : A → Set} →
         (∀ x → B₁ x ↔ B₂ x) → ∃ B₁ ↔ ∃ B₂
∃-cong B₁↔B₂ = record
  { surjection      = Surjection.∃-cong (surjection ⊚ B₁↔B₂)
  ; left-inverse-of = left-inverse-of′
  }
  where
  open _↔_

  abstract
    left-inverse-of′ = λ p →
      cong (_,_ (proj₁ p)) $
           left-inverse-of (B₁↔B₂ (proj₁ p)) (proj₂ p)

-- ∃ distributes "from the left" over _⊎_.

∃-⊎-distrib-left : ∀ {A : Set} {B C : A → Set} →
                   (∃ λ x → B x ⊎ C x) ↔ ∃ B ⊎ ∃ C
∃-⊎-distrib-left = record
  { surjection = record
    { equivalence = record
      { to   = uncurry λ x → [ inj₁ ⊚ _,_ x , inj₂ ⊚ _,_ x ]
      ; from = [ Σ-map P.id inj₁ , Σ-map P.id inj₂ ]
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of =
      uncurry λ x → [ refl ⊚ _,_ x ⊚ inj₁ , refl ⊚ _,_ x ⊚ inj₂ ]
  }

-- ∃ also distributes "from the right" over _⊎_.

∃-⊎-distrib-right : ∀ {A B : Set} {C : A ⊎ B → Set} →
                    Σ (A ⊎ B) C ↔ Σ A (C ⊚ inj₁) ⊎ Σ B (C ⊚ inj₂)
∃-⊎-distrib-right {A} {B} {C} = record
  { surjection = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of = from∘to
  }
  where
  to : Σ (A ⊎ B) C → Σ A (C ⊚ inj₁) ⊎ Σ B (C ⊚ inj₂)
  to (inj₁ x , y) = inj₁ (x , y)
  to (inj₂ x , y) = inj₂ (x , y)

  from = [ Σ-map inj₁ P.id , Σ-map inj₂ P.id ]

  from∘to : ∀ p → from (to p) ≡ p
  from∘to (inj₁ x , y) = refl _
  from∘to (inj₂ x , y) = refl _

-- ∃ is "commutative".

∃-comm : ∀ {A B : Set} {C : A → B → Set} →
         (∃ λ x → ∃ λ y → C x y) ↔ (∃ λ y → ∃ λ x → C x y)
∃-comm = record
  { surjection = record
    { equivalence = record
      { to   = uncurry λ x → uncurry λ y z → (y , (x , z))
      ; from = uncurry λ x → uncurry λ y z → (y , (x , z))
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- One can introduce an existential by also introducing an equality.

∃-intro : ∀ {A : Set} (B : A → Set) (x : A) →
          B x ↔ ∃ λ y → B y × y ≡ x
∃-intro B x =
  B x                    ↔⟨ inverse ×-right-identity ⟩
  B x × ⊤                ↔⟨ id ×-cong inverse (contractible↔⊤ (singleton-contractible x)) ⟩
  B x × (∃ λ y → y ≡ x)  ↔⟨ ∃-comm ⟩
  (∃ λ y → B x × y ≡ x)  ↔⟨ ∃-cong (λ _ → ×-comm) ⟩
  (∃ λ y → y ≡ x × B x)  ↔⟨ ∃-cong (λ y → ∃-cong (λ y≡x → subst (λ x → B x ↔ B y) y≡x id)) ⟩
  (∃ λ y → y ≡ x × B y)  ↔⟨ ∃-cong (λ _ → ×-comm) ⟩∎
  (∃ λ y → B y × y ≡ x)  ∎

------------------------------------------------------------------------
-- _⊎_ and _×_ form a commutative semiring

-- _×_ distributes from the left over _⊎_.

×-⊎-distrib-left : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
×-⊎-distrib-left = ∃-⊎-distrib-left

-- _×_ distributes from the right over _⊎_.

×-⊎-distrib-right : {A B C : Set} → (A ⊎ B) × C ↔ (A × C) ⊎ (B × C)
×-⊎-distrib-right = ∃-⊎-distrib-right
