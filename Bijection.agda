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

-- ⊤ is a left and right identity of _×_.

×-left-identity : {A : Set} → ⊤ × A ↔ A
×-left-identity = record
  { surjection = record
    { equivalence = record
      { to   = proj₂
      ; from = λ x → (tt , x)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

×-right-identity : {A : Set} → A × ⊤ ↔ A
×-right-identity {A} =
  A × ⊤  ↔⟨ ×-comm ⟩
  ⊤ × A  ↔⟨ ×-left-identity ⟩∎
  A      ∎

-- ⊥ is a left and right zero of _×_.

×-left-zero : {A : Set} → ⊥ × A ↔ ⊥
×-left-zero = record
  { surjection = record
    { equivalence = record
      { to   = proj₁
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = ⊥-elim ⊚ proj₁
  }

×-right-zero : {A : Set} → A × ⊥ ↔ ⊥
×-right-zero {A} =
  A × ⊥  ↔⟨ ×-comm ⟩
  ⊥ × A  ↔⟨ ×-left-zero ⟩∎
  ⊥      ∎

------------------------------------------------------------------------
-- _⊎_ and _×_ form a commutative semiring

-- _×_ distributes from the left over _⊎_.

×-⊎-distrib-left : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
×-⊎-distrib-left = record
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

-- _×_ distributes from the right over _⊎_.

×-⊎-distrib-right : {A B C : Set} → (A ⊎ B) × C ↔ (A × C) ⊎ (B × C)
×-⊎-distrib-right {A} {B} {C} =
  (A ⊎ B) × C        ↔⟨ ×-comm ⟩
  C × (A ⊎ B)        ↔⟨ ×-⊎-distrib-left ⟩
  (C × A) ⊎ (C × B)  ↔⟨ ×-comm ⊎-cong ×-comm ⟩∎
  (A × C) ⊎ (B × C)  ∎
