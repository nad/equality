------------------------------------------------------------------------
-- A universe which includes several kinds of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Function-universe
  {reflexive} (eq : Equality-with-J reflexive) where

open Derived-definitions-and-properties eq
open import Equivalence using (_⇔_; module _⇔_)
private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection using (_↔_; module _↔_)
import Equality.Decision-procedures as ED; open ED eq
import H-level.Closure; open H-level.Closure eq
private
  module Injection where
    import Injection; open Injection eq public
open Injection using (_↣_; module _↣_; Injective)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
private
  module Surjection where
    import Surjection; open Surjection eq public
open Surjection using (_↠_; module _↠_)
private
  module Weak where
    import Weak-equivalence; open Weak-equivalence eq public
open Weak using (_≈_; module _≈_)

------------------------------------------------------------------------
-- The universe

-- The universe includes implications, equivalences, injections,
-- surjections, bijections and weak equivalences.

data Kind : Set where
  implication
    equivalence
    injection
    surjection
    bijection
    weak-equivalence : Kind

-- The interpretation of the universe.

infix 0 _↝[_]_

_↝[_]_ : Set → Kind → Set → Set
A ↝[ implication      ] B = A → B
A ↝[ equivalence      ] B = A ⇔ B
A ↝[ injection        ] B = A ↣ B
A ↝[ surjection       ] B = A ↠ B
A ↝[ bijection        ] B = A ↔ B
A ↝[ weak-equivalence ] B = A ≈ B

-- Bijections can be converted to all kinds of functions.

from-bijection : ∀ {k} {A B : Set} → A ↔ B → A ↝[ k ] B
from-bijection {implication}      = _↔_.to
from-bijection {equivalence}      = _↔_.equivalence
from-bijection {injection}        = _↔_.injection
from-bijection {surjection}       = _↔_.surjection
from-bijection {bijection}        = P.id
from-bijection {weak-equivalence} = Weak.bijection⇒weak-equivalence

-- Weak equivalences can be converted to all kinds of functions.

from-weak-equivalence : ∀ {k} {A B : Set} → A ≈ B → A ↝[ k ] B
from-weak-equivalence {implication}      = _≈_.to
from-weak-equivalence {equivalence}      = _≈_.equivalence
from-weak-equivalence {injection}        = _≈_.injection
from-weak-equivalence {surjection}       = _≈_.surjection
from-weak-equivalence {bijection}        = _≈_.bijection
from-weak-equivalence {weak-equivalence} = P.id

-- All kinds of functions can be converted to implications.

to-implication : ∀ {k} {A B : Set} → A ↝[ k ] B → A → B
to-implication {implication}      = P.id
to-implication {equivalence}      = _⇔_.to
to-implication {injection}        = _↣_.to
to-implication {surjection}       = _↠_.to
to-implication {bijection}        = _↔_.to
to-implication {weak-equivalence} = _≈_.to

------------------------------------------------------------------------
-- Preorder

-- All the different kinds of functions form preorders.

-- Composition.

infixr 9 _∘_

_∘_ : {k : Kind} {A B C : Set} →
      B ↝[ k ] C → A ↝[ k ] B → A ↝[ k ] C
_∘_ {implication}      = λ f g → f ⊚ g
_∘_ {equivalence}      = Equivalence._∘_
_∘_ {injection}        = Injection._∘_
_∘_ {surjection}       = Surjection._∘_
_∘_ {bijection}        = Bijection._∘_
_∘_ {weak-equivalence} = Weak._∘_

-- Identity.

id : ∀ {k} {A : Set} → A ↝[ k ] A
id = from-bijection Bijection.id

-- "Equational" reasoning combinators.

infixr 0 _↝⟨_⟩_ _↔⟨_⟩_ _≈⟨_⟩_
infix  0 finally-↝ finally-↔ finally-≈
infix  0 _□

_↝⟨_⟩_ : {k : Kind} (A : Set) {B C : Set} →
         A ↝[ k ] B → B ↝[ k ] C → A ↝[ k ] C
_ ↝⟨ A↝B ⟩ B↝C = B↝C ∘ A↝B

_↔⟨_⟩_ : {k : Kind} (A : Set) {B C : Set} →
         A ↔ B → B ↝[ k ] C → A ↝[ k ] C
_ ↔⟨ A↔B ⟩ B↝C = _ ↝⟨ from-bijection A↔B ⟩ B↝C

_≈⟨_⟩_ : {k : Kind} (A : Set) {B C : Set} →
         A ≈ B → B ↝[ k ] C → A ↝[ k ] C
_ ≈⟨ A≈B ⟩ B↝C = _ ↝⟨ from-weak-equivalence A≈B ⟩ B↝C

_□ : ∀ {k} (A : Set) → A ↝[ k ] A
A □ = id

finally-↝ : {k : Kind} (A : Set) (B : Set) →
            A ↝[ k ] B → A ↝[ k ] B
finally-↝ _ _ A↝B = A↝B

finally-↔ : {k : Kind} (A : Set) (B : Set) →
            A ↔ B → A ↝[ k ] B
finally-↔ _ _ A↔B = from-bijection A↔B

finally-≈ : {k : Kind} (A : Set) (B : Set) →
            A ≈ B → A ↝[ k ] B
finally-≈ _ _ A≈B = from-weak-equivalence A≈B

syntax finally-↝ A B A↝B = A ↝⟨ A↝B ⟩□ B □
syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩□ B □
syntax finally-≈ A B A≈B = A ≈⟨ A≈B ⟩□ B □

------------------------------------------------------------------------
-- A sub-universe of symmetric kinds of functions

data Symmetric-kind : Set where
  equivalence bijection weak-equivalence : Symmetric-kind

⌊_⌋ : Symmetric-kind → Kind
⌊ equivalence      ⌋ = equivalence
⌊ bijection        ⌋ = bijection
⌊ weak-equivalence ⌋ = weak-equivalence

inverse : {k : Symmetric-kind} {A B : Set} →
          A ↝[ ⌊ k ⌋ ] B → B ↝[ ⌊ k ⌋ ] A
inverse {equivalence}      = Equivalence.inverse
inverse {bijection}        = Bijection.inverse
inverse {weak-equivalence} = Weak.inverse

------------------------------------------------------------------------
-- Lots of properties
------------------------------------------------------------------------

-- Properties of the form A ↝[ k ] B, for arbitrary k, are only stated
-- for bijections; converting to the other forms is easy.

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

-- _⊎_ preserves all kinds of functions.

private

  ⊎-cong-eq : {A₁ A₂ B₁ B₂ : Set} →
              A₁ ⇔ A₂ → B₁ ⇔ B₂ → A₁ ⊎ B₁ ⇔ A₂ ⊎ B₂
  ⊎-cong-eq A₁⇔A₂ B₁⇔B₂ = record
    { to   = ⊎-map (to   A₁⇔A₂) (to   B₁⇔B₂)
    ; from = ⊎-map (from A₁⇔A₂) (from B₁⇔B₂)
    } where open _⇔_

  ⊎-cong-inj : {A₁ A₂ B₁ B₂ : Set} →
               A₁ ↣ A₂ → B₁ ↣ B₂ → A₁ ⊎ B₁ ↣ A₂ ⊎ B₂
  ⊎-cong-inj A₁↣A₂ B₁↣B₂ = record
    { to        = to′
    ; injective = injective′
    }
    where
    open _↣_

    to′ = ⊎-map (to A₁↣A₂) (to B₁↣B₂)

    abstract
      injective′ : Injective to′
      injective′ {x = inj₁ x} {y = inj₁ y} = cong inj₁ ⊚ injective A₁↣A₂ ⊚ ⊎.cancel-inj₁
      injective′ {x = inj₂ x} {y = inj₂ y} = cong inj₂ ⊚ injective B₁↣B₂ ⊚ ⊎.cancel-inj₂
      injective′ {x = inj₁ x} {y = inj₂ y} = ⊥-elim ⊚ ⊎.inj₁≢inj₂
      injective′ {x = inj₂ x} {y = inj₁ y} = ⊥-elim ⊚ ⊎.inj₁≢inj₂ ⊚ sym

  ⊎-cong-surj : {A₁ A₂ B₁ B₂ : Set} →
                A₁ ↠ A₂ → B₁ ↠ B₂ → A₁ ⊎ B₁ ↠ A₂ ⊎ B₂
  ⊎-cong-surj A₁↠A₂ B₁↠B₂ = record
    { equivalence      = ⊎-cong-eq (_↠_.equivalence A₁↠A₂)
                                   (_↠_.equivalence B₁↠B₂)
    ; right-inverse-of =
        [ cong inj₁ ⊚ _↠_.right-inverse-of A₁↠A₂
        , cong inj₂ ⊚ _↠_.right-inverse-of B₁↠B₂
        ]
    }

  ⊎-cong-bij : {A₁ A₂ B₁ B₂ : Set} →
               A₁ ↔ A₂ → B₁ ↔ B₂ → A₁ ⊎ B₁ ↔ A₂ ⊎ B₂
  ⊎-cong-bij A₁↔A₂ B₁↔B₂ = record
    { surjection      = ⊎-cong-surj (_↔_.surjection A₁↔A₂)
                                    (_↔_.surjection B₁↔B₂)
    ; left-inverse-of =
        [ cong inj₁ ⊚ _↔_.left-inverse-of A₁↔A₂
        , cong inj₂ ⊚ _↔_.left-inverse-of B₁↔B₂
        ]
    }

infixr 1 _⊎-cong_

_⊎-cong_ : ∀ {k} {A₁ A₂ B₁ B₂ : Set} →
           A₁ ↝[ k ] A₂ → B₁ ↝[ k ] B₂ → A₁ ⊎ B₁ ↝[ k ] A₂ ⊎ B₂
_⊎-cong_ {implication}      = ⊎-map
_⊎-cong_ {equivalence}      = ⊎-cong-eq
_⊎-cong_ {injection}        = ⊎-cong-inj
_⊎-cong_ {surjection}       = ⊎-cong-surj
_⊎-cong_ {bijection}        = ⊎-cong-bij
_⊎-cong_ {weak-equivalence} = λ A₁≈A₂ B₁≈B₂ →
  from-bijection $ ⊎-cong-bij (from-weak-equivalence A₁≈A₂)
                              (from-weak-equivalence B₁≈B₂)

-- _⊎_ is commutative.

⊎-comm : {A B : Set} → A ⊎ B ↔ B ⊎ A
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

⊎-assoc : {A B C : Set} → A ⊎ (B ⊎ C) ↔ (A ⊎ B) ⊎ C
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
      { to   = [ (λ ()) , id ]
      ; from = inj₂
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = [ (λ ()) , refl ⊚ inj₂ ]
  }

⊎-right-identity : {A : Set} → A ⊎ ⊥ ↔ A
⊎-right-identity {A} =
  A ⊎ ⊥  ↔⟨ ⊎-comm ⟩
  ⊥ ⊎ A  ↔⟨ ⊎-left-identity ⟩□
  A      □

-- For equivalences _⊎_ is also idempotent. (This lemma could be
-- generalised to cover surjections and implications.)

⊎-idempotent : {A : Set} → A ⊎ A ⇔ A
⊎-idempotent = record
  { to   = [ id , id ]
  ; from = inj₁
  }

------------------------------------------------------------------------
-- _×_ is a commutative monoid with a zero

-- _×_ preserves all kinds of functions.

private

  ×-cong-eq : {A₁ A₂ B₁ B₂ : Set} →
              A₁ ⇔ A₂ → B₁ ⇔ B₂ → A₁ × B₁ ⇔ A₂ × B₂
  ×-cong-eq A₁⇔A₂ B₁⇔B₂ = record
    { to   = Σ-map (to   A₁⇔A₂) (to   B₁⇔B₂)
    ; from = Σ-map (from A₁⇔A₂) (from B₁⇔B₂)
    } where open _⇔_

  ×-cong-inj : {A₁ A₂ B₁ B₂ : Set} →
               A₁ ↣ A₂ → B₁ ↣ B₂ → A₁ × B₁ ↣ A₂ × B₂
  ×-cong-inj A₁↣A₂ B₁↣B₂ = record
    { to        = to′
    ; injective = injective′
    }
    where
    open _↣_

    to′ = Σ-map (to A₁↣A₂) (to B₁↣B₂)

    abstract
      injective′ : Injective to′
      injective′ to′-x≡to′-y =
        cong₂ _,_ (injective A₁↣A₂ (cong proj₁ to′-x≡to′-y))
                  (injective B₁↣B₂ (cong proj₂ to′-x≡to′-y))

  ×-cong-surj : {A₁ A₂ B₁ B₂ : Set} →
                A₁ ↠ A₂ → B₁ ↠ B₂ → A₁ × B₁ ↠ A₂ × B₂
  ×-cong-surj A₁↠A₂ B₁↠B₂ = record
    { equivalence      = ×-cong-eq (_↠_.equivalence A₁↠A₂)
                                   (_↠_.equivalence B₁↠B₂)
    ; right-inverse-of = uncurry λ x y →
        cong₂ _,_ (_↠_.right-inverse-of A₁↠A₂ x)
                  (_↠_.right-inverse-of B₁↠B₂ y)
    }

  ×-cong-bij : {A₁ A₂ B₁ B₂ : Set} →
               A₁ ↔ A₂ → B₁ ↔ B₂ → A₁ × B₁ ↔ A₂ × B₂
  ×-cong-bij A₁↔A₂ B₁↔B₂ = record
    { surjection      = ×-cong-surj (_↔_.surjection A₁↔A₂)
                                    (_↔_.surjection B₁↔B₂)
    ; left-inverse-of = uncurry λ x y →
        cong₂ _,_ (_↔_.left-inverse-of A₁↔A₂ x)
                  (_↔_.left-inverse-of B₁↔B₂ y)
    }

infixr 2 _×-cong_

_×-cong_ : ∀ {k} {A₁ A₂ B₁ B₂ : Set} →
           A₁ ↝[ k ] A₂ → B₁ ↝[ k ] B₂ → A₁ × B₁ ↝[ k ] A₂ × B₂
_×-cong_ {implication}      = λ f g → Σ-map f g
_×-cong_ {equivalence}      = ×-cong-eq
_×-cong_ {injection}        = ×-cong-inj
_×-cong_ {surjection}       = ×-cong-surj
_×-cong_ {bijection}        = ×-cong-bij
_×-cong_ {weak-equivalence} = λ A₁≈A₂ B₁≈B₂ →
  from-bijection $ ×-cong-bij (from-weak-equivalence A₁≈A₂)
                              (from-weak-equivalence B₁≈B₂)

-- _×_ is commutative.

×-comm : {A B : Set} → A × B ↔ B × A
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

×-assoc : {A B C : Set} → A × (B × C) ↔ (A × B) × C
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
  ⊤ × A  ↔⟨ ×-left-identity ⟩□
  A      □

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
  ⊥ × A  ↔⟨ ×-left-zero ⟩□
  ⊥      □

------------------------------------------------------------------------
-- Some lemmas related to Σ/∃

-- See also Σ-left-zero and Σ-right-zero above.

-- Σ preserves bijections in its first argument and all kinds of
-- functions in its second argument.

Σ-cong : ∀ {k} {A₁ A₂ : Set} {B₁ : A₁ → Set} {B₂ : A₂ → Set} →
         (A₁↔A₂ : A₁ ↔ A₂) →
         (∀ x → B₁ x ↝[ k ] B₂ (_↔_.to A₁↔A₂ x)) →
         Σ A₁ B₁ ↝[ k ] Σ A₂ B₂
Σ-cong {implication}      A₁↔A₂ = Weak.∃-preserves-functions
                                    (from-bijection A₁↔A₂)
Σ-cong {equivalence}      A₁↔A₂ = Weak.∃-preserves-equivalences
                                    (from-bijection A₁↔A₂)
Σ-cong {injection}        A₁↔A₂ = Weak.∃-preserves-injections
                                    (from-bijection A₁↔A₂)
Σ-cong {surjection}       A₁↔A₂ = Weak.∃-preserves-surjections
                                    (from-bijection A₁↔A₂)
Σ-cong {bijection}        A₁↔A₂ = Weak.∃-preserves-bijections
                                    (from-bijection A₁↔A₂)
Σ-cong {weak-equivalence} A₁↔A₂ = Weak.Σ-preserves
                                    (from-bijection A₁↔A₂)

-- ∃ preserves all kinds of functions. One could define
-- ∃-cong = Σ-cong id, but the resulting "from" functions would
-- contain an unnecessary use of substitutivity, and I want to avoid
-- that.

private

  ∃-cong-impl : {A : Set} {B₁ B₂ : A → Set} →
                (∀ x → B₁ x → B₂ x) → ∃ B₁ → ∃ B₂
  ∃-cong-impl B₁→B₂ = Σ-map id (λ {x} → B₁→B₂ x)

  ∃-cong-eq : {A : Set} {B₁ B₂ : A → Set} →
              (∀ x → B₁ x ⇔ B₂ x) → ∃ B₁ ⇔ ∃ B₂
  ∃-cong-eq B₁⇔B₂ = record
    { to   = ∃-cong-impl (to   ⊚ B₁⇔B₂)
    ; from = ∃-cong-impl (from ⊚ B₁⇔B₂)
    } where open _⇔_

  ∃-cong-surj : {A : Set} {B₁ B₂ : A → Set} →
                (∀ x → B₁ x ↠ B₂ x) → ∃ B₁ ↠ ∃ B₂
  ∃-cong-surj B₁↠B₂ = record
    { equivalence      = ∃-cong-eq (_↠_.equivalence ⊚ B₁↠B₂)
    ; right-inverse-of = uncurry λ x y →
        cong (_,_ x) (_↠_.right-inverse-of (B₁↠B₂ x) y)
    }

  ∃-cong-bij : {A : Set} {B₁ B₂ : A → Set} →
               (∀ x → B₁ x ↔ B₂ x) → ∃ B₁ ↔ ∃ B₂
  ∃-cong-bij B₁↔B₂ = record
    { surjection      = ∃-cong-surj (_↔_.surjection ⊚ B₁↔B₂)
    ; left-inverse-of = uncurry λ x y →
        cong (_,_ x) (_↔_.left-inverse-of (B₁↔B₂ x) y)
    }

∃-cong : ∀ {k} {A : Set} {B₁ B₂ : A → Set} →
         (∀ x → B₁ x ↝[ k ] B₂ x) → ∃ B₁ ↝[ k ] ∃ B₂
∃-cong {implication}      = ∃-cong-impl
∃-cong {equivalence}      = ∃-cong-eq
∃-cong {injection}        = Σ-cong id
∃-cong {surjection}       = ∃-cong-surj
∃-cong {bijection}        = ∃-cong-bij
∃-cong {weak-equivalence} = λ B₁≈B₂ →
  from-bijection $ ∃-cong-bij (from-weak-equivalence ⊚ B₁≈B₂)

-- ∃ distributes "from the left" over _⊎_.

∃-⊎-distrib-left : {A : Set} {B C : A → Set} →
                   (∃ λ x → B x ⊎ C x) ↔ ∃ B ⊎ ∃ C
∃-⊎-distrib-left = record
  { surjection = record
    { equivalence = record
      { to   = uncurry λ x → [ inj₁ ⊚ _,_ x , inj₂ ⊚ _,_ x ]
      ; from = [ Σ-map id inj₁ , Σ-map id inj₂ ]
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of =
      uncurry λ x → [ refl ⊚ _,_ x ⊚ inj₁ , refl ⊚ _,_ x ⊚ inj₂ ]
  }

-- ∃ also distributes "from the right" over _⊎_.

∃-⊎-distrib-right : {A B : Set} {C : A ⊎ B → Set} →
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

  from = [ Σ-map inj₁ id , Σ-map inj₂ id ]

  from∘to : ∀ p → from (to p) ≡ p
  from∘to (inj₁ x , y) = refl _
  from∘to (inj₂ x , y) = refl _

-- ∃ is "commutative".

∃-comm : {A B : Set} {C : A → B → Set} →
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

∃-intro : {A : Set} (B : A → Set) (x : A) →
          B x ↔ ∃ λ y → B y × y ≡ x
∃-intro B x =
  B x                    ↔⟨ inverse ×-right-identity ⟩
  B x × ⊤                ↔⟨ id ×-cong inverse (contractible↔⊤ (singleton-contractible x)) ⟩
  B x × (∃ λ y → y ≡ x)  ↔⟨ ∃-comm ⟩
  (∃ λ y → B x × y ≡ x)  ↔⟨ ∃-cong (λ _ → ×-comm) ⟩
  (∃ λ y → y ≡ x × B x)  ↔⟨ ∃-cong (λ y → ∃-cong (λ y≡x → subst (λ x → B x ↔ B y) y≡x id)) ⟩
  (∃ λ y → y ≡ x × B y)  ↔⟨ ∃-cong (λ _ → ×-comm) ⟩□
  (∃ λ y → B y × y ≡ x)  □

------------------------------------------------------------------------
-- _⊎_ and _×_ form a commutative semiring

-- _×_ distributes from the left over _⊎_.

×-⊎-distrib-left : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
×-⊎-distrib-left = ∃-⊎-distrib-left

-- _×_ distributes from the right over _⊎_.

×-⊎-distrib-right : {A B C : Set} → (A ⊎ B) × C ↔ (A × C) ⊎ (B × C)
×-⊎-distrib-right = ∃-⊎-distrib-right

------------------------------------------------------------------------
-- A property related to ℕ

-- The natural numbers are isomorphic to the natural numbers extended
-- with another element.

ℕ↔ℕ⊎⊤ : ℕ ↔ ℕ ⊎ ⊤
ℕ↔ℕ⊎⊤ = record
  { surjection = record
    { equivalence = record
      { to   = ℕ-rec (inj₂ tt) (λ n _ → inj₁ n)
      ; from = [ suc , const zero ]
      }
    ; right-inverse-of = [ refl ⊚ inj₁ , refl ⊚ inj₂ ]
    }
  ; left-inverse-of = ℕ-rec (refl 0) (λ n _ → refl (suc n))
  }

------------------------------------------------------------------------
-- Left cancellation for _⊎_

-- In general _⊎_ is not left cancellative.

¬-⊎-left-cancellative :
  ∀ k → ¬ ((A B C : Set) → A ⊎ B ↝[ k ] A ⊎ C → B ↝[ k ] C)
¬-⊎-left-cancellative k cancel =
  ¬B→C $ to-implication $ cancel A B C (from-bijection A⊎B↔A⊎C)
  where
  A = ℕ
  B = ⊤
  C = ⊥

  A⊎B↔A⊎C : A ⊎ B ↔ A ⊎ C
  A⊎B↔A⊎C =
    ℕ ⊎ ⊤  ↔⟨ inverse ℕ↔ℕ⊎⊤ ⟩
    ℕ      ↔⟨ inverse ⊎-right-identity ⟩
    ℕ ⊎ ⊥  □

  ¬B→C : ¬ (B → C)
  ¬B→C B→C = B→C tt

-- However, it is left cancellative for certain well-behaved
-- bijections.

-- A function is "left-persistent" if all "left" results of the
-- function are mapped to new "left" results.

Left-persistent : {A B C : Set} → (A ⊎ B → A ⊎ C) → Set
Left-persistent f =
  ∀ {a a′ c} → f (inj₁ a) ≡ inj₁ a′ → f (inj₁ a′) ≢ inj₂ c

⊎-left-cancellative :
  {A B C : Set} →
  (inv : A ⊎ B ↔ A ⊎ C) →
  Left-persistent (_↔_.to   inv) →
  Left-persistent (_↔_.from inv) →
  B ↔ C
⊎-left-cancellative inv to-hyp from-hyp = record
  { surjection = record
    { equivalence = record
      { to   = f          inv  from-hyp
      ; from = f (inverse inv) to-hyp
      }
    ; right-inverse-of = f∘f (inverse inv) from-hyp to-hyp
    }
  ; left-inverse-of    = f∘f          inv  to-hyp from-hyp
  }
  where
  open _↔_

  f : ∀ {A B C : Set} →
      (inv : A ⊎ B ↔ A ⊎ C) →
      Left-persistent (_↔_.from inv) →
      B → C
  f inv hyp b with to inv (inj₂ b) | left-inverse-of inv (inj₂ b)
  f inv hyp b | inj₂ b′ | _     = b′
  f inv hyp b | inj₁ a  | ₁→₂ with to inv (inj₁ a) | left-inverse-of inv (inj₁ a)
  f inv hyp b | inj₁ a  | ₁→₂ | inj₂ b′ | ₁→₁ = b′
  f inv hyp b | inj₁ a  | ₁→₂ | inj₁ a′ | ₁→₁ = ⊥-elim $ hyp ₁→₁ ₁→₂

  abstract

    f∘f : ∀ {A B C : Set} →
          (inv : A ⊎ B ↔ A ⊎ C) →
          (to-hyp   : Left-persistent (_↔_.to   inv)) →
          (from-hyp : Left-persistent (_↔_.from inv)) →
          ∀ b → f (inverse inv) to-hyp (f inv from-hyp b) ≡ b
    f∘f inv to-hyp from-hyp b with to inv (inj₂ b) | left-inverse-of inv (inj₂ b)
    f∘f inv to-hyp from-hyp b | inj₂ b′ | ₁→₂ with from inv (inj₂ b′) | right-inverse-of inv (inj₂ b′)
    f∘f inv to-hyp from-hyp b | inj₂ b′ | ₁→₂ | inj₂ b″ | _ = ⊎.cancel-inj₂ ₁→₂
    f∘f inv to-hyp from-hyp b | inj₂ b′ | ₁→₂ | inj₁ a  | _ = ⊥-elim $ ⊎.inj₁≢inj₂ ₁→₂
    f∘f inv to-hyp from-hyp b | inj₁ a  | ₁→₂ with to inv (inj₁ a) | left-inverse-of inv (inj₁ a)
    f∘f inv to-hyp from-hyp b | inj₁ a  | ₁→₂ | inj₁ a′ | ₁→₁ = ⊥-elim $ from-hyp ₁→₁ ₁→₂
    f∘f inv to-hyp from-hyp b | inj₁ a  | ₁→₂ | inj₂ b′ | ₁→₁ with from inv (inj₂ b′) | right-inverse-of inv (inj₂ b′)
    f∘f inv to-hyp from-hyp b | inj₁ a  | ₁→₂ | inj₂ b′ | ₁→₁ | inj₂ b″ | _    = ⊥-elim $ ⊎.inj₁≢inj₂ $ sym ₁→₁
    f∘f inv to-hyp from-hyp b | inj₁ a  | ₁→₂ | inj₂ b′ | ₁→₁ | inj₁ a′ | ₁→₂′ with from inv (inj₁ a′) | right-inverse-of inv (inj₁ a′)
    f∘f inv to-hyp from-hyp b | inj₁ a  | ₁→₂ | inj₂ b′ | ₁→₁ | inj₁ a′ | ₁→₂′ | inj₁ a″ | ₁→₁′ = ⊥-elim $ to-hyp ₁→₁′ ₁→₂′
    f∘f inv to-hyp from-hyp b | inj₁ a  | ₁→₂ | inj₂ b′ | ₁→₁ | inj₁ a′ | ₁→₂′ | inj₂ b″ | ₂→₁  = ⊎.cancel-inj₂ (
      inj₂ b″                      ≡⟨ sym $ left-inverse-of inv _ ⟩
      from inv (to inv (inj₂ b″))  ≡⟨ cong (from inv) ₂→₁ ⟩
      from inv (inj₁ a′)           ≡⟨ cong (from inv ⊚ inj₁) $ ⊎.cancel-inj₁ ₁→₁ ⟩
      from inv (inj₁ a)            ≡⟨ ₁→₂ ⟩∎
      inj₂ b                       ∎)

-- This property does not generalise to equivalences.

¬-⊎-left-cancellative′ :
  ¬ ({A B C : Set} →
     (eq : A ⊎ B ⇔ A ⊎ C) →
     Left-persistent (_⇔_.to   eq) →
     Left-persistent (_⇔_.from eq) →
     B ⇔ C)
¬-⊎-left-cancellative′ cancel =
  _⇔_.to (cancel equiv to-hyp from-hyp) tt
  where
  A = ⊤
  B = ⊤
  C = ⊥

  equiv : A ⊎ B ⇔ A ⊎ C
  equiv =
    ⊤ ⊎ ⊤  ↝⟨ ⊎-idempotent ⟩
    ⊤      ↔⟨ inverse ⊎-right-identity ⟩
    ⊤ ⊎ ⊥  □

  to-hyp : Left-persistent (_⇔_.to equiv)
  to-hyp {c = ()} _ _

  from-hyp : Left-persistent (_⇔_.from equiv)
  from-hyp _ ₁→₂ = ⊎.inj₁≢inj₂ ₁→₂
