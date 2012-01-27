------------------------------------------------------------------------
-- A universe which includes several kinds of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Function-universe
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Equivalence using (_⇔_; module _⇔_)
private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection using (_↔_; module _↔_)
import Equality.Decision-procedures as ED; open ED eq
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

_↝[_]_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Kind → Set ℓ₂ → Set _
A ↝[ implication      ] B = A → B
A ↝[ equivalence      ] B = A ⇔ B
A ↝[ injection        ] B = A ↣ B
A ↝[ surjection       ] B = A ↠ B
A ↝[ bijection        ] B = A ↔ B
A ↝[ weak-equivalence ] B = A ≈ B

-- Bijections can be converted to all kinds of functions.

from-bijection : ∀ {k a b} {A : Set a} {B : Set b} →
                 A ↔ B → A ↝[ k ] B
from-bijection {implication}      = _↔_.to
from-bijection {equivalence}      = _↔_.equivalence
from-bijection {injection}        = _↔_.injection
from-bijection {surjection}       = _↔_.surjection
from-bijection {bijection}        = P.id
from-bijection {weak-equivalence} = Weak.bijection⇒weak-equivalence

-- Weak equivalences can be converted to all kinds of functions.

from-weak-equivalence : ∀ {k a b} {A : Set a} {B : Set b} →
                        A ≈ B → A ↝[ k ] B
from-weak-equivalence {implication}      = _≈_.to
from-weak-equivalence {equivalence}      = _≈_.equivalence
from-weak-equivalence {injection}        = _≈_.injection
from-weak-equivalence {surjection}       = _≈_.surjection
from-weak-equivalence {bijection}        = _≈_.bijection
from-weak-equivalence {weak-equivalence} = P.id

-- All kinds of functions can be converted to implications.

to-implication : ∀ {k a b} {A : Set a} {B : Set b} →
                 A ↝[ k ] B → A → B
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

_∘_ : ∀ {k a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ↝[ k ] C → A ↝[ k ] B → A ↝[ k ] C
_∘_ {implication}      = λ f g → f ⊚ g
_∘_ {equivalence}      = Equivalence._∘_
_∘_ {injection}        = Injection._∘_
_∘_ {surjection}       = Surjection._∘_
_∘_ {bijection}        = Bijection._∘_
_∘_ {weak-equivalence} = Weak._∘_

-- Identity.

id : ∀ {k a} {A : Set a} → A ↝[ k ] A
id = from-bijection Bijection.id

-- "Equational" reasoning combinators.

infixr 0 _↝⟨_⟩_ _↔⟨_⟩_ _≈⟨_⟩_
infix  0 finally-↝ finally-↔ finally-≈
infix  0 _□

_↝⟨_⟩_ : ∀ {k a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↝[ k ] B → B ↝[ k ] C → A ↝[ k ] C
_ ↝⟨ A↝B ⟩ B↝C = B↝C ∘ A↝B

_↔⟨_⟩_ : ∀ {k a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↔ B → B ↝[ k ] C → A ↝[ k ] C
_ ↔⟨ A↔B ⟩ B↝C = _ ↝⟨ from-bijection A↔B ⟩ B↝C

_≈⟨_⟩_ : ∀ {k a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ≈ B → B ↝[ k ] C → A ↝[ k ] C
_ ≈⟨ A≈B ⟩ B↝C = _ ↝⟨ from-weak-equivalence A≈B ⟩ B↝C

_□ : ∀ {k a} (A : Set a) → A ↝[ k ] A
A □ = id

finally-↝ : ∀ {k a b} (A : Set a) (B : Set b) →
            A ↝[ k ] B → A ↝[ k ] B
finally-↝ _ _ A↝B = A↝B

finally-↔ : ∀ {k a b} (A : Set a) (B : Set b) →
            A ↔ B → A ↝[ k ] B
finally-↔ _ _ A↔B = from-bijection A↔B

finally-≈ : ∀ {k a b} (A : Set a) (B : Set b) →
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

inverse : ∀ {k a b} {A : Set a} {B : Set b} →
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

contractible↔⊤ : ∀ {a} {A : Set a} → Contractible A → A ↔ ⊤
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

  ⊎-cong-eq : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                {B₁ : Set b₁} {B₂ : Set b₂} →
              A₁ ⇔ A₂ → B₁ ⇔ B₂ → A₁ ⊎ B₁ ⇔ A₂ ⊎ B₂
  ⊎-cong-eq A₁⇔A₂ B₁⇔B₂ = record
    { to   = ⊎-map (to   A₁⇔A₂) (to   B₁⇔B₂)
    ; from = ⊎-map (from A₁⇔A₂) (from B₁⇔B₂)
    } where open _⇔_

  ⊎-cong-inj : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                 {B₁ : Set b₁} {B₂ : Set b₂} →
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

  ⊎-cong-surj : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                  {B₁ : Set b₁} {B₂ : Set b₂} →
                A₁ ↠ A₂ → B₁ ↠ B₂ → A₁ ⊎ B₁ ↠ A₂ ⊎ B₂
  ⊎-cong-surj A₁↠A₂ B₁↠B₂ = record
    { equivalence      = ⊎-cong-eq (_↠_.equivalence A₁↠A₂)
                                   (_↠_.equivalence B₁↠B₂)
    ; right-inverse-of =
        [ cong inj₁ ⊚ _↠_.right-inverse-of A₁↠A₂
        , cong inj₂ ⊚ _↠_.right-inverse-of B₁↠B₂
        ]
    }

  ⊎-cong-bij : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                 {B₁ : Set b₁} {B₂ : Set b₂} →
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

_⊎-cong_ : ∀ {k a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
             {B₁ : Set b₁} {B₂ : Set b₂} →
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

⊎-comm : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B ↔ B ⊎ A
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

⊎-assoc : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
          A ⊎ (B ⊎ C) ↔ (A ⊎ B) ⊎ C
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

⊎-left-identity : ∀ {a} {A : Set a} → ⊥ ⊎ A ↔ A
⊎-left-identity = record
  { surjection = record
    { equivalence = record
      { to   = λ { (inj₁ ()); (inj₂ x) → x }
      ; from = inj₂
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = λ { (inj₁ ()); (inj₂ x) → refl (inj₂ x) }
  }

⊎-right-identity : ∀ {a} {A : Set a} → A ⊎ ⊥ ↔ A
⊎-right-identity {A = A} =
  A ⊎ ⊥  ↔⟨ ⊎-comm ⟩
  ⊥ ⊎ A  ↔⟨ ⊎-left-identity ⟩□
  A      □

-- For equivalences _⊎_ is also idempotent. (This lemma could be
-- generalised to cover surjections and implications.)

⊎-idempotent : ∀ {a} {A : Set a} → A ⊎ A ⇔ A
⊎-idempotent = record
  { to   = [ id , id ]
  ; from = inj₁
  }

------------------------------------------------------------------------
-- _×_ is a commutative monoid with a zero

-- _×_ preserves all kinds of functions.

private

  ×-cong-eq : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                {B₁ : Set b₁} {B₂ : Set b₂} →
              A₁ ⇔ A₂ → B₁ ⇔ B₂ → A₁ × B₁ ⇔ A₂ × B₂
  ×-cong-eq A₁⇔A₂ B₁⇔B₂ = record
    { to   = Σ-map (to   A₁⇔A₂) (to   B₁⇔B₂)
    ; from = Σ-map (from A₁⇔A₂) (from B₁⇔B₂)
    } where open _⇔_

  ×-cong-inj : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                 {B₁ : Set b₁} {B₂ : Set b₂} →
               A₁ ↣ A₂ → B₁ ↣ B₂ → A₁ × B₁ ↣ A₂ × B₂
  ×-cong-inj {A₁ = A₁} {A₂} {B₁} {B₂} A₁↣A₂ B₁↣B₂ = record
    { to        = to′
    ; injective = injective′
    }
    where
    open _↣_

    to′ : A₁ × B₁ → A₂ × B₂
    to′ = Σ-map (to A₁↣A₂) (to B₁↣B₂)

    abstract
      injective′ : Injective to′
      injective′ to′-x≡to′-y =
        cong₂ _,_ (injective A₁↣A₂ (cong proj₁ to′-x≡to′-y))
                  (injective B₁↣B₂ (cong proj₂ to′-x≡to′-y))

  ×-cong-surj : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                  {B₁ : Set b₁} {B₂ : Set b₂} →
                A₁ ↠ A₂ → B₁ ↠ B₂ → A₁ × B₁ ↠ A₂ × B₂
  ×-cong-surj A₁↠A₂ B₁↠B₂ = record
    { equivalence      = ×-cong-eq (_↠_.equivalence A₁↠A₂)
                                   (_↠_.equivalence B₁↠B₂)
    ; right-inverse-of = uncurry λ x y →
        cong₂ _,_ (_↠_.right-inverse-of A₁↠A₂ x)
                  (_↠_.right-inverse-of B₁↠B₂ y)
    }

  ×-cong-bij : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                 {B₁ : Set b₁} {B₂ : Set b₂} →
               A₁ ↔ A₂ → B₁ ↔ B₂ → A₁ × B₁ ↔ A₂ × B₂
  ×-cong-bij A₁↔A₂ B₁↔B₂ = record
    { surjection      = ×-cong-surj (_↔_.surjection A₁↔A₂)
                                    (_↔_.surjection B₁↔B₂)
    ; left-inverse-of = uncurry λ x y →
        cong₂ _,_ (_↔_.left-inverse-of A₁↔A₂ x)
                  (_↔_.left-inverse-of B₁↔B₂ y)
    }

infixr 2 _×-cong_

_×-cong_ : ∀ {k a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
             {B₁ : Set b₁} {B₂ : Set b₂} →
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

×-comm : ∀ {a b} {A : Set a} {B : Set b} → A × B ↔ B × A
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

×-assoc : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
          A × (B × C) ↔ (A × B) × C
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

Σ-left-identity : ∀ {a} {A : ⊤ → Set a} → Σ ⊤ A ↔ A tt
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

×-left-identity : ∀ {a} {A : Set a} → ⊤ × A ↔ A
×-left-identity = Σ-left-identity

×-right-identity : ∀ {a} {A : Set a} → A × ⊤ ↔ A
×-right-identity {A = A} =
  A × ⊤  ↔⟨ ×-comm ⟩
  ⊤ × A  ↔⟨ ×-left-identity ⟩□
  A      □

-- ⊥ is a left and right zero of _×_ and Σ.

Σ-left-zero : ∀ {a} {A : ⊥ → Set a} → Σ ⊥ A ↔ ⊥
Σ-left-zero = record
  { surjection = record
    { equivalence = record
      { to   = λ { (() , _) }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { (() , _) }
  }

×-left-zero : ∀ {a} {A : Set a} → ⊥ × A ↔ ⊥
×-left-zero = Σ-left-zero

×-right-zero : ∀ {a} {A : Set a} → A × ⊥ ↔ ⊥
×-right-zero {A = A} =
  A × ⊥  ↔⟨ ×-comm ⟩
  ⊥ × A  ↔⟨ ×-left-zero ⟩□
  ⊥      □

------------------------------------------------------------------------
-- Some lemmas related to Σ/∃

-- See also Σ-left-zero and Σ-right-zero above.

-- Σ preserves bijections in its first argument and all kinds of
-- functions in its second argument.

Σ-cong : ∀ {k a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
           {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂} →
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

  ∃-cong-impl : ∀ {a b₁ b₂}
                  {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
                (∀ x → B₁ x → B₂ x) → ∃ B₁ → ∃ B₂
  ∃-cong-impl B₁→B₂ = Σ-map id (λ {x} → B₁→B₂ x)

  ∃-cong-eq : ∀ {a b₁ b₂}
                {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
              (∀ x → B₁ x ⇔ B₂ x) → ∃ B₁ ⇔ ∃ B₂
  ∃-cong-eq B₁⇔B₂ = record
    { to   = ∃-cong-impl (to   ⊚ B₁⇔B₂)
    ; from = ∃-cong-impl (from ⊚ B₁⇔B₂)
    } where open _⇔_

  ∃-cong-surj : ∀ {a b₁ b₂}
                  {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
                (∀ x → B₁ x ↠ B₂ x) → ∃ B₁ ↠ ∃ B₂
  ∃-cong-surj B₁↠B₂ = record
    { equivalence      = ∃-cong-eq (_↠_.equivalence ⊚ B₁↠B₂)
    ; right-inverse-of = uncurry λ x y →
        cong (_,_ x) (_↠_.right-inverse-of (B₁↠B₂ x) y)
    }

  ∃-cong-bij : ∀ {a b₁ b₂}
                 {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
               (∀ x → B₁ x ↔ B₂ x) → ∃ B₁ ↔ ∃ B₂
  ∃-cong-bij B₁↔B₂ = record
    { surjection      = ∃-cong-surj (_↔_.surjection ⊚ B₁↔B₂)
    ; left-inverse-of = uncurry λ x y →
        cong (_,_ x) (_↔_.left-inverse-of (B₁↔B₂ x) y)
    }

∃-cong : ∀ {k a b₁ b₂}
           {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
         (∀ x → B₁ x ↝[ k ] B₂ x) → ∃ B₁ ↝[ k ] ∃ B₂
∃-cong {implication}      = ∃-cong-impl
∃-cong {equivalence}      = ∃-cong-eq
∃-cong {injection}        = Σ-cong id
∃-cong {surjection}       = ∃-cong-surj
∃-cong {bijection}        = ∃-cong-bij
∃-cong {weak-equivalence} = λ B₁≈B₂ →
  from-bijection $ ∃-cong-bij (from-weak-equivalence ⊚ B₁≈B₂)

-- ∃ distributes "from the left" over _⊎_.

∃-⊎-distrib-left :
  ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c} →
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

∃-⊎-distrib-right :
  ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c} →
  Σ (A ⊎ B) C ↔ Σ A (C ⊚ inj₁) ⊎ Σ B (C ⊚ inj₂)
∃-⊎-distrib-right {A = A} {B} {C} = record
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

∃-comm : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
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

∃-intro : ∀ {a b} {A : Set a} (B : A → Set b) (x : A) →
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

×-⊎-distrib-left : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                   A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
×-⊎-distrib-left = ∃-⊎-distrib-left

-- _×_ distributes from the right over _⊎_.

×-⊎-distrib-right : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                    (A ⊎ B) × C ↔ (A × C) ⊎ (B × C)
×-⊎-distrib-right = ∃-⊎-distrib-right

------------------------------------------------------------------------
-- Some lemmas related to functions

Π-left-identity : ∀ {a} {A : ⊤ → Set a} → ((x : ⊤) → A x) ↔ A tt
Π-left-identity = record
  { surjection = record
    { equivalence = record
      { to   = λ f → f tt
      ; from = λ x _ → x
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

→-right-zero : ∀ {a} {A : Set a} → (A → ⊤) ↔ ⊤
→-right-zero = record
  { surjection = record
    { equivalence = record
      { to   = λ _ → tt
      ; from = λ _ _ → tt
      }
    ; right-inverse-of = λ _ → refl tt
    }
  ; left-inverse-of = λ _ → refl (λ _ → tt)
  }

------------------------------------------------------------------------
-- Lemmas related to if

-- A generalisation of if-encoding (which is defined below).

if-lemma : ∀ {a b p} {A : Set a} {B : Set b} (P : Bool → Set p) →
           A ↔ P true → B ↔ P false →
           ∀ b → T b × A ⊎ T (not b) × B ↔ P b
if-lemma {A = A} {B} P A↔ B↔ true =
  ⊤ × A ⊎ ⊥ × B  ↔⟨ ×-left-identity ⊎-cong ×-left-zero ⟩
  A ⊎ ⊥          ↔⟨ ⊎-right-identity ⟩
  A              ↔⟨ A↔ ⟩
  P true         □
if-lemma {A = A} {B} P A↔ B↔ false =
  ⊥ × A ⊎ ⊤ × B  ↔⟨ ×-left-zero ⊎-cong ×-left-identity ⟩
  ⊥ ⊎ B          ↔⟨ ⊎-left-identity ⟩
  B              ↔⟨ B↔ ⟩
  P false        □

-- An encoding of if_then_else_ in terms of _⊎_, _×_, T and not.

if-encoding : ∀ {ℓ} {A B : Set ℓ} →
              ∀ b → if b then A else B ↔ T b × A ⊎ T (not b) × B
if-encoding {A = A} {B} =
  inverse ⊚ if-lemma (λ b → if b then A else B) id id

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

-- A function is "well-behaved" if any "left" element which is the
-- image of a "right" element is in turn not mapped to another "left"
-- element.

Well-behaved : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
               (A ⊎ B → A ⊎ C) → Set _
Well-behaved f =
  ∀ {b a a′} → f (inj₂ b) ≡ inj₁ a → f (inj₁ a) ≢ inj₁ a′

-- TODO: Make this property more general.

⊎-left-cancellative :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A ⊎ B ↔ A ⊎ C) →
  Well-behaved (_↔_.to   f) →
  Well-behaved (_↔_.from f) →
  B ↔ C
⊎-left-cancellative inv to-hyp from-hyp = record
  { surjection = record
    { equivalence = record
      { to   = g (to   inv) to-hyp
      ; from = g (from inv) from-hyp
      }
    ; right-inverse-of = g∘g (inverse inv) from-hyp to-hyp
    }
  ; left-inverse-of    = g∘g          inv  to-hyp from-hyp
  }
  where
  open _↔_

  g : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
      (f : A ⊎ B → A ⊎ C) → Well-behaved f → (B → C)
  g f hyp b with inspect (f (inj₂ b))
  g f hyp b | inj₂ c with-≡ eq₁ = c
  g f hyp b | inj₁ a with-≡ eq₁ with inspect (f (inj₁ a))
  g f hyp b | inj₁ a with-≡ eq₁ | inj₂ c  with-≡ eq₂ = c
  g f hyp b | inj₁ a with-≡ eq₁ | inj₁ a′ with-≡ eq₂ =
    ⊥-elim $ hyp eq₁ eq₂

  abstract

    g∘g : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A ⊎ B ↔ A ⊎ C) →
          (to-hyp   : Well-behaved (to   f)) →
          (from-hyp : Well-behaved (from f)) →
          ∀ b → g (from f) from-hyp (g (to f) to-hyp b) ≡ b
    g∘g f to-hyp from-hyp b = g∘g′
      where
      g∘g′ : g (from f) from-hyp (g (to f) to-hyp b) ≡ b
      g∘g′ with inspect (to f (inj₂ b))
      g∘g′ | inj₂ c with-≡ eq₁ with inspect (from f (inj₂ c))
      g∘g′ | inj₂ c with-≡ eq₁ | inj₂ b′ with-≡ eq₂ = ⊎.cancel-inj₂ (
                                                        inj₂ b′          ≡⟨ sym eq₂ ⟩
                                                        from f (inj₂ c)  ≡⟨ to-from f eq₁ ⟩∎
                                                        inj₂ b           ∎)
      g∘g′ | inj₂ c with-≡ eq₁ | inj₁ a  with-≡ eq₂ = ⊥-elim $ ⊎.inj₁≢inj₂ (
                                                        inj₁ a           ≡⟨ sym eq₂ ⟩
                                                        from f (inj₂ c)  ≡⟨ to-from f eq₁ ⟩∎
                                                        inj₂ b           ∎)
      g∘g′ | inj₁ a with-≡ eq₁ with inspect (to f (inj₁ a))
      g∘g′ | inj₁ a with-≡ eq₁ | inj₁ a′ with-≡ eq₂ = ⊥-elim $ to-hyp eq₁ eq₂
      g∘g′ | inj₁ a with-≡ eq₁ | inj₂ c  with-≡ eq₂ with inspect (from f (inj₂ c))
      g∘g′ | inj₁ a with-≡ eq₁ | inj₂ c  with-≡ eq₂ | inj₂ b′ with-≡ eq₃ = ⊥-elim $ ⊎.inj₁≢inj₂ (
                                                                             inj₁ a           ≡⟨ sym $ to-from f eq₂ ⟩
                                                                             from f (inj₂ c)  ≡⟨ eq₃ ⟩∎
                                                                             inj₂ b′          ∎)
      g∘g′ | inj₁ a with-≡ eq₁ | inj₂ c  with-≡ eq₂ | inj₁ a′ with-≡ eq₃ with inspect (from f (inj₁ a′))
      g∘g′ | inj₁ a with-≡ eq₁ | inj₂ c  with-≡ eq₂ | inj₁ a′ with-≡ eq₃ | inj₁ a″ with-≡ eq₄ = ⊥-elim $ from-hyp eq₃ eq₄
      g∘g′ | inj₁ a with-≡ eq₁ | inj₂ c  with-≡ eq₂ | inj₁ a′ with-≡ eq₃ | inj₂ b′ with-≡ eq₄ = ⊎.cancel-inj₂ (
        let lemma =
              inj₁ a′          ≡⟨ sym eq₃ ⟩
              from f (inj₂ c)  ≡⟨ to-from f eq₂ ⟩∎
              inj₁ a           ∎
        in
        inj₂ b′           ≡⟨ sym eq₄ ⟩
        from f (inj₁ a′)  ≡⟨ cong (from f ⊚ inj₁) $ ⊎.cancel-inj₁ lemma ⟩
        from f (inj₁ a)   ≡⟨ to-from f eq₁ ⟩∎
        inj₂ b            ∎)
