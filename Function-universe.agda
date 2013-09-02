------------------------------------------------------------------------
-- A universe which includes several kinds of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Function-universe
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection using (_↔_; module _↔_)
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_; module _≃_)
open import H-level eq
open import Injection eq as Injection using (_↣_; module _↣_; Injective)
open import Logical-equivalence using (_⇔_; module _⇔_)
open import Preimage eq using (_⁻¹_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
open import Surjection eq as Surjection using (_↠_; module _↠_)

------------------------------------------------------------------------
-- The universe

-- The universe includes implications, logical equivalences,
-- injections, surjections, bijections and equivalences.

data Kind : Set where
  implication
    logical-equivalence
    injection
    surjection
    bijection
    equivalence : Kind

-- The interpretation of the universe.

infix 0 _↝[_]_

_↝[_]_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Kind → Set ℓ₂ → Set _
A ↝[ implication         ] B = A → B
A ↝[ logical-equivalence ] B = A ⇔ B
A ↝[ injection           ] B = A ↣ B
A ↝[ surjection          ] B = A ↠ B
A ↝[ bijection           ] B = A ↔ B
A ↝[ equivalence         ] B = A ≃ B

-- Bijections can be converted to all kinds of functions.

from-bijection : ∀ {k a b} {A : Set a} {B : Set b} →
                 A ↔ B → A ↝[ k ] B
from-bijection {implication}         = _↔_.to
from-bijection {logical-equivalence} = _↔_.logical-equivalence
from-bijection {injection}           = _↔_.injection
from-bijection {surjection}          = _↔_.surjection
from-bijection {bijection}           = P.id
from-bijection {equivalence}         = Eq.↔⇒≃

-- Equivalences can be converted to all kinds of functions.

from-equivalence : ∀ {k a b} {A : Set a} {B : Set b} →
                   A ≃ B → A ↝[ k ] B
from-equivalence {implication}         = _≃_.to
from-equivalence {logical-equivalence} = _≃_.logical-equivalence
from-equivalence {injection}           = _≃_.injection
from-equivalence {surjection}          = _≃_.surjection
from-equivalence {bijection}           = _≃_.bijection
from-equivalence {equivalence}         = P.id

-- All kinds of functions can be converted to implications.

to-implication : ∀ {k a b} {A : Set a} {B : Set b} →
                 A ↝[ k ] B → A → B
to-implication {implication}         = P.id
to-implication {logical-equivalence} = _⇔_.to
to-implication {injection}           = _↣_.to
to-implication {surjection}          = _↠_.to
to-implication {bijection}           = _↔_.to
to-implication {equivalence}         = _≃_.to

------------------------------------------------------------------------
-- A sub-universe of symmetric kinds of functions

data Symmetric-kind : Set where
  logical-equivalence bijection equivalence : Symmetric-kind

⌊_⌋-sym : Symmetric-kind → Kind
⌊ logical-equivalence ⌋-sym = logical-equivalence
⌊ bijection           ⌋-sym = bijection
⌊ equivalence         ⌋-sym = equivalence

inverse : ∀ {k a b} {A : Set a} {B : Set b} →
          A ↝[ ⌊ k ⌋-sym ] B → B ↝[ ⌊ k ⌋-sym ] A
inverse {logical-equivalence} = Logical-equivalence.inverse
inverse {bijection}           = Bijection.inverse
inverse {equivalence}         = Eq.inverse

------------------------------------------------------------------------
-- A sub-universe of isomorphisms

data Isomorphism-kind : Set where
  bijection equivalence : Isomorphism-kind

⌊_⌋-iso : Isomorphism-kind → Kind
⌊ bijection   ⌋-iso = bijection
⌊ equivalence ⌋-iso = equivalence

infix 0 _↔[_]_

_↔[_]_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Isomorphism-kind → Set ℓ₂ → Set _
A ↔[ k ] B = A ↝[ ⌊ k ⌋-iso ] B

from-isomorphism : ∀ {k₁ k₂ a b} {A : Set a} {B : Set b} →
                   A ↔[ k₁ ] B → A ↝[ k₂ ] B
from-isomorphism {bijection}   = from-bijection
from-isomorphism {equivalence} = from-equivalence

-- Lemma: to-implication after from-isomorphism is the same as
-- to-implication.

to-implication∘from-isomorphism :
  ∀ {a b} {A : Set a} {B : Set b} k₁ k₂ {A↔B : A ↔[ k₁ ] B} →
  to-implication A↔B ≡
  to-implication (from-isomorphism {k₂ = k₂} A↔B)
to-implication∘from-isomorphism {A = A} {B} = t∘f
  where
  t∘f : ∀ k₁ k₂ {A↔B : A ↔[ k₁ ] B} →
        to-implication A↔B ≡
        to-implication (from-isomorphism {k₂ = k₂} A↔B)
  t∘f bijection   implication         = refl _
  t∘f bijection   logical-equivalence = refl _
  t∘f bijection   injection           = refl _
  t∘f bijection   surjection          = refl _
  t∘f bijection   bijection           = refl _
  t∘f bijection   equivalence         = refl _
  t∘f equivalence implication         = refl _
  t∘f equivalence logical-equivalence = refl _
  t∘f equivalence injection           = refl _
  t∘f equivalence surjection          = refl _
  t∘f equivalence bijection           = refl _
  t∘f equivalence equivalence         = refl _

------------------------------------------------------------------------
-- Preorder

-- All the different kinds of functions form preorders.

-- Composition.

infixr 9 _∘_

_∘_ : ∀ {k a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ↝[ k ] C → A ↝[ k ] B → A ↝[ k ] C
_∘_ {implication}         = λ f g → f ⊚ g
_∘_ {logical-equivalence} = Logical-equivalence._∘_
_∘_ {injection}           = Injection._∘_
_∘_ {surjection}          = Surjection._∘_
_∘_ {bijection}           = Bijection._∘_
_∘_ {equivalence}         = Eq._∘_

-- Identity.

id : ∀ {k a} {A : Set a} → A ↝[ k ] A
id {implication}         = P.id
id {logical-equivalence} = Logical-equivalence.id
id {injection}           = Injection.id
id {surjection}          = Surjection.id
id {bijection}           = Bijection.id
id {equivalence}         = Eq.id

-- "Equational" reasoning combinators.

infixr 0 _↝⟨_⟩_ _↔⟨_⟩_ _↔⟨⟩_
infix  0 finally-↝ finally-↔
infix  0 _□

_↝⟨_⟩_ : ∀ {k a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↝[ k ] B → B ↝[ k ] C → A ↝[ k ] C
_ ↝⟨ A↝B ⟩ B↝C = B↝C ∘ A↝B

_↔⟨_⟩_ : ∀ {k₁ k₂ a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↔[ k₁ ] B → B ↝[ k₂ ] C → A ↝[ k₂ ] C
_ ↔⟨ A↔B ⟩ B↝C = _ ↝⟨ from-isomorphism A↔B ⟩ B↝C

_↔⟨⟩_ : ∀ {k a b} (A : Set a) {B : Set b} →
        A ↝[ k ] B → A ↝[ k ] B
_ ↔⟨⟩ A↝B = A↝B

_□ : ∀ {k a} (A : Set a) → A ↝[ k ] A
A □ = id

finally-↝ : ∀ {k a b} (A : Set a) (B : Set b) →
            A ↝[ k ] B → A ↝[ k ] B
finally-↝ _ _ A↝B = A↝B

finally-↔ : ∀ {k₁ k₂ a b} (A : Set a) (B : Set b) →
            A ↔[ k₁ ] B → A ↝[ k₂ ] B
finally-↔ _ _ A↔B = from-isomorphism A↔B

syntax finally-↝ A B A↝B = A ↝⟨ A↝B ⟩□ B □
syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩□ B □

-- Lemma: to-implication maps id to the identity function.

to-implication-id :
  ∀ {a} {A : Set a} k →
  to-implication {k = k} id ≡ id {A = A}
to-implication-id implication         = refl _
to-implication-id logical-equivalence = refl _
to-implication-id injection           = refl _
to-implication-id surjection          = refl _
to-implication-id bijection           = refl _
to-implication-id equivalence         = refl _

-- Lemma: to-implication is homomorphic with respect to _∘_.

to-implication-∘ :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  (k : Kind) {f : A ↝[ k ] B} {g : B ↝[ k ] C} →
  to-implication (g ∘ f) ≡ to-implication g ∘ to-implication f
to-implication-∘ implication         = refl _
to-implication-∘ logical-equivalence = refl _
to-implication-∘ injection           = refl _
to-implication-∘ surjection          = refl _
to-implication-∘ bijection           = refl _
to-implication-∘ equivalence         = refl _

-- Lemma: to-implication maps inverse id to the identity function.

to-implication-inverse-id :
  ∀ {a} {A : Set a} k →
  to-implication (inverse {k = k} id) ≡ id {A = A}
to-implication-inverse-id logical-equivalence = refl _
to-implication-inverse-id bijection           = refl _
to-implication-inverse-id equivalence         = refl _

------------------------------------------------------------------------
-- Lots of properties
------------------------------------------------------------------------

-- Properties of the form A ↝[ k ] B, for arbitrary k, are only stated
-- for bijections; converting to the other forms is easy.

------------------------------------------------------------------------
-- Equalities can be converted to all kinds of functions

≡⇒↝ : ∀ k {ℓ} {A B : Set ℓ} → A ≡ B → A ↝[ k ] B
≡⇒↝ k = elim (λ {A B} _ → A ↝[ k ] B) (λ _ → id)

abstract

  -- Some lemmas that can be used to manipulate expressions involving
  -- ≡⇒↝ and refl/sym/trans.

  ≡⇒↝-refl : ∀ {k a} {A : Set a} →
             ≡⇒↝ k (refl A) ≡ id
  ≡⇒↝-refl {k} = elim-refl (λ {A B} _ → A ↝[ k ] B) _

  ≡⇒↝-sym : ∀ k {ℓ} {A B : Set ℓ} {eq : A ≡ B} →
            to-implication (≡⇒↝ ⌊ k ⌋-sym (sym eq)) ≡
            to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym eq))
  ≡⇒↝-sym k {A = A} {eq = eq} = elim¹
    (λ eq → to-implication (≡⇒↝ ⌊ k ⌋-sym (sym eq)) ≡
            to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym eq)))
    (to-implication (≡⇒↝ ⌊ k ⌋-sym (sym (refl A)))      ≡⟨ cong (to-implication ∘ ≡⇒↝ ⌊ k ⌋-sym) sym-refl ⟩
     to-implication (≡⇒↝ ⌊ k ⌋-sym (refl A))            ≡⟨ cong (to-implication {k = ⌊ k ⌋-sym}) ≡⇒↝-refl ⟩
     to-implication {k = ⌊ k ⌋-sym} id                  ≡⟨ to-implication-id ⌊ k ⌋-sym ⟩
     id                                                 ≡⟨ sym $ to-implication-inverse-id k ⟩
     to-implication (inverse {k = k} id)                ≡⟨ cong (to-implication ∘ inverse {k = k}) $ sym ≡⇒↝-refl ⟩∎
     to-implication (inverse (≡⇒↝ ⌊ k ⌋-sym (refl A)))  ∎)
    eq

  ≡⇒↝-trans : ∀ k {ℓ} {A B C : Set ℓ} {A≡B : A ≡ B} {B≡C : B ≡ C} →
              to-implication (≡⇒↝ k (trans A≡B B≡C)) ≡
              to-implication (≡⇒↝ k B≡C ∘ ≡⇒↝ k A≡B)
  ≡⇒↝-trans k {B = B} {A≡B = A≡B} = elim¹
    (λ B≡C → to-implication (≡⇒↝ k (trans A≡B B≡C)) ≡
             to-implication (≡⇒↝ k B≡C ∘ ≡⇒↝ k A≡B))
    (to-implication (≡⇒↝ k (trans A≡B (refl B)))             ≡⟨ cong (to-implication ∘ ≡⇒↝ k) $ trans-reflʳ _ ⟩
     to-implication (≡⇒↝ k A≡B)                              ≡⟨ sym $ cong (λ f → f ∘ to-implication (≡⇒↝ k A≡B)) $ to-implication-id k ⟩
     to-implication {k = k} id ∘ to-implication (≡⇒↝ k A≡B)  ≡⟨ sym $ to-implication-∘ k ⟩
     to-implication (id ∘ ≡⇒↝ k A≡B)                         ≡⟨ sym $ cong (λ f → to-implication (f ∘ ≡⇒↝ k A≡B)) ≡⇒↝-refl ⟩∎
     to-implication (≡⇒↝ k (refl B) ∘ ≡⇒↝ k A≡B)             ∎)
    _

  -- One can sometimes "push" ≡⇒↝ through cong.
  --
  -- This is a generalisation of a lemma due to Thierry Coquand.

  ≡⇒↝-cong : ∀ {k ℓ p A B} {eq : A ≡ B}
             (P : Set ℓ → Set p)
             (P-cong : ∀ {A B} → A ↝[ k ] B → P A ↝[ k ] P B) →
             P-cong (id {A = A}) ≡ id →
             ≡⇒↝ _ (cong P eq) ≡ P-cong (≡⇒↝ _ eq)
  ≡⇒↝-cong {eq = eq} P P-cong P-cong-id = elim¹
    (λ eq → ≡⇒↝ _ (cong P eq) ≡ P-cong (≡⇒↝ _ eq))
    (≡⇒↝ _ (cong P (refl _))  ≡⟨ cong (≡⇒↝ _) $ cong-refl P ⟩
     ≡⇒↝ _ (refl _)           ≡⟨ elim-refl (λ {A B} _ → A ↝[ _ ] B) _ ⟩
     id                       ≡⟨ sym P-cong-id ⟩
     P-cong id                ≡⟨ cong P-cong $ sym $
                                   elim-refl (λ {A B} _ → A ↝[ _ ] B) _ ⟩∎
     P-cong (≡⇒↝ _ (refl _))  ∎)
    eq

------------------------------------------------------------------------
-- A lemma related to ⊤

-- Contractible sets are isomorphic to ⊤.

contractible↔⊤ : ∀ {a} {A : Set a} → Contractible A → A ↔ ⊤
contractible↔⊤ c = record
  { surjection = record
    { logical-equivalence = record
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
    { logical-equivalence = ⊎-cong-eq (_↠_.logical-equivalence A₁↠A₂)
                                      (_↠_.logical-equivalence B₁↠B₂)
    ; right-inverse-of    =
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
_⊎-cong_ {implication}         = ⊎-map
_⊎-cong_ {logical-equivalence} = ⊎-cong-eq
_⊎-cong_ {injection}           = ⊎-cong-inj
_⊎-cong_ {surjection}          = ⊎-cong-surj
_⊎-cong_ {bijection}           = ⊎-cong-bij
_⊎-cong_ {equivalence}         = λ A₁≃A₂ B₁≃B₂ →
  from-bijection $ ⊎-cong-bij (from-equivalence A₁≃A₂)
                              (from-equivalence B₁≃B₂)

-- _⊎_ is commutative.

⊎-comm : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B ↔ B ⊎ A
⊎-comm = record
  { surjection = record
    { logical-equivalence = record
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
    { logical-equivalence = record
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

⊎-left-identity : ∀ {a ℓ} {A : Set a} → ⊥ {ℓ = ℓ} ⊎ A ↔ A
⊎-left-identity = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (inj₁ ()); (inj₂ x) → x }
      ; from = inj₂
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = λ { (inj₁ ()); (inj₂ x) → refl (inj₂ x) }
  }

⊎-right-identity : ∀ {a ℓ} {A : Set a} → A ⊎ ⊥ {ℓ = ℓ} ↔ A
⊎-right-identity {A = A} =
  A ⊎ ⊥  ↔⟨ ⊎-comm ⟩
  ⊥ ⊎ A  ↔⟨ ⊎-left-identity ⟩□
  A      □

-- For logical equivalences _⊎_ is also idempotent. (This lemma could
-- be generalised to cover surjections and implications.)

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
    { logical-equivalence = ×-cong-eq (_↠_.logical-equivalence A₁↠A₂)
                                      (_↠_.logical-equivalence B₁↠B₂)
    ; right-inverse-of    = uncurry λ x y →
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
_×-cong_ {implication}         = λ f g → Σ-map f g
_×-cong_ {logical-equivalence} = ×-cong-eq
_×-cong_ {injection}           = ×-cong-inj
_×-cong_ {surjection}          = ×-cong-surj
_×-cong_ {bijection}           = ×-cong-bij
_×-cong_ {equivalence}         = λ A₁≃A₂ B₁≃B₂ →
  from-bijection $ ×-cong-bij (from-equivalence A₁≃A₂)
                              (from-equivalence B₁≃B₂)

-- _×_ is commutative.

×-comm : ∀ {a b} {A : Set a} {B : Set b} → A × B ↔ B × A
×-comm = record
  { surjection = record
    { logical-equivalence = record
      { to   = uncurry λ x y → (y , x)
      ; from = uncurry λ x y → (y , x)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Σ is associative.

Σ-assoc : ∀ {a b c}
            {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
          (Σ A λ x → Σ (B x) (C x)) ↔ Σ (Σ A B) (uncurry C)
Σ-assoc = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (x , (y , z)) → (x , y) , z }
      ; from = λ { ((x , y) , z) → x , (y , z) }
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- _×_ is associative.

×-assoc : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
          A × (B × C) ↔ (A × B) × C
×-assoc = Σ-assoc

-- ⊤ is a left and right identity of _×_ and Σ.

Σ-left-identity : ∀ {a} {A : ⊤ → Set a} → Σ ⊤ A ↔ A tt
Σ-left-identity = record
  { surjection = record
    { logical-equivalence = record
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

Σ-left-zero : ∀ {ℓ₁ a ℓ₂} {A : ⊥ {ℓ = ℓ₁} → Set a} →
              Σ ⊥ A ↔ ⊥ {ℓ = ℓ₂}
Σ-left-zero = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (() , _) }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { (() , _) }
  }

×-left-zero : ∀ {a ℓ₁ ℓ₂} {A : Set a} → ⊥ {ℓ = ℓ₁} × A ↔ ⊥ {ℓ = ℓ₂}
×-left-zero = Σ-left-zero

×-right-zero : ∀ {a ℓ₁ ℓ₂} {A : Set a} → A × ⊥ {ℓ = ℓ₁} ↔ ⊥ {ℓ = ℓ₂}
×-right-zero {A = A} =
  A × ⊥  ↔⟨ ×-comm ⟩
  ⊥ × A  ↔⟨ ×-left-zero ⟩□
  ⊥      □

------------------------------------------------------------------------
-- Some lemmas related to Σ/∃/_×_

-- See also Σ-left-zero and Σ-right-zero above.

-- Σ preserves isomorphisms in its first argument and all kinds of
-- functions in its second argument.
--
-- The first two clauses are included as an optimisation intended to
-- make some proof terms easier to work with.

Σ-cong : ∀ {k₁ k₂ a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
           {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂} →
         (A₁↔A₂ : A₁ ↔[ k₁ ] A₂) →
         (∀ x → B₁ x ↝[ k₂ ] B₂ (to-implication A₁↔A₂ x)) →
         Σ A₁ B₁ ↝[ k₂ ] Σ A₂ B₂
Σ-cong {equivalence} {equivalence} A₁≃A₂ B₁≃B₂ =
  Eq.Σ-preserves A₁≃A₂ B₁≃B₂
Σ-cong {equivalence} {bijection} A₁≃A₂ B₁↔B₂ =
  Eq.∃-preserves-bijections A₁≃A₂ B₁↔B₂
Σ-cong {k₁} {k₂} {A₁ = A₁} {A₂} {B₁} {B₂} A₁↔A₂ B₁↝B₂ = helper k₂ B₁↝B₂′
  where
  A₁≃A₂ : A₁ ≃ A₂
  A₁≃A₂ = from-isomorphism A₁↔A₂

  B₁↝B₂′ : ∀ x → B₁ x ↝[ k₂ ] B₂ (_≃_.to A₁≃A₂ x)
  B₁↝B₂′ x =
    B₁ x                                    ↝⟨ B₁↝B₂ x ⟩
    B₂ (to-implication A₁↔A₂ x)             ↝⟨ ≡⇒↝ _ $ cong (λ f → B₂ (f x)) $
                                                 to-implication∘from-isomorphism k₁ equivalence ⟩
    B₂ (_≃_.to (from-isomorphism A₁↔A₂) x)  □

  helper : ∀ k₂ → (∀ x → B₁ x ↝[ k₂ ] B₂ (_≃_.to A₁≃A₂ x)) →
           Σ A₁ B₁ ↝[ k₂ ] Σ A₂ B₂
  helper implication         = Eq.∃-preserves-functions            A₁≃A₂
  helper logical-equivalence = Eq.∃-preserves-logical-equivalences A₁≃A₂
  helper injection           = Eq.∃-preserves-injections           A₁≃A₂
  helper surjection          = Eq.∃-preserves-surjections          A₁≃A₂
  helper bijection           = Eq.∃-preserves-bijections           A₁≃A₂
  helper equivalence         = Eq.Σ-preserves                      A₁≃A₂

-- ∃ preserves all kinds of functions. One could define
-- ∃-cong = Σ-cong Bijection.id, but the resulting "from" functions
-- would contain an unnecessary use of substitutivity, and I want to
-- avoid that.

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
    { logical-equivalence = ∃-cong-eq (_↠_.logical-equivalence ⊚ B₁↠B₂)
    ; right-inverse-of    = uncurry λ x y →
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
∃-cong {implication}         = ∃-cong-impl
∃-cong {logical-equivalence} = ∃-cong-eq
∃-cong {injection}           = Σ-cong Bijection.id
∃-cong {surjection}          = ∃-cong-surj
∃-cong {bijection}           = ∃-cong-bij
∃-cong {equivalence}         = λ B₁≃B₂ →
  from-bijection $ ∃-cong-bij (from-equivalence ⊚ B₁≃B₂)

-- ∃ distributes "from the left" over _⊎_.

∃-⊎-distrib-left :
  ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c} →
  (∃ λ x → B x ⊎ C x) ↔ ∃ B ⊎ ∃ C
∃-⊎-distrib-left = record
  { surjection = record
    { logical-equivalence = record
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
    { logical-equivalence = record
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
    { logical-equivalence = record
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

-- A non-dependent variant of Σ-≡,≡↔≡.

≡×≡↔≡ : ∀ {a b} {A : Set a} {B : Set b} {p₁ p₂ : A × B} →
        (proj₁ p₁ ≡ proj₁ p₂ × proj₂ p₁ ≡ proj₂ p₂) ↔ (p₁ ≡ p₂)
≡×≡↔≡ {B = B} {p₁} {p₂} =
  (proj₁ p₁ ≡ proj₁ p₂ × proj₂ p₁ ≡ proj₂ p₂)  ↝⟨ ∃-cong (λ _ → ≡⇒↝ _ $ cong (λ q → q ≡ proj₂ p₂) $
                                                                  sym $ subst-const _) ⟩
  (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
     subst (λ _ → B) p (proj₂ p₁) ≡ proj₂ p₂)  ↝⟨ Bijection.Σ-≡,≡↔≡ ⟩□

  (p₁ ≡ p₂)                                    □

-- If one is given an equality between pairs, where the second
-- components of the pairs are propositional, then one can restrict
-- attention to the first components.

ignore-propositional-component :
  ∀ {a b} {A : Set a} {B : A → Set b} {p q : Σ A B} →
  Is-proposition (B (proj₁ q)) →
  (proj₁ p ≡ proj₁ q) ↔ (p ≡ q)
ignore-propositional-component {B = B} {p₁ , p₂} {q₁ , q₂} Bq₁-prop =
  (p₁ ≡ q₁)                                  ↝⟨ inverse ×-right-identity ⟩
  (p₁ ≡ q₁ × ⊤)                              ↝⟨ ∃-cong (λ _ → inverse $ contractible↔⊤ (Bq₁-prop _ _)) ⟩
  (∃ λ (eq : p₁ ≡ q₁) → subst B eq p₂ ≡ q₂)  ↝⟨ Bijection.Σ-≡,≡↔≡ ⟩□
  ((p₁ , p₂) ≡ (q₁ , q₂))                    □

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

→-cong-⇔ : ∀ {a b c d}
             {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
           A ⇔ B → C ⇔ D → (A → C) ⇔ (B → D)
→-cong-⇔ A⇔B C⇔D = record
  { to   = λ f → to   C⇔D ∘ f ∘ from A⇔B
  ; from = λ f → from C⇔D ∘ f ∘ to   A⇔B
  }
  where open _⇔_

→-cong : ∀ {a b c d} → Extensionality (a ⊔ b) (c ⊔ d) →
         {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
         ∀ {k} → A ↝[ ⌊ k ⌋-sym ] B → C ↝[ ⌊ k ⌋-sym ] D →
         (A → C) ↝[ ⌊ k ⌋-sym ] (B → D)
→-cong {a} {b} {c} {d} ext {A} {B} {C} {D} = helper _
  where
  →-cong-↔ : A ↔ B → C ↔ D → (A → C) ↔ (B → D)
  →-cong-↔ A↔B C↔D = record
    { surjection = record
      { logical-equivalence = logical-equiv
      ; right-inverse-of    = right-inv
      }
    ; left-inverse-of = left-inv
    }
    where
    open _↔_

    logical-equiv = →-cong-⇔ (_↔_.logical-equivalence A↔B)
                             (_↔_.logical-equivalence C↔D)

    abstract
      right-inv :
        ∀ f → _⇔_.to logical-equiv (_⇔_.from logical-equiv f) ≡ f
      right-inv f = lower-extensionality a c ext λ x →
        to C↔D (from C↔D (f (to A↔B (from A↔B x))))  ≡⟨ right-inverse-of C↔D _ ⟩
        f (to A↔B (from A↔B x))                      ≡⟨ cong f $ right-inverse-of A↔B _ ⟩∎
        f x                                          ∎

      left-inv :
        ∀ f → _⇔_.from logical-equiv (_⇔_.to logical-equiv f) ≡ f
      left-inv f = lower-extensionality b d ext λ x →
        from C↔D (to C↔D (f (from A↔B (to A↔B x))))  ≡⟨ left-inverse-of C↔D _ ⟩
        f (from A↔B (to A↔B x))                      ≡⟨ cong f $ left-inverse-of A↔B _ ⟩∎
        f x                                          ∎

  helper : ∀ k → A ↝[ ⌊ k ⌋-sym ] B → C ↝[ ⌊ k ⌋-sym ] D →
           (A → C) ↝[ ⌊ k ⌋-sym ] (B → D)
  helper logical-equivalence      A⇔B C⇔D = →-cong-⇔ A⇔B C⇔D
  helper bijection        A↔B C↔D = →-cong-↔ A↔B C↔D
  helper equivalence A≃B C≃D = record
    { to             = to
    ; is-equivalence = λ y →
        ((from y , right-inverse-of y) , irrelevance y)
    }
    where
    A→B≃C→D = Eq.↔⇒≃
                (→-cong-↔ (_≃_.bijection A≃B) (_≃_.bijection C≃D))

    to   = _≃_.to   A→B≃C→D
    from = _≃_.from A→B≃C→D

    abstract
      right-inverse-of : ∀ x → to (from x) ≡ x
      right-inverse-of = _≃_.right-inverse-of A→B≃C→D

      irrelevance : ∀ y (p : to ⁻¹ y) →
                    (from y , right-inverse-of y) ≡ p
      irrelevance = _≃_.irrelevance A→B≃C→D

Π-left-identity : ∀ {a} {A : ⊤ → Set a} → ((x : ⊤) → A x) ↔ A tt
Π-left-identity = record
  { surjection = record
    { logical-equivalence = record
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
    { logical-equivalence = record
      { to   = λ _ → tt
      ; from = λ _ _ → tt
      }
    ; right-inverse-of = λ _ → refl tt
    }
  ; left-inverse-of = λ _ → refl (λ _ → tt)
  }

-- Π is "commutative".

Π-comm : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
         (∀ x y → C x y) ↔ (∀ y x → C x y)
Π-comm = record
  { surjection = record
    { logical-equivalence = record { to = flip; from = flip }
    ; right-inverse-of    = refl
    }
  ; left-inverse-of = refl
  }

-- There is a (split) surjection from products of equality
-- isomorphisms to equalities.

Π≡↔≡-↠-≡ : ∀ k {a} {A : Set a} (x y : A) →
           (∀ z → (z ≡ x) ↔[ k ] (z ≡ y)) ↠ (x ≡ y)
Π≡↔≡-↠-≡ k x y = record
  { logical-equivalence = record { to = to; from = from }
  ; right-inverse-of    = to∘from
  }
  where
  to : (∀ z → (z ≡ x) ↔[ k ] (z ≡ y)) → x ≡ y
  to f = to-implication (f x) (refl x)

  from′ : x ≡ y → ∀ z → (z ≡ x) ↔ (z ≡ y)
  from′ x≡y z = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ z≡x → trans z≡x      x≡y
        ; from = λ z≡y → trans z≡y (sym x≡y)
        }
      ; right-inverse-of = λ z≡y → trans-[trans-sym] z≡y x≡y
      }
    ; left-inverse-of = λ z≡x → trans-[trans]-sym z≡x x≡y
    }

  from : x ≡ y → ∀ z → (z ≡ x) ↔[ k ] (z ≡ y)
  from x≡y z = from-bijection (from′ x≡y z)

  abstract
    to∘from : ∀ x≡y → to (from x≡y) ≡ x≡y
    to∘from x≡y =
      to (from x≡y)       ≡⟨ sym $ cong (λ f → f (refl x)) $ to-implication∘from-isomorphism bijection ⌊ k ⌋-iso ⟩
      trans (refl x) x≡y  ≡⟨ trans-reflˡ _ ⟩∎
      x≡y                 ∎

-- Products of equivalences of equalities are isomorphic to equalities
-- (assuming extensionality).

Π≡≃≡-↔-≡ : ∀ {a} → Extensionality a a →
           {A : Set a} (x y : A) →
           (∀ z → (z ≡ x) ≃ (z ≡ y)) ↔ (x ≡ y)
Π≡≃≡-↔-≡ ext x y = record
  { surjection      = surj
  ; left-inverse-of = from∘to
  }
  where
  surj = Π≡↔≡-↠-≡ equivalence x y

  open _↠_ surj

  abstract
    from∘to : ∀ f → from (to f) ≡ f
    from∘to f = ext λ z → Eq.lift-equality ext $ ext λ z≡x →
      trans z≡x (_≃_.to (f x) (refl x))  ≡⟨ elim (λ {u v} u≡v →
                                                    (f : ∀ z → (z ≡ v) ≃ (z ≡ y)) →
                                                    trans u≡v (_≃_.to (f v) (refl v)) ≡
                                                    _≃_.to (f u) u≡v)
                                                 (λ _ _ → trans-reflˡ _)
                                                 z≡x f ⟩∎
      _≃_.to (f z) z≡x                   ∎

-- One can introduce a universal quantifier by also introducing an
-- equality (assuming extensionality).

∀-intro : ∀ {a b} →
          Extensionality a (a ⊔ b) →
          {A : Set a} {x : A} (B : (y : A) → x ≡ y → Set b) →
          B x (refl x) ↔ (∀ y (x≡y : x ≡ y) → B y x≡y)
∀-intro {a} ext {x = x} B = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = λ f → f x (refl x)
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : B x (refl x) → ∀ y (x≡y : x ≡ y) → B y x≡y
  to b y x≡y =
    subst (uncurry B)
          (proj₂ (other-singleton-contractible x) (y , x≡y))
          b

  abstract

    from∘to : ∀ b → to b x (refl x) ≡ b
    from∘to b =
      subst (uncurry B)
            (proj₂ (other-singleton-contractible x) (x , refl x)) b  ≡⟨ cong (λ eq → subst (uncurry B) eq b) $
                                                                             other-singleton-contractible-refl x ⟩
      subst (uncurry B) (refl (x , refl x)) b                        ≡⟨ subst-refl (uncurry B) _ ⟩∎
      b                                                              ∎

    to∘from : ∀ f → to (f x (refl x)) ≡ f
    to∘from f = ext λ y → lower-extensionality lzero a ext λ x≡y →
      elim¹ (λ {y} x≡y →
               subst (uncurry B)
                     (proj₂ (other-singleton-contractible x) (y , x≡y))
                     (f x (refl x)) ≡
               f y x≡y)
            (subst (uncurry B)
                   (proj₂ (other-singleton-contractible x) (x , refl x))
                   (f x (refl x))                                         ≡⟨ from∘to (f x (refl x)) ⟩∎
             f x (refl x)                                                 ∎)
            x≡y

-- Equality expression rearrangement lemmas.

from≡↔≡to : ∀ {a b k} →
            {A : Set a} {B : Set b}
            (A≃B : A ≃ B) {x : B} {y : A} →
            (_≃_.from A≃B x ≡ y) ↔[ k ] (x ≡ _≃_.to A≃B y)
from≡↔≡to A≃B {x} {y} =
  (_≃_.from A≃B x ≡ y)                          ↔⟨ inverse $ Eq.≃-≡ A≃B ⟩
  (_≃_.to A≃B (_≃_.from A≃B x) ≡ _≃_.to A≃B y)  ↝⟨ ≡⇒↝ _ $ cong (λ z → z ≡ _≃_.to A≃B y) $ _≃_.right-inverse-of A≃B x ⟩□
  (x ≡ _≃_.to A≃B y)                            □

∘from≡↔≡∘to : ∀ {a b c k} →
              Extensionality (a ⊔ b) c →
              {A : Set a} {B : Set b} {C : Set c}
              (A≃B : A ≃ B) {f : A → C} {g : B → C} →
              (f ∘ _≃_.from A≃B ≡ g) ↔[ k ] (f ≡ g ∘ _≃_.to A≃B)
∘from≡↔≡∘to ext A≃B = from≡↔≡to (→-cong ext (inverse A≃B) Eq.id)

to∘≡↔≡from∘ : ∀ {a b c k} →
              Extensionality a (b ⊔ c) →
              {A : Set a} {B : A → Set b} {C : A → Set c}
              (B≃C : ∀ {x} → B x ≃ C x)
              {f : (x : A) → B x} {g : (x : A) → C x} →
              (_≃_.to B≃C ⊚ f ≡ g) ↔[ k ] (f ≡ _≃_.from B≃C ⊚ g)
to∘≡↔≡from∘ ext B≃C =
  from≡↔≡to (Eq.∀-preserves ext (λ _ → inverse B≃C))

------------------------------------------------------------------------
-- Lemmas related to ↑

-- ↑ _ preserves all kinds of functions.

private

  ↑-cong-→ :
    ∀ {a b c} {B : Set b} {C : Set c} →
    (B → C) → ↑ a B → ↑ a C
  ↑-cong-→ B→C = lift ⊚ B→C ⊚ lower

  ↑-cong-⇔ :
    ∀ {a b c} {B : Set b} {C : Set c} →
    B ⇔ C → ↑ a B ⇔ ↑ a C
  ↑-cong-⇔ B⇔C = record
    { to   = ↑-cong-→ to
    ; from = ↑-cong-→ from
    } where open _⇔_ B⇔C

  ↑-cong-↣ :
    ∀ {a b c} {B : Set b} {C : Set c} →
    B ↣ C → ↑ a B ↣ ↑ a C
  ↑-cong-↣ {a} B↣C = record
    { to        = to′
    ; injective = injective′
    }
    where
    open _↣_ B↣C

    to′ = ↑-cong-→ {a = a} to

    abstract
      injective′ : Injective to′
      injective′ = cong lift ⊚ injective ⊚ cong lower

  ↑-cong-↠ :
    ∀ {a b c} {B : Set b} {C : Set c} →
    B ↠ C → ↑ a B ↠ ↑ a C
  ↑-cong-↠ {a} B↠C = record
    { logical-equivalence = logical-equivalence′
    ; right-inverse-of    = right-inverse-of′
    }
    where
    open _↠_ B↠C renaming (logical-equivalence to logical-equiv)

    logical-equivalence′ = ↑-cong-⇔ {a = a} logical-equiv

    abstract
      right-inverse-of′ : ∀ x →
                          _⇔_.to logical-equivalence′
                            (_⇔_.from logical-equivalence′ x) ≡
                          x
      right-inverse-of′ = cong lift ⊚ right-inverse-of ⊚ lower

  ↑-cong-↔ :
    ∀ {a b c} {B : Set b} {C : Set c} →
    B ↔ C → ↑ a B ↔ ↑ a C
  ↑-cong-↔ {a} B↔C = record
    { surjection      = surjection′
    ; left-inverse-of = left-inverse-of′
    }
    where
    open _↔_ B↔C renaming (surjection to surj)

    surjection′ = ↑-cong-↠ {a = a} surj

    abstract
      left-inverse-of′ :
        ∀ x → _↠_.from surjection′ (_↠_.to surjection′ x) ≡ x
      left-inverse-of′ = cong lift ⊚ left-inverse-of ⊚ lower

↑-cong : ∀ {k a b c} {B : Set b} {C : Set c} →
           B ↝[ k ] C → ↑ a B ↝[ k ] ↑ a C
↑-cong {implication}         = ↑-cong-→
↑-cong {logical-equivalence} = ↑-cong-⇔
↑-cong {injection}           = ↑-cong-↣
↑-cong {surjection}          = ↑-cong-↠
↑-cong {bijection}           = ↑-cong-↔
↑-cong {equivalence}         =
  from-bijection ∘ ↑-cong-↔ ∘ from-equivalence

------------------------------------------------------------------------
-- Lemmas related to if

-- A generalisation of if-encoding (which is defined below).

if-lemma : ∀ {a b p} {A : Set a} {B : Set b} (P : Bool → Set p) →
           A ↔ P true → B ↔ P false →
           ∀ b → T b × A ⊎ T (not b) × B ↔ P b
if-lemma {A = A} {B} P A↔ B↔ true =
  ⊤ × A ⊎ ⊥ × B  ↔⟨ ×-left-identity ⊎-cong ×-left-zero ⟩
  A ⊎ ⊥₀         ↔⟨ ⊎-right-identity ⟩
  A              ↔⟨ A↔ ⟩
  P true         □
if-lemma {A = A} {B} P A↔ B↔ false =
  ⊥ × A ⊎ ⊤ × B  ↔⟨ ×-left-zero ⊎-cong ×-left-identity ⟩
  ⊥₀ ⊎ B         ↔⟨ ⊎-left-identity ⟩
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
    { logical-equivalence = record
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
    { logical-equivalence = record
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
