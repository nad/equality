------------------------------------------------------------------------
-- Pointed types and loop spaces
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Largely but not entirely following the HoTT book.

open import Equality

module Pointed-type
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Equivalence eq as E using (_≃_)
open import Function-universe eq hiding (id; _∘_)
open import H-level eq
open import Surjection eq using (_↠_)

-- Pointed types.

Pointed-type : ∀ ℓ → Type (lsuc ℓ)
Pointed-type a = ∃ λ (A : Type a) → A

private
  variable
    a b ℓ : Level
    A B   : Type a
    P Q   : Pointed-type a
    x     : A
    k     : Kind

-- Based maps (generalised to several kinds of underlying
-- "functions").

infix 4 _↝[_]ᴮ_ _→ᴮ_ _≃ᴮ_

_↝[_]ᴮ_ : Pointed-type a → Kind → Pointed-type b → Type (a ⊔ b)
(A , x) ↝[ k ]ᴮ (B , y) =
  ∃ λ (f : A ↝[ k ] B) → to-implication f x ≡ y

-- Based maps.

_→ᴮ_ : Pointed-type a → Pointed-type b → Type (a ⊔ b)
_→ᴮ_ = _↝[ implication ]ᴮ_

-- Based equivalences.

_≃ᴮ_ : Pointed-type a → Pointed-type b → Type (a ⊔ b)
_≃ᴮ_ = _↝[ equivalence ]ᴮ_

-- The loop space of a pointed type.

Ω : Pointed-type ℓ → Pointed-type ℓ
Ω (A , x) = (x ≡ x) , refl x

-- Iterated loop spaces.
--
-- The HoTT book uses Ω[ n ] ∘ Ω rather than Ω ∘ Ω[ n ]. I prefer
-- the following definition, because with the other definition the
-- type of Equality.Groupoid.Ω[2+n]-commutative would not be
-- well-formed. (See also Ω∘Ω[]≡Ω[]∘Ω.)

Ω[_] : ℕ → Pointed-type ℓ → Pointed-type ℓ
Ω[ zero  ] = id
Ω[ suc n ] = Ω ∘ Ω[ n ]

-- A rearrangement lemma for Ω and Ω[_].

Ω∘Ω[]≡Ω[]∘Ω : ∀ n → Ω (Ω[ n ] P) ≡ Ω[ n ] (Ω P)
Ω∘Ω[]≡Ω[]∘Ω {P = P} zero =
  Ω P  ∎
Ω∘Ω[]≡Ω[]∘Ω {P = P} (suc n) =
  Ω (Ω[ suc n ] P)  ≡⟨⟩
  Ω (Ω (Ω[ n ] P))  ≡⟨ cong Ω $ Ω∘Ω[]≡Ω[]∘Ω n ⟩
  Ω (Ω[ n ] (Ω P))  ≡⟨⟩
  Ω[ suc n ] (Ω P)  ∎

-- There is a split surjection from based maps from
-- (Maybe A , nothing) to functions.

Maybe→ᴮ↠→ : (Maybe A , nothing) →ᴮ (B , x) ↠ (A → B)
Maybe→ᴮ↠→ {A = A} {B = B} {x = x} = record
  { logical-equivalence = record
    { to   = (Maybe A , nothing) →ᴮ (B , x)  ↝⟨ proj₁ ⟩
             (Maybe A → B)                   ↝⟨ _∘ inj₂ ⟩□
             (A → B)                         □
    ; from = λ f → [ (λ _ → x) , f ] , refl x
    }
  ; right-inverse-of = refl
  }

-- Based maps from (Maybe A , nothing) are isomorphic to functions
-- (assuming extensionality).

Maybe→ᴮ↔→ :
  ∀ {A : Type a} {B : Type b} {x} →
  Extensionality? k a b →
  (Maybe A , nothing) →ᴮ (B , x) ↝[ k ] (A → B)
Maybe→ᴮ↔→ {A = A} {B} {x} = generalise-ext?
  (_↠_.logical-equivalence Maybe→ᴮ↠→)
  (λ ext → record
     { surjection      = Maybe→ᴮ↠→
     ; left-inverse-of = λ { (f , eq) → Σ-≡,≡→≡
         (apply-ext (E.good-ext ext)
            [ (λ _ →
                 x          ≡⟨ sym eq ⟩∎
                 f nothing  ∎)
            , (λ _ → refl _)
            ])
         (subst (λ f → f nothing ≡ x)
                (apply-ext (E.good-ext ext)
                   [ (λ _ → sym eq) , (λ _ → refl _) ])
                (refl x)                                 ≡⟨ E.subst-good-ext ext _ _ ⟩

          subst (_≡ x) (sym eq) (refl x)                 ≡⟨ subst-trans _ ⟩

          trans eq (refl x)                              ≡⟨ trans-reflʳ _ ⟩∎

          eq                                             ∎) }
     })

-- A corollary.

Bool→ᴮ↔ :
  ∀ {A : Type a} {x} →
  Extensionality? k lzero a →
  (Bool , true) →ᴮ (A , x) ↝[ k ] A
Bool→ᴮ↔ {A = A} {x = x} ext =
  (Bool , true) →ᴮ (A , x)  ↝⟨ Maybe→ᴮ↔→ ext ⟩
  (⊤ → A)                   ↔⟨ Π-left-identity ⟩□
  A                         □

-- Ω preserves based equivalences.

Ω-cong : P ≃ᴮ Q → Ω P ≃ᴮ Ω Q
Ω-cong {P = A , x} {Q = B , y} (A≃B , to≡) =
    (x ≡ x                        ↝⟨ inverse $ E.≃-≡ A≃B ⟩
     _≃_.to A≃B x ≡ _≃_.to A≃B x  ↝⟨ ≡⇒↝ _ $ cong₂ _≡_ to≡ to≡ ⟩□
     y ≡ y                        □)
  , (_≃_.to (≡⇒↝ _ $ cong₂ _≡_ to≡ to≡) (_≃_.from (E.≃-≡ A≃B) (refl x))  ≡⟨⟩
     _≃_.to (≡⇒↝ _ $ cong₂ _≡_ to≡ to≡) (cong (_≃_.to A≃B) (refl x))     ≡⟨ cong (_≃_.to (≡⇒↝ _ $ cong₂ _≡_ to≡ to≡)) $ cong-refl _ ⟩
     _≃_.to (≡⇒↝ _ $ cong₂ _≡_ to≡ to≡) (refl (_≃_.to A≃B x))            ≡⟨ elim¹
                                                                              (λ to≡ → _≃_.to (≡⇒↝ _ $ cong₂ _≡_ to≡ to≡) (refl (_≃_.to A≃B x)) ≡
                                                                                       refl _)
                                                                              (
         _≃_.to (≡⇒↝ _ $ cong₂ _≡_ (refl _) (refl _)) (refl _)                 ≡⟨ cong (λ eq → _≃_.to (≡⇒↝ _ eq) (refl _)) $ cong₂-refl _≡_ ⟩
         _≃_.to (≡⇒↝ _ $ refl _) (refl _)                                      ≡⟨ cong (λ eq → _≃_.to eq (refl _)) ≡⇒↝-refl ⟩∎
         refl _                                                                ∎)
                                                                              _ ⟩∎
     refl y                                                              ∎)

-- Ω[ n ] preserves based equivalences.

Ω[_]-cong : ∀ n → P ≃ᴮ Q → Ω[ n ] P ≃ᴮ Ω[ n ] Q
Ω[ zero  ]-cong A≃B = A≃B
Ω[ suc n ]-cong A≃B = Ω-cong (Ω[ n ]-cong A≃B)

-- A has h-level 1 + n iff the iterated loop space Ω[ n ] (A , x) is
-- contractible for every x : A.

+⇔∀contractible-Ω[] :
  ∀ n →
  H-level (1 + n) A
    ⇔
  ((x : A) → Contractible (proj₁ $ Ω[ n ] (A , x)))
+⇔∀contractible-Ω[] {A = A} zero =
  Is-proposition A      ↝⟨ record { to   = propositional⇒inhabited⇒contractible
                                  ; from = [inhabited⇒contractible]⇒propositional
                                  } ⟩□
  (A → Contractible A)  □

+⇔∀contractible-Ω[] {A = A} (suc zero) =
  Is-set A                            ↝⟨ 2+⇔∀1+≡ 0 ⟩
  ((x : A) → Is-proposition (x ≡ x))  ↝⟨ (∀-cong _ λ x → record { to   = flip propositional⇒inhabited⇒contractible (refl x)
                                                                ; from = mono₁ 0
                                                                }) ⟩□
  ((x : A) → Contractible (x ≡ x))    □

+⇔∀contractible-Ω[] {A = A} (suc (suc n)) =
  H-level (3 + n) A                                                  ↝⟨ 2+⇔∀1+≡ (1 + n) ⟩

  ((x : A) → H-level (2 + n) (x ≡ x))                                ↝⟨ (∀-cong _ λ _ → +⇔∀contractible-Ω[] (suc n)) ⟩

  ((x : A) (p : x ≡ x) →
   Contractible (proj₁ $ Ω[ 1 + n ] ((x ≡ x) , p)))                  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → H-level-cong _ _ $ proj₁ $
                                                                         Ω[ 1 + n ]-cong $ lemma _) ⟩

  ((x : A) → x ≡ x → Contractible (proj₁ $ Ω[ 1 + n ] (Ω (A , x))))  ↝⟨ (∀-cong _ λ x → _↠_.logical-equivalence $ inhabited→↠ (refl x)) ⟩

  ((x : A) → Contractible (proj₁ $ Ω[ 1 + n ] (Ω (A , x))))          ↝⟨ (∀-cong _ λ _ → ≡⇒↝ _ $ cong (Contractible ∘ proj₁) $ sym $
                                                                         Ω∘Ω[]≡Ω[]∘Ω (1 + n)) ⟩□
  ((x : A) → Contractible (proj₁ $ Ω[ 2 + n ] (A , x)))              □
  where
  lemma : (p : x ≡ x) → ((x ≡ x) , p) ≃ᴮ Ω (A , x)
  lemma p = E.↔⇒≃ (inverse $ flip-trans-isomorphism p)
          , (trans p (sym p)  ≡⟨ trans-symʳ _ ⟩∎
             refl _           ∎)
