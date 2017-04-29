------------------------------------------------------------------------
-- Results relating different instances of certain axioms related to
-- equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equality.Instances-related where

import Bijection
open import Equality
import Equivalence
import Function-universe
import H-level
import H-level.Closure
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (id)

-- All families of equality types that satisfy certain axioms are
-- pointwise isomorphic. One of the families are used to define what
-- "isomorphic" means.

all-equality-types-isomorphic :
  ∀ {refl₁ refl₂}
  (eq₁ : ∀ {a p} → Equality-with-J a p refl₁)
  (eq₂ : ∀ {a p} → Equality-with-J a p refl₂) →
  let open Bijection eq₁ in
  ∀ {a} {A : Set a} {x y : A} →
  Reflexive-relation′._≡_ refl₁ x y ↔ Reflexive-relation′._≡_ refl₂ x y
all-equality-types-isomorphic {refl₁} {refl₂} eq₁ eq₂ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to refl₂ eq₁
      ; from = to refl₁ eq₂
      }
    ; right-inverse-of = λ x≡y → to refl₁ eq₂ (to∘to _ _ eq₂ eq₁ x≡y)
    }
  ; left-inverse-of = to∘to _ _ eq₁ eq₂
  }
  where
  open Reflexive-relation′
  open Equality-with-J′ hiding (_≡_; refl)

  to : ∀ {refl₁} refl₂ (eq₁ : ∀ {a p} → Equality-with-J a p refl₁)
       {a} {A : Set a} {x y : A} →
       _≡_ refl₁ x y → _≡_ refl₂ x y
  to refl₂ eq₁ {x = x} x≡y = subst eq₁ (_≡_ refl₂ x) x≡y (refl refl₂ x)

  to∘to : ∀ refl₁ refl₂
          (eq₁ : ∀ {a p} → Equality-with-J a p refl₁)
          (eq₂ : ∀ {a p} → Equality-with-J a p refl₂) →
          ∀ {a} {A : Set a} {x y : A} (x≡y : _≡_ refl₁ x y) →
          _≡_ refl₁ (to refl₁ eq₂ (to refl₂ eq₁ x≡y)) x≡y
  to∘to refl₁ refl₂ eq₁ eq₂ = elim eq₁
    (λ {x y} x≡y → _≡_ refl₁ (to refl₁ eq₂ (to refl₂ eq₁ x≡y)) x≡y)
    (λ x → to refl₁ eq₂ (to refl₂ eq₁ (refl refl₁ x))  ≡⟨ cong eq₁ (to refl₁ eq₂) (subst-refl eq₁ (_≡_ refl₂ x) (refl refl₂ x)) ⟩
           to refl₁ eq₂ (refl refl₂ x)                 ≡⟨ to refl₁ eq₂ $ subst-refl eq₂ (_≡_ refl₁ x) (refl refl₁ x) ⟩∎
           refl refl₁ x                                ∎)
    where
    open Derived-definitions-and-properties eq₁
      using (step-≡; finally)

module _ {reflexive}
         (eq : ∀ {a p} → Equality-with-J a p reflexive)
         where

  open Bijection eq hiding (id; inverse; step-↔)
  open Derived-definitions-and-properties eq
  open Equivalence eq hiding (id; inverse)
  open Function-universe eq
  open H-level.Closure eq

  abstract

    -- The type Equality-with-J a p reflexive is contractible (given
    -- the assumptions in the telescope above, and assuming
    -- extensionality). A slight variant of this observation came up
    -- in a discussion between Thierry Coquand, Simon Huber and
    -- Nicolai Kraus. The proof is based on one due to Nicolai Kraus.

    Equality-with-J-contractible :
      ∀ {a p} →
      Extensionality (lsuc (a ⊔ p)) (a ⊔ lsuc p) →
      Contractible (Equality-with-J a p reflexive)
    Equality-with-J-contractible {a} {p} ext =                     $⟨ contr ⟩
      Contractible ({A : Set a} (P : A → Set p) (r : ∀ x → P x) →
                    Singleton r)                                   ↝⟨ H-level.respects-surjection eq surj 0 ⟩
      Contractible (Equality-with-J a p reflexive)                 □
      where
      contr :
        Contractible ({A : Set a} (P : A → Set p) (r : ∀ x → P x) →
                      Singleton r)
      contr =
        implicit-Π-closure (lower-extensionality (lsuc p) lzero    ext) 0 λ _ →
        Π-closure          (lower-extensionality (lsuc a) (lsuc p) ext) 0 λ _ →
        Π-closure          (lower-extensionality _        (lsuc p) ext) 0 λ _ →
        singleton-contractible _

      lemma : ∀ {q} {A : Set a} {Q : A → Set q} →
              Extensionality a (a ⊔ q) →
              (∀ x → Q x) ↔ (∀ {x y} → x ≡ y → Q x)
      lemma {q} {Q = Q} ext =
        (∀ x → Q x)                    ↝⟨ ∀-cong (lower-extensionality lzero a ext) (λ _ → inverse Π-left-identity) ⟩
        (∀ x → ⊤ → Q x)                ↝⟨ ∀-cong ext (λ _ →
                                          →-cong (lower-extensionality lzero a ext)
                                            (inverse $ _⇔_.to contractible⇔↔⊤ $ other-singleton-contractible _)
                                            id) ⟩
        (∀ x → (∃ λ y → x ≡ y) → Q x)  ↝⟨ ∀-cong ext (λ _ → currying) ⟩
        (∀ x y → x ≡ y → Q x)          ↝⟨ ∀-cong ext (λ _ → inverse implicit-Π↔Π) ⟩
        (∀ x → ∀ {y} → x ≡ y → Q x)    ↝⟨ inverse implicit-Π↔Π ⟩□
        (∀ {x y} → x ≡ y → Q x)        □

      surj =
        ({A : Set a} (P : A → Set p) (r : ∀ x → P x) →
         Singleton r)                                               ↔⟨ implicit-∀-cong (lower-extensionality (lsuc p) lzero ext) $
                                                                       ∀-cong (lower-extensionality (lsuc a) (lsuc p) ext) (λ _ →
                                                                       ∀-cong (lower-extensionality _ (lsuc p) ext) λ _ →
                                                                       ∃-cong λ _ → inverse $
                                                                       extensionality-isomorphism (lower-extensionality _ _ ext)) ⟩
        ({A : Set a} (P : A → Set p) (r : ∀ x → P x) →
         ∃ λ (elim : ∀ x → P x) → ∀ x → elim x ≡ r x)               ↔⟨ implicit-∀-cong (lower-extensionality (lsuc p) lzero ext) $
                                                                       Π-preserves (lower-extensionality (lsuc a) (lsuc p) ext)
                                                                         (↔⇒≃ $ lemma (lower-extensionality _ lzero ext)) (λ _ →
                                                                       ∀-cong (lower-extensionality _ (lsuc p) ext) λ _ →
                                                                       Σ-cong (lemma (lower-extensionality _ (lsuc p) ext)) λ _ →
                                                                              (↔⇒≃ $ inverse implicit-Π↔Π)) ⟩
        ({A : Set a}
         (P : {x y : A} → x ≡ y → Set p)
         (r : ∀ x → P (refl x)) →
         ∃ λ (elim : ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
           ∀ {x} → elim (refl x) ≡ r x)                             ↔⟨ implicit-∀-cong (lower-extensionality (lsuc p) lzero ext) $
                                                                       ∀-cong (lower-extensionality (lsuc a) (lsuc p) ext) (λ _ →
                                                                       ΠΣ-comm) ⟩
        ({A : Set a}
         (P : {x y : A} → x ≡ y → Set p) →
         ∃ λ (elim : (∀ x → P (refl x)) →
                     ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
           (r : ∀ x → P (refl x)) →
           ∀ {x} → elim r (refl x) ≡ r x)                           ↔⟨ implicit-∀-cong (lower-extensionality (lsuc p) lzero ext)
                                                                       ΠΣ-comm ⟩
        ({A : Set a} →
         ∃ λ (elim : (P : {x y : A} → x ≡ y → Set p) →
                     (∀ x → P (refl x)) →
                     ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
           (P : {x y : A} → x ≡ y → Set p)
           (r : ∀ x → P (refl x)) →
           ∀ {x} → elim P r (refl x) ≡ r x)                         ↔⟨ implicit-ΠΣ-comm ⟩

        (∃ λ (elim : {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
                     (∀ x → P (refl x)) →
                     ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
             ∀ {A : Set a} (P : {x y : A} → x ≡ y → Set p)
             (r : ∀ x → P (refl x)) {x} →
             elim P r (refl x) ≡ r x)                               ↝⟨ record
                                                                         { logical-equivalence = record
                                                                           { to   = uncurry λ elim elim-refl → record
                                                                                      { elim      = λ {_} → elim      {_}
                                                                                      ; elim-refl = λ {_} → elim-refl {_}
                                                                                      }
                                                                           ; from = λ eq → Equality-with-J.elim      eq
                                                                                         , Equality-with-J.elim-refl eq
                                                                           }
                                                                         ; right-inverse-of = refl
                                                                         } ⟩□
        Equality-with-J a p reflexive                               □
