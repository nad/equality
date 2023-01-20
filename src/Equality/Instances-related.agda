------------------------------------------------------------------------
-- Results relating different instances of certain axioms related to
-- equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Equality.Instances-related where

import Bijection
open import Equality
import Equivalence
import Extensionality
import Function-universe
import H-level
import H-level.Closure
open import Logical-equivalence using (_⇔_)
open import Prelude
import Surjection

private
  module E (e⁺ : ∀ e → Equivalence-relation⁺ e) where
    open Reflexive-relation′
           (λ e → Equivalence-relation⁺.reflexive-relation (e⁺ e))
         public

-- All families of equality types that satisfy certain axioms are
-- pointwise isomorphic. One of the families are used to define what
-- "isomorphic" means.
--
-- The isomorphisms map reflexivity to reflexivity in both directions.
--
-- Hofmann and Streicher prove something similar in "The groupoid
-- interpretation of type theory".

all-equality-types-isomorphic :
  ∀ {e₁ e₂}
  (eq₁ : ∀ {a p} → Equality-with-J a p e₁)
  (eq₂ : ∀ {a p} → Equality-with-J a p e₂) →
  let open Bijection eq₁ in
  ∀ {a} {A : Type a} →
  ∃ λ (iso : {x y : A} → E._≡_ e₁ x y ↔ E._≡_ e₂ x y) →
    (∀ {x} → E._≡_ e₂ (_↔_.to   iso (E.refl e₁ x)) (E.refl e₂ x)) ×
    (∀ {x} → E._≡_ e₁ (_↔_.from iso (E.refl e₂ x)) (E.refl e₁ x))
all-equality-types-isomorphic {e₁ = c₁} {e₂ = c₂} eq₁ eq₂ =
    record
      { surjection = record
        { logical-equivalence = record
          { to   = to c₂ eq₁
          ; from = to c₁ eq₂
          }
        ; right-inverse-of = to c₁ eq₂ ∘ to∘to _ _ eq₂ eq₁
        }
      ; left-inverse-of = to∘to _ _ eq₁ eq₂
      }
  , to-refl c₂ eq₁
  , to-refl c₁ eq₂
  where
  open E
  open module Eq {c} (eq : ∀ {a p} → Equality-with-J a p c) =
    Equality-with-J′ eq hiding (_≡_; refl)

  to : ∀ {c₁} c₂ (eq₁ : ∀ {a p} → Equality-with-J a p c₁)
       {a} {A : Type a} {x y : A} →
       _≡_ c₁ x y → _≡_ c₂ x y
  to c₂ eq₁ {x} x≡y = subst eq₁ (_≡_ c₂ x) x≡y (refl c₂ x)

  to-refl :
    ∀ {c₁} c₂ (eq₁ : ∀ {a p} → Equality-with-J a p c₁)
    {a} {A : Type a} {x : A} →
    _≡_ c₂ (to c₂ eq₁ (refl c₁ x)) (refl c₂ x)
  to-refl c₂ eq₁ = to c₂ eq₁ $ subst-refl eq₁ (_≡_ c₂ _) _

  to∘to : ∀ c₁ c₂
          (eq₁ : ∀ {a p} → Equality-with-J a p c₁)
          (eq₂ : ∀ {a p} → Equality-with-J a p c₂) →
          ∀ {a} {A : Type a} {x y : A} (x≡y : _≡_ c₁ x y) →
          _≡_ c₁ (to c₁ eq₂ (to c₂ eq₁ x≡y)) x≡y
  to∘to c₁ c₂ eq₁ eq₂ = elim eq₁
    (λ {x y} x≡y → _≡_ c₁ (to c₁ eq₂ (to c₂ eq₁ x≡y)) x≡y)
    (λ x → to c₁ eq₂ (to c₂ eq₁ (refl c₁ x))  ≡⟨ cong eq₁ (to c₁ eq₂) (subst-refl eq₁ (_≡_ c₂ x) (refl c₂ x)) ⟩
           to c₁ eq₂ (refl c₂ x)              ≡⟨ to c₁ eq₂ $ subst-refl eq₂ (_≡_ c₁ x) (refl c₁ x) ⟩∎
           refl c₁ x                          ∎)
    where
    open Derived-definitions-and-properties eq₁
      using (step-≡; finally)

module _ {congruence⁺}
         (eq : ∀ {a p} → Equality-with-J a p congruence⁺)
         where

  open Derived-definitions-and-properties eq
  open Extensionality eq
  open Function-universe eq hiding (_∘_) renaming (id to ⟨id⟩)
  open H-level.Closure eq
  open Surjection eq using (_↠_)

  private
    open module Eq = Equivalence eq using (_≃_)

  abstract

    -- The type Equality-with-J₀ a p reflexive-relation is
    -- contractible (given the assumptions in the telescope above, and
    -- assuming extensionality). A slight variant of this observation
    -- came up in a discussion between Thierry Coquand, Simon Huber
    -- and Nicolai Kraus. The proof is based on one due to Nicolai
    -- Kraus.

    Equality-with-J-contractible :
      ∀ {a p} →
      Extensionality (lsuc (a ⊔ p)) (a ⊔ lsuc p) →
      Contractible (Equality-with-J₀ a p (λ _ → reflexive-relation))
    Equality-with-J-contractible {a} {p} ext =                        $⟨ contr ⟩
      Contractible ((A : Type a) (P : I A → Type p)
                    (d : ∀ x → P (to x)) → Singleton d)               ↝⟨ H-level.respects-surjection eq surj 0 ⟩

      Contractible (Equality-with-J₀ a p (λ _ → reflexive-relation))  □
      where
      I : Type a → Type a
      I A = ∃ λ (x : A) → ∃ λ (y : A) → x ≡ y

      to : ∀ {A} → A → I A
      to x = x , x , refl x

      ≃I : ∀ {A} → A ≃ I A
      ≃I = Eq.↔⇒≃ (record
        { surjection = record
          { logical-equivalence = record
            { to   = to
            ; from = proj₁
            }
          ; right-inverse-of = λ q →
              let x , y , x≡y = q in
              cong (x ,_) $
                Σ-≡,≡→≡ x≡y
                        (subst (x ≡_) x≡y (refl x)  ≡⟨ sym trans-subst ⟩
                         trans (refl x) x≡y         ≡⟨ trans-reflˡ x≡y ⟩∎
                         x≡y                        ∎)
          }
        ; left-inverse-of = refl
        })

      contr :
        Contractible ((A : Type a) (P : I A → Type p)
                      (d : ∀ x → P (to x)) → Singleton d)
      contr =
        Π-closure          (lower-extensionality (lsuc p) lzero    ext) 0 λ _ →
        Π-closure          (lower-extensionality (lsuc a) (lsuc p) ext) 0 λ _ →
        Π-closure          (lower-extensionality _        (lsuc p) ext) 0 λ _ →
        singleton-contractible _

      surj :
        ((A : Type a) (P : I A → Type p)
         (d : ∀ x → P (to x)) → Singleton d) ↠
        Equality-with-J₀ a p (λ _ → reflexive-relation)
      surj =
        ((A : Type a) (P : I A → Type p)
         (d : ∀ x → P (to x)) → Singleton d)                    ↔⟨⟩

        ((A : Type a) (P : I A → Type p)
         (d : ∀ x → P (to x)) →
         ∃ λ (j : (x : A) → P (to x)) → j ≡ d)                  ↔⟨ (∀-cong (lower-extensionality (lsuc p) lzero ext) λ _ →
                                                                              ∀-cong (lower-extensionality (lsuc a) (lsuc p) ext) λ _ →
                                                                              ∀-cong (lower-extensionality _ (lsuc p) ext) λ _ →
                                                                              ∃-cong λ _ → inverse $
                                                                              Eq.extensionality-isomorphism (lower-extensionality _ _ ext)) ⟩
        ((A : Type a) (P : I A → Type p)
         (d : ∀ x → P (to x)) →
         ∃ λ (j : (x : A) → P (to x)) → (x : A) → j x ≡ d x)    ↔⟨ (∀-cong (lower-extensionality (lsuc p) lzero ext) λ _ →
                                                                              ∀-cong (lower-extensionality (lsuc a) (lsuc p) ext) λ _ →
                                                                              ∀-cong (lower-extensionality _ (lsuc p) ext) λ _ → inverse $
                                                                              Σ-cong (inverse $ Π-cong (lower-extensionality _ _ ext)
                                                                                                       ≃I λ _ → ⟨id⟩ {k = equivalence}) λ _ →
                                                                              ⟨id⟩ {k = equivalence}) ⟩
        ((A : Type a) (P : I A → Type p)
         (d : ∀ x → P (to x)) →
         ∃ λ (j : (q : I A) → P q) → (x : A) → j (to x) ≡ d x)  ↔⟨ (∀-cong (lower-extensionality (lsuc p) lzero ext) λ _ →
                                                                              ∀-cong (lower-extensionality (lsuc a) (lsuc p) ext) λ _ →
                                                                              ΠΣ-comm) ⟩
        ((A : Type a) (P : I A → Type p) →
         ∃ λ (j : (d : ∀ x → P (to x)) →
                  (q : I A) → P q) →
             (d : ∀ x → P (to x))
             (x : A) → j d (to x) ≡ d x)                        ↔⟨ (∀-cong (lower-extensionality (lsuc p) lzero ext) λ _ →
                                                                              ΠΣ-comm) ⟩
        ((A : Type a) →
         ∃ λ (j : (P : I A → Type p) (d : ∀ x → P (to x)) →
                  (q : I A) → P q) →
             (P : I A → Type p) (d : ∀ x → P (to x))
             (x : A) → j P d (to x) ≡ d x)                      ↔⟨ ΠΣ-comm ⟩

        (∃ λ (J : (A : Type a) (P : I A → Type p)
                  (d : ∀ x → P (to x)) →
                  (q : I A) → P q) →
             (A : Type a) (P : I A → Type p)
             (d : ∀ x → P (to x))
             (x : A) → J A P d (to x) ≡ d x)                    ↝⟨ record
                                                                     { logical-equivalence = record
                                                                       { to   = uncurry λ J Jβ → record
                                                                                  { elim      = λ P r x≡y →
                                                                                                  J _ (P ∘ proj₂ ∘ proj₂) r (_ , _ , x≡y)
                                                                                  ; elim-refl = λ P r → Jβ _ (P ∘ proj₂ ∘ proj₂) r _
                                                                                  }
                                                                       ; from = λ eq →
                                                                             (λ A P d q → Equality-with-J₀.elim eq
                                                                                            (λ x≡y → P (_ , _ , x≡y)) d (proj₂ (proj₂ q)))
                                                                           , (λ A P d x → Equality-with-J₀.elim-refl eq
                                                                                            (λ x≡y → P (_ , _ , x≡y)) d)
                                                                       }
                                                                     ; right-inverse-of = refl
                                                                     } ⟩□
        Equality-with-J₀ a p (λ _ → reflexive-relation)         □

  private

    -- A related example. It had been suggested that the two proofs
    -- proof₁ and proof₂ below might not be provably equal, but Simon
    -- Huber managed to prove that they are (using a slightly
    -- different type for elim-refl).

    module _ {a p} {A : Type a}
             (P : A → Type p)
             {x : A} (y : P x) where

      subst′ : {x y : A} (P : A → Type p) → x ≡ y → P x → P y
      subst′ P = elim (λ {u v} _ → P u → P v) (λ _ p → p)

      subst′-refl≡id : {x : A} (P : A → Type p) → subst′ P (refl x) ≡ id
      subst′-refl≡id P = elim-refl (λ {u v} _ → P u → P v) (λ _ p → p)

      proof₁ proof₂ :
        subst′ P (refl x) (subst′ P (refl x) y) ≡ subst′ P (refl x) y

      proof₁ = cong (_$ subst′ P (refl x) y) (subst′-refl≡id P)

      proof₂ = cong (subst′ P (refl x)) (cong (_$ y) (subst′-refl≡id P))

      proof₁≡proof₂ : proof₁ ≡ proof₂
      proof₁≡proof₂ =
        subst (λ (s : Singleton id) →
                 ∀ y → cong (_$ proj₁ s y) (proj₂ s) ≡
                       cong (proj₁ s) (cong (_$ y) (proj₂ s)))

              (id                , refl id           ≡⟨ proj₂ (singleton-contractible _) _ ⟩∎
               subst′ P (refl x) , subst′-refl≡id P  ∎)

              (λ y →
                 cong (_$ y) (refl id)            ≡⟨ cong-id _ ⟩∎
                 cong id (cong (_$ y) (refl id))  ∎)

              y
