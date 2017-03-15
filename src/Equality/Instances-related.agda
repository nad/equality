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
open import Logical-equivalence using (_⇔_)
open import Prelude
import Surjection

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

  open Derived-definitions-and-properties eq
  open Equivalence eq hiding (inverse)
  open Function-universe eq
  open H-level eq
  open Surjection eq

  abstract

    -- The type Equality-with-J a p reflexive is contractible (given
    -- the assumptions in the telescope above, and assuming
    -- extensionality). A slight variant of this observation came up
    -- in a discussion between Thierry Coquand, Simon Huber and
    -- Nicolai Kraus.

    Equality-with-J-contractible :
      ∀ {a p} →
      Extensionality (lsuc (a ⊔ p)) (a ⊔ lsuc p) →
      Contractible (Equality-with-J a p reflexive)
    Equality-with-J-contractible {a} {p} ext =        $⟨ irr ⟩
      Proof-irrelevant Eq-with-J₂                     ↝⟨ _⇔_.from propositional⇔irrelevant ⟩
      Is-proposition Eq-with-J₂                       ↝⟨ H-level.respects-surjection eq surj₂ 1 ⟩
      Is-proposition Eq-with-J₁                       ↝⟨ H-level.respects-surjection eq surj₁ 1 ⟩
      Is-proposition (Equality-with-J a p reflexive)  ↝⟨ flip propositional⇒inhabited⇒contractible eq ⟩□
      Contractible (Equality-with-J a p reflexive)    □
      where
      Eq-with-J₁ =
        ∃ λ (elim : {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
                    (∀ x → P (refl x)) →
                    ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
            ∀ {A : Set a} (P : {x y : A} → x ≡ y → Set p)
            (r : ∀ x → P (refl x)) {x} →
            elim P r (refl x) ≡ r x

      Eq-with-J₂ =
        (A : Set a)
        (P : {x y : A} → x ≡ y → Set p)
        (r : ∀ x → P (refl x)) →
        ∃ λ (elim : ∀ x y (x≡y : x ≡ y) → P x≡y) →
          ∀ x → elim x x (refl x) ≡ r x

      surj₁ : Eq-with-J₁ ↠ Equality-with-J a p reflexive
      surj₁ = record
        { logical-equivalence = record
          { to   = uncurry λ elim elim-refl → record
                     { elim      = λ {_} → elim      {_}
                     ; elim-refl = λ {_} → elim-refl {_}
                     }
          ; from = λ eq → Equality-with-J.elim      eq
                        , Equality-with-J.elim-refl eq
          }
        ; right-inverse-of = refl
        }

      surj₂ : Eq-with-J₂ ↠ Eq-with-J₁
      surj₂ =
        ((A : Set a)
         (P : {x y : A} → x ≡ y → Set p)
         (r : ∀ x → P (refl x)) →
         ∃ λ (elim : ∀ x y (x≡y : x ≡ y) → P x≡y) →
           ∀ x → elim x x (refl x) ≡ r x)                           ↝⟨ ∀-cong (lower-extensionality (lsuc p) lzero ext) (λ _ →
                                                                       ∀-cong (lower-extensionality (lsuc a) (lsuc p) ext) λ _ →
                                                                       ∀-cong (lower-extensionality _ (lsuc p) ext) λ _ →
                                                                       Σ-cong (∀-cong (lower-extensionality _ (lsuc p) ext) λ _ →
                                                                               inverse $ Bijection.implicit-Π↔Π eq) λ _ →
                                                                       Surjection.id eq) ⟩
        ((A : Set a)
         (P : {x y : A} → x ≡ y → Set p)
         (r : ∀ x → P (refl x)) →
         ∃ λ (elim : ∀ x {y} (x≡y : x ≡ y) → P x≡y) →
           ∀ x → elim x (refl x) ≡ r x)                             ↔⟨ ∀-cong (lower-extensionality (lsuc p) lzero ext) (λ _ →
                                                                       ∀-cong (lower-extensionality (lsuc a) (lsuc p) ext) λ _ →
                                                                       ∀-cong (lower-extensionality _ (lsuc p) ext) λ _ → inverse $
                                                                       Σ-cong (Bijection.implicit-Π↔Π eq) λ _ →
                                                                       Bijection.implicit-Π↔Π eq) ⟩
        ((A : Set a)
         (P : {x y : A} → x ≡ y → Set p)
         (r : ∀ x → P (refl x)) →
         ∃ λ (elim : ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
           ∀ {x} → elim (refl x) ≡ r x)                             ↔⟨ ∀-cong (lower-extensionality (lsuc p) lzero ext) (λ _ →
                                                                       ∀-cong (lower-extensionality (lsuc a) (lsuc p) ext) λ _ →
                                                                         ΠΣ-comm) ⟩
        ((A : Set a)
         (P : {x y : A} → x ≡ y → Set p) →
         ∃ λ (elim : (∀ x → P (refl x)) →
                     ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
           (r : ∀ x → P (refl x)) →
           ∀ {x} → elim r (refl x) ≡ r x)                           ↔⟨ ∀-cong (lower-extensionality (lsuc p) lzero ext) (λ _ →
                                                                         ΠΣ-comm) ⟩
        ((A : Set a) →
         ∃ λ (elim : (P : {x y : A} → x ≡ y → Set p) →
                     (∀ x → P (refl x)) →
                     ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
           (P : {x y : A} → x ≡ y → Set p)
           (r : ∀ x → P (refl x)) →
           ∀ {x} → elim P r (refl x) ≡ r x)                         ↔⟨ inverse $ Bijection.implicit-Π↔Π eq ⟩

        ({A : Set a} →
         ∃ λ (elim : (P : {x y : A} → x ≡ y → Set p) →
                     (∀ x → P (refl x)) →
                     ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
           (P : {x y : A} → x ≡ y → Set p)
           (r : ∀ x → P (refl x)) →
           ∀ {x} → elim P r (refl x) ≡ r x)                         ↔⟨ implicit-ΠΣ-comm ⟩□

        (∃ λ (elim : {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
                     (∀ x → P (refl x)) →
                     ∀ {x y} (x≡y : x ≡ y) → P x≡y) →
             ∀ {A : Set a} (P : {x y : A} → x ≡ y → Set p)
             (r : ∀ x → P (refl x)) {x} →
             elim P r (refl x) ≡ r x)                               □

      irr : Proof-irrelevant Eq-with-J₂
      irr eq₁ eq₂ =
        lower-extensionality (lsuc p) lzero ext λ A →
        lower-extensionality (lsuc a) (lsuc p) ext λ P →
        lower-extensionality _ (lsuc p) ext λ r →

        let elim₁ , elim₁-refl = eq₁ A (λ x≡y → P x≡y) r
            elim₂ , elim₂-refl = eq₂ A (λ x≡y → P x≡y) r
        in

        Σ-≡,≡→≡
          (good-ext (lower-extensionality _ (lsuc p) ext) λ x →
           good-ext (lower-extensionality _ (lsuc p) ext) λ y →
           good-ext (lower-extensionality _ _ ext) λ x≡y →
              proj₁ (eq₁ A
                         (λ {x y} x≡y → elim₁ x y x≡y ≡ elim₂ x y x≡y)
                         (λ x →
                            elim₁ x x (refl x)  ≡⟨ elim₁-refl x ⟩
                            r x                 ≡⟨ sym (elim₂-refl x) ⟩∎
                            elim₂ x x (refl x)  ∎))
                    x y x≡y)
          (lower-extensionality _ _ ext λ x →

             subst (λ elim → ∀ x → elim x x (refl x) ≡ r x)
                   (good-ext (lower-extensionality _ (lsuc p) ext) λ x →
                    good-ext (lower-extensionality _ (lsuc p) ext) λ y →
                    good-ext (lower-extensionality _ _ ext) λ x≡y →
                    proj₁ (eq₁ A (λ x≡y → elim₁ _ _ x≡y ≡ elim₂ _ _ x≡y)
                               (λ x → trans (elim₁-refl x)
                                            (sym (elim₂-refl x))))
                          x y x≡y)
                   elim₁-refl x                                           ≡⟨ sym $ push-subst-application _ _ ⟩

             subst (λ elim → elim x x (refl x) ≡ r x)
                   (good-ext (lower-extensionality _ (lsuc p) ext) λ x →
                    good-ext (lower-extensionality _ (lsuc p) ext) λ y →
                    good-ext (lower-extensionality _ _ ext) λ x≡y →
                    proj₁ (eq₁ A (λ x≡y → elim₁ _ _ x≡y ≡ elim₂ _ _ x≡y)
                               (λ x → trans (elim₁-refl x)
                                            (sym (elim₂-refl x))))
                          x y x≡y)
                   (elim₁-refl x)                                         ≡⟨ subst-good-ext (lower-extensionality _ (lsuc p) ext) _ _ ⟩

             subst (λ elim → elim x (refl x) ≡ r x)
                   (good-ext (lower-extensionality _ (lsuc p) ext) λ y →
                    good-ext (lower-extensionality _ _ ext) λ x≡y →
                    proj₁ (eq₁ A (λ x≡y → elim₁ _ _ x≡y ≡ elim₂ _ _ x≡y)
                               (λ x → trans (elim₁-refl x)
                                            (sym (elim₂-refl x))))
                          x y x≡y)
                   (elim₁-refl x)                                         ≡⟨ subst-good-ext (lower-extensionality _ (lsuc p) ext) _ _ ⟩

             subst (λ elim → elim (refl x) ≡ r x)
                   (good-ext (lower-extensionality _ _ ext) λ x≡x →
                    proj₁ (eq₁ A (λ x≡y → elim₁ _ _ x≡y ≡ elim₂ _ _ x≡y)
                               (λ x → trans (elim₁-refl x)
                                            (sym (elim₂-refl x))))
                          x x x≡x)
                   (elim₁-refl x)                                         ≡⟨ subst-good-ext (lower-extensionality _ _ ext) _ _ ⟩

             subst (λ elim → elim ≡ r x)
                   (proj₁ (eq₁ A (λ x≡y → elim₁ _ _ x≡y ≡ elim₂ _ _ x≡y)
                               (λ x → trans (elim₁-refl x)
                                            (sym (elim₂-refl x))))
                          x x (refl x))
                   (elim₁-refl x)                                         ≡⟨ cong (λ eq → subst (_≡ r x) eq _) $ sym $ sym-sym _ ⟩

             subst (_≡ r x)
                   (sym $ sym $
                    proj₁ (eq₁ A (λ x≡y → elim₁ _ _ x≡y ≡ elim₂ _ _ x≡y)
                               (λ x → trans (elim₁-refl x)
                                            (sym (elim₂-refl x))))
                          x x (refl x))
                   (elim₁-refl x)                                         ≡⟨ subst-trans _ ⟩

             trans (sym $
                    proj₁ (eq₁ A (λ x≡y → elim₁ _ _ x≡y ≡ elim₂ _ _ x≡y)
                               (λ x → trans (elim₁-refl x)
                                            (sym (elim₂-refl x))))
                          x x (refl x))
                   (elim₁-refl x)                                         ≡⟨ cong (λ eq → trans (sym eq) _) $ proj₂ (eq₁ _ _ _) x ⟩

             trans (sym $ trans (elim₁-refl x) (sym (elim₂-refl x)))
                   (elim₁-refl x)                                         ≡⟨ cong (flip trans _) $ sym-trans _ _ ⟩

             trans (trans (sym (sym (elim₂-refl x)))
                          (sym (elim₁-refl x)))
                   (elim₁-refl x)                                         ≡⟨ trans-[trans-sym]- _ _ ⟩

             sym (sym (elim₂-refl x))                                     ≡⟨ sym-sym _ ⟩∎

             elim₂-refl x                                                 ∎)
