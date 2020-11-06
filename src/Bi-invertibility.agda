------------------------------------------------------------------------
-- Bi-invertibility
------------------------------------------------------------------------

-- The development is based on the presentation of bi-invertibility
-- (for types and functions) and related things in the HoTT book.

{-# OPTIONS --without-K --safe #-}

open import Equality
open import Prelude hiding (id; _∘_)

-- The code is parametrised by something like a "raw" category.

module Bi-invertibility
  {e⁺}
  (eq : ∀ {a p} → Equality-with-J a p e⁺)
  {o h}
  (Obj : Type o)
  (Hom : Obj → Obj → Type h)
  (id : {A : Obj} → Hom A A)
  (_∘′_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C)
  where

open Derived-definitions-and-properties eq
open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq as F hiding (id; _∘_)
open import Logical-equivalence using (_⇔_)
open import H-level eq
open import H-level.Closure eq
open import Preimage eq
open import Surjection eq using (_↠_)

private
  variable
    A B : Obj
    f   : Hom A B

  infixr 9 _∘_

  _∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
  _∘_ = _∘′_

-- Has-left-inverse f means that f has a left inverse.

Has-left-inverse : Hom A B → Type h
Has-left-inverse f = ∃ λ f⁻¹ → f⁻¹ ∘ f ≡ id

-- Has-right-inverse f means that f has a right inverse.

Has-right-inverse : Hom A B → Type h
Has-right-inverse f = ∃ λ f⁻¹ → f ∘ f⁻¹ ≡ id

-- Is-bi-invertible f means that f has a left inverse and a (possibly
-- distinct) right inverse.

Is-bi-invertible : Hom A B → Type h
Is-bi-invertible f =
  Has-left-inverse f × Has-right-inverse f

-- Has-quasi-inverse f means that f has a left inverse that is also a
-- right inverse.

Has-quasi-inverse : Hom A B → Type h
Has-quasi-inverse f =
  ∃ λ f⁻¹ → f ∘ f⁻¹ ≡ id × f⁻¹ ∘ f ≡ id

-- Some notions of isomorphism or equivalence.

infix 4 _≊_ _≅_

_≊_ : Obj → Obj → Type h
A ≊ B = ∃ λ (f : Hom A B) → Is-bi-invertible f

_≅_ : Obj → Obj → Type h
A ≅ B = ∃ λ (f : Hom A B) → Has-quasi-inverse f

-- Morphisms with quasi-inverses are bi-invertible.

Has-quasi-inverse→Is-bi-invertible :
  (f : Hom A B) → Has-quasi-inverse f → Is-bi-invertible f
Has-quasi-inverse→Is-bi-invertible _ (f⁻¹ , f∘f⁻¹≡id , f⁻¹∘f≡id) =
    (f⁻¹ , f⁻¹∘f≡id)
  , (f⁻¹ , f∘f⁻¹≡id)

≅→≊ : A ≅ B → A ≊ B
≅→≊ = ∃-cong Has-quasi-inverse→Is-bi-invertible

-- The remaining code relies on some further assumptions, similar to
-- those of a precategory. However, note that Hom A B is not required
-- to be a set (some properties require Hom A A to be a set for some
-- A).

module More
  (left-identity  : {A B : Obj} (f : Hom A B) → id ∘ f ≡ f)
  (right-identity : {A B : Obj} (f : Hom A B) → f ∘ id ≡ f)
  (associativity  : {A B C D : Obj}
                    (f : Hom C D) (g : Hom B C) (h : Hom A B) →
                    f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h)
  where

  -- Bi-invertible morphisms have quasi-inverses.

  Is-bi-invertible→Has-quasi-inverse :
    Is-bi-invertible f → Has-quasi-inverse f
  Is-bi-invertible→Has-quasi-inverse
    {f = f} ((f⁻¹₁ , f⁻¹₁∘f≡id) , (f⁻¹₂ , f∘f⁻¹₂≡id)) =
      (f⁻¹₁ ∘ f ∘ f⁻¹₂)
    , (f ∘ f⁻¹₁ ∘ f ∘ f⁻¹₂    ≡⟨ cong (f ∘_) $ associativity _ _ _ ⟩
       f ∘ (f⁻¹₁ ∘ f) ∘ f⁻¹₂  ≡⟨ cong (λ f′ → f ∘ f′ ∘ f⁻¹₂) f⁻¹₁∘f≡id ⟩
       f ∘ id ∘ f⁻¹₂          ≡⟨ cong (f ∘_) $ left-identity _ ⟩
       f ∘ f⁻¹₂               ≡⟨ f∘f⁻¹₂≡id ⟩∎
       id                     ∎)
    , ((f⁻¹₁ ∘ f ∘ f⁻¹₂) ∘ f  ≡⟨ cong (λ f′ → (f⁻¹₁ ∘ f′) ∘ f) f∘f⁻¹₂≡id ⟩
       (f⁻¹₁ ∘ id) ∘ f        ≡⟨ cong (_∘ f) $ right-identity _ ⟩
       f⁻¹₁ ∘ f               ≡⟨ f⁻¹₁∘f≡id ⟩∎
       id                     ∎)

  -- Has-left-inverse f is contractible if f has a quasi-inverse.

  Has-left-inverse-contractible :
    Has-quasi-inverse f → Contractible (Has-left-inverse f)
  Has-left-inverse-contractible
    {f = f} (f⁻¹ , f∘f⁻¹≡id , f⁻¹∘f≡id) =
    bijection⁻¹-contractible (record
      { surjection = record
        { logical-equivalence = record
          { to   = _∘ f
          ; from = _∘ f⁻¹
          }
        ; right-inverse-of = λ g →
            (g ∘ f⁻¹) ∘ f  ≡⟨ sym $ associativity _ _ _ ⟩
            g ∘ f⁻¹ ∘ f    ≡⟨ cong (g ∘_) f⁻¹∘f≡id ⟩
            g ∘ id         ≡⟨ right-identity _ ⟩∎
            g              ∎
        }
      ; left-inverse-of = λ g →
          (g ∘ f) ∘ f⁻¹  ≡⟨ sym $ associativity _ _ _ ⟩
          g ∘ f ∘ f⁻¹    ≡⟨ cong (g ∘_) f∘f⁻¹≡id ⟩
          g ∘ id         ≡⟨ right-identity _ ⟩∎
          g              ∎
      })
      id

  -- Has-right-inverse f is contractible if f has a quasi-inverse.

  Has-right-inverse-contractible :
    Has-quasi-inverse f → Contractible (Has-right-inverse f)
  Has-right-inverse-contractible
    {f = f} (f⁻¹ , f∘f⁻¹≡id , f⁻¹∘f≡id) =
    bijection⁻¹-contractible (record
      { surjection = record
        { logical-equivalence = record
          { to   = f ∘_
          ; from = f⁻¹ ∘_
          }
        ; right-inverse-of = λ g →
            f ∘ f⁻¹ ∘ g    ≡⟨ associativity _ _ _ ⟩
            (f ∘ f⁻¹) ∘ g  ≡⟨ cong (_∘ g) f∘f⁻¹≡id ⟩
            id ∘ g         ≡⟨ left-identity _ ⟩∎
            g              ∎
        }
      ; left-inverse-of = λ g →
          f⁻¹ ∘ f ∘ g    ≡⟨ associativity _ _ _ ⟩
          (f⁻¹ ∘ f) ∘ g  ≡⟨ cong (_∘ g) f⁻¹∘f≡id ⟩
          id ∘ g         ≡⟨ left-identity _ ⟩∎
          g              ∎
      })
      id

  -- Is-bi-invertible f is a proposition.

  Is-bi-invertible-propositional :
    (f : Hom A B) → Is-proposition (Is-bi-invertible f)
  Is-bi-invertible-propositional f =
    [inhabited⇒+]⇒+ 0 λ b →
      let q = Is-bi-invertible→Has-quasi-inverse b in
      mono₁ 0 $
      ×-closure 0
        (Has-left-inverse-contractible  q)
        (Has-right-inverse-contractible q)

  -- If Hom A A is a set, where A is the domain of f, then
  -- Has-quasi-inverse f is a proposition.

  Has-quasi-inverse-propositional-domain :
    {f : Hom A B} →
    Is-set (Hom A A) →
    Is-proposition (Has-quasi-inverse f)
  Has-quasi-inverse-propositional-domain {f = f} s =              $⟨ (λ inv → Σ-closure 1
                                                                                (mono₁ 0 $ Has-right-inverse-contractible inv)
                                                                                (λ _ → s)) ⟩
    (Has-quasi-inverse f →
     Is-proposition (∃ λ ((f⁻¹ , _) : Has-right-inverse f) →
                       f⁻¹ ∘ f ≡ id))                             ↝⟨ (∀-cong _ λ _ → H-level-cong _ 1 (inverse Σ-assoc)) ⟩

    (Has-quasi-inverse f → Is-proposition (Has-quasi-inverse f))  ↝⟨ [inhabited⇒+]⇒+ 0 ⟩□

    Is-proposition (Has-quasi-inverse f)                          □

  -- If Hom B B is a set, where B is the codomain of f, then
  -- Has-quasi-inverse f is a proposition.

  Has-quasi-inverse-propositional-codomain :
    {f : Hom A B} →
    Is-set (Hom B B) →
    Is-proposition (Has-quasi-inverse f)
  Has-quasi-inverse-propositional-codomain {f = f} s =            $⟨ (λ inv → Σ-closure 1
                                                                                (mono₁ 0 $ Has-left-inverse-contractible inv)
                                                                                (λ _ → s)) ⟩
    (Has-quasi-inverse f →
     Is-proposition (∃ λ ((f⁻¹ , _) : Has-left-inverse f) →
                       f ∘ f⁻¹ ≡ id))                             ↝⟨ (∀-cong _ λ _ → H-level-cong _ 1 lemma) ⟩

    (Has-quasi-inverse f → Is-proposition (Has-quasi-inverse f))  ↝⟨ [inhabited⇒+]⇒+ 0 ⟩□

    Is-proposition (Has-quasi-inverse f)                          □
    where
    lemma =
      (∃ λ ((f⁻¹ , _) : Has-left-inverse f) → f ∘ f⁻¹ ≡ id)      ↔⟨⟩
      (∃ λ ((f⁻¹ , _) : ∃ λ f⁻¹ → f⁻¹ ∘ f ≡ id) → f ∘ f⁻¹ ≡ id)  ↝⟨ inverse Σ-assoc ⟩
      (∃ λ f⁻¹ → f⁻¹ ∘ f ≡ id × f ∘ f⁻¹ ≡ id)                    ↝⟨ (∃-cong λ _ → ×-comm) ⟩
      (∃ λ f⁻¹ → f ∘ f⁻¹ ≡ id × f⁻¹ ∘ f ≡ id)                    ↔⟨⟩
      Has-quasi-inverse f                                        □

  -- There is a split surjection from Has-quasi-inverse f to
  -- Is-bi-invertible f.

  Has-quasi-inverse↠Is-bi-invertible :
    Has-quasi-inverse f ↠ Is-bi-invertible f
  Has-quasi-inverse↠Is-bi-invertible = record
    { logical-equivalence = record
      { to   = Has-quasi-inverse→Is-bi-invertible _
      ; from = Is-bi-invertible→Has-quasi-inverse
      }
    ; right-inverse-of = λ _ → Is-bi-invertible-propositional _ _ _
    }

  -- There is a split surjection from A ≅ B to A ≊ B.

  ≅↠≊ : (A ≅ B) ↠ (A ≊ B)
  ≅↠≊ = ∃-cong λ _ → Has-quasi-inverse↠Is-bi-invertible

  -- Is-bi-invertible and Has-quasi-inverse are equivalent for
  -- morphisms with domain A for which Hom A A is a set.

  Is-bi-invertible≃Has-quasi-inverse-domain :
    {f : Hom A B} →
    Is-set (Hom A A) →
    Is-bi-invertible f ≃ Has-quasi-inverse f
  Is-bi-invertible≃Has-quasi-inverse-domain s =
    inverse $ Eq.↔⇒≃ (record
      { surjection = Has-quasi-inverse↠Is-bi-invertible
      ; left-inverse-of = λ _ →
          Has-quasi-inverse-propositional-domain s _ _
      })

  -- Is-bi-invertible and Has-quasi-inverse are equivalent for
  -- morphisms with codomain B for which Hom B B is a set.

  Is-bi-invertible≃Has-quasi-inverse-codomain :
    {f : Hom A B} →
    Is-set (Hom B B) →
    Is-bi-invertible f ≃ Has-quasi-inverse f
  Is-bi-invertible≃Has-quasi-inverse-codomain s =
    inverse $ Eq.↔⇒≃ (record
      { surjection = Has-quasi-inverse↠Is-bi-invertible
      ; left-inverse-of = λ _ →
          Has-quasi-inverse-propositional-codomain s _ _
      })

  -- A ≊ B and A ≅ B are equivalent if Hom A A is a set.

  ≊≃≅-domain :
    Is-set (Hom A A) →
    (A ≊ B) ≃ (A ≅ B)
  ≊≃≅-domain s =
    ∃-cong λ _ → Is-bi-invertible≃Has-quasi-inverse-domain s

  -- A ≊ B and A ≅ B are equivalent if Hom B B is a set.

  ≊≃≅-codomain :
    Is-set (Hom B B) →
    (A ≊ B) ≃ (A ≅ B)
  ≊≃≅-codomain s =
    ∃-cong λ _ → Is-bi-invertible≃Has-quasi-inverse-codomain s

  -- An equality characterisation lemma for _≊_.

  equality-characterisation-≊ :
    (f g : A ≊ B) → (f ≡ g) ≃ (proj₁ f ≡ proj₁ g)
  equality-characterisation-≊ _ _ =
    Eq.↔⇒≃ $ inverse $ ignore-propositional-component $
      Is-bi-invertible-propositional _

  -- Two equality characterisation lemmas for _≅_.

  equality-characterisation-≅-domain :
    Is-set (Hom A A) →
    (f g : A ≅ B) → (f ≡ g) ≃ (proj₁ f ≡ proj₁ g)
  equality-characterisation-≅-domain s _ _ =
    Eq.↔⇒≃ $ inverse $ ignore-propositional-component $
      Has-quasi-inverse-propositional-domain s

  equality-characterisation-≅-codomain :
    Is-set (Hom B B) →
    (f g : A ≅ B) → (f ≡ g) ≃ (proj₁ f ≡ proj₁ g)
  equality-characterisation-≅-codomain s _ _ =
    Eq.↔⇒≃ $ inverse $ ignore-propositional-component $
      Has-quasi-inverse-propositional-codomain s

  -- If f : Hom A B has a quasi-inverse, then Has-quasi-inverse f is
  -- equivalent to id ≡ id, where id stands for either the identity at
  -- A or at B.

  Has-quasi-inverse≃id≡id-domain :
    {f : Hom A B} →
    Has-quasi-inverse f →
    Has-quasi-inverse f ≃ (id ≡ id {A = A})
  Has-quasi-inverse≃id≡id-domain {f = f} q-inv@(f⁻¹ , _ , f⁻¹∘f≡id) =
    Has-quasi-inverse f                                     ↔⟨ Σ-assoc ⟩
    (∃ λ ((f⁻¹ , _) : Has-right-inverse f) → f⁻¹ ∘ f ≡ id)  ↔⟨ drop-⊤-left-Σ (_⇔_.to contractible⇔↔⊤ $ Has-right-inverse-contractible q-inv) ⟩
    (f⁻¹ ∘ id) ∘ f ≡ id                                     ↝⟨ ≡⇒↝ _ $ cong (λ f′ → f′ ∘ _ ≡ _) $ right-identity _ ⟩
    f⁻¹ ∘ f ≡ id                                            ↝⟨ ≡⇒↝ _ $ cong (_≡ _) f⁻¹∘f≡id ⟩□
    id ≡ id                                                 □

  Has-quasi-inverse≃id≡id-codomain :
    {f : Hom A B} →
    Has-quasi-inverse f →
    Has-quasi-inverse f ≃ (id ≡ id {A = B})
  Has-quasi-inverse≃id≡id-codomain {f = f} q-inv@(f⁻¹ , f∘f⁻¹≡id , _) =
    Has-quasi-inverse f                                    ↔⟨ Σ-assoc F.∘ (∃-cong λ _ → ×-comm) ⟩
    (∃ λ ((f⁻¹ , _) : Has-left-inverse f) → f ∘ f⁻¹ ≡ id)  ↔⟨ drop-⊤-left-Σ (_⇔_.to contractible⇔↔⊤ $ Has-left-inverse-contractible q-inv) ⟩
    f ∘ id ∘ f⁻¹ ≡ id                                      ↝⟨ ≡⇒↝ _ $ cong (λ f′ → _ ∘ f′ ≡ _) $ left-identity _ ⟩
    f ∘ f⁻¹ ≡ id                                           ↝⟨ ≡⇒↝ _ $ cong (_≡ _) f∘f⁻¹≡id ⟩□
    id ≡ id                                                □
