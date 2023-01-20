------------------------------------------------------------------------
-- Some decision procedures for equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Equality.Decision-procedures
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Equality.Decidable-UIP eq
open import Prelude
  hiding (module ⊤; module ⊥; module ↑; module ℕ; module Σ; module List)

------------------------------------------------------------------------
-- The unit type

module ⊤ where

  -- Equality of values of the unit type is decidable.

  infix 4 _≟_

  _≟_ : Decidable-equality ⊤
  _ ≟ _ = yes (refl _)

------------------------------------------------------------------------
-- The empty type

module ⊥ {ℓ} where

  -- Equality of values of the empty type is decidable.

  infix 4 _≟_

  _≟_ : Decidable-equality (⊥ {ℓ = ℓ})
  () ≟ ()

------------------------------------------------------------------------
-- Lifting

module ↑ {a ℓ} {A : Type a} where

  -- ↑ preserves decidability of equality.

  module Dec (dec : Decidable-equality A) where

    infix 4 _≟_

    _≟_ : Decidable-equality (↑ ℓ A)
    lift x ≟ lift y = ⊎-map (cong lift) (_∘ cong lower) (dec x y)

------------------------------------------------------------------------
-- Booleans

module Bool where

  -- The values true and false are distinct.

  abstract

    true≢false : true ≢ false
    true≢false true≡false = subst T true≡false _

  -- Equality of booleans is decidable.

  infix 4 _≟_

  _≟_ : Decidable-equality Bool
  true  ≟ true  = yes (refl _)
  false ≟ false = yes (refl _)
  true  ≟ false = no true≢false
  false ≟ true  = no (true≢false ∘ sym)

------------------------------------------------------------------------
-- Σ-types

module Σ {a b} {A : Type a} {B : A → Type b} where

  -- Two variants of Dec._≟_ (which is defined below).

  set⇒dec⇒dec⇒dec :
    {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂} →
    Is-set A →
    Dec (x₁ ≡ x₂) →
    (∀ eq → Dec (subst B eq y₁ ≡ y₂)) →
    Dec ((x₁ , y₁) ≡ (x₂ , y₂))
  set⇒dec⇒dec⇒dec set₁ (no  x₁≢x₂) dec₂ = no (x₁≢x₂ ∘ cong proj₁)
  set⇒dec⇒dec⇒dec set₁ (yes x₁≡x₂) dec₂ with dec₂ x₁≡x₂
  … | yes cast-y₁≡y₂ = yes (Σ-≡,≡→≡ x₁≡x₂ cast-y₁≡y₂)
  … | no  cast-y₁≢y₂ =
    no (cast-y₁≢y₂ ∘
        subst (λ p → subst B p _ ≡ _) (set₁ _ _) ∘
        proj₂ ∘ Σ-≡,≡←≡)

  decidable⇒dec⇒dec :
    {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂} →
    Decidable-equality A →
    (∀ eq → Dec (subst B eq y₁ ≡ y₂)) →
    Dec ((x₁ , y₁) ≡ (x₂ , y₂))
  decidable⇒dec⇒dec dec =
    set⇒dec⇒dec⇒dec (decidable⇒set dec) (dec _ _)

  -- Σ preserves decidability of equality.

  module Dec (_≟A_ : Decidable-equality A)
             (_≟B_ : {x : A} → Decidable-equality (B x)) where

    infix 4 _≟_

    _≟_ : Decidable-equality (Σ A B)
    _ ≟ _ = decidable⇒dec⇒dec _≟A_ (λ _ → _ ≟B _)

------------------------------------------------------------------------
-- Binary products

module × {a b} {A : Type a} {B : Type b} where

  -- _,_ preserves decided equality.

  dec⇒dec⇒dec :
    {x₁ x₂ : A} {y₁ y₂ : B} →
    Dec (x₁ ≡ x₂) →
    Dec (y₁ ≡ y₂) →
    Dec ((x₁ , y₁) ≡ (x₂ , y₂))
  dec⇒dec⇒dec (no  x₁≢x₂) _           = no (x₁≢x₂ ∘ cong proj₁)
  dec⇒dec⇒dec _           (no  y₁≢y₂) = no (y₁≢y₂ ∘ cong proj₂)
  dec⇒dec⇒dec (yes x₁≡x₂) (yes y₁≡y₂) = yes (cong₂ _,_ x₁≡x₂ y₁≡y₂)

  -- _×_ preserves decidability of equality.

  module Dec (_≟A_ : Decidable-equality A)
             (_≟B_ : Decidable-equality B) where

    infix 4 _≟_

    _≟_ : Decidable-equality (A × B)
    _ ≟ _ = dec⇒dec⇒dec (_ ≟A _) (_ ≟B _)

------------------------------------------------------------------------
-- Binary sums

module ⊎ {a b} {A : Type a} {B : Type b} where

  abstract

    -- The values inj₁ x and inj₂ y are never equal.

    inj₁≢inj₂ : {x : A} {y : B} → inj₁ x ≢ inj₂ y
    inj₁≢inj₂ = Bool.true≢false ∘ cong (if_then true else false)

  -- The inj₁ and inj₂ constructors are cancellative.

  cancel-inj₁ : {x y : A} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
  cancel-inj₁ {x = x} = cong {A = A ⊎ B} {B = A} [ id , const x ]

  cancel-inj₂ : {x y : B} → _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y) → x ≡ y
  cancel-inj₂ {x = x} = cong {A = A ⊎ B} {B = B} [ const x , id ]

  -- _⊎_ preserves decidability of equality.

  module Dec (_≟A_ : Decidable-equality A)
             (_≟B_ : Decidable-equality B) where

    infix 4 _≟_

    _≟_ : Decidable-equality (A ⊎ B)
    inj₁ x ≟ inj₁ y = ⊎-map (cong (inj₁ {B = B})) (λ x≢y → x≢y ∘ cancel-inj₁) (x ≟A y)
    inj₂ x ≟ inj₂ y = ⊎-map (cong (inj₂ {A = A})) (λ x≢y → x≢y ∘ cancel-inj₂) (x ≟B y)
    inj₁ x ≟ inj₂ y = no inj₁≢inj₂
    inj₂ x ≟ inj₁ y = no (inj₁≢inj₂ ∘ sym)

------------------------------------------------------------------------
-- Lists

module List {a} {A : Type a} where

  abstract

    -- The values [] and x ∷ xs are never equal.

    []≢∷ : ∀ {x : A} {xs} → [] ≢ x ∷ xs
    []≢∷ = Bool.true≢false ∘
             cong (λ { [] → true; (_ ∷ _) → false })

  -- The _∷_ constructor is cancellative in both arguments.

  private

    head? : A → List A → A
    head? x []      = x
    head? _ (x ∷ _) = x

    tail? : List A → List A
    tail? []       = []
    tail? (_ ∷ xs) = xs

  cancel-∷-head : ∀ {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
  cancel-∷-head {x} = cong (head? x)

  cancel-∷-tail : ∀ {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  cancel-∷-tail = cong tail?

  abstract

    -- An η-like result for the cancellation lemmas.

    unfold-∷ : ∀ {x y : A} {xs ys} (eq : x ∷ xs ≡ y ∷ ys) →
               eq ≡ cong₂ _∷_ (cancel-∷-head eq) (cancel-∷-tail eq)
    unfold-∷ {x} eq =
      eq                                             ≡⟨ sym $ trans-reflʳ eq ⟩
      trans eq (refl _)                              ≡⟨ sym $ cong (trans eq) sym-refl ⟩
      trans eq (sym (refl _))                        ≡⟨ sym $ trans-reflˡ _ ⟩
      trans (refl _) (trans eq (sym (refl _)))       ≡⟨ sym $ cong-roughly-id (λ xs → head? x xs ∷ tail? xs)
                                                                              non-empty eq tt tt lemma₁ ⟩
      cong (λ xs → head? x xs ∷ tail? xs) eq         ≡⟨ lemma₂ _∷_ (head? x) tail? eq ⟩∎
      cong₂ _∷_ (cong (head? x) eq) (cong tail? eq)  ∎
      where
      non-empty : List A → Bool
      non-empty []      = false
      non-empty (_ ∷ _) = true

      lemma₁ : (xs : List A) →
               if non-empty xs then ⊤ else ⊥ →
               head? x xs ∷ tail? xs ≡ xs
      lemma₁ []      ()
      lemma₁ (_ ∷ _) _ = refl _

      lemma₂ : {A B C D : Type a} {x y : A}
               (f : B → C → D) (g : A → B) (h : A → C) →
               (eq : x ≡ y) →
               cong (λ x → f (g x) (h x)) eq ≡
               cong₂ f (cong g eq) (cong h eq)
      lemma₂ f g h =
        elim (λ eq → cong (λ x → f (g x) (h x)) eq ≡
                     cong₂ f (cong g eq) (cong h eq))
             (λ x → cong (λ x → f (g x) (h x)) (refl x)          ≡⟨ cong-refl (λ x → f (g x) (h x)) ⟩
                    refl (f (g x) (h x))                         ≡⟨ sym $ cong₂-refl f ⟩
                    cong₂ f (refl (g x)) (refl (h x))            ≡⟨ sym $ cong₂ (cong₂ f) (cong-refl g) (cong-refl h) ⟩∎
                    cong₂ f (cong g (refl x)) (cong h (refl x))  ∎)

  -- List preserves decidability of equality.

  module Dec (_≟A_ : Decidable-equality A) where

    infix 4 _≟_

    _≟_ : Decidable-equality (List A)
    []       ≟ []       = yes (refl [])
    []       ≟ (_ ∷ _)  = no []≢∷
    (_ ∷ _)  ≟ []       = no ([]≢∷ ∘ sym)
    (x ∷ xs) ≟ (y ∷ ys) with x ≟A y
    ... | no  x≢y = no (x≢y ∘ cancel-∷-head)
    ... | yes x≡y with xs ≟ ys
    ...   | yes xs≡ys = yes (cong₂ _∷_ x≡y xs≡ys)
    ...   | no  xs≢ys = no  (xs≢ys ∘ cancel-∷-tail)

------------------------------------------------------------------------
-- Finite sets

module Fin where

  -- Equality of finite numbers is decidable.

  infix 4 _≟_

  _≟_ : ∀ {n} → Decidable-equality (Fin n)
  _≟_ {(zero)} = λ ()
  _≟_ {suc n}  = ⊎.Dec._≟_ (λ _ _ → yes (refl tt)) (_≟_ {n})
