------------------------------------------------------------------------
-- Some decision procedures for equality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Equality.Decision-procedures
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Equality.Decidable-UIP eq
open import Prelude
  hiding ( module ⊤; module ⊥; module Bool; module ℕ; module Σ
         ; module List
         )

------------------------------------------------------------------------
-- The unit type

module ⊤ where

  -- Equality of values of the unit type is decidable.

  _≟_ : Decidable-equality ⊤
  _ ≟ _ = inj₁ (refl _)

------------------------------------------------------------------------
-- The empty type

module ⊥ {ℓ} where

  -- Equality of values of the empty type is decidable.

  _≟_ : Decidable-equality (⊥ {ℓ = ℓ})
  () ≟ ()

------------------------------------------------------------------------
-- Booleans

module Bool where

  -- The values true and false are distinct.

  abstract

    true≢false : true ≢ false
    true≢false true≡false = subst T true≡false _

  -- Equality of booleans is decidable.

  _≟_ : Decidable-equality Bool
  true  ≟ true  = inj₁ (refl _)
  false ≟ false = inj₁ (refl _)
  true  ≟ false = inj₂ true≢false
  false ≟ true  = inj₂ (true≢false ∘ sym)

------------------------------------------------------------------------
-- Natural numbers

module ℕ where

  -- Inhabited only for zero.

  Zero : ℕ → Set
  Zero zero    = ⊤
  Zero (suc n) = ⊥

  -- Predecessor (except if the argument is zero).

  pred : ℕ → ℕ
  pred zero    = zero
  pred (suc n) = n

  abstract

    -- Zero is not equal to the successor of any number.

    0≢+ : {n : ℕ} → zero ≢ suc n
    0≢+ 0≡+ = subst Zero 0≡+ tt

  -- The suc constructor is cancellative.

  cancel-suc : {m n : ℕ} → suc m ≡ suc n → m ≡ n
  cancel-suc = cong pred

  -- Equality of natural numbers is decidable.

  _≟_ : Decidable-equality ℕ
  zero  ≟ zero  = inj₁ (refl _)
  suc m ≟ suc n = ⊎-map (cong suc) (λ m≢n → m≢n ∘ cancel-suc) (m ≟ n)
  zero  ≟ suc n = inj₂ 0≢+
  suc m ≟ zero  = inj₂ (0≢+ ∘ sym)

------------------------------------------------------------------------
-- Σ-types

module Σ {a b} {A : Set a} {B : A → Set b} where

  -- Σ preserves decidability of equality.

  module Dec (_≟A_ : Decidable-equality A)
             (_≟B_ : {x : A} → Decidable-equality (B x)) where

    _≟_ : Decidable-equality (Σ A B)
    (x₁ , y₁) ≟ (x₂ , y₂) with x₁ ≟A x₂
    ... | inj₂ x₁≢x₂ = inj₂ (x₁≢x₂ ∘ cong proj₁)
    ... | inj₁ x₁≡x₂ with subst B x₁≡x₂ y₁ ≟B y₂
    ...   | inj₁ cast-y₁≡y₂ = inj₁ (Σ-≡,≡→≡ x₁≡x₂ cast-y₁≡y₂)
    ...   | inj₂ cast-y₁≢y₂ =
      inj₂ (cast-y₁≢y₂ ∘
            subst (λ p → subst B p y₁ ≡ y₂) (decidable⇒UIP _≟A_ _ _) ∘
            proj₂ ∘ Σ-≡,≡←≡)

------------------------------------------------------------------------
-- Binary products

module × {a b} {A : Set a} {B : Set b} where

  -- _×_ preserves decidability of equality.

  module Dec (_≟A_ : Decidable-equality A)
             (_≟B_ : Decidable-equality B) where

    _≟_ : Decidable-equality (A × B)
    _≟_ = Σ.Dec._≟_ _≟A_ _≟B_

------------------------------------------------------------------------
-- Binary sums

module ⊎ {a b} {A : Set a} {B : Set b} where

  abstract

    -- The values inj₁ x and inj₂ y are never equal.

    inj₁≢inj₂ : {x : A} {y : B} → inj₁ x ≢ inj₂ y
    inj₁≢inj₂ = Bool.true≢false ∘
                cong {A = A ⊎ B} {B = Bool} [ const true , const false ]

  -- The inj₁ and inj₂ constructors are cancellative.

  cancel-inj₁ : {x y : A} → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
  cancel-inj₁ {x = x} = cong {A = A ⊎ B} {B = A} [ id , const x ]

  cancel-inj₂ : {x y : B} → _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y) → x ≡ y
  cancel-inj₂ {x = x} = cong {A = A ⊎ B} {B = B} [ const x , id ]

  -- _⊎_ preserves decidability of equality.

  module Dec (_≟A_ : Decidable-equality A)
             (_≟B_ : Decidable-equality B) where

    _≟_ : Decidable-equality (A ⊎ B)
    inj₁ x ≟ inj₁ y = ⊎-map (cong (inj₁ {B = B})) (λ x≢y → x≢y ∘ cancel-inj₁) (x ≟A y)
    inj₂ x ≟ inj₂ y = ⊎-map (cong (inj₂ {A = A})) (λ x≢y → x≢y ∘ cancel-inj₂) (x ≟B y)
    inj₁ x ≟ inj₂ y = inj₂ inj₁≢inj₂
    inj₂ x ≟ inj₁ y = inj₂ (inj₁≢inj₂ ∘ sym)

------------------------------------------------------------------------
-- Lists

module List {a} {A : Set a} where

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

      lemma₂ : {A B C D : Set a} {x y : A}
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

    _≟_ : Decidable-equality (List A)
    []       ≟ []       = inj₁ (refl [])
    []       ≟ (_ ∷ _)  = inj₂ []≢∷
    (_ ∷ _)  ≟ []       = inj₂ ([]≢∷ ∘ sym)
    (x ∷ xs) ≟ (y ∷ ys) with x ≟A y
    ... | inj₂ x≢y = inj₂ (x≢y ∘ cancel-∷-head)
    ... | inj₁ x≡y with xs ≟ ys
    ...   | inj₁ xs≡ys = inj₁ (cong₂ _∷_ x≡y xs≡ys)
    ...   | inj₂ xs≢ys = inj₂ (xs≢ys ∘ cancel-∷-tail)

------------------------------------------------------------------------
-- Finite sets

module Fin where

  -- Equality of finite numbers is decidable.

  _≟_ : ∀ {n} → Decidable-equality (Fin n)
  _≟_ {zero}  = λ ()
  _≟_ {suc n} = ⊎.Dec._≟_ (λ _ _ → inj₁ (refl tt)) (_≟_ {n})
