------------------------------------------------------------------------
-- Certain isomorphic structures are equal (assuming univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality.Examples
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq
open Derived-definitions-and-properties eq
open import Equivalence
open import H-level eq
open import H-level.Closure eq
open import Prelude
open import Univalence-axiom eq
open import Weak-equivalence eq

------------------------------------------------------------------------
-- An example: if two magmas are isomorphic, then they are equal

module Magma where

  -- Magmas.

  record Magma : Set₁ where
    constructor magma

    infix 8 _∙_

    field
      Carrier : Set
      _∙_     : Carrier → Carrier → Carrier

  -- Magma morphisms.

  Is-magma-morphism :
    ∀ M₁ M₂ → (Magma.Carrier M₁ → Magma.Carrier M₂) → Set
  Is-magma-morphism M₁ M₂ f =
    ∀ x y → f (Magma._∙_ M₁ x y) ≡ Magma._∙_ M₂ (f x) (f y)

  -- Magma isomorphisms.

  record Magma-isomorphism (M₁ M₂ : Magma) : Set where
    field
      bijection      : Magma.Carrier M₁ ↔ Magma.Carrier M₂
      to-homomorphic : Is-magma-morphism M₁ M₂ (_↔_.to bijection)

    open _↔_ bijection public

  -- If two magmas are isomorphic, then they are equal (assuming
  -- univalence).

  isomorphic-equal :
    Univalence-axiom′ (Set ²/≡) Set →
    Univalence-axiom lzero →
    ∀ {M₁ M₂} → Magma-isomorphism M₁ M₂ → M₁ ≡ M₂
  isomorphic-equal univ₁ univ₂ {magma A₁ _∙₁_} {magma A₂ _∙₂_} iso =
    magma A₁ _∙₁_                                  ≡⟨ elim (λ {A₁ A₂} A₁≡A₂ → (f : A₁ → A₁ → A₁) →
                                                              magma A₁ f ≡
                                                              magma A₂ (subst (λ A → A → A → A) A₁≡A₂ f))
                                                           (λ A f → cong (magma A) (sym $ subst-refl (λ A → A → A → A) f))
                                                           A₁≡A₂ _∙₁_ ⟩
    magma A₂ (subst (λ A → A → A → A) A₁≡A₂ _∙₁_)  ≡⟨ cong (magma A₂) subst-isomorphism ⟩∎
    magma A₂ _∙₂_                                  ∎
    where
    open Magma-isomorphism iso

    ext : Extensionality lzero lzero
    ext = dependent-extensionality univ₁ (λ _ → univ₂)

    A₁≡A₂ : A₁ ≡ A₂
    A₁≡A₂ = _≈_.from (≡≈≈ univ₂) $
              bijection⇒weak-equivalence bijection

    cast : (A₁ → A₁ → A₁) → (A₂ → A₂ → A₂)
    cast f = λ x y → to (f (from x) (from y))

    cast-is-subst : ∀ f → cast f ≡ subst (λ A → A → A → A) A₁≡A₂ f
    cast-is-subst f =
      subst-unique
        (λ A → A → A → A)
        (λ A≈B f x y → _≈_.to A≈B (f (_≈_.from A≈B x) (_≈_.from A≈B y)))
        refl
        univ₂
        (bijection⇒weak-equivalence bijection)
        f

    subst-isomorphism : subst (λ A → A → A → A) A₁≡A₂ _∙₁_ ≡ _∙₂_
    subst-isomorphism = ext λ x → ext λ y →
      subst (λ A → A → A → A) A₁≡A₂ _∙₁_ x y  ≡⟨ cong (λ f → f x y) $ sym $ cast-is-subst _∙₁_ ⟩
      to (from x ∙₁ from y)                   ≡⟨ to-homomorphic (from x) (from y) ⟩
      to (from x) ∙₂ to (from y)              ≡⟨ cong₂ _∙₂_ (right-inverse-of x) (right-inverse-of y) ⟩∎
      x ∙₂ y                                  ∎

------------------------------------------------------------------------
-- Another example

module Another-example where

  -- Some kind of algebraic structure (a set with a function and a
  -- fixed point of this function).

  Set-with-fixed-point : Set₁
  Set-with-fixed-point =
    ∃ λ (A     : Set     ) →
    ∃ λ (A-set : Is-set A) →
    ∃ λ (x     : A       ) →
    ∃ λ (f     : A → A   ) →
                 f x ≡ x

  -- Names for some of the substructures.

  Fixed-point :
    (Σ (Σ (∃ λ A → Is-set A)
          λ { (A , _) → A })
       λ { ((A , _) , _) → A → A }) →
    Set
  Fixed-point ((_ , x) , f) = f x ≡ x

  Is-fixed-point : (∃ λ { (A , _) → A }) → Set
  Is-fixed-point ((A , A-set) , x) =
    ∃ λ (f : A → A) → Fixed-point (((A , A-set) , x) , f)

  Is-type-with-fixed-point : (∃ λ A → Is-set A) → Set
  Is-type-with-fixed-point (A , A-set) =
    ∃ λ (x : A) → Is-fixed-point ((A , A-set) , x)

  Is-set-with-fixed-point : Set → Set
  Is-set-with-fixed-point A =
    ∃ λ (A-set : Is-set A) → Is-type-with-fixed-point (A , A-set)

  -- A notion of morphism for the structure introduced above.

  Is-morphism :
    {A₁ : Set} → Is-set-with-fixed-point A₁ →
    {A₂ : Set} → Is-set-with-fixed-point A₂ →
    (A₁ → A₂) → Set
  Is-morphism (_ , x₁ , f₁ , _) (_ , x₂ , f₂ , _) m =
    m x₁ ≡ x₂ ×
    (∀ y → m (f₁ y) ≡ f₂ (m y))

  -- A notion of isomorphism for the structure introduced above.

  Isomorphism : (F₁ F₂ : Set-with-fixed-point) → Set
  Isomorphism (A₁ , F₁) (A₂ , F₂) =
    ∃ λ (bijection : A₁ ↔ A₂) →
    Is-morphism F₁ F₂ (_↔_.to bijection)

  -- If two "sets with fixed points" are isomorphic, then they are
  -- equal (assuming univalence).

  isomorphic-equal :
    Univalence-axiom′ (Set ²/≡) Set →
    Univalence-axiom lzero →
    ∀ {F₁ F₂} → Isomorphism F₁ F₂ → F₁ ≡ F₂
  isomorphic-equal univ₁ univ₂
    {A₁ , A₁-set , x₁ , f₁ , f₁x₁≡x₁}
    {A₂ , A₂-set , x₂ , f₂ , f₂x₂≡x₂}
    (bijection , (x₁₂ , f₁₂)) =

    (A₁ , A₁-set , x₁ , f₁ , f₁x₁≡x₁)                                           ≡⟨                                        lemma₀ ⟩
    (A₂ , subst Is-set-with-fixed-point A₁≡A₂ (A₁-set , x₁ , f₁ , f₁x₁≡x₁))     ≡⟨ cong (λ p → A₂ , p)                    lemma₁ ⟩
    (A₂ , A₂-set , subst Is-type-with-fixed-point lemma₁″ (x₁ , f₁ , f₁x₁≡x₁))  ≡⟨ cong (λ p → A₂ , A₂-set , p)           lemma₂ ⟩
    (A₂ , A₂-set , x₂ , subst Is-fixed-point lemma₂″ (f₁ , f₁x₁≡x₁))            ≡⟨ cong (λ p → A₂ , A₂-set , x₂ , p)      lemma₃ ⟩
    (A₂ , A₂-set , x₂ , f₂ , subst Fixed-point lemma₃″ f₁x₁≡x₁)                 ≡⟨ cong (λ p → A₂ , A₂-set , x₂ , f₂ , p) lemma₄ ⟩∎
    (A₂ , A₂-set , x₂ , f₂ , f₂x₂≡x₂)                                           ∎

    where
    open _↔_ bijection

    abstract
      ext : Extensionality lzero lzero
      ext = dependent-extensionality univ₁ (λ _ → univ₂)

    A₁≡A₂ : A₁ ≡ A₂
    A₁≡A₂ = _≈_.from (≡≈≈ univ₂) $
              bijection⇒weak-equivalence bijection

    lemma₀ : (A₁ , A₁-set , x₁ , f₁ , f₁x₁≡x₁) ≡
             (A₂ , subst Is-set-with-fixed-point A₁≡A₂
                     (A₁-set , x₁ , f₁ , f₁x₁≡x₁))
    lemma₀ = elim¹
      (λ {A₂} A₁≡A₂ → ∀ A₁-is →
         (A₁ , A₁-is) ≡
         (A₂ , subst Is-set-with-fixed-point A₁≡A₂ A₁-is))
      (λ A₁-is → sym $
         cong (_,_ A₁) (subst-refl Is-set-with-fixed-point A₁-is))
      A₁≡A₂ _

    lemma₁′ : subst Is-set A₁≡A₂ A₁-set ≡ A₂-set
    lemma₁′ =
      _⇔_.to propositional⇔irrelevant (H-level-propositional ext 2) _ _

    lemma₁″ : (A₁ , A₁-set) ≡ (A₂ , A₂-set)
    lemma₁″ = Σ-≡,≡→≡ A₁≡A₂ lemma₁′

    lemma₁ : subst Is-set-with-fixed-point A₁≡A₂
               (A₁-set , x₁ , f₁ , f₁x₁≡x₁) ≡
             (A₂-set , subst Is-type-with-fixed-point lemma₁″
                         (x₁ , f₁ , f₁x₁≡x₁))
    lemma₁ = push-subst-pair′ Is-set Is-type-with-fixed-point lemma₁′

    to-is-subst : ∀ x → to x ≡ subst (λ A → A) A₁≡A₂ x
    to-is-subst x =
      subst-unique
        (λ A → A)
        (λ A≈B x → _≈_.to A≈B x)
        refl
        univ₂
        (bijection⇒weak-equivalence bijection)
        x

    lemma₂′ : subst (λ { (A , _) → A }) lemma₁″ x₁ ≡ x₂
    lemma₂′ =
      subst (λ { (A , _) → A }) lemma₁″ x₁  ≡⟨ subst₂-proj₁ (λ A → A) ⟩
      subst (λ A → A) A₁≡A₂ x₁              ≡⟨ sym $ to-is-subst x₁ ⟩
      to x₁                                 ≡⟨ x₁₂ ⟩∎
      x₂                                    ∎

    lemma₂″ : ((A₁ , A₁-set) , x₁) ≡ ((A₂ , A₂-set) , x₂)
    lemma₂″ = Σ-≡,≡→≡ lemma₁″ lemma₂′

    lemma₂ :
      subst Is-type-with-fixed-point lemma₁″ (x₁ , f₁ , f₁x₁≡x₁) ≡
      (x₂ , subst Is-fixed-point lemma₂″ (f₁ , f₁x₁≡x₁))
    lemma₂ = push-subst-pair′ (λ { (A , _) → A }) Is-fixed-point lemma₂′

    cast : (A₁ → A₁) → (A₂ → A₂)
    cast f = λ x → to (f (from x))

    cast-is-subst : ∀ f → cast f ≡ subst (λ A → A → A) A₁≡A₂ f
    cast-is-subst f =
      subst-unique
        (λ A → A → A)
        (λ A≈B f x → _≈_.to A≈B (f (_≈_.from A≈B x)))
        refl
        univ₂
        (bijection⇒weak-equivalence bijection)
        f

    lemma₃′ : subst (λ { ((A , _) , _) → A → A }) lemma₂″ f₁ ≡ f₂
    lemma₃′ = ext λ x →
      subst (λ { ((A , _) , _) → A → A }) lemma₂″ f₁ x  ≡⟨ cong (λ f → f x) $ subst₂-proj₁ (λ { (A , _) → A → A }) ⟩
      subst (λ { (A , _) → A → A }) lemma₁″ f₁ x        ≡⟨ cong (λ f → f x) $ subst₂-proj₁ (λ A → A → A) ⟩
      subst (λ A → A → A) A₁≡A₂ f₁ x                    ≡⟨ cong (λ f → f x) $ sym $ cast-is-subst f₁ ⟩
      to (f₁ (from x))                                  ≡⟨ f₁₂ (from x) ⟩
      f₂ (to (from x))                                  ≡⟨ cong f₂ (right-inverse-of x) ⟩∎
      f₂ x                                              ∎

    lemma₃″ : (((A₁ , A₁-set) , x₁) , f₁) ≡
              (((A₂ , A₂-set) , x₂) , f₂)
    lemma₃″ = Σ-≡,≡→≡ lemma₂″ lemma₃′

    lemma₃ : subst Is-fixed-point lemma₂″ (f₁ , f₁x₁≡x₁) ≡
             (f₂ , subst Fixed-point lemma₃″ f₁x₁≡x₁)
    lemma₃ = push-subst-pair′ (λ { ((A , _) , _) → A → A }) Fixed-point
               lemma₃′

    lemma₄ : subst Fixed-point lemma₃″ f₁x₁≡x₁ ≡ f₂x₂≡x₂
    lemma₄ = _⇔_.to set⇔UIP A₂-set _ _
