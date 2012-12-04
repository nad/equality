------------------------------------------------------------------------
-- Certain isomorphic structures are equal (assuming univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality.Examples
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq hiding (id)
open Derived-definitions-and-properties eq
open import Equivalence using (module _⇔_)
open import H-level eq
open import H-level.Closure eq
open import Prelude hiding (id)
open import Univalence-axiom eq
open import Weak-equivalence eq hiding (id)

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

------------------------------------------------------------------------
-- Yet another example: if two monoids (on sets) are isomorphic, then
-- they are equal

-- This is proved twice, once using a right-nested definition of
-- monoids, and once using a left-nested definition.

module Monoid-right-nested where

  -- Monoid laws (including the assumption that the carrier type is a
  -- set).

  Is-monoid : (A : Set) → (A → A → A) → A → Set
  Is-monoid A _∙_ id =

    -- A is a set.
    Is-set A ×

    -- Left and right identity laws.
    (∀ x → id ∙ x ≡ x) ×
    (∀ x → x ∙ id ≡ x) ×

    -- Associativity.
    (∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z)

  -- Monoids (on sets).

  Monoid : Set₁
  Monoid =
    -- Carrier.
    Σ Set λ A →

    -- Binary operation.
    Σ (A → A → A) λ _∙_ →

    -- Identity.
    Σ A λ id →

    -- Laws.
    Is-monoid A _∙_ id

  -- The carrier type.

  Carrier : Monoid → Set
  Carrier M = proj₁ M

  -- The binary operation.

  op : (M : Monoid) → Carrier M → Carrier M → Carrier M
  op M = proj₁ (proj₂ M)

  -- The identity element.

  id : (M : Monoid) → Carrier M
  id M = proj₁ (proj₂ (proj₂ M))

  -- The monoid laws.

  monoid-laws : (M : Monoid) → Is-monoid (Carrier M) (op M) (id M)
  monoid-laws M = proj₂ (proj₂ (proj₂ M))

  -- The monoid laws are propositional (assuming extensionality).
  --
  -- I got the idea to formulate this property as a separate lemma
  -- from Mike Shulman. /NAD

  monoid-laws-propositional :
    Extensionality (# 0) (# 0) →
    (M : Monoid) →
    Propositional (Is-monoid (Carrier M) (op M) (id M))
  monoid-laws-propositional ext M =
    ×-closure 1 (H-level-propositional ext 2)
    (×-closure 1 (Π-closure ext 1 λ _ →
                  is-set _ _)
    (×-closure 1 (Π-closure ext 1 λ _ →
                  is-set _ _)
                 (Π-closure ext 1 λ _ →
                  Π-closure ext 1 λ _ →
                  Π-closure ext 1 λ _ →
                  is-set _ _)))
    where is-set = proj₁ (monoid-laws M)

  -- One can prove that two monoids are equal by proving that the
  -- carrier sets, binary operations and identity elements (suitably
  -- transported) are equal (assuming extensionality).
  --
  -- I got the idea to formulate this property as a separate lemma
  -- from Mike Shulman. /NAD

  monoids-equal-if :
    Extensionality (# 0) (# 0) →
    (M₁ M₂ : Monoid)
    (C-eq : Carrier M₁ ≡ Carrier M₂) →
    subst (λ A → A → A → A) C-eq (op M₁) ≡ op M₂ →
    subst (λ A → A) C-eq (id M₁) ≡ id M₂ →
    M₁ ≡ M₂
  monoids-equal-if ext M₁ M₂ C-eq ∙-eq id-eq =

    (Carrier M₁ , op M₁ , id M₁ , monoid-laws M₁)                         ≡⟨ Σ-≡,≡→≡ C-eq (refl _) ⟩

    (Carrier M₂ ,
       subst (λ A → Σ (A → A → A) λ _∙_ → Σ A λ id → Is-monoid A _∙_ id)
             C-eq
             (op M₁ , id M₁ , monoid-laws M₁))                            ≡⟨ cong (λ rest → Carrier M₂ , rest) $
                                                                               push-subst-pair′
                                                                                 (λ A → A → A → A)
                                                                                 (λ { (A , _∙_) → Σ A λ id → Is-monoid A _∙_ id })
                                                                                 ∙-eq ⟩
    (Carrier M₂ , op M₂ ,
       subst (λ { (A , _∙_) → Σ A λ id → Is-monoid A _∙_ id })
             (Σ-≡,≡→≡ C-eq ∙-eq)
             (id M₁ , monoid-laws M₁))                                    ≡⟨ cong (λ rest → Carrier M₂ , op M₂ , rest) $
                                                                               push-subst-pair′
                                                                                 (λ { (A , _∙_) → A })
                                                                                 (λ { ((A , _∙_) , id) → Is-monoid A _∙_ id })
                                                                                 id-eq′ ⟩
    (Carrier M₂ , op M₂ , id M₂ ,
       subst (λ { ((A , _∙_) , id) → Is-monoid A _∙_ id })
             (Σ-≡,≡→≡ (Σ-≡,≡→≡ C-eq ∙-eq) id-eq′)
             (monoid-laws M₁))                                            ≡⟨ cong (λ rest → Carrier M₂ , op M₂ , id M₂ , rest) $
                                                                               _⇔_.to propositional⇔irrelevant
                                                                                      (monoid-laws-propositional ext M₂) _ _ ⟩∎
    (Carrier M₂ , op M₂ , id M₂ , monoid-laws M₂)                         ∎

    where
    id-eq′ =
      subst (λ { (A , _∙_) → A }) (Σ-≡,≡→≡ C-eq ∙-eq) (id M₁)   ≡⟨ subst-∘ (λ A → A) proj₁ _ ⟩
      subst (λ A → A) (cong proj₁ (Σ-≡,≡→≡ C-eq ∙-eq)) (id M₁)  ≡⟨ cong (λ eq → subst (λ A → A) eq (id M₁)) $ proj₁-Σ-≡,≡→≡ _ _ ⟩
      subst (λ A → A) C-eq (id M₁)                              ≡⟨ id-eq ⟩∎
      id M₂                                                     ∎

  -- Monoid morphisms.

  Is-monoid-morphism :
    ∀ M₁ M₂ → (Carrier M₁ → Carrier M₂) → Set
  Is-monoid-morphism M₁ M₂ f =
    (∀ x y → f (op M₁ x y) ≡ op M₂ (f x) (f y)) ×
    (f (id M₁) ≡ id M₂)

  -- Monoid isomorphisms.

  _≅_ : Monoid → Monoid → Set
  M₁ ≅ M₂ =
    Σ (Carrier M₁ ↔ Carrier M₂) λ f →
    Is-monoid-morphism M₁ M₂ (_↔_.to f)

  -- If two monoids are isomorphic, then they are equal (assuming
  -- univalence).

  isomorphic-equal :
    Univalence-axiom (# 0) →
    Univalence-axiom (# 1) →
    ∀ M₁ M₂ → M₁ ≅ M₂ → M₁ ≡ M₂
  isomorphic-equal univ₀ univ₁ M₁ M₂ (bijection , op-homo , id-homo) =
    monoids-equal-if ext M₁ M₂ C-eq ∙-eq id-eq
    where
    open _↔_ bijection

    -- Extensionality follows from univalence.

    ext : Extensionality (# 0) (# 0)
    ext = dependent-extensionality univ₁ (λ _ → univ₀)

    -- There is a bijection between the carrier sets, so, by
    -- univalence, they are equal.

    C-eq : Carrier M₁ ≡ Carrier M₂
    C-eq = ≈⇒≡ univ₀ $ bijection⇒weak-equivalence bijection

    -- One can "cast" binary operators on one monoid so that they
    -- apply to the other instead.

    cast₂ : (Carrier M₁ → Carrier M₁ → Carrier M₁) →
            (Carrier M₂ → Carrier M₂ → Carrier M₂)
    cast₂ f = λ x y → to (f (from x) (from y))

    -- The transport theorem implies that the cast operator can be
    -- expressed using subst.

    cast₂-is-subst : ∀ f → cast₂ f ≡ subst (λ A → A → A → A) C-eq f
    cast₂-is-subst f =
      subst-unique
        (λ A → A → A → A)
        (λ A≈B f x y → _≈_.to A≈B (f (_≈_.from A≈B x) (_≈_.from A≈B y)))
        refl
        univ₀
        (bijection⇒weak-equivalence bijection)
        f

    -- One can transport one binary operator to the other using C-eq.
    -- This follows from extensionality, cast₂-is-subst, and the fact
    -- that the bijection is a monoid homomorphism.

    ∙-eq : subst (λ A → A → A → A) C-eq (op M₁) ≡ op M₂
    ∙-eq = ext λ x → ext λ y →
      subst (λ A → A → A → A) C-eq (op M₁) x y  ≡⟨ cong (λ f → f x y) $ sym $ cast₂-is-subst (op M₁) ⟩
      to (op M₁ (from x) (from y))              ≡⟨ op-homo (from x) (from y) ⟩
      op M₂ (to (from x)) (to (from y))         ≡⟨ cong₂ (op M₂) (right-inverse-of x) (right-inverse-of y) ⟩∎
      op M₂ x y                                 ∎

    -- The development above can be repeated for the identity
    -- elements.

    cast₀ : Carrier M₁ → Carrier M₂
    cast₀ x = to x

    cast₀-is-subst : ∀ x → cast₀ x ≡ subst (λ A → A) C-eq x
    cast₀-is-subst x =
      subst-unique
        (λ A → A)
        (λ A≈B x → _≈_.to A≈B x)
        refl
        univ₀
        (bijection⇒weak-equivalence bijection)
        x

    id-eq : subst (λ A → A) C-eq (id M₁) ≡ id M₂
    id-eq =
      subst (λ A → A) C-eq (id M₁)  ≡⟨ sym $ cast₀-is-subst (id M₁) ⟩
      to (id M₁)                    ≡⟨ id-homo ⟩∎
      id M₂                         ∎

module Monoid-left-nested where

  open Monoid-right-nested public using (Is-monoid)

  -- Monoids (on sets).

  Monoid : Set₁
  Monoid =
    Σ (Σ (Σ

    -- Carrier.
    Set λ A →

    -- Binary operation.
    A → A → A) λ { (A , _) →

    -- Identity.
    A }) λ { ((A , _∙_) , id) →

    -- Laws.
    Is-monoid A _∙_ id }

  -- The carrier type.

  Carrier : Monoid → Set
  Carrier M = proj₁ (proj₁ (proj₁ M))

  -- The binary operation.

  op : (M : Monoid) → Carrier M → Carrier M → Carrier M
  op M = proj₂ (proj₁ (proj₁ M))

  -- The identity element.

  id : (M : Monoid) → Carrier M
  id M = proj₂ (proj₁ M)

  -- The monoid laws.

  monoid-laws : (M : Monoid) → Is-monoid (Carrier M) (op M) (id M)
  monoid-laws M = proj₂ M

  -- Converts a "left-nested monoid" to a "right-nested" one.

  right-nested : Monoid → Monoid-right-nested.Monoid
  right-nested (((A , op) , id) , laws) = (A , op , id , laws)

  -- The monoid laws are propositional (assuming extensionality).
  --
  -- I got the idea to formulate this property as a separate lemma
  -- from Mike Shulman. /NAD

  monoid-laws-propositional :
    Extensionality (# 0) (# 0) →
    (M : Monoid) →
    Propositional (Is-monoid (Carrier M) (op M) (id M))
  monoid-laws-propositional ext M =
    Monoid-right-nested.monoid-laws-propositional
      ext (right-nested M)

  -- One can prove that two monoids are equal by proving that the
  -- carrier sets, binary operations and identity elements (suitably
  -- transported) are equal (assuming extensionality).
  --
  -- I got the idea to formulate this property as a separate lemma
  -- from Mike Shulman. /NAD

  monoids-equal-if :
    Extensionality (# 0) (# 0) →
    (M₁ M₂ : Monoid)
    (C-eq : Carrier M₁ ≡ Carrier M₂) →
    subst (λ A → A → A → A) C-eq (op M₁) ≡ op M₂ →
    subst (λ A → A) C-eq (id M₁) ≡ id M₂ →
    M₁ ≡ M₂
  monoids-equal-if ext M₁ M₂ C-eq ∙-eq id-eq =
    Σ-≡,≡→≡ (Σ-≡,≡→≡ (Σ-≡,≡→≡ C-eq ∙-eq) id-eq′)
            (_⇔_.to propositional⇔irrelevant
                    (monoid-laws-propositional ext M₂) _ _)
    where
    id-eq′ =
      subst (λ { (A , _∙_) → A }) (Σ-≡,≡→≡ C-eq ∙-eq) (id M₁)   ≡⟨ subst-∘ (λ A → A) proj₁ _ ⟩
      subst (λ A → A) (cong proj₁ (Σ-≡,≡→≡ C-eq ∙-eq)) (id M₁)  ≡⟨ cong (λ eq → subst (λ A → A) eq (id M₁)) $ proj₁-Σ-≡,≡→≡ _ _ ⟩
      subst (λ A → A) C-eq (id M₁)                              ≡⟨ id-eq ⟩∎
      id M₂                                                     ∎

  -- Monoid morphisms.

  Is-monoid-morphism :
    ∀ M₁ M₂ → (Carrier M₁ → Carrier M₂) → Set
  Is-monoid-morphism M₁ M₂ f =
    Monoid-right-nested.Is-monoid-morphism
      (right-nested M₁) (right-nested M₂) f

  -- Monoid isomorphisms.

  _≅_ : Monoid → Monoid → Set
  M₁ ≅ M₂ = Monoid-right-nested._≅_ (right-nested M₁) (right-nested M₂)

  -- If two monoids are isomorphic, then they are equal (assuming
  -- univalence).

  isomorphic-equal :
    Univalence-axiom (# 0) →
    Univalence-axiom (# 1) →
    ∀ M₁ M₂ → M₁ ≅ M₂ → M₁ ≡ M₂
  isomorphic-equal univ₀ univ₁ M₁ M₂ (bijection , op-homo , id-homo) =
    monoids-equal-if ext M₁ M₂ C-eq ∙-eq id-eq
    where
    open _↔_ bijection

    -- Extensionality follows from univalence.

    ext : Extensionality (# 0) (# 0)
    ext = dependent-extensionality univ₁ (λ _ → univ₀)

    -- There is a bijection between the carrier sets, so, by
    -- univalence, they are equal.

    C-eq : Carrier M₁ ≡ Carrier M₂
    C-eq = ≈⇒≡ univ₀ $ bijection⇒weak-equivalence bijection

    -- One can "cast" binary operators on one monoid so that they
    -- apply to the other instead.

    cast₂ : (Carrier M₁ → Carrier M₁ → Carrier M₁) →
            (Carrier M₂ → Carrier M₂ → Carrier M₂)
    cast₂ f = λ x y → to (f (from x) (from y))

    -- The transport theorem implies that the cast operator can be
    -- expressed using subst.

    cast₂-is-subst : ∀ f → cast₂ f ≡ subst (λ A → A → A → A) C-eq f
    cast₂-is-subst f =
      subst-unique
        (λ A → A → A → A)
        (λ A≈B f x y → _≈_.to A≈B (f (_≈_.from A≈B x) (_≈_.from A≈B y)))
        refl
        univ₀
        (bijection⇒weak-equivalence bijection)
        f

    -- One can transport one binary operator to the other using C-eq.
    -- This follows from extensionality, cast₂-is-subst, and the fact
    -- that the bijection is a monoid homomorphism.

    ∙-eq : subst (λ A → A → A → A) C-eq (op M₁) ≡ op M₂
    ∙-eq = ext λ x → ext λ y →
      subst (λ A → A → A → A) C-eq (op M₁) x y  ≡⟨ cong (λ f → f x y) $ sym $ cast₂-is-subst (op M₁) ⟩
      to (op M₁ (from x) (from y))              ≡⟨ op-homo (from x) (from y) ⟩
      op M₂ (to (from x)) (to (from y))         ≡⟨ cong₂ (op M₂) (right-inverse-of x) (right-inverse-of y) ⟩∎
      op M₂ x y                                 ∎

    -- The development above can be repeated for the identity
    -- elements.

    cast₀ : Carrier M₁ → Carrier M₂
    cast₀ x = to x

    cast₀-is-subst : ∀ x → cast₀ x ≡ subst (λ A → A) C-eq x
    cast₀-is-subst x =
      subst-unique
        (λ A → A)
        (λ A≈B x → _≈_.to A≈B x)
        refl
        univ₀
        (bijection⇒weak-equivalence bijection)
        x

    id-eq : subst (λ A → A) C-eq (id M₁) ≡ id M₂
    id-eq =
      subst (λ A → A) C-eq (id M₁)  ≡⟨ sym $ cast₀-is-subst (id M₁) ⟩
      to (id M₁)                    ≡⟨ id-homo ⟩∎
      id M₂                         ∎

-- The main differences between the use of right-nested and
-- left-nested definitions of monoids seem to be the following:
-- * It is a bit harder to write down a left-nested definition.
-- * It is much harder to prove the "monoids-equal-if" property for
--   the right-nested definition.
