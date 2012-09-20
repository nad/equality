------------------------------------------------------------------------
-- Certain isomorphic structures are equal (assuming univalence)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- This module has been developed in collaboration with Thierry
-- Coquand.

-- The module starts with two concrete examples, and ends with a more
-- general development.

open import Equality

module Univalence-axiom.Isomorphism-implies-equality
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

import Bijection; open Bijection eq
open Derived-definitions-and-properties eq
open import Equivalence
import H-level; open H-level eq
import H-level.Closure; open H-level.Closure eq
open import Prelude renaming (_∘_ to _⊚_)
import Univalence-axiom; open Univalence-axiom eq
import Weak-equivalence
private
  open module Weak = Weak-equivalence eq

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

    ext : {A : Set} {B : A → Set} → Extensionality A B
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

      -- A variant of push-subst-pair.

      push-subst-pair′ :
        ∀ {a b c} {A : Set a} {y z : A} {y≡z : y ≡ z}
        (B : A → Set b) (C : Σ A B → Set c) {p p₁} →
        (p₁≡p₁ : subst B y≡z (proj₁ p) ≡ p₁) →
        subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
        (p₁ , subst₂ C y≡z p₁≡p₁ (proj₂ p))
      push-subst-pair′ {y≡z = y≡z} B C {p} =
        elim¹ (λ {p₁} p₁≡p₁ →
                 subst (λ x → Σ (B x) (curry C x)) y≡z p ≡
                 (p₁ , subst₂ C y≡z p₁≡p₁ (proj₂ p)))
              (push-subst-pair B C)

    ext : {A : Set} {B : A → Set} → Extensionality A B
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
-- N-ary functions

-- N-ary functions.

_^_⟶_ : Set → ℕ → Set → Set
A ^ zero  ⟶ B = B
A ^ suc n ⟶ B = A → A ^ n ⟶ B

-- N-ary function morphisms.

Is-_-ary-morphism :
  (n : ℕ) {A B : Set} → A ^ n ⟶ A → B ^ n ⟶ B → (A → B) → Set
Is- zero  -ary-morphism f₁ f₂ m = m f₁ ≡ f₂
Is- suc n -ary-morphism f₁ f₂ m =
  ∀ x → Is- n -ary-morphism (f₁ x) (f₂ (m x)) m

abstract

  -- If _↔_.to m is a morphism, then _↔_.from m is also a morphism.

  from-also-_-ary-morphism :
    (n : ℕ) {A B : Set} (f₁ : A ^ n ⟶ A) (f₂ : B ^ n ⟶ B) (m : A ↔ B) →
    Is- n -ary-morphism f₁ f₂ (_↔_.to m) →
    Is- n -ary-morphism f₂ f₁ (_↔_.from m)
  from-also- zero  -ary-morphism f₁ f₂ m is = _↔_.to-from m is
  from-also- suc n -ary-morphism f₁ f₂ m is = λ x →
    from-also- n -ary-morphism (f₁ (from x)) (f₂ x) m
      (subst (λ y → Is- n -ary-morphism (f₁ (from x)) (f₂ y) to)
             (right-inverse-of x)
             (is (from x)))
    where open _↔_ m

-- Changes the type of an n-ary function.

cast : {A₁ A₂ : Set} → A₁ ≈ A₂ → ∀ n → A₁ ^ n ⟶ A₁ → A₂ ^ n ⟶ A₂
cast A₁≈A₂ zero    = _≈_.to A₁≈A₂
cast A₁≈A₂ (suc n) = λ f x → cast A₁≈A₂ n (f (_≈_.from A₁≈A₂ x))

abstract

  -- Cast simplification lemma.

  cast-id : {A : Set} →
            (∀ n → Extensionality A (λ _ → A ^ n ⟶ A)) →
            ∀ n (f : A ^ n ⟶ A) → cast Weak.id n f ≡ f
  cast-id ext zero    f = refl f
  cast-id ext (suc n) f = ext n $ λ x → cast-id ext n (f x)

  -- We can express cast as an instance of subst (assuming
  -- extensionality and univalence).

  cast-is-subst :
    (∀ {A : Set} n → Extensionality A (λ _ → A ^ n ⟶ A)) →
    {A₁ A₂ : Set}
    (univ : Univalence-axiom′ A₁ A₂)
    (A₁≈A₂ : A₁ ≈ A₂) (n : ℕ) (f : A₁ ^ n ⟶ A₁) →
    cast A₁≈A₂ n f ≡
    subst (λ C → C ^ n ⟶ C) (_≈_.from (≡≈≈ univ) A₁≈A₂) f
  cast-is-subst ext univ A₁≈A₂ n =
    subst-unique
      (λ A → A ^ n ⟶ A)
      (λ A≈B f → cast A≈B n f)
      (cast-id ext n)
      univ
      A₁≈A₂

  -- If there is an isomorphism from f₁ to f₂, then the corresponding
  -- instance of cast maps f₁ to f₂ (assuming extensionality).

  cast-isomorphism :
    {A₁ A₂ : Set} →
    (∀ n → Extensionality A₂ (λ _ → A₂ ^ n ⟶ A₂)) →
    (A₁≈A₂ : A₁ ≈ A₂)
    (n : ℕ) (f₁ : A₁ ^ n ⟶ A₁) (f₂ : A₂ ^ n ⟶ A₂) →
    Is- n -ary-morphism f₁ f₂ (_≈_.to A₁≈A₂) →
    cast A₁≈A₂ n f₁ ≡ f₂
  cast-isomorphism ext A₁≈A₂ zero    f₁ f₂ is = is
  cast-isomorphism ext A₁≈A₂ (suc n) f₁ f₂ is = ext n $ λ x →
    cast A₁≈A₂ n (f₁ (from x))  ≡⟨ cast-isomorphism ext A₁≈A₂ n _ _ (is (from x)) ⟩
    f₂ (to (from x))            ≡⟨ cong f₂ (right-inverse-of x) ⟩∎
    f₂ x                        ∎
    where open _≈_ A₁≈A₂

  -- Combining the results above we get the following: if there is an
  -- isomorphism from f₁ to f₂, then the corresponding instance of
  -- subst maps f₁ to f₂ (assuming extensionality and univalence).

  subst-isomorphism :
    (∀ {A : Set} n → Extensionality A (λ _ → A ^ n ⟶ A)) →
    {A₁ A₂ : Set}
    (univ : Univalence-axiom′ A₁ A₂)
    (A₁≈A₂ : A₁ ≈ A₂)
    (n : ℕ) (f₁ : A₁ ^ n ⟶ A₁) (f₂ : A₂ ^ n ⟶ A₂) →
    Is- n -ary-morphism f₁ f₂ (_≈_.to A₁≈A₂) →
    subst (λ A → A ^ n ⟶ A) (_≈_.from (≡≈≈ univ) A₁≈A₂) f₁ ≡ f₂
  subst-isomorphism ext univ A₁≈A₂ n f₁ f₂ is =
    subst (λ A → A ^ n ⟶ A) (_≈_.from (≡≈≈ univ) A₁≈A₂) f₁  ≡⟨ sym $ cast-is-subst ext univ A₁≈A₂ n f₁ ⟩
    cast A₁≈A₂ n f₁                                         ≡⟨ cast-isomorphism ext A₁≈A₂ n f₁ f₂ is ⟩∎
    f₂                                                      ∎

------------------------------------------------------------------------
-- A class of algebraic structures

-- An algebraic structure universe.

mutual

  -- Codes for structures.

  infixl 5 _+operator_ _+axiom_

  data Structure : Set₁ where
    empty : Structure

    -- N-ary functions.
    _+operator_ : Structure → (n : ℕ) → Structure

    -- Arbitrary /propositional/ axioms.
    _+axiom_ : (s : Structure)
               (P : ∃ λ (P : (A : ∃ Is-set) → ⟦ s ⟧ A → Set) →
                      ∀ A s → Propositional (P A s)) →
               Structure

  -- Interpretation of the codes.

  ⟦_⟧ : Structure → ∃ Is-set → Set₁
  ⟦ empty                 ⟧ A = ↑ _ ⊤
  ⟦ s +operator n         ⟧ A = ⟦ s ⟧ A × (proj₁ A ^ n ⟶ proj₁ A)
  ⟦ s +axiom (P , P-prop) ⟧ A = Σ (⟦ s ⟧ A) (P A)

-- Top-level interpretation.

⟦̂_⟧ : Structure → Set₁
⟦̂ s ⟧ = ∃ ⟦ s ⟧

-- Morphisms.

Is-structure-morphism :
  (s : Structure) →
  {A B : ∃ Is-set} → ⟦ s ⟧ A → ⟦ s ⟧ B →
  (proj₁ A → proj₁ B) → Set
Is-structure-morphism empty           _          _          m = ⊤
Is-structure-morphism (s +axiom _)    (s₁ , _)   (s₂ , _)   m =
  Is-structure-morphism s s₁ s₂ m
Is-structure-morphism (s +operator n) (s₁ , op₁) (s₂ , op₂) m =
  Is-structure-morphism s s₁ s₂ m × Is- n -ary-morphism op₁ op₂ m

-- Isomorphisms.

Isomorphism : (s : Structure) → ⟦̂ s ⟧ → ⟦̂ s ⟧ → Set
Isomorphism s ((A₁ , _) , s₁) ((A₂ , _) , s₂) =
  ∃ λ (m : A₁ ↔ A₂) → Is-structure-morphism s s₁ s₂ (_↔_.to m)

abstract

  -- If _↔_.to m is a morphism, then _↔_.from m is also a morphism.

  from-also-structure-morphism :
    (s : Structure) →
    {A B : ∃ Is-set} {s₁ : ⟦ s ⟧ A} {s₂ : ⟦ s ⟧ B} →
    (m : proj₁ A ↔ proj₁ B) →
    Is-structure-morphism s s₁ s₂ (_↔_.to m) →
    Is-structure-morphism s s₂ s₁ (_↔_.from m)
  from-also-structure-morphism empty           m = _
  from-also-structure-morphism (s +axiom _)    m =
    from-also-structure-morphism s m
  from-also-structure-morphism (s +operator n) m =
    Σ-map (from-also-structure-morphism s m)
          (from-also- n -ary-morphism _ _ m)

------------------------------------------------------------------------
-- Some example structures

-- Example: magmas.

magma : Structure
magma = empty +operator 2

Magma : Set₁
Magma = ⟦̂ magma ⟧

private

  -- An unfolding of Magma.

  Magma-unfolded : Magma ≡
                   ∃ λ { (A , A-set) → ↑ _ ⊤ × (A → A → A) }
  Magma-unfolded = refl _

-- Example: semigroups. The definition uses extensionality to prove
-- that the axiom is propositional.

semigroup :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure
semigroup ext =
  empty

  +operator 2

  +axiom
    ( (λ { _ (_ , _∙_) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
    , assoc-prop
    )

  where
  assoc-prop = λ { (A , A-set) _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    A-set _ _ }

Semigroup :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Semigroup ext = ⟦̂ semigroup ext ⟧

private

  -- An unfolding of Semigroup.

  Semigroup-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Semigroup ext ≡
    ∃ λ { (A , A-set) →
          Σ (↑ _ ⊤ ×
             (A → A → A)) λ { (_ , _∙_) →
          ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z }
        }
  Semigroup-unfolded _ = refl _

-- Example: abelian groups. The definition uses extensionality to
-- prove that the axioms are propositional.

abelian-group :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Structure
abelian-group ext =
  empty

  -- The binary group operation.
  +operator 2

  -- Commutativity.
  +axiom
    ( (λ { _ (_ , _∙_) →
           ∀ x y → x ∙ y ≡ y ∙ x })
    , comm-prop
    )

  -- Associativity.
  +axiom
    ( (λ { _ ((_ , _∙_) , _) →
           ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z })
    , assoc-prop
    )

  -- Identity.
  +operator 0

  -- Left identity.
  +axiom
    ( (λ { _ ((((_ , _∙_) , _) , _) , e) →
           ∀ x → e ∙ x ≡ x })
    , left-identity-prop
    )

  -- Right identity.
  +axiom
    ( (λ { _ (((((_ , _∙_) , _) , _) , e) , _) →
           ∀ x → x ∙ e ≡ x })
    , right-identity-prop
    )

  -- Inverse.
  +operator 1

  -- Left inverse.
  +axiom
    ( (λ { _ (((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) →
           ∀ x → (x ⁻¹) ∙ x ≡ e })
    , left-inverse-prop
    )

  -- Right inverse.
  +axiom
    ( (λ { _ ((((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) , _) →
           ∀ x → x ∙ (x ⁻¹) ≡ e })
    , right-inverse-prop
    )

  where
  comm-prop = λ { (A , A-set) _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    A-set _ _ }

  assoc-prop = λ { (A , A-set) _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    A-set _ _ }

  left-identity-prop = λ { (A , A-set) _ →
    Π-closure ext 1 λ _ →
    A-set _ _ }

  right-identity-prop = λ { (A , A-set) _ →
    Π-closure ext 1 λ _ →
    A-set _ _ }

  left-inverse-prop = λ { (A , A-set) _ →
    Π-closure ext 1 λ _ →
    A-set _ _ }

  right-inverse-prop = λ { (A , A-set) _ →
    Π-closure ext 1 λ _ →
    A-set _ _ }

Abelian-group :
  ({A : Set} {B : A → Set} → Extensionality A B) →
  Set₁
Abelian-group ext = ⟦̂ abelian-group ext ⟧

private

  -- An unfolding of Abelian-group. Note that the inner structure is
  -- left-nested.

  Abelian-group-unfolded :
    (ext : {A : Set} {B : A → Set} → Extensionality A B) →
    Abelian-group ext ≡

    Σ (Σ

    Set                                    λ A →
    Is-set A                             ) λ { (A , _) → Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (Σ (↑ _ ⊤) λ _ →
    A → A → A                            ) λ {        (_ , _∙_) →
    ∀ x y → x ∙ y ≡ y ∙ x               }) λ {       ((_ , _∙_) , _) →
    ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z }) λ _ →
    A                                    ) λ {     ((((_ , _∙_) , _) , _) , e) →
    ∀ x → e ∙ x ≡ x                     }) λ {    (((((_ , _∙_) , _) , _) , e) , _) →
    ∀ x → x ∙ e ≡ x                     }) λ _ →
    A → A                                ) λ {  (((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) →
    ∀ x → (x ⁻¹) ∙ x ≡ e                }) λ { ((((((((_ , _∙_) , _) , _) , e) , _) , _) , _⁻¹) , _) →
    ∀ x → x ∙ (x ⁻¹) ≡ e                }}

  Abelian-group-unfolded _ = refl _

------------------------------------------------------------------------
-- Isomorphic structures are equal (assuming univalence)

abstract

  -- Isomorphic structures are equal (assuming univalence).

  isomorphic-equal :
    Univalence-axiom′ (Set ²/≡) Set →
    Univalence-axiom lzero →
    (s : Structure) (s₁ s₂ : ⟦̂ s ⟧) →
    Isomorphism s s₁ s₂ → s₁ ≡ s₂
  isomorphic-equal univ₁ univ₂
    s ((A₁ , A₁-set) , s₁) ((A₂ , A₂-set) , s₂) (m , is) =

    ((A₁ , A₁-set) , s₁)  ≡⟨ Σ-≡,≡→≡ A₁≡A₂′ (lemma s s₁ s₂ is) ⟩∎
    ((A₂ , A₂-set) , s₂)  ∎

    where
    open _↔_ m

    -- Extensionality follows from univalence.

    ext : {A : Set} {B : A → Set} → Extensionality A B
    ext = dependent-extensionality univ₁ (λ _ → univ₂)

    -- The presence of the bijection implies that the structure's
    -- underlying types are equal (due to univalence).

    A₁≡A₂ : A₁ ≡ A₂
    A₁≡A₂ = _≈_.from (≡≈≈ univ₂) $ bijection⇒weak-equivalence m

    -- Equality still holds if the types are paired up with proofs
    -- showing that they are sets.

    A₁≡A₂′ : (A₁ , A₁-set) ≡ (A₂ , A₂-set)
    A₁≡A₂′ =
      Σ-≡,≡→≡ A₁≡A₂
              (_⇔_.to propositional⇔irrelevant
                      (H-level-propositional ext 2) _ _)

    -- We can lift subst-isomorphism to structures by recursion on
    -- structure codes.

    lemma : (s : Structure)
            (s₁ : ⟦ s ⟧ (A₁ , A₁-set)) (s₂ : ⟦ s ⟧ (A₂ , A₂-set)) →
            Is-structure-morphism s s₁ s₂ to →
            subst ⟦ s ⟧ A₁≡A₂′ s₁ ≡ s₂
    lemma empty _ _ _ = refl _

    lemma (s +axiom (P , P-prop)) (s₁ , ax₁) (s₂ , ax₂) is =
      subst (λ A → Σ (⟦ s ⟧ A) (P A)) A₁≡A₂′ (s₁ , ax₁)                 ≡⟨ push-subst-pair ⟦ s ⟧ (uncurry P) ⟩
      (subst ⟦ s ⟧ A₁≡A₂′ s₁ , subst₂ (uncurry P) A₁≡A₂′ (refl _) ax₁)  ≡⟨ Σ-≡,≡→≡ (lemma s s₁ s₂ is)
                                                                                   (_⇔_.to propositional⇔irrelevant (P-prop _ _) _ _) ⟩∎
      (s₂ , ax₂)                                                        ∎

    lemma (s +operator n) (s₁ , op₁) (s₂ , op₂) (is-s , is-o) =
      subst (λ A → ⟦ s ⟧ A × (proj₁ A ^ n ⟶ proj₁ A)) A₁≡A₂′ (s₁ , op₁)  ≡⟨ push-subst-pair ⟦ s ⟧ (λ { ((A , _) , _) → A ^ n ⟶ A }) ⟩

      (subst ⟦ s ⟧ A₁≡A₂′ s₁ ,
       subst₂ (λ { ((A , _) , _) → A ^ n ⟶ A }) A₁≡A₂′ (refl _) op₁)     ≡⟨ cong (_,_ _) $ subst₂-proj₁ (λ { (A , _) → A ^ n ⟶ A }) ⟩

      (subst ⟦ s ⟧ A₁≡A₂′ s₁ ,
       subst (λ { (A , _) → A ^ n ⟶ A }) A₁≡A₂′ op₁)                     ≡⟨ cong (_,_ _) $ subst₂-proj₁ (λ A → A ^ n ⟶ A) ⟩

      (subst ⟦ s ⟧ A₁≡A₂′ s₁ , subst (λ A → A ^ n ⟶ A) A₁≡A₂ op₁)        ≡⟨ Σ-≡,≡→≡ (lemma s s₁ s₂ is-s) lemma₂ ⟩∎

      (s₂ , op₂)                                                         ∎

      where
      lemma₂ : subst (λ _ → A₂ ^ n ⟶ A₂) (lemma s s₁ s₂ is-s)
                 (subst (λ A → A ^ n ⟶ A) A₁≡A₂ op₁) ≡
               op₂
      lemma₂ =
        subst (λ _ → A₂ ^ n ⟶ A₂) (lemma s s₁ s₂ is-s)
          (subst (λ A → A ^ n ⟶ A) A₁≡A₂ op₁)           ≡⟨ subst-const ⟩

        subst (λ A → A ^ n ⟶ A) A₁≡A₂ op₁               ≡⟨ subst-isomorphism (λ _ → ext) univ₂
                                                             (bijection⇒weak-equivalence m) n op₁ op₂ is-o ⟩∎
        op₂                                             ∎
