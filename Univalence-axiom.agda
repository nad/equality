------------------------------------------------------------------------
-- The univalence axiom
------------------------------------------------------------------------

{-# OPTIONS --without-K --type-in-type #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module Univalence-axiom
  {reflexive} (eq : Equality-with-J reflexive) where

private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection hiding (id; _∘_)
open Derived-definitions-and-properties eq
import Equality.Decision-procedures as ED; open ED eq
import H-level; open H-level eq
import H-level.Closure; open H-level.Closure eq
open import Prelude
private
  module Weak where
    import Weak-equivalence; open Weak-equivalence eq public
open Weak hiding (_∘_; id)

------------------------------------------------------------------------
-- The univalence axiom

-- If two sets are equal, then they are weakly equivalent.

≡⇒≈ : ∀ {A B} → A ≡ B → A ≈ B
≡⇒≈ = elim (λ {A B} _ → A ≈ B) (λ _ → Weak.id)

-- The univalence axiom states that ≡⇒≈ is a weak equivalence.

Univalence-axiom′ : Set → Set → Set
Univalence-axiom′ A B = Is-weak-equivalence (≡⇒≈ {A} {B})

Univalence-axiom : Set₁
Univalence-axiom = ∀ {A B} → Univalence-axiom′ A B

-- An immediate consequence is that equalities are weakly equivalent
-- to weak equivalences.

≡≈≈ : ∀ {A B} → Univalence-axiom′ A B → (A ≡ B) ≈ (A ≈ B)
≡≈≈ univ = weq ≡⇒≈ univ

------------------------------------------------------------------------
-- A consequence: Set is not a set

abstract

  -- The univalence axiom implies that Set is not a set. (This was
  -- pointed out to me by Thierry Coquand.)

  ¬-Set-set : Univalence-axiom′ Bool Bool → ¬ Is-set Set
  ¬-Set-set univ is-set = Bool.true≢false $ cong (λ f → f true) id≡not
    where
    not : Bool → Bool
    not b = if b then false else true

    not∘not : ∀ b → not (not b) ≡ b
    not∘not true  = refl _
    not∘not false = refl _

    Bool↔Bool : Bool ↔ Bool
    Bool↔Bool = record
      { surjection = record
        { equivalence      = record { from = not; to = not }
        ; right-inverse-of = not∘not
        }
      ; left-inverse-of = not∘not
      }

    Bool≈Bool : Bool ≈ Bool
    Bool≈Bool = bijection⇒weak-equivalence Bool↔Bool

    id≡not : id ≡ not
    id≡not =
      id                            ≡⟨ cong _≈_.to $ sym $ elim-refl (λ {A B} _ → A ≈ B) _ ⟩
      _≈_.to (≡⇒≈ (refl Bool))      ≡⟨ refl _ ⟩
      _≈_.to (to (refl Bool))       ≡⟨ cong (_≈_.to ∘ to) $ proj₁ $ is-set _ _ _ _ ⟩
      _≈_.to (to (from Bool≈Bool))  ≡⟨ cong _≈_.to $ right-inverse-of Bool≈Bool ⟩
      _≈_.to Bool≈Bool              ≡⟨ refl not ⟩∎
      not                           ∎
      where open _≈_ (≡≈≈ univ)

------------------------------------------------------------------------
-- A consequence: extensionality for functions

abstract

  -- If the univalence axiom holds, then "subst P ∘ from" is unique
  -- (up to extensional equality).

  subst-unique :
    (P : Set → Set) →
    (resp : ∀ {A B} → A ≈ B → P A → P B) →
    (∀ {A} (p : P A) → resp Weak.id p ≡ p) →
    ∀ {A B} (univ : Univalence-axiom′ A B) →
    (A≈B : A ≈ B) (p : P A) →
    resp A≈B p ≡ subst P (_≈_.from (≡≈≈ univ) A≈B) p
  subst-unique P resp resp-id univ A≈B p =
    resp A≈B p              ≡⟨ sym $ cong (λ q → resp q p) (right-inverse-of A≈B) ⟩
    resp (to (from A≈B)) p  ≡⟨ elim (λ {A B} A≡B → ∀ p →
                                       resp (≡⇒≈ A≡B) p ≡ subst P A≡B p)
                                    (λ A p →
                                       resp (≡⇒≈ (refl A)) p  ≡⟨ cong (λ q → resp q p) (elim-refl (λ {A B} _ → A ≈ B) _) ⟩
                                       resp Weak.id p         ≡⟨ resp-id p ⟩
                                       p                      ≡⟨ sym $ subst-refl P p ⟩∎
                                       subst P (refl A) p     ∎) _ _ ⟩∎
    subst P (from A≈B) p    ∎
    where open _≈_ (≡≈≈ univ)

  -- If the univalence axiom holds, then any "resp" function
  -- satisfying resp Weak.id p ≡ p is a weak equivalence family.

  resp-is-weak-equivalence :
    (P : Set → Set) →
    (resp : ∀ {A B} → A ≈ B → P A → P B) →
    (∀ {A} (p : P A) → resp Weak.id p ≡ p) →
    ∀ {A B} (univ : Univalence-axiom′ A B) →
    (A≈B : A ≈ B) → Is-weak-equivalence (resp A≈B)
  resp-is-weak-equivalence P resp resp-id univ A≈B =
    Weak.respects-extensional-equality
      (λ p → sym $ subst-unique P resp resp-id univ A≈B p)
      (subst-is-weak-equivalence P (_≈_.from (≡≈≈ univ) A≈B))

  -- If f is a weak equivalence, then (non-dependent) precomposition
  -- with f is also a weak equivalence (assuming univalence).

  precomposition-is-weak-equivalence :
    ∀ {A B C} → Univalence-axiom′ B A →
    (A≈B : A ≈ B) →
    Is-weak-equivalence (λ (g : B → C) → g ∘ _≈_.to A≈B)
  precomposition-is-weak-equivalence {C = C} univ A≈B =
    resp-is-weak-equivalence P resp refl univ (Weak.inverse A≈B)
    where
    P : Set → Set
    P X = X → C

    resp : ∀ {A B} → A ≈ B → P A → P B
    resp A≈B p = p ∘ _≈_.from A≈B

-- If h is a weak equivalence, then one can cancel (non-dependent)
-- precompositions with h (assuming univalence).

precompositions-cancel :
  ∀ {A B C} → Univalence-axiom′ B A →
  (A≈B : A ≈ B) {f g : B → C} →
  let open _≈_ A≈B in
  f ∘ to ≡ g ∘ to → f ≡ g
precompositions-cancel univ A≈B {f} {g} f∘to≡g∘to =
  f            ≡⟨ sym $ left-inverse-of f ⟩
  from (to f)  ≡⟨ cong from f∘to≡g∘to ⟩
  from (to g)  ≡⟨ left-inverse-of g ⟩∎
  g            ∎
  where open _≈_ (weq _ (precomposition-is-weak-equivalence univ A≈B))

-- Pairs of equal elements.

_²/≡ : Set → Set
A ²/≡ = ∃ λ (x : A) → ∃ λ (y : A) → y ≡ x

-- The set of such pairs is isomorphic to the underlying type.

-²/≡↔- : ∀ {A} → (A ²/≡) ↔ A
-²/≡↔- = record
  { surjection = record
    { equivalence = record
      { to   = proj₁
      ; from = λ x → (x , x , refl x)
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = λ p →
      (proj₁ p , proj₁ p , refl (proj₁ p))  ≡⟨ cong (_,_ (proj₁ p))
                                                    (proj₂ (singleton-contractible (proj₁ p)) (proj₂ p)) ⟩∎
      p                                     ∎
  }

abstract

  -- The univalence axiom implies non-dependent functional
  -- extensionality.

  extensionality :
    ∀ {A B} → Univalence-axiom′ (B ²/≡) B →
    {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
  extensionality {A} {B} univ {f} {g} f≡g =
    f          ≡⟨ refl f ⟩
    f′ ∘ pair  ≡⟨ cong (λ h → h ∘ pair) f′≡g′ ⟩
    g′ ∘ pair  ≡⟨ refl g ⟩∎
    g          ∎
    where
    f′ : B ²/≡ → B
    f′ = proj₁ ∘ proj₂

    g′ : B ²/≡ → B
    g′ = proj₁

    f′≡g′ : f′ ≡ g′
    f′≡g′ = precompositions-cancel
              univ
              (bijection⇒weak-equivalence $ Bijection.inverse -²/≡↔-)
              (refl id)

    pair : A → B ²/≡
    pair x = (g x , f x , f≡g x)

  -- The univalence axiom implies that contractibility is closed under
  -- Π A.

  Π-closure-contractible :
    Univalence-axiom′ (Set ²/≡) Set →
    {A : Set} {B : A → Set} →
    (∀ x → Univalence-axiom′ ⊤ (B x)) →
    (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)
  Π-closure-contractible univ₁ {A} {B} univ₂ contr =
    subst Contractible A→⊤≡[x:A]→Bx →⊤-contractible
    where
    const-⊤≡B : const ⊤ ≡ B
    const-⊤≡B = extensionality univ₁ λ x →
      _≈_.from (≡≈≈ (univ₂ x)) $
        bijection⇒weak-equivalence $
          contractible-isomorphic ⊤-contractible (contr x)

    A→⊤≡[x:A]→Bx : (A → ⊤) ≡ ((x : A) → B x)
    A→⊤≡[x:A]→Bx = cong (λ X → (x : A) → X x) const-⊤≡B

    →⊤-contractible : Contractible (A → ⊤)
    →⊤-contractible = (_ , λ _ → refl _)

  -- Thus we also get extensionality for dependent functions.
  --
  -- (This code doesn't type check, probably due to mixing of
  -- --type-in-type and --universe-polymorphism.)

  -- dependent-extensionality :
  --   Univalence-axiom′ (Set ²/≡) Set →
  --   Univalence-axiom →
  --   ∀ {A B} → Extensionality A B
  -- dependent-extensionality univ₁ univ₂ =
  --   _⇔_.to Π-closure-contractible⇔extensionality
  --     (Π-closure-contractible univ₁ univ₂)

------------------------------------------------------------------------
-- An example: if two magmas are isomorphic, then they are equal

-- This example is (mostly) due to Thierry Coquand.

private

  -- This example makes use of dependent-extensionality.

  postulate
    dependent-extensionality :
      Univalence-axiom′ (Set ²/≡) Set →
      Univalence-axiom →
      ∀ {A B} → Extensionality A B

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
      bijection        : Magma.Carrier M₁ ↔ Magma.Carrier M₂
      to-homomorphic   : Is-magma-morphism M₁ M₂ (_↔_.to   bijection)
      from-homomorphic : Is-magma-morphism M₂ M₁ (_↔_.from bijection)

    open _↔_ bijection public

  -- If two magmas are isomorphic, then they are equal (assuming
  -- univalence).

  isomorphic-equal :
    Univalence-axiom′ (Set ²/≡) Set →
    Univalence-axiom →
    ∀ {M₁ M₂} → Magma-isomorphism M₁ M₂ → M₁ ≡ M₂
  isomorphic-equal univ₁ univ₂ {magma A₁ _∙₁_} {magma A₂ _∙₂_} iso =
    magma A₁ _∙₁_                                  ≡⟨ elim (λ {A₁ A₂} A₁≡A₂ → (f : A₁ → A₁ → A₁) →
                                                              magma A₁ f ≡
                                                              magma A₂ (subst (λ A → A → A → A) A₁≡A₂ f))
                                                           (λ A f → cong (magma A) (sym $ subst-refl (λ A → A → A → A) f))
                                                           A₁≡A₂ _∙₁_ ⟩
    magma A₂ (subst (λ A → A → A → A) A₁≡A₂ _∙₁_)  ≡⟨ cong (magma A₂) lemma ⟩∎
    magma A₂ _∙₂_                                  ∎
    where
    open Magma-isomorphism iso

    A₁≡A₂ : A₁ ≡ A₂
    A₁≡A₂ = _≈_.from (≡≈≈ univ₂) $
              bijection⇒weak-equivalence bijection

    cast : (A₁ → A₁ → A₁) → (A₂ → A₂ → A₂)
    cast f = λ x y → to (f (from x) (from y))

    cast-lemma : ∀ f → subst (λ A → A → A → A) A₁≡A₂ f ≡ cast f
    cast-lemma f =
      sym $ subst-unique
        (λ A → A → A → A)
        (λ A≈B f x y → _≈_.to A≈B (f (_≈_.from A≈B x) (_≈_.from A≈B y)))
        refl
        univ₂
        (bijection⇒weak-equivalence bijection)
        f

    lemma : subst (λ A → A → A → A) A₁≡A₂ _∙₁_ ≡ _∙₂_
    lemma =
      dependent-extensionality univ₁ univ₂ $ λ x →
      dependent-extensionality univ₁ univ₂ $ λ y →
        subst (λ A → A → A → A) A₁≡A₂ _∙₁_ x y  ≡⟨ cong (λ f → f x y) $ cast-lemma _∙₁_ ⟩
        to (from x ∙₁ from y)                   ≡⟨ cong to $ sym $ from-homomorphic x y ⟩
        to (from (x ∙₂ y))                      ≡⟨ right-inverse-of (x ∙₂ y) ⟩∎
        x ∙₂ y                                  ∎
