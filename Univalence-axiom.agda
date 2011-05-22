------------------------------------------------------------------------
-- The univalence axiom
------------------------------------------------------------------------

{-# OPTIONS --without-K --universe-polymorphism #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module Univalence-axiom
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection hiding (id; _∘_)
open Derived-definitions-and-properties eq
import Equality.Decision-procedures as ED; open ED eq
open import Equivalence hiding (id; _∘_)
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

≡⇒≈ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≈ B
≡⇒≈ = elim (λ {A B} _ → A ≈ B) (λ _ → Weak.id)

-- The univalence axiom states that ≡⇒≈ is a weak equivalence.

Univalence-axiom′ : ∀ {ℓ} → Set ℓ → Set ℓ → Set (suc ℓ)
Univalence-axiom′ A B = Is-weak-equivalence (≡⇒≈ {A = A} {B = B})

Univalence-axiom : ∀ ℓ → Set (suc ℓ)
Univalence-axiom ℓ = {A B : Set ℓ} → Univalence-axiom′ A B

-- An immediate consequence is that equalities are weakly equivalent
-- to weak equivalences.

≡≈≈ : ∀ {ℓ} {A B : Set ℓ} → Univalence-axiom′ A B → (A ≡ B) ≈ (A ≈ B)
≡≈≈ univ = weq ≡⇒≈ univ

------------------------------------------------------------------------
-- A consequence: Set is not a set

-- The univalence axiom implies that Set is not a set. (This was
-- pointed out to me by Thierry Coquand.)

abstract

  -- First a lemma: Some equality types have more than one inhabitant
  -- (assuming univalence).

  equality-can-have-more-than-one-inhabitant :
    Univalence-axiom′ Bool Bool →
    ∃ λ (A : Set) → ∃ λ (B : Set) →
    ∃ λ (p₁ : A ≡ B) → ∃ λ (p₂ : A ≡ B) → p₁ ≢ p₂
  equality-can-have-more-than-one-inhabitant univ =
    (Bool , Bool , cast p₁ , cast p₂ , cast-p₁≢cast-p₂)
    where
    cast : Bool ≈ Bool → Bool ≡ Bool
    cast = _≈_.from (≡≈≈ univ)

    p₁ : Bool ≈ Bool
    p₁ = Weak.id

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

    p₂ : Bool ≈ Bool
    p₂ = bijection⇒weak-equivalence Bool↔Bool

    p₁≢p₂ : p₁ ≢ p₂
    p₁≢p₂ p₁≡p₂ =
      Bool.true≢false $
      cong (λ f → f true) $
      cong _≈_.to p₁≡p₂

    cast-p₁≢cast-p₂ : cast p₁ ≢ cast p₂
    cast-p₁≢cast-p₂ cast-p₁≡cast-p₂ = p₁≢p₂ $
      p₁             ≡⟨ sym $ _≈_.right-inverse-of (≡≈≈ univ) p₁ ⟩
      ≡⇒≈ (cast p₁)  ≡⟨ cong ≡⇒≈ cast-p₁≡cast-p₂ ⟩
      ≡⇒≈ (cast p₂)  ≡⟨ _≈_.right-inverse-of (≡≈≈ univ) p₂ ⟩∎
      p₂             ∎

  -- Set is not a set.

  ¬-Set-set : Univalence-axiom′ Bool Bool → ¬ Is-set Set
  ¬-Set-set univ is-set
    with equality-can-have-more-than-one-inhabitant univ
  ... | (A , B , p₁ , p₂ , p₁≢p₂) = p₁≢p₂ $ proj₁ $ is-set A B p₁ p₂

------------------------------------------------------------------------
-- A consequence: extensionality for functions

abstract

  -- If the univalence axiom holds, then "subst P ∘ from" is unique
  -- (up to extensional equality).

  subst-unique :
    ∀ {p} (P : Set p → Set p) →
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
    ∀ {p} (P : Set p → Set p) →
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
    ∀ {ℓ} {A B C : Set ℓ} → Univalence-axiom′ B A →
    (A≈B : A ≈ B) →
    Is-weak-equivalence (λ (g : B → C) → g ∘ _≈_.to A≈B)
  precomposition-is-weak-equivalence {ℓ} {C = C} univ A≈B =
    resp-is-weak-equivalence P resp refl univ (Weak.inverse A≈B)
    where
    P : Set ℓ → Set ℓ
    P X = X → C

    resp : ∀ {A B} → A ≈ B → P A → P B
    resp A≈B p = p ∘ _≈_.from A≈B

-- If h is a weak equivalence, then one can cancel (non-dependent)
-- precompositions with h (assuming univalence).

precompositions-cancel :
  ∀ {ℓ} {A B C : Set ℓ} → Univalence-axiom′ B A →
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

_²/≡ : ∀ {ℓ} → Set ℓ → Set ℓ
A ²/≡ = ∃ λ (x : A) → ∃ λ (y : A) → y ≡ x

-- The set of such pairs is isomorphic to the underlying type.

-²/≡↔- : ∀ {a} {A : Set a} → (A ²/≡) ↔ A
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
    ∀ {a b} {A : Set a} {B : Set b} →
    Univalence-axiom′ (B ²/≡) B →
    {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
  extensionality {A = A} {B} univ {f} {g} f≡g =
    f          ≡⟨ refl f ⟩
    f′ ∘ pair  ≡⟨ cong (λ (h : B ²/≡ → B) → h ∘ pair) f′≡g′ ⟩
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
    ∀ {b} → Univalence-axiom′ (Set b ²/≡) (Set b) →
    ∀ {a} {A : Set a} {B : A → Set b} →
    (∀ x → Univalence-axiom′ ⊤ (B x)) →
    (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)
  Π-closure-contractible {b} univ₁ {A = A} {B} univ₂ contr =
    subst Contractible A→⊤≡[x:A]→Bx →⊤-contractible
    where
    const-⊤≡B : const ⊤ ≡ B
    const-⊤≡B = extensionality univ₁ λ x →
      _≈_.from (≡≈≈ (univ₂ x)) $
        bijection⇒weak-equivalence $
          contractible-isomorphic ⊤-contractible (contr x)

    A→⊤≡[x:A]→Bx : (A → ⊤ {ℓ = b}) ≡ ((x : A) → B x)
    A→⊤≡[x:A]→Bx = cong (λ X → (x : A) → X x) const-⊤≡B

    →⊤-contractible : Contractible (A → ⊤)
    →⊤-contractible = (_ , λ _ → refl _)

  -- Thus we also get extensionality for dependent functions.

  dependent-extensionality :
    ∀ {b} → Univalence-axiom′ (Set b ²/≡) (Set b) →
    ∀ {a} {A : Set a} →
    (∀ {B : A → Set b} x → Univalence-axiom′ ⊤ (B x)) →
    {B : A → Set b} → Extensionality A B
  dependent-extensionality univ₁ univ₂ =
    _⇔_.to Π-closure-contractible⇔extensionality
      (Π-closure-contractible univ₁ univ₂)

------------------------------------------------------------------------
-- An example: if two magmas are isomorphic, then they are equal

-- This example is (mostly) due to Thierry Coquand.

private

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
    Univalence-axiom zero →
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
      dependent-extensionality univ₁ (λ _ → univ₂) $ λ x →
      dependent-extensionality univ₁ (λ _ → univ₂) $ λ y →
        subst (λ A → A → A → A) A₁≡A₂ _∙₁_ x y  ≡⟨ cong (λ f → f x y) $ cast-lemma _∙₁_ ⟩
        to (from x ∙₁ from y)                   ≡⟨ cong to $ sym $ from-homomorphic x y ⟩
        to (from (x ∙₂ y))                      ≡⟨ right-inverse-of (x ∙₂ y) ⟩∎
        x ∙₂ y                                  ∎
