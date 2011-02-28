------------------------------------------------------------------------
-- The univalence axiom
------------------------------------------------------------------------

{-# OPTIONS --without-K --type-in-type #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

module Univalence-axiom where

open import Bijection hiding (_∘_; id)
open import Equality
open import Equality.Decision-procedures
import Equality.Groupoid as EG
private module G {A : Set} = EG.Groupoid (EG.groupoid A)
import Equality.Tactic as Tactic; open Tactic.Eq
open import Equivalence using (module _⇔_)
open import H-level
open import H-level.Closure
import Preimage
open import Prelude
open import Weak-equivalence as Weak hiding (_∘_; id)

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
  ¬-Set-set univ is-set = true≢false $ cong (λ f → f true) id≡not
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

  -- The function subst is a weak equivalence family.
  --
  -- Note that this proof would be easier if subst P (refl x) p
  -- reduced to p.

  subst-is-weak-equivalence :
    ∀ (P : Set → Set) {A B} (A≡B : A ≡ B) →
    Is-weak-equivalence (subst P A≡B)
  subst-is-weak-equivalence P = elim
    (λ {A B} A≡B → Is-weak-equivalence (subst P A≡B))
    (λ A p → _ , λ q →
       let srq = Lift (subst-refl P (proj₁ q))
           q₂  = Lift (proj₂ q)
       in
       (p , subst-refl P p)                                     ≡⟨ elim
                                                                     (λ {u v : P A} u≡v →
                                                                        _≡_ {A = ∃ λ (x : P A) → subst P (refl A) x ≡ v}
                                                                            (v , subst-refl P v)
                                                                            (u , trans (subst-refl P u) u≡v))
                                                                     (λ p → cong (_,_ p) (let srp = Lift (subst-refl P p) in
                                                                              Tactic.prove srp (Trans srp Refl) (refl _)))
                                                                     (proj₁ q                     ≡⟨ sym $ subst-refl P (proj₁ q) ⟩
                                                                      subst P (refl A) (proj₁ q)  ≡⟨ proj₂ q ⟩∎
                                                                      p                           ∎) ⟩
       (proj₁ q , (trans      (subst-refl P (proj₁ q))  $
                   trans (sym (subst-refl P (proj₁ q))) $
                         proj₂ q))                              ≡⟨ cong (_,_ (proj₁ q)) $
                                                                     Tactic.prove (Trans srq (Trans (Sym srq) q₂))
                                                                                  (Trans (Trans srq (Sym srq)) q₂)
                                                                                  (refl _) ⟩
       (proj₁ q , trans (trans      (subst-refl P (proj₁ q))
                               (sym (subst-refl P (proj₁ q))))
                        (proj₂ q))                              ≡⟨ cong (λ eq → proj₁ q , trans eq (proj₂ q)) $ G.left-inverse _ ⟩
       (proj₁ q , trans (refl _) (proj₂ q))                     ≡⟨ cong (_,_ (proj₁ q)) $ Tactic.prove (Trans Refl q₂) q₂ (refl _) ⟩∎
       q                                                        ∎)

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
