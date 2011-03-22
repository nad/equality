------------------------------------------------------------------------
-- Weak equivalences
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module Weak-equivalence
  {reflexive} (eq : Equality-with-J reflexive) where

private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection hiding (id; _∘_; inverse)
open Derived-definitions-and-properties eq
private
  module Groupoid where
    import Equality.Groupoid as EG; open EG eq public
  open Groupoid using (Groupoid)
  module G {A : Set} = Groupoid.Groupoid (Groupoid.groupoid A)
import Equality.Tactic as Tactic; open Tactic eq
open import Equivalence hiding (id; _∘_; inverse)
private
  module H-level where
    import H-level; open H-level eq public
open H-level
import H-level.Closure; open H-level.Closure eq
private
  module Injection where
    import Injection; open Injection eq public
open Injection using (_↣_; module _↣_; Injective)
private
  module Preimage where
    import Preimage; open Preimage eq public
open Preimage using (_⁻¹_)
open import Prelude hiding (id) renaming (_∘_ to _⊚_)
private
  module Surjection where
    import Surjection; open Surjection eq public
open Surjection using (_↠_; module _↠_)

------------------------------------------------------------------------
-- Is-weak-equivalence

-- A function f is a weak equivalence if all preimages under f are
-- contractible.

Is-weak-equivalence : {A B : Set} → (A → B) → Set
Is-weak-equivalence f = ∀ y → Contractible (f ⁻¹ y)

abstract

  -- Is-weak-equivalence f is a proposition, assuming extensional
  -- equality.

  propositional :
    (∀ {A B} → Extensionality A B) →
    ∀ {A B} (f : A → B) → Propositional (Is-weak-equivalence f)
  propositional ext f =
    Π-closure ext 1 λ _ → Contractible-propositional ext

-- Is-weak-equivalence respects extensional equality.

respects-extensional-equality :
  ∀ {A B} {f g : A → B} →
  (∀ x → f x ≡ g x) →
  Is-weak-equivalence f → Is-weak-equivalence g
respects-extensional-equality f≡g f-weq = λ b →
  H-level.respects-surjection
    (_↔_.surjection (Preimage.respects-extensional-equality f≡g))
    0
    (f-weq b)

abstract

  -- The function subst is a weak equivalence family.
  --
  -- Note that this proof would be easier if subst P (refl x) p
  -- reduced to p.

  subst-is-weak-equivalence :
    {A : Set} (P : A → Set) {x y : A} (x≡y : x ≡ y) →
    Is-weak-equivalence (subst P x≡y)
  subst-is-weak-equivalence P = elim
    (λ {x y} x≡y → Is-weak-equivalence (subst P x≡y))
    (λ x p → _ , λ q →
       let srq = Lift (subst-refl P (proj₁ q))
           q₂  = Lift (proj₂ q)
       in
       (p , subst-refl P p)                                     ≡⟨ elim
                                                                     (λ {u v : P x} u≡v →
                                                                        _≡_ {A = ∃ λ (w : P x) → subst P (refl x) w ≡ v}
                                                                            (v , subst-refl P v)
                                                                            (u , trans (subst-refl P u) u≡v))
                                                                     (λ p → cong (_,_ p) (let srp = Lift (subst-refl P p) in
                                                                              prove srp (Trans srp Refl) (refl _)))
                                                                     (proj₁ q                     ≡⟨ sym $ subst-refl P (proj₁ q) ⟩
                                                                      subst P (refl x) (proj₁ q)  ≡⟨ proj₂ q ⟩∎
                                                                      p                           ∎) ⟩
       (proj₁ q , (trans      (subst-refl P (proj₁ q))  $
                   trans (sym (subst-refl P (proj₁ q))) $
                         proj₂ q))                              ≡⟨ cong (_,_ (proj₁ q)) $
                                                                     prove (Trans srq (Trans (Sym srq) q₂))
                                                                           (Trans (Trans srq (Sym srq)) q₂)
                                                                           (refl _) ⟩
       (proj₁ q , trans (trans      (subst-refl P (proj₁ q))
                               (sym (subst-refl P (proj₁ q))))
                        (proj₂ q))                              ≡⟨ cong (λ eq → proj₁ q , trans eq (proj₂ q)) $ G.left-inverse _ ⟩
       (proj₁ q , trans (refl _) (proj₂ q))                     ≡⟨ cong (_,_ (proj₁ q)) $ prove (Trans Refl q₂) q₂ (refl _) ⟩∎
       q                                                        ∎)

------------------------------------------------------------------------
-- _≈_

-- Weak equivalences.

infix 4 _≈_

record _≈_ (A B : Set) : Set where
  constructor weq
  field
    to                  : A → B
    is-weak-equivalence : Is-weak-equivalence to

  -- Weakly equivalent sets are isomorphic.

  abstract
    right-inverse-of = proj₂ ⊚ proj₁ ⊚ is-weak-equivalence
    left-inverse-of  = λ x →
      cong proj₁ $
        proj₂ (is-weak-equivalence (to x)) (x , refl (to x))

  bijection : A ↔ B
  bijection = record
    { surjection = record
      { equivalence = record
        { to   = to
        ; from = proj₁ ⊚ proj₁ ⊚ is-weak-equivalence
        }
      ; right-inverse-of = right-inverse-of
      }
    ; left-inverse-of = left-inverse-of
    }

  open _↔_ bijection public
    hiding (to; right-inverse-of; left-inverse-of)

  abstract

    -- All preimages of an element under the weak equivalence are
    -- equal.

    irrelevance : ∀ y (p : to ⁻¹ y) → (from y , right-inverse-of y) ≡ p
    irrelevance = proj₂ ⊚ is-weak-equivalence

    -- The two proofs left-inverse-of and right-inverse-of are
    -- related.

    left-right-lemma :
      ∀ x → cong to (left-inverse-of x) ≡ right-inverse-of (to x)
    left-right-lemma x =
      lemma₁ to _ _ (lemma₂ (irrelevance (to x) (x , refl (to x))))
      where
      lemma₁ : ∀ {A} {x y : A}
               (f : A → B) (p : x ≡ y) (q : f x ≡ f y) →
               refl (f y) ≡ trans (cong f (sym p)) q →
               cong f p ≡ q
      lemma₁ f = elim
        (λ {x y} p → ∀ q → refl (f y) ≡ trans (cong f (sym p)) q →
                           cong f p ≡ q)
        (λ x q hyp →
           cong f (refl x)                  ≡⟨ prove (Cong f Refl) Refl (refl _) ⟩
           refl (f x)                       ≡⟨ hyp ⟩
           trans (cong f (sym (refl x))) q  ≡⟨ prove (Trans (Cong f (Sym Refl)) (Lift q)) (Lift q) (refl _) ⟩∎
           q                                ∎)

      lemma₂ : ∀ {A B} {f : A → B} {y} {f⁻¹y₁ f⁻¹y₂ : f ⁻¹ y}
               (p : f⁻¹y₁ ≡ f⁻¹y₂) →
               proj₂ f⁻¹y₂ ≡
               trans (cong f (sym (cong proj₁ p))) (proj₂ f⁻¹y₁)
      lemma₂ {f = f} = elim
        (λ {f⁻¹y₁ f⁻¹y₂} p →
           proj₂ f⁻¹y₂ ≡
           trans (cong f (sym (cong proj₁ p))) (proj₂ f⁻¹y₁))
        (λ f⁻¹y →
           prove
             (Lift (proj₂ f⁻¹y))
             (Trans (Cong f (Sym (Cong proj₁ Refl)))
                    (Lift (proj₂ f⁻¹y)))
             (refl _))

-- Bijections are weak equivalences.

bijection⇒weak-equivalence : ∀ {A B} → A ↔ B → A ≈ B
bijection⇒weak-equivalence A↔B = record
  { to                  = _↔_.to A↔B
  ; is-weak-equivalence = Preimage.bijection⁻¹-contractible A↔B
  }

------------------------------------------------------------------------
-- Equivalence

-- Weak equivalences are equivalence relations.

id : ∀ {A} → A ≈ A
id = bijection⇒weak-equivalence Bijection.id

inverse : ∀ {A B} → A ≈ B → B ≈ A
inverse =
  bijection⇒weak-equivalence ⊚
  Bijection.inverse ⊚
  _≈_.bijection

infixr 9 _∘_

_∘_ : ∀ {A B C} → B ≈ C → A ≈ B → A ≈ C
f ∘ g =
  bijection⇒weak-equivalence $
    Bijection._∘_ (_≈_.bijection f) (_≈_.bijection g)

-- Equational reasoning combinators.

infixr 0 _≈⟨_⟩_
infix  0 finally-≈

_≈⟨_⟩_ : ∀ A {B C} → A ≈ B → B ≈ C → A ≈ C
_ ≈⟨ A≈B ⟩ B≈C = B≈C ∘ A≈B

finally-≈ : ∀ A B → A ≈ B → A ≈ B
finally-≈ _ _ A≈B = A≈B

syntax finally-≈ A B A≈B = A ≈⟨ A≈B ⟩□ B □

------------------------------------------------------------------------
-- Groupoid

abstract

  -- Two proofs of weak equivalence are equal if the function
  -- components are equal (assuming extensionality).

  lift-equality : (∀ {A B} → Extensionality A B) →
                  ∀ {A B} {p q : A ≈ B} →
                  (∀ x → _≈_.to p x ≡ _≈_.to q x) → p ≡ q
  lift-equality ext {p = weq f f-weq} {q = weq g g-weq} f≡g =
    elim (λ {f g} f≡g → ∀ f-weq g-weq → weq f f-weq ≡ weq g g-weq)
         (λ f f-weq g-weq →
            cong (weq f)
              (_⇔_.to propositional⇔irrelevant
                 (propositional ext f) f-weq g-weq))
         (ext f≡g) f-weq g-weq

{- The definition below is commented out because it takes too long to
   type check (on my current machine). It checked a lot faster when
   some key definitions in Equality were abstract, but I want these
   definitions to unfold automatically.

-- _≈_ comes with a groupoid structure (assuming extensionality).
--
-- Note that, at the time of writing (and on a particular system), the
-- following proof takes about three times as long to type-check as
-- the rest of the development.

groupoid : (∀ {A B} → Extensionality A B) →
           Groupoid (suc zero)
groupoid ext = record
  { Object         = Set
  ; _∼_            = _≈_
  ; id             = id
  ; _∘_            = _∘_
  ; _⁻¹            = inverse
  ; left-identity  = left-identity
  ; right-identity = right-identity
  ; assoc          = assoc
  ; left-inverse   = left-inverse
  ; right-inverse  = right-inverse
  }
  where
  abstract
    left-identity : ∀ {X Y} (p : X ≈ Y) → id ∘ p ≡ p
    left-identity _ = lift-equality ext (λ _ → refl _)

    right-identity : ∀ {X Y} (p : X ≈ Y) → p ∘ id ≡ p
    right-identity _ = lift-equality ext (λ _ → refl _)

    assoc : ∀ {W X Y Z} (p : Y ≈ Z) (q : X ≈ Y) (r : W ≈ X) →
            p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
    assoc _ _ _ = lift-equality ext (λ _ → refl _)

    left-inverse : ∀ {X Y} (p : X ≈ Y) → inverse p ∘ p ≡ id
    left-inverse p = lift-equality ext (_≈_.left-inverse-of p)

    right-inverse : ∀ {X Y} (p : X ≈ Y) → p ∘ inverse p ≡ id
    right-inverse p = lift-equality ext (_≈_.right-inverse-of p)

-}

------------------------------------------------------------------------
-- Closure, preservation

abstract

  -- Positive h-levels are closed under the weak equivalence operator
  -- (assuming extensionality).

  right-closure :
    (∀ {A B} → Extensionality A B) →
    ∀ {A B} n → H-level (1 + n) B → H-level (1 + n) (A ≈ B)
  right-closure ext {A} {B} n h =
    H-level.respects-surjection surj (1 + n) lemma
    where
    lemma : H-level (1 + n) (∃ λ (to : A → B) → Is-weak-equivalence to)
    lemma = Σ-closure (1 + n)
              (Π-closure ext (1 + n) (const h))
              (mono (m≤m+n 1 n) ⊚ propositional ext)

    surj : (∃ λ (to : A → B) → Is-weak-equivalence to) ↠ (A ≈ B)
    surj = record
      { equivalence = record
          { to   = λ A≈B → weq (proj₁ A≈B) (proj₂ A≈B)
          ; from = λ A≈B → (_≈_.to A≈B , _≈_.is-weak-equivalence A≈B)
          }
      ; right-inverse-of = λ _ → refl _
      }

  left-closure :
    (∀ {A B} → Extensionality A B) →
    ∀ {A B} n → H-level (1 + n) A → H-level (1 + n) (A ≈ B)
  left-closure ext {A} {B} n h =
    H-level.[inhabited⇒+]⇒+ n λ (A≈B : A ≈ B) →
      right-closure ext n $
        H-level.respects-surjection (_≈_.surjection A≈B) (1 + n) h

-- Equalities are closed, in a strong sense, under applications of
-- weak equivalences.

≈-≡ : ∀ {A B} (A≈B : A ≈ B) {x y : A} →
      let open _≈_ A≈B in
      (to x ≡ to y) ≈ (x ≡ y)
≈-≡ A≈B {x} {y} =
  bijection⇒weak-equivalence record
    { surjection      = Surjection.↠-≡ $
                        _↔_.surjection $
                        Bijection.inverse $
                        _≈_.bijection A≈B
    ; left-inverse-of = left-inverse-of′
    }
  where
  open _≈_ A≈B

  abstract
    left-inverse-of′ = λ to-x≡to-y →
      cong to (
        trans (sym (left-inverse-of x)) $
        trans (cong from to-x≡to-y) $
        left-inverse-of y)                         ≡⟨ prove (Cong to (Trans (Sym (Lift (left-inverse-of x)))
                                                                      (Trans (Cong from (Lift to-x≡to-y))
                                                                      (Lift (left-inverse-of y)))))
                                                            (Trans (Sym (Cong to (Lift (left-inverse-of x))))
                                                             (Trans (Cong to (Cong from (Lift to-x≡to-y)))
                                                             (Cong to (Lift (left-inverse-of y)))))
                                                            (refl _) ⟩
      trans (sym (cong to (left-inverse-of x))) (
        trans (cong to (cong from to-x≡to-y)) (
        cong to (left-inverse-of y)))              ≡⟨ cong₂ (λ eq₁ eq₂ → trans (sym eq₁) $
                                                                         trans (cong to (cong from to-x≡to-y)) $
                                                                         eq₂)
                                                           (left-right-lemma x)
                                                           (left-right-lemma y) ⟩
      trans (sym (right-inverse-of (to x))) (
        trans (cong to (cong from to-x≡to-y)) (
        right-inverse-of (to y)))                  ≡⟨ _↠_.right-inverse-of (Surjection.↠-≡ $ _≈_.surjection A≈B) to-x≡to-y ⟩∎
      to-x≡to-y                                    ∎

abstract
  private

    -- We can push subst through certain function applications.

    push-subst :
      ∀ {A₁ A₂} (B₁ : A₁ → Set) {B₂ : A₂ → Set}
        {f : A₂ → A₁} {x₁ x₂ : A₂} {y : B₁ (f x₁)}
      (g : ∀ x → B₁ (f x) → B₂ x) (eq : x₁ ≡ x₂) →
      subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong f eq) y)
    push-subst B₁ {B₂} {f} g eq = elim
      (λ {x₁ x₂} eq → ∀ y → subst B₂ eq (g x₁ y) ≡
                            g x₂ (subst B₁ (cong f eq) y))
      (λ x y → subst B₂ (refl x) (g x y)           ≡⟨ subst-refl B₂ _ ⟩
               g x y                               ≡⟨ sym $ cong (g x) $ subst-refl B₁ _ ⟩
               g x (subst B₁ (refl (f x)) y)       ≡⟨ cong (λ eq → g x (subst B₁ eq y)) (sym $ cong-refl f) ⟩∎
               g x (subst B₁ (cong f (refl x)) y)  ∎)
      eq _

    push-subst′ :
      ∀ {A₁ A₂} (A₁≈A₂ : A₁ ≈ A₂) (B₁ : A₁ → Set) (B₂ : A₂ → Set) →
      let open _≈_ A₁≈A₂ in {x₁ x₂ : A₁} {y : B₁ (from (to x₁))}
      (g : ∀ x → B₁ (from (to x)) → B₂ (to x)) (eq : to x₁ ≡ to x₂) →
      subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong from eq) y)
    push-subst′ A₁≈A₂ B₁ B₂ {x₁} {x₂} {y} g eq =
      subst B₂ eq (g x₁ y)                    ≡⟨ cong (subst B₂ eq) $ sym $ g′-lemma _ _ ⟩
      subst B₂ eq (g′ (to x₁) y)              ≡⟨ push-subst B₁ g′ eq ⟩
      g′ (to x₂) (subst B₁ (cong from eq) y)  ≡⟨ g′-lemma _ _ ⟩∎
      g x₂ (subst B₁ (cong from eq) y)        ∎
      where
      open _≈_ A₁≈A₂

      g′ : ∀ x′ → B₁ (from x′) → B₂ x′
      g′ x′ y = subst B₂ (right-inverse-of x′) $
                g (from x′) $
                subst B₁ (sym $ cong from $ right-inverse-of x′) y

      g′-lemma : ∀ x y → g′ (to x) y ≡ g x y
      g′-lemma x y =
        subst B₂ (right-inverse-of (to x))
          (g (from (to x)) $
           subst B₁ (sym $ cong from $
                       right-inverse-of (to x)) y)  ≡⟨ cong (λ p → subst B₂ p (g (from (to x)) $ subst B₁ (sym $ cong from p) y)) $
                                                         sym $ left-right-lemma x ⟩
        subst B₂ (cong to $ left-inverse-of x)
          (g (from (to x)) $
           subst B₁ (sym $ cong from $ cong to $
                       left-inverse-of x) y)        ≡⟨ elim¹
                                                         (λ {x′} eq →
                                                            (y : B₁ (from (to x′))) →
                                                            subst B₂ (cong to eq)
                                                              (g (from (to x)) $ subst B₁ (sym $ cong from $ cong to eq) y) ≡
                                                            g x′ y)
                                                         lemma
                                                         (left-inverse-of x) y ⟩∎
        g x y                                       ∎
        where
        lemma = λ y →
          let gy = g (from (to x)) $
                     subst B₁ (sym $ cong from $ cong to (refl _)) y in
          subst B₂ (cong to (refl _)) gy         ≡⟨ cong (λ p → subst B₂ p gy) $
                                                      prove (Cong to Refl) Refl (refl _) ⟩
          subst B₂ (refl _) gy                   ≡⟨ subst-refl B₂ gy ⟩
          gy                                     ≡⟨ cong (λ p → g (from (to x)) $ subst B₁ p y) $
                                                      prove (Sym (Cong from (Cong to Refl))) Refl (refl _) ⟩
          g (from (to x)) (subst B₁ (refl _) y)  ≡⟨ cong (g (from (to x))) $ subst-refl B₁ y ⟩∎
          g (from (to x)) y                      ∎

-- If the first component is instantiated to id, then the following
-- lemmas state that ∃ preserves functions, equivalences, injections,
-- surjections and bijections.

∃-preserves-functions :
  ∀ {A₁ A₂ B₁ B₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x → B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ → Σ A₂ B₂
∃-preserves-functions A₁≈A₂ B₁→B₂ = Σ-map (_≈_.to A₁≈A₂) (B₁→B₂ _)

∃-preserves-equivalences :
  ∀ {A₁ A₂ B₁ B₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ⇔ B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ ⇔ Σ A₂ B₂
∃-preserves-equivalences {B₂ = B₂} A₁≈A₂ B₁⇔B₂ = record
  { to   = ∃-preserves-functions A₁≈A₂ (_⇔_.to ⊚ B₁⇔B₂)
  ; from =
     ∃-preserves-functions
       (inverse A₁≈A₂)
       (λ x y → _⇔_.from
                  (B₁⇔B₂ (_≈_.from A₁≈A₂ x))
                  (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂ x)) y))
  }

∃-preserves-injections :
  ∀ {A₁ A₂ B₁ B₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ↣ B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ ↣ Σ A₂ B₂
∃-preserves-injections {B₁ = B₁} {B₂ = B₂} A₁≈A₂ B₁↣B₂ = record
  { to        = to′
  ; injective = injective′
  }
  where
  open _↣_

  to′ = ∃-preserves-functions A₁≈A₂ (_↣_.to ⊚ B₁↣B₂)

  abstract
    injective′ : Injective to′
    injective′ {x = (x₁ , x₂)} {y = (y₁ , y₂)} =
      _↔_.to Σ-≡,≡↔≡ ⊚
      Σ-map (_≈_.injective A₁≈A₂) (λ {eq₁} eq₂ →
        let lemma =
              to (B₁↣B₂ y₁) (subst B₁ (_≈_.injective A₁≈A₂ eq₁) x₂)      ≡⟨ refl _ ⟩
              to (B₁↣B₂ y₁)
                (subst B₁ (trans (sym (_≈_.left-inverse-of A₁≈A₂ x₁)) $
                           trans (cong (_≈_.from A₁≈A₂) eq₁)
                                 (_≈_.left-inverse-of A₁≈A₂ y₁))
                          x₂)                                            ≡⟨ cong (to (B₁↣B₂ y₁)) $ sym $
                                                                              Groupoid.subst-subst B₁ _ _ _ ⟩
              to (B₁↣B₂ y₁)
                 (subst B₁ (trans (cong (_≈_.from A₁≈A₂) eq₁)
                                  (_≈_.left-inverse-of A₁≈A₂ y₁)) $
                  subst B₁ (sym (_≈_.left-inverse-of A₁≈A₂ x₁))
                           x₂)                                           ≡⟨ cong (to (B₁↣B₂ y₁)) $ sym $
                                                                              Groupoid.subst-subst B₁ _ _ _ ⟩
              to (B₁↣B₂ y₁)
                 (subst B₁ (_≈_.left-inverse-of A₁≈A₂ y₁) $
                  subst B₁ (cong (_≈_.from A₁≈A₂) eq₁) $
                  subst B₁ (sym (_≈_.left-inverse-of A₁≈A₂ x₁)) x₂)      ≡⟨ sym $ push-subst′ A₁≈A₂ B₁ B₂
                                                                              (λ x y → to (B₁↣B₂ x)
                                                                                          (subst B₁ (_≈_.left-inverse-of A₁≈A₂ x) y))
                                                                              eq₁ ⟩
              subst B₂ eq₁
                (to (B₁↣B₂ x₁) $
                 subst B₁ (_≈_.left-inverse-of A₁≈A₂ x₁) $
                 subst B₁ (sym (_≈_.left-inverse-of A₁≈A₂ x₁)) x₂)       ≡⟨ cong (subst B₂ eq₁ ⊚ to (B₁↣B₂ x₁)) $
                                                                              Groupoid.subst-subst B₁ _ _ _ ⟩
              subst B₂ eq₁
                (to (B₁↣B₂ x₁) $
                 subst B₁ (trans (sym (_≈_.left-inverse-of A₁≈A₂ x₁))
                                 (_≈_.left-inverse-of A₁≈A₂ x₁))
                          x₂)                                            ≡⟨ cong (λ p → subst B₂ eq₁ (to (B₁↣B₂ x₁) (subst B₁ p x₂))) $
                                                                                 G.right-inverse _ ⟩
              subst B₂ eq₁ (to (B₁↣B₂ x₁) $ subst B₁ (refl _) x₂)        ≡⟨ cong (subst B₂ eq₁ ⊚ to (B₁↣B₂ x₁)) $
                                                                                 subst-refl B₁ x₂ ⟩
              subst B₂ eq₁ (to (B₁↣B₂ x₁) x₂)                            ≡⟨ eq₂ ⟩∎
              to (B₁↣B₂ y₁) y₂                                           ∎
        in
        subst B₁ (_≈_.injective A₁≈A₂ eq₁) x₂  ≡⟨ _↣_.injective (B₁↣B₂ y₁) lemma ⟩∎
        y₂                                     ∎) ⊚
      _↔_.from Σ-≡,≡↔≡

∃-preserves-surjections :
  ∀ {A₁ A₂ B₁ B₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ↠ B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ ↠ Σ A₂ B₂
∃-preserves-surjections {B₂ = B₂} A₁≈A₂ B₁↠B₂ = record
  { equivalence      = ∃-preserves-equivalences
                         A₁≈A₂ (equivalence ⊚ B₁↠B₂)
  ; right-inverse-of = right-inverse-of′
  }
  where
  open _↠_

  abstract
    right-inverse-of′ = λ p → _↔_.to Σ-≡,≡↔≡
      ( _≈_.right-inverse-of A₁≈A₂ (proj₁ p)
      , (subst B₂ (_≈_.right-inverse-of A₁≈A₂ (proj₁ p))
           (to (B₁↠B₂ _) (from (B₁↠B₂ _)
              (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂ (proj₁ p)))
                 (proj₂ p))))                                         ≡⟨ cong (subst B₂ _) $ right-inverse-of (B₁↠B₂ _) _ ⟩
         subst B₂ (_≈_.right-inverse-of A₁≈A₂ (proj₁ p))
           (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂ (proj₁ p)))
              (proj₂ p))                                              ≡⟨ Groupoid.subst-subst-sym B₂ _ _ ⟩∎
         proj₂ p ∎)
      )

∃-preserves-bijections :
  ∀ {A₁ A₂ B₁ B₂}
  (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ↔ B₂ (_≈_.to A₁≈A₂ x)) →
  Σ A₁ B₁ ↔ Σ A₂ B₂
∃-preserves-bijections {B₁ = B₁} {B₂} A₁≈A₂ B₁↔B₂ = record
  { surjection      = ∃-preserves-surjections A₁≈A₂ (surjection ⊚ B₁↔B₂)
  ; left-inverse-of = left-inverse-of′
  }
  where
  open _↔_

  abstract
    left-inverse-of′ = λ p → _↔_.to Σ-≡,≡↔≡
      ( _≈_.left-inverse-of A₁≈A₂ (proj₁ p)
      , (subst B₁ (_≈_.left-inverse-of A₁≈A₂ (proj₁ p))
           (from (B₁↔B₂ _)
              (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂
                                (_≈_.to A₁≈A₂ (proj₁ p))))
                 (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ push-subst B₂ (λ x → from (B₁↔B₂ x))
                                                                        (_≈_.left-inverse-of A₁≈A₂ (proj₁ p)) ⟩
         from (B₁↔B₂ _)
           (subst B₂ (cong (_≈_.to A₁≈A₂)
                           (_≈_.left-inverse-of A₁≈A₂ (proj₁ p)))
              (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂
                                (_≈_.to A₁≈A₂ (proj₁ p))))
                 (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ cong (λ eq → from (B₁↔B₂ _)
                                                                                     (subst B₂ eq
                                                                                        (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂ _))
                                                                                           (to (B₁↔B₂ _) (proj₂ p))))) $
                                                                           _≈_.left-right-lemma A₁≈A₂ _ ⟩
         from (B₁↔B₂ _)
           (subst B₂ (_≈_.right-inverse-of A₁≈A₂
                        (_≈_.to A₁≈A₂ (proj₁ p)))
              (subst B₂ (sym (_≈_.right-inverse-of A₁≈A₂
                                (_≈_.to A₁≈A₂ (proj₁ p))))
                 (to (B₁↔B₂ _) (proj₂ p))))                        ≡⟨ cong (from (B₁↔B₂ _)) $ Groupoid.subst-subst-sym B₂ _ _ ⟩
         from (B₁↔B₂ _) (to (B₁↔B₂ _) (proj₂ p))                   ≡⟨ left-inverse-of (B₁↔B₂ _) _ ⟩∎
         proj₂ p                                                   ∎)
      )

-- Σ preserves weak equivalence.

Σ-preserves : ∀ {A₁ A₂ B₁ B₂}
              (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ≈ B₂ (_≈_.to A₁≈A₂ x)) →
              Σ A₁ B₁ ≈ Σ A₂ B₂
Σ-preserves A₁≈A₂ B₁≈B₂ = bijection⇒weak-equivalence $
  ∃-preserves-bijections A₁≈A₂ (_≈_.bijection ⊚ B₁≈B₂)

-- Π preserves weak equivalence (assuming extensionality).

Π-preserves : (∀ {A B} → Extensionality A B) →
              ∀ {A₁ A₂} {B₁ : A₁ → Set} {B₂ : A₂ → Set} →
              (A₁≈A₂ : A₁ ≈ A₂) → (∀ x → B₁ x ≈ B₂ (_≈_.to A₁≈A₂ x)) →
              ((x : A₁) → B₁ x) ≈ ((x : A₂) → B₂ x)
Π-preserves ext {B₁ = B₁} {B₂} A₁≈A₂ B₁≈B₂ =
  bijection⇒weak-equivalence record
    { surjection = record
      { equivalence = record
        { to   = λ f x → subst B₂ (right-inverse-of A₁≈A₂ x)
                               (to (B₁≈B₂ (from A₁≈A₂ x))
                                   (f (from A₁≈A₂ x)))
        ; from = λ f x → from (B₁≈B₂ x) (f (to A₁≈A₂ x))
        }
      ; right-inverse-of = right-inverse-of′
      }
    ; left-inverse-of = left-inverse-of′
    }
  where
  open _≈_

  abstract
    right-inverse-of′ = λ f → ext λ x →
      subst B₂ (right-inverse-of A₁≈A₂ x)
            (to (B₁≈B₂ (from A₁≈A₂ x))
                (from (B₁≈B₂ (from A₁≈A₂ x))
                      (f (to A₁≈A₂ (from A₁≈A₂ x)))))  ≡⟨ cong (subst B₂ (right-inverse-of A₁≈A₂ x)) $
                                                               right-inverse-of (B₁≈B₂ _) _ ⟩
      subst B₂ (right-inverse-of A₁≈A₂ x)
            (f (to A₁≈A₂ (from A₁≈A₂ x)))              ≡⟨ elim (λ {x y} x≡y → subst B₂ x≡y (f x) ≡ f y)
                                                               (λ x → subst-refl B₂ (f x))
                                                               (right-inverse-of A₁≈A₂ x) ⟩∎
      f x                                              ∎

    left-inverse-of′ = λ f → ext λ x →
      from (B₁≈B₂ x)
           (subst B₂ (right-inverse-of A₁≈A₂ (to A₁≈A₂ x))
                  (to (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                      (f (from A₁≈A₂ (to A₁≈A₂ x)))))             ≡⟨ cong (λ eq → from (B₁≈B₂ x)
                                                                                    (subst B₂ eq
                                                                                       (to (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                                                                                          (f (from A₁≈A₂ (to A₁≈A₂ x))))))
                                                                          (sym $ left-right-lemma A₁≈A₂ x) ⟩
      from (B₁≈B₂ x)
           (subst B₂ (cong (to A₁≈A₂) (left-inverse-of A₁≈A₂ x))
                  (to (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                      (f (from A₁≈A₂ (to A₁≈A₂ x)))))             ≡⟨ sym $ push-subst B₂ (λ x y → from (B₁≈B₂ x) y)
                                                                                      (left-inverse-of A₁≈A₂ x) ⟩
      subst B₁ (left-inverse-of A₁≈A₂ x)
            (from (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                  (to (B₁≈B₂ (from A₁≈A₂ (to A₁≈A₂ x)))
                      (f (from A₁≈A₂ (to A₁≈A₂ x)))))             ≡⟨ cong (subst B₁ (left-inverse-of A₁≈A₂ x)) $
                                                                       left-inverse-of (B₁≈B₂ _) _ ⟩
      subst B₁ (left-inverse-of A₁≈A₂ x)
            (f (from A₁≈A₂ (to A₁≈A₂ x)))                         ≡⟨ elim (λ {x y} x≡y → subst B₁ x≡y (f x) ≡ f y)
                                                                          (λ x → subst-refl B₁ (f x))
                                                                          (left-inverse-of A₁≈A₂ x) ⟩∎
      f x                                                         ∎
