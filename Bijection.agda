------------------------------------------------------------------------
-- Bijections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Bijection
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Equivalence using (_⇔_)
open import H-level eq
open import Injection eq using (Injective; _↣_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)
open import Surjection eq as Surjection using (_↠_; module _↠_)

------------------------------------------------------------------------
-- Bijections

infix 0 _↔_

record _↔_ {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    surjection : From ↠ To

  open _↠_ surjection

  field
    left-inverse-of : ∀ x → from (to x) ≡ x

  injective : Injective to
  injective {x = x} {y = y} to-x≡to-y =
    x            ≡⟨ sym (left-inverse-of x) ⟩
    from (to x)  ≡⟨ cong from to-x≡to-y ⟩
    from (to y)  ≡⟨ left-inverse-of y ⟩∎
    y            ∎

  injection : From ↣ To
  injection = record
    { to        = to
    ; injective = injective
    }

  -- A lemma.

  to-from : ∀ {x y} → to x ≡ y → from y ≡ x
  to-from {x} {y} to-x≡y =
    from y       ≡⟨ cong from $ sym to-x≡y ⟩
    from (to x)  ≡⟨ left-inverse-of x ⟩∎
    x            ∎

  open _↠_ surjection public

------------------------------------------------------------------------
-- Equivalence

-- _↔_ is an equivalence relation.

id : ∀ {a} {A : Set a} → A ↔ A
id = record
  { surjection      = Surjection.id
  ; left-inverse-of = refl
  }

inverse : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → B ↔ A
inverse A↔B = record
  { surjection = record
    { equivalence      = Equivalence.inverse equivalence
    ; right-inverse-of = left-inverse-of
    }
  ; left-inverse-of = right-inverse-of
  } where open _↔_ A↔B

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      B ↔ C → A ↔ B → A ↔ C
f ∘ g = record
  { surjection      = Surjection._∘_ (surjection f) (surjection g)
  ; left-inverse-of = from∘to
  }
  where
  open _↔_

  abstract
    from∘to : ∀ x → from g (from f (to f (to g x))) ≡ x
    from∘to = λ x →
      from g (from f (to f (to g x)))  ≡⟨ cong (from g) (left-inverse-of f (to g x)) ⟩
      from g (to g x)                  ≡⟨ left-inverse-of g x ⟩∎
      x                                ∎

-- "Equational" reasoning combinators.

infix  0 finally-↔
infixr 0 _↔⟨_⟩_

_↔⟨_⟩_ : ∀ {a b c} (A : Set a) {B : Set b} {C : Set c} →
         A ↔ B → B ↔ C → A ↔ C
_ ↔⟨ A↔B ⟩ B↔C = B↔C ∘ A↔B

finally-↔ : ∀ {a b} (A : Set a) (B : Set b) → A ↔ B → A ↔ B
finally-↔ _ _ A↔B = A↔B

syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩□ B □

------------------------------------------------------------------------
-- More lemmas

-- Equality between pairs can be expressed as a pair of equalities.

Σ-≡,≡↔≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} →
          (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
             subst B p (proj₂ p₁) ≡ proj₂ p₂) ↔
          (p₁ ≡ p₂)
Σ-≡,≡↔≡ {A = A} {B} {p₁} {p₂} = record
  { surjection = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  from-P = λ {p₁ p₂ : Σ A B} (_ : p₁ ≡ p₂) →
             ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
               subst B p (proj₂ p₁) ≡ proj₂ p₂

  from : {p₁ p₂ : Σ A B} →
         p₁ ≡ p₂ →
         ∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
           subst B p (proj₂ p₁) ≡ proj₂ p₂
  from = elim from-P (λ p → refl _ , subst-refl B _)

  to : {p₁ p₂ : Σ A B} →
       (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
          subst B p (proj₂ p₁) ≡ proj₂ p₂) →
       p₁ ≡ p₂
  to = uncurry Σ-≡,≡→≡

  abstract

    to∘from : ∀ eq → to (from {p₁ = p₁} {p₂ = p₂} eq) ≡ eq
    to∘from = elim (λ p≡q → to (from p≡q) ≡ p≡q) λ x →
      let lem = subst-refl B (proj₂ x) in
      to (from (refl x))                          ≡⟨ cong to (elim-refl from-P _) ⟩
      to (refl (proj₁ x) , lem)                   ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩
      cong (_,_ (proj₁ x)) (trans (sym lem) lem)  ≡⟨ cong (cong (_,_ (proj₁ x))) $ trans-symˡ lem ⟩
      cong (_,_ (proj₁ x)) (refl (proj₂ x))       ≡⟨ cong-refl (_,_ (proj₁ x)) {x = proj₂ x} ⟩∎
      refl x                                      ∎

    from∘to : ∀ p → from (to {p₁ = p₁} {p₂ = p₂} p) ≡ p
    from∘to p = elim
      (λ {x₁ x₂} x₁≡x₂ →
         ∀ {y₁ y₂} (y₁′≡y₂ : subst B x₁≡x₂ y₁ ≡ y₂) →
         from (to (x₁≡x₂ , y₁′≡y₂)) ≡ (x₁≡x₂ , y₁′≡y₂))
      (λ x {y₁} y₁′≡y₂ → elim
         (λ {y₁ y₂} (y₁≡y₂ : y₁ ≡ y₂) →
            (y₁′≡y₂ : subst B (refl x) y₁ ≡ y₂) →
            y₁≡y₂ ≡ trans (sym $ subst-refl B y₁) y₁′≡y₂ →
            from (to (refl x , y₁′≡y₂)) ≡ (refl x , y₁′≡y₂))
         (λ y y′≡y eq →
          let lem = subst-refl B y in
          from (to (refl x , y′≡y))                   ≡⟨ cong from $ Σ-≡,≡→≡-reflˡ _ ⟩
          from (cong (_,_ x) (trans (sym lem) y′≡y))  ≡⟨ cong (from ⊚ cong (_,_ x)) $ sym eq ⟩
          from (cong (_,_ x) (refl y))                ≡⟨ cong from $ cong-refl (_,_ x) {x = y} ⟩
          from (refl (x , y))                         ≡⟨ elim-refl from-P _ ⟩
          (refl x , lem)                              ≡⟨ cong (_,_ (refl x)) (
             lem                                           ≡⟨ sym $ trans-reflʳ _ ⟩
             trans lem (refl _)                            ≡⟨ cong (trans lem) eq ⟩
             trans lem (trans (sym lem) y′≡y)              ≡⟨ sym $ trans-assoc _ _ _ ⟩
             trans (trans lem (sym lem)) y′≡y              ≡⟨ cong (λ p → trans p y′≡y) $ trans-symʳ lem ⟩
             trans (refl _) y′≡y                           ≡⟨ trans-reflˡ _ ⟩∎
             y′≡y                                          ∎) ⟩∎
          (refl x , y′≡y)                             ∎)
         (trans (sym $ subst-refl B y₁) y₁′≡y₂)
         y₁′≡y₂
         (refl _))
      (proj₁ p) (proj₂ p)

-- If one is given an equality between pairs, where the second
-- components of the pairs are propositional, then one can restrict
-- attention to the first components.

ignore-propositional-component :
  ∀ {a b} {A : Set a} {B : A → Set b} {p q : Σ A B} →
  Propositional (B (proj₁ q)) →
  (proj₁ p ≡ proj₁ q) ↔ (p ≡ q)
ignore-propositional-component {p = p₁ , p₂} {q₁ , q₂} Bq₁-prop = record
  { surjection = record
    { equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : p₁ ≡ q₁ → (p₁ , p₂) ≡ (q₁ , q₂)
  to = λ p₁≡q₁ →
    Σ-≡,≡→≡ p₁≡q₁ (_⇔_.to propositional⇔irrelevant Bq₁-prop _ _)

  from : (p₁ , p₂) ≡ (q₁ , q₂) → p₁ ≡ q₁
  from = proj₁ ⊚ _↔_.from Σ-≡,≡↔≡

  abstract

    to∘from : ∀ p≡q → to (from p≡q) ≡ p≡q
    to∘from p≡q =
      Σ-≡,≡→≡ (proj₁ $ _↔_.from Σ-≡,≡↔≡ p≡q) _  ≡⟨ cong (Σ-≡,≡→≡ _) $ _⇔_.to set⇔UIP (mono₁ 1 Bq₁-prop) _ _ ⟩
      Σ-≡,≡→≡ (proj₁ $ _↔_.from Σ-≡,≡↔≡ p≡q) _  ≡⟨ _↔_.right-inverse-of Σ-≡,≡↔≡ _ ⟩∎
      p≡q                                       ∎

    from∘to : ∀ p₁≡q₁ → from (to p₁≡q₁) ≡ p₁≡q₁
    from∘to p₁≡q₁ =
      proj₁ (_↔_.from Σ-≡,≡↔≡ (Σ-≡,≡→≡ p₁≡q₁ _))  ≡⟨ cong proj₁ $ _↔_.left-inverse-of Σ-≡,≡↔≡ _ ⟩∎
      p₁≡q₁                                       ∎

-- Decidable equality respects bijections.

decidable-equality-respects :
  ∀ {a b} {A : Set a} {B : Set b} →
  A ↔ B → Decidable-equality A → Decidable-equality B
decidable-equality-respects A↔B _≟A_ x y =
  ⊎-map (_↔_.injective (inverse A↔B))
                       (λ from-x≢from-y → from-x≢from-y ⊚ cong from)
        (from x ≟A from y)
  where open _↔_ A↔B

-- All contractible types are isomorphic.

contractible-isomorphic :
  ∀ {a b} {A : Set a} {B : Set b} →
  Contractible A → Contractible B → A ↔ B
contractible-isomorphic {A} {B} cA cB = record
  { surjection = record
    { equivalence = record
      { to   = const (proj₁ cB)
      ; from = const (proj₁ cA)
      }
    ; right-inverse-of = proj₂ cB
    }
  ; left-inverse-of = proj₂ cA
  }

-- Implicit and explicit Πs are isomorphic.

implicit-Π↔Π : ∀ {a b} {A : Set a} {B : A → Set b} →
               ({x : A} → B x) ↔ ((x : A) → B x)
implicit-Π↔Π = record
  { surjection = record
    { equivalence = record
      { to   = λ f x → f {x}
      ; from = λ f {x} → f x
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }
