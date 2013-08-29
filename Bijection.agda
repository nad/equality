------------------------------------------------------------------------
-- Bijections
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Equality

module Bijection
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import H-level eq
open import Injection eq using (Injective; _↣_)
open import Logical-equivalence using (_⇔_)
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
    { logical-equivalence = Logical-equivalence.inverse
                              logical-equivalence
    ; right-inverse-of    = left-inverse-of
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
    { logical-equivalence = record
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
  from = Σ-≡,≡←≡

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

-- Equalities are closed, in a strong sense, under applications of
-- certain injections (at least inj₁ and inj₂).

≡↔inj₁≡inj₁ : ∀ {a b} {A : Set a} {B : Set b} {x y : A} →
              (x ≡ y) ↔ _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y)
≡↔inj₁≡inj₁ {A = A} {B} {x} {y} = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : x ≡ y → _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y)
  to = cong inj₁

  from = ⊎.cancel-inj₁

  abstract

    to∘from : ∀ ix≡iy → to (from ix≡iy) ≡ ix≡iy
    to∘from ix≡iy =
      cong inj₁ (⊎.cancel-inj₁ ix≡iy)              ≡⟨ cong-∘ inj₁ [ P.id , const x ] ix≡iy ⟩
      cong f ix≡iy                                 ≡⟨ cong-roughly-id f p ix≡iy _ _ f≡id ⟩
      trans (refl _) (trans ix≡iy $ sym (refl _))  ≡⟨ trans-reflˡ _ ⟩
      trans ix≡iy (sym $ refl _)                   ≡⟨ cong (trans ix≡iy) sym-refl ⟩
      trans ix≡iy (refl _)                         ≡⟨ trans-reflʳ _ ⟩∎
      ix≡iy                                        ∎
      where
      f : A ⊎ B → A ⊎ B
      f = inj₁ ⊚ [ P.id , const x ]

      p : A ⊎ B → Bool
      p = [ const true , const false ]

      f≡id : ∀ z → T (p z) → f z ≡ z
      f≡id (inj₁ x) = const (refl (inj₁ x))
      f≡id (inj₂ y) = ⊥-elim

    from∘to : ∀ x≡y → from (to x≡y) ≡ x≡y
    from∘to x≡y =
      cong [ P.id , const x ] (cong inj₁ x≡y)  ≡⟨ cong-∘ [ P.id , const x ] inj₁ _ ⟩
      cong P.id x≡y                            ≡⟨ sym $ cong-id _ ⟩∎
      x≡y                                      ∎

≡↔inj₂≡inj₂ : ∀ {a b} {A : Set a} {B : Set b} {x y : B} →
              (x ≡ y) ↔ _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y)
≡↔inj₂≡inj₂ {A = A} {B} {x} {y} = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : x ≡ y → _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y)
  to = cong inj₂

  from = ⊎.cancel-inj₂

  abstract

    to∘from : ∀ ix≡iy → to (from ix≡iy) ≡ ix≡iy
    to∘from ix≡iy =
      cong inj₂ (⊎.cancel-inj₂ ix≡iy)              ≡⟨ cong-∘ inj₂ [ const x , P.id ] ix≡iy ⟩
      cong f ix≡iy                                 ≡⟨ cong-roughly-id f p ix≡iy _ _ f≡id ⟩
      trans (refl _) (trans ix≡iy $ sym (refl _))  ≡⟨ trans-reflˡ _ ⟩
      trans ix≡iy (sym $ refl _)                   ≡⟨ cong (trans ix≡iy) sym-refl ⟩
      trans ix≡iy (refl _)                         ≡⟨ trans-reflʳ _ ⟩∎
      ix≡iy                                        ∎
      where
      f : A ⊎ B → A ⊎ B
      f = inj₂ ⊚ [ const x , P.id ]

      p : A ⊎ B → Bool
      p = [ const false , const true ]

      f≡id : ∀ z → T (p z) → f z ≡ z
      f≡id (inj₁ x) = ⊥-elim
      f≡id (inj₂ y) = const (refl (inj₂ y))

    from∘to : ∀ x≡y → from (to x≡y) ≡ x≡y
    from∘to x≡y =
      cong [ const x , P.id ] (cong inj₂ x≡y)  ≡⟨ cong-∘ [ const x , P.id ] inj₂ _ ⟩
      cong P.id x≡y                            ≡⟨ sym $ cong-id _ ⟩∎
      x≡y                                      ∎

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
    { logical-equivalence = record
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
    { logical-equivalence = record
      { to   = λ f x → f {x}
      ; from = λ f {x} → f x
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- A lifted set is isomorphic to the underlying one.

↑↔ : ∀ {a b} {A : Set a} → ↑ b A ↔ A
↑↔ {b = b} {A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = lower
      ; from = lift
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }
