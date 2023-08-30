------------------------------------------------------------------------
-- Bijections
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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

record _↔_ {f t} (From : Type f) (To : Type t) : Type (f ⊔ t) where
  field
    surjection : From ↠ To

  open _↠_ surjection

  field
    left-inverse-of : ∀ x → from (to x) ≡ x

  injective : Injective to
  injective {x} {y} to-x≡to-y =
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

  -- Every right inverse of to is pointwise equal to from.

  right-inverse-unique :
    (f : To → From) →
    (∀ x → to (f x) ≡ x) →
    (∀ x → f x ≡ from x)
  right-inverse-unique _ right x = sym $ to-from (right x)

  -- Every left inverse of from is pointwise equal to to.

  left-inverse-of-from-unique :
    (f : From → To) →
    (∀ x → f (from x) ≡ x) →
    (∀ x → f x ≡ to x)
  left-inverse-of-from-unique f left x =
    f x              ≡⟨ cong f $ sym $ left-inverse-of _ ⟩
    f (from (to x))  ≡⟨ left _ ⟩∎
    to x             ∎

  open _↠_ surjection public

-- The type of quasi-inverses of a function (as defined in the HoTT
-- book).

Has-quasi-inverse :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A → B) → Type (a ⊔ b)
Has-quasi-inverse {A} {B} to =
  ∃ λ (from : B → A) →
    (∀ x → to (from x) ≡ x) ×
    (∀ x → from (to x) ≡ x)

-- An alternative characterisation of bijections.

↔-as-Σ :
  ∀ {a b} {A : Type a} {B : Type b} →
  (A ↔ B) ↔ ∃ λ (f : A → B) → Has-quasi-inverse f
↔-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ A↔B → _↔_.to A↔B
                     , _↔_.from A↔B
                     , _↔_.right-inverse-of A↔B
                     , _↔_.left-inverse-of A↔B
      ; from = λ (t , f , r , l) → record
          { surjection = record
            { logical-equivalence = record
              { to   = t
              ; from = f
              }
            ; right-inverse-of = r
            }
          ; left-inverse-of = l
          }
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

------------------------------------------------------------------------
-- Equivalence

-- _↔_ is an equivalence relation.

id : ∀ {a} {A : Type a} → A ↔ A
id = record
  { surjection      = Surjection.id
  ; left-inverse-of = refl
  }

inverse : ∀ {a b} {A : Type a} {B : Type b} → A ↔ B → B ↔ A
inverse A↔B = record
  { surjection = record
    { logical-equivalence = Logical-equivalence.inverse
                              logical-equivalence
    ; right-inverse-of    = left-inverse-of
    }
  ; left-inverse-of = right-inverse-of
  } where open _↔_ A↔B

infixr 9 _∘_

_∘_ : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
      B ↔ C → A ↔ B → A ↔ C
f ∘ g = record
  { surjection      = Surjection._∘_ (surjection f) (surjection g)
  ; left-inverse-of = from∘to
  }
  where
  open _↔_

  from∘to : ∀ x → from g (from f (to f (to g x))) ≡ x
  from∘to = λ x →
    from g (from f (to f (to g x)))  ≡⟨ cong (from g) (left-inverse-of f (to g x)) ⟩
    from g (to g x)                  ≡⟨ left-inverse-of g x ⟩∎
    x                                ∎

-- "Equational" reasoning combinators.

infix  -1 finally-↔
infixr -2 step-↔

-- For an explanation of why step-↔ is defined in this way, see
-- Equality.step-≡.

step-↔ : ∀ {a b c} (A : Type a) {B : Type b} {C : Type c} →
         B ↔ C → A ↔ B → A ↔ C
step-↔ _ = _∘_

syntax step-↔ A B↔C A↔B = A ↔⟨ A↔B ⟩ B↔C

finally-↔ : ∀ {a b} (A : Type a) (B : Type b) → A ↔ B → A ↔ B
finally-↔ _ _ A↔B = A↔B

syntax finally-↔ A B A↔B = A ↔⟨ A↔B ⟩□ B □

------------------------------------------------------------------------
-- One can replace either of the functions with an extensionally equal
-- function

with-other-function :
  ∀ {a b} {A : Type a} {B : Type b}
  (A↔B : A ↔ B) (f : A → B) →
  (∀ x → _↔_.to A↔B x ≡ f x) →
  A ↔ B
with-other-function A↔B f ≡f = record
  { surjection = record
    { logical-equivalence = record
      { to   = f
      ; from = _↔_.from A↔B
      }
    ; right-inverse-of = λ x →
        f (_↔_.from A↔B x)           ≡⟨ sym $ ≡f _ ⟩
        _↔_.to A↔B (_↔_.from A↔B x)  ≡⟨ _↔_.right-inverse-of A↔B _ ⟩∎
        x                            ∎
    }
  ; left-inverse-of = λ x →
      _↔_.from A↔B (f x)           ≡⟨ cong (_↔_.from A↔B) $ sym $ ≡f _ ⟩
      _↔_.from A↔B (_↔_.to A↔B x)  ≡⟨ _↔_.left-inverse-of A↔B _ ⟩∎
      x                            ∎
  }

with-other-inverse :
  ∀ {a b} {A : Type a} {B : Type b}
  (A↔B : A ↔ B) (f : B → A) →
  (∀ x → _↔_.from A↔B x ≡ f x) →
  A ↔ B
with-other-inverse A↔B f ≡f =
  inverse $ with-other-function (inverse A↔B) f ≡f

private

  -- The two functions above compute in the right way.

  to∘with-other-function :
    ∀ {a b} {A : Type a} {B : Type b}
    (A↔B : A ↔ B) (f : A → B)
    (to≡f : ∀ x → _↔_.to A↔B x ≡ f x) →
    _↔_.to (with-other-function A↔B f to≡f) ≡ f
  to∘with-other-function _ _ _ = refl _

  from∘with-other-function :
    ∀ {a b} {A : Type a} {B : Type b}
    (A↔B : A ↔ B) (f : A → B)
    (to≡f : ∀ x → _↔_.to A↔B x ≡ f x) →
    _↔_.from (with-other-function A↔B f to≡f) ≡ _↔_.from A↔B
  from∘with-other-function _ _ _ = refl _

  to∘with-other-inverse :
    ∀ {a b} {A : Type a} {B : Type b}
    (A↔B : A ↔ B) (g : B → A)
    (from≡g : ∀ x → _↔_.from A↔B x ≡ g x) →
    _↔_.to (with-other-inverse A↔B g from≡g) ≡ _↔_.to A↔B
  to∘with-other-inverse _ _ _ = refl _

  from∘with-other-inverse :
    ∀ {a b} {A : Type a} {B : Type b}
    (A↔B : A ↔ B) (g : B → A)
    (from≡g : ∀ x → _↔_.from A↔B x ≡ g x) →
    _↔_.from (with-other-inverse A↔B g from≡g) ≡ g
  from∘with-other-inverse _ _ _ = refl _

------------------------------------------------------------------------
-- More lemmas

-- Uninhabited types are isomorphic to the empty type.

⊥↔uninhabited : ∀ {a ℓ} {A : Type a} → ¬ A → ⊥ {ℓ = ℓ} ↔ A
⊥↔uninhabited ¬A = record
  { surjection = record
    { logical-equivalence = record
      { to   = ⊥-elim
      ; from = ⊥-elim ⊚ ¬A
      }
    ; right-inverse-of = ⊥-elim ⊚ ¬A
    }
  ; left-inverse-of = λ ()
  }

-- A lifted set is isomorphic to the underlying one.

↑↔ : ∀ {a b} {A : Type a} → ↑ b A ↔ A
↑↔ {b} {A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = lower
      ; from = lift
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Equality between pairs can be expressed as a pair of equalities.

Σ-≡,≡↔≡ : ∀ {a b} {A : Type a} {B : A → Type b} {p₁ p₂ : Σ A B} →
          (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
             subst B p (proj₂ p₁) ≡ proj₂ p₂) ↔
          (p₁ ≡ p₂)
Σ-≡,≡↔≡ {A} {B} {p₁} {p₂} = record
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

  opaque

    to∘from : ∀ eq → to (from {p₁ = p₁} {p₂ = p₂} eq) ≡ eq
    to∘from = elim (λ p≡q → to (from p≡q) ≡ p≡q) λ x →
      let lem = subst-refl B (proj₂ x) in
      to (from (refl x))                          ≡⟨ cong to (elim-refl from-P _) ⟩
      to (refl (proj₁ x) , lem)                   ≡⟨ Σ-≡,≡→≡-reflˡ _ ⟩
      cong (_,_ (proj₁ x)) (trans (sym lem) lem)  ≡⟨ cong (cong (_,_ (proj₁ x))) $ trans-symˡ lem ⟩
      cong (_,_ (proj₁ x)) (refl (proj₂ x))       ≡⟨ cong-refl (_,_ (proj₁ x)) ⟩∎
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
          from (cong (_,_ x) (refl y))                ≡⟨ cong from $ cong-refl (_,_ x) ⟩
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

≡↔inj₁≡inj₁ : ∀ {a b} {A : Type a} {B : Type b} {x y : A} →
              (x ≡ y) ↔ _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y)
≡↔inj₁≡inj₁ {A} {B} {x} {y} = record
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

  opaque

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
      p = if_then true else false

      f≡id : ∀ z → T (p z) → f z ≡ z
      f≡id (inj₁ x) = const (refl (inj₁ x))
      f≡id (inj₂ y) = ⊥-elim

    from∘to : ∀ x≡y → from (to x≡y) ≡ x≡y
    from∘to x≡y =
      cong [ P.id , const x ] (cong inj₁ x≡y)  ≡⟨ cong-∘ [ P.id , const x ] inj₁ _ ⟩
      cong P.id x≡y                            ≡⟨ sym $ cong-id _ ⟩∎
      x≡y                                      ∎

≡↔inj₂≡inj₂ : ∀ {a b} {A : Type a} {B : Type b} {x y : B} →
              (x ≡ y) ↔ _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y)
≡↔inj₂≡inj₂ {A} {B} {x} {y} = record
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

  opaque

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
      p = if_then false else true

      f≡id : ∀ z → T (p z) → f z ≡ z
      f≡id (inj₁ x) = ⊥-elim
      f≡id (inj₂ y) = const (refl (inj₂ y))

    from∘to : ∀ x≡y → from (to x≡y) ≡ x≡y
    from∘to x≡y =
      cong [ const x , P.id ] (cong inj₂ x≡y)  ≡⟨ cong-∘ [ const x , P.id ] inj₂ _ ⟩
      cong P.id x≡y                            ≡⟨ sym $ cong-id _ ⟩∎
      x≡y                                      ∎

-- An alternative characterisation of equality for binary sums.

Equality-⊎ : ∀ {a b} {A : Type a} {B : Type b} →
             A ⊎ B → A ⊎ B → Type (a ⊔ b)
Equality-⊎ {b} (inj₁ x) (inj₁ y) = ↑ b (x ≡ y)
Equality-⊎     (inj₁ x) (inj₂ y) = ⊥
Equality-⊎     (inj₂ x) (inj₁ y) = ⊥
Equality-⊎ {a} (inj₂ x) (inj₂ y) = ↑ a (x ≡ y)

≡↔⊎ : ∀ {a b} {A : Type a} {B : Type b} {x y : A ⊎ B} →
      x ≡ y ↔ Equality-⊎ x y
≡↔⊎ {x = inj₁ x} {inj₁ y} = inj₁ x ≡ inj₁ y  ↔⟨ inverse ≡↔inj₁≡inj₁ ⟩
                            x ≡ y            ↔⟨ inverse ↑↔ ⟩□
                            ↑ _ (x ≡ y)      □
≡↔⊎ {x = inj₁ x} {inj₂ y} = inj₁ x ≡ inj₂ y  ↔⟨ inverse (⊥↔uninhabited ⊎.inj₁≢inj₂) ⟩□
                            ⊥                □
≡↔⊎ {x = inj₂ x} {inj₁ y} = inj₂ x ≡ inj₁ y  ↔⟨ inverse (⊥↔uninhabited (⊎.inj₁≢inj₂ ⊚ sym)) ⟩□
                            ⊥                □
≡↔⊎ {x = inj₂ x} {inj₂ y} = inj₂ x ≡ inj₂ y  ↔⟨ inverse ≡↔inj₂≡inj₂ ⟩
                            x ≡ y            ↔⟨ inverse ↑↔ ⟩□
                            ↑ _ (x ≡ y)      □

-- Decidable equality respects bijections.

decidable-equality-respects :
  ∀ {a b} {A : Type a} {B : Type b} →
  A ↔ B → Decidable-equality A → Decidable-equality B
decidable-equality-respects A↔B _≟A_ x y =
  ⊎-map (_↔_.injective (inverse A↔B))
                       (λ from-x≢from-y → from-x≢from-y ⊚ cong from)
        (from x ≟A from y)
  where open _↔_ A↔B

-- All contractible types are isomorphic.

contractible-isomorphic :
  ∀ {a b} {A : Type a} {B : Type b} →
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

-- Implicit and explicit Π's are isomorphic.

implicit-Π↔Π : ∀ {a b} {A : Type a} {B : A → Type b} →
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

-- Implicit and explicit Π's with erased domains are isomorphic.

implicit-Πᴱ↔Πᴱ :
  ∀ {a b} {A : Type a} {B : A → Type b} →
  ({@0 x : A} → B x) ↔ ((@0 x : A) → B x)
implicit-Πᴱ↔Πᴱ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f x → f {x}
      ; from = λ f {x} → f x
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- A variant of implicit-Πᴱ↔Πᴱ.

implicit-Πᴱ↔Πᴱ′ :
  ∀ {a b} {@0 A : Type a} {B : @0 A → Type b} →
  ({@0 x : A} → B x) ↔ ((@0 x : A) → B x)
implicit-Πᴱ↔Πᴱ′ {A} {B} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f x → f {x}
      ; from = λ f {x} → f x
      }
    ; right-inverse-of = refl {A = (@0 x : A) → B x}
    }
  ; left-inverse-of = refl {A = {@0 x : A} → B x}
  }

-- Σ is associative.

Σ-assoc : ∀ {a b c}
            {A : Type a} {B : A → Type b} {C : (x : A) → B x → Type c} →
          (Σ A λ x → Σ (B x) (C x)) ↔ Σ (Σ A B) (uncurry C)
Σ-assoc = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (x , (y , z)) → (x , y) , z }
      ; from = λ { ((x , y) , z) → x , (y , z) }
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Π and Σ commute (in a certain sense).

ΠΣ-comm :
  ∀ {a b c} {A : Type a} {B : A → Type b} {C : (x : A) → B x → Type c} →
  (∀ x → ∃ λ (y : B x) → C x y)
    ↔
  (∃ λ (f : ∀ x → B x) → ∀ x → C x (f x))
ΠΣ-comm = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → proj₁ ⊚ f , proj₂ ⊚ f
      ; from = λ { (f , g) x → f x , g x }
      }
    ; right-inverse-of = refl
    }
  ; left-inverse-of = refl
  }

-- Equality is commutative.

≡-comm :
  ∀ {a} {A : Type a} {x y : A} →
  x ≡ y ↔ y ≡ x
≡-comm = record
  { surjection = record
    { logical-equivalence = record { to = sym }
    ; right-inverse-of    = sym-sym
    }
  ; left-inverse-of = sym-sym
  }

-- Families of functions that satisfy a kind of involution property
-- can be turned into bijections.

bijection-from-involutive-family :
  ∀ {a b} {A : Type a} {B : A → Type b} →
  (f : ∀ a₁ a₂ → B a₁ → B a₂) →
  (∀ a₁ a₂ (x : B a₁) → f _ _ (f _ a₂ x) ≡ x) →
  ∀ a₁ a₂ → B a₁ ↔ B a₂
bijection-from-involutive-family f f-involutive _ _ = record
  { surjection = record
    { logical-equivalence = record
      { to   = f _ _
      ; from = f _ _
      }
    ; right-inverse-of = f-involutive _ _
    }
  ; left-inverse-of = f-involutive _ _
  }

opaque

  -- An equality rearrangement lemma.

  trans-to-to≡to-trans :
    ∀ {a b} {A : Type a} {B : Type b} {f : A → B}
    (iso : ∀ x y → f x ≡ f y ↔ x ≡ y) →
    (∀ x → _↔_.from (iso x x) (refl x) ≡ refl (f x)) →
    ∀ {x y z p q} →
    trans (_↔_.to (iso x y) p) (_↔_.to (iso y z) q) ≡
    _↔_.to (iso x z) (trans p q)
  trans-to-to≡to-trans {f} iso iso-refl {x} {y} {z} {p} {q} =
    trans (_↔_.to (iso x y) p) (_↔_.to (iso y z) q)               ≡⟨ elim₁ (λ {x} p → trans p (_↔_.to (iso y z) q) ≡
                                                                                      _↔_.to (iso x z) (trans (_↔_.from (iso x y) p) q)) (
        trans (refl y) (_↔_.to (iso y z) q)                              ≡⟨ trans-reflˡ _ ⟩
        _↔_.to (iso y z) q                                               ≡⟨ cong (_↔_.to (iso y z)) $ sym $ trans-reflˡ _ ⟩
        _↔_.to (iso y z) (trans (refl (f y)) q)                          ≡⟨ cong (_↔_.to (iso y z) ⊚ flip trans _) $ sym $ iso-refl y ⟩∎
        _↔_.to (iso y z) (trans (_↔_.from (iso y y) (refl y)) q)         ∎)
                                                                           (_↔_.to (iso x y) p) ⟩
    _↔_.to (iso x z)
      (trans (_↔_.from (iso x y) (_↔_.to (iso x y) p)) q)         ≡⟨ cong (_↔_.to (iso x z) ⊚ flip trans _) $
                                                                       _↔_.left-inverse-of (iso _ _) _ ⟩∎
    _↔_.to (iso x z) (trans p q)                                  ∎
