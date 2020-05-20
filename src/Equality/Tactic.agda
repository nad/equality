------------------------------------------------------------------------
-- A simple tactic for proving equality of equality proofs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equality.Tactic
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Prelude hiding (Level; lift; lower)

private
  variable
    a       : Prelude.Level
    A B     : Set a
    ℓ x y z : A
    x≡y y≡z : x ≡ y

------------------------------------------------------------------------
-- Equality expressions

-- Equality expressions.
--
-- Note that the presence of the Refl constructor means that Eq is a
-- definition of equality with a concrete, evaluating eliminator.

data Eq {A : Set a} : A → A → Set (lsuc a) where
  Lift  : (x≡y : x ≡ y) → Eq x y
  Refl  : Eq x x
  Sym   : (x≈y : Eq x y) → Eq y x
  Trans : (x≈y : Eq x y) (y≈z : Eq y z) → Eq x z
  Cong  : ∀ {B : Set a} {x y}
          (f : B → A) (x≈y : Eq x y) → Eq (f x) (f y)

-- Semantics.

⟦_⟧ : Eq x y → x ≡ y
⟦ Lift x≡y      ⟧ = x≡y
⟦ Refl          ⟧ = refl _
⟦ Sym x≈y       ⟧ = sym ⟦ x≈y ⟧
⟦ Trans x≈y y≈z ⟧ = trans ⟦ x≈y ⟧ ⟦ y≈z ⟧
⟦ Cong f x≈y    ⟧ = cong f ⟦ x≈y ⟧

-- A derived combinator.

Cong₂ : {A B C : Set a} (f : A → B → C) {x y : A} {u v : B} →
        Eq x y → Eq u v → Eq (f x u) (f y v)
Cong₂ f {y = y} {u} x≈y u≈v =
  Trans (Cong (flip f u) x≈y) (Cong (f y) u≈v)

private

  Cong₂-correct :
    {A B C : Set a} (f : A → B → C) {x y : A} {u v : B}
    (x≈y : Eq x y) (u≈v : Eq u v) →
    ⟦ Cong₂ f x≈y u≈v ⟧ ≡ cong₂ f ⟦ x≈y ⟧ ⟦ u≈v ⟧
  Cong₂-correct f x≈y u≈v = refl _

------------------------------------------------------------------------
-- Simplified expressions

private

  -- The simplified expressions are stratified into three levels.

  data Level : Set where
    upper middle lower : Level

  data EqS {A : Set a} : Level → A → A → Set (lsuc a) where

    -- Bottom layer: a single use of congruence applied to an actual
    -- equality.

    Cong : {B : Set a} {x y : B} (f : B → A) (x≡y : x ≡ y) →
           EqS lower (f x) (f y)

    -- Middle layer: at most one use of symmetry.

    No-Sym : (x≈y : EqS lower x y) → EqS middle x y
    Sym    : (x≈y : EqS lower x y) → EqS middle y x

    -- Uppermost layer: a sequence of equalities, combined using
    -- transitivity and a single use of reflexivity.

    Refl : EqS upper x x
    Cons : (x≈y : EqS middle x y) (y≈z : EqS upper y z) →
           EqS upper x z

  -- Semantics of simplified expressions.

  ⟦_⟧S : EqS ℓ x y → x ≡ y
  ⟦ Cong f x≡y   ⟧S = cong f x≡y
  ⟦ No-Sym x≈y   ⟧S =     ⟦ x≈y ⟧S
  ⟦ Sym    x≈y   ⟧S = sym ⟦ x≈y ⟧S
  ⟦ Refl         ⟧S = refl _
  ⟦ Cons x≈y y≈z ⟧S = trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S

------------------------------------------------------------------------
-- Manipulation of expressions

private

  lift : x ≡ y → EqS upper x y
  lift x≡y = Cons (No-Sym (Cong id x≡y)) Refl

  abstract

    lift-correct : (x≡y : x ≡ y) → x≡y ≡ ⟦ lift x≡y ⟧S
    lift-correct x≡y =
      x≡y                           ≡⟨ cong-id _ ⟩
      cong id x≡y                   ≡⟨ sym (trans-reflʳ _) ⟩∎
      trans (cong id x≡y) (refl _)  ∎

  snoc : EqS upper x y → EqS middle y z → EqS upper x z
  snoc Refl           y≈z = Cons y≈z Refl
  snoc (Cons x≈y y≈z) z≈u = Cons x≈y (snoc y≈z z≈u)

  abstract

    snoc-correct :
      (z≈y : EqS upper z y) (y≈x : EqS middle y x) →
      sym y≡z ≡ ⟦ z≈y ⟧S → sym x≡y ≡ ⟦ y≈x ⟧S →
      sym (trans x≡y y≡z) ≡ ⟦ snoc z≈y y≈x ⟧S
    snoc-correct {y≡z = y≡z} {x≡y = x≡y} Refl y≈z h₁ h₂ =
      sym (trans x≡y y≡z)        ≡⟨ sym-trans _ _ ⟩
      trans (sym y≡z) (sym x≡y)  ≡⟨ cong₂ trans h₁ h₂ ⟩
      trans (refl _) ⟦ y≈z ⟧S    ≡⟨ trans-reflˡ _ ⟩
      ⟦ y≈z ⟧S                   ≡⟨ sym (trans-reflʳ _) ⟩∎
      trans ⟦ y≈z ⟧S (refl _)    ∎
    snoc-correct {y≡z = y≡z} {x≡y = x≡y} (Cons x≈y y≈z) z≈u h₁ h₂ =
      sym (trans x≡y y≡z)                                    ≡⟨ sym-trans _ _ ⟩
      trans (sym y≡z) (sym x≡y)                              ≡⟨ cong₂ trans h₁ (refl (sym x≡y)) ⟩
      trans (trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S) (sym x≡y)              ≡⟨ trans-assoc _ _ _ ⟩
      trans ⟦ x≈y ⟧S (trans ⟦ y≈z ⟧S (sym x≡y))              ≡⟨ cong (trans ⟦ x≈y ⟧S) $
                                                                  cong₂ trans (sym (sym-sym ⟦ y≈z ⟧S)) (refl (sym x≡y)) ⟩
      trans ⟦ x≈y ⟧S (trans (sym (sym ⟦ y≈z ⟧S)) (sym x≡y))  ≡⟨ cong (trans _) $ sym (sym-trans x≡y (sym ⟦ y≈z ⟧S)) ⟩
      trans ⟦ x≈y ⟧S (sym (trans x≡y (sym ⟦ y≈z ⟧S)))        ≡⟨ cong (trans _) $ snoc-correct y≈z z≈u (sym-sym _) h₂ ⟩∎
      trans ⟦ x≈y ⟧S ⟦ snoc y≈z z≈u ⟧S                       ∎

  append : EqS upper x y → EqS upper y z → EqS upper x z
  append Refl           x≈y = x≈y
  append (Cons x≈y y≈z) z≈u = Cons x≈y (append y≈z z≈u)

  abstract

    append-correct :
      (x≈y : EqS upper x y) (y≈z : EqS upper y z) →
      x≡y ≡ ⟦ x≈y ⟧S → y≡z ≡ ⟦ y≈z ⟧S →
      trans x≡y y≡z ≡ ⟦ append x≈y y≈z ⟧S
    append-correct {x≡y = x≡y} {y≡z} Refl x≈y h₁ h₂ =
      trans x≡y y≡z            ≡⟨ cong₂ trans h₁ h₂ ⟩
      trans (refl _) ⟦ x≈y ⟧S  ≡⟨ trans-reflˡ _ ⟩∎
      ⟦ x≈y ⟧S                 ∎
    append-correct {x≡y = x≡z} {z≡u} (Cons x≈y y≈z) z≈u h₁ h₂ =
      trans x≡z z≡u                        ≡⟨ cong₂ trans h₁ (refl z≡u) ⟩
      trans (trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S) z≡u  ≡⟨ trans-assoc _ _ _ ⟩
      trans ⟦ x≈y ⟧S (trans ⟦ y≈z ⟧S z≡u)  ≡⟨ cong (trans _) $ append-correct y≈z z≈u (refl _) h₂ ⟩∎
      trans ⟦ x≈y ⟧S ⟦ append y≈z z≈u ⟧S   ∎

  map-sym : EqS middle x y → EqS middle y x
  map-sym (No-Sym x≈y) = Sym    x≈y
  map-sym (Sym    x≈y) = No-Sym x≈y

  abstract

    map-sym-correct :
      (x≈y : EqS middle x y) →
      x≡y ≡ ⟦ x≈y ⟧S → sym x≡y ≡ ⟦ map-sym x≈y ⟧S
    map-sym-correct {x≡y = x≡y} (No-Sym x≈y) h =
      sym x≡y       ≡⟨ cong sym h ⟩∎
      sym ⟦ x≈y ⟧S  ∎
    map-sym-correct {x≡y = x≡y} (Sym x≈y) h =
      sym x≡y             ≡⟨ cong sym h ⟩
      sym (sym ⟦ x≈y ⟧S)  ≡⟨ sym-sym _ ⟩∎
      ⟦ x≈y ⟧S            ∎

  reverse : EqS upper x y → EqS upper y x
  reverse Refl           = Refl
  reverse (Cons x≈y y≈z) = snoc (reverse y≈z) (map-sym x≈y)

  abstract

    reverse-correct :
      (x≈y : EqS upper x y) →
      x≡y ≡ ⟦ x≈y ⟧S → sym x≡y ≡ ⟦ reverse x≈y ⟧S
    reverse-correct {x≡y = x≡y} Refl h =
      sym x≡y       ≡⟨ cong sym h ⟩
      sym (refl _)  ≡⟨ sym-refl ⟩∎
      refl _        ∎
    reverse-correct {x≡y = x≡y} (Cons x≈y y≈z) h =
      sym x≡y                                ≡⟨ cong sym h ⟩
      sym (trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S)          ≡⟨ snoc-correct (reverse y≈z) _
                                                             (reverse-correct y≈z (refl _))
                                                             (map-sym-correct x≈y (refl _)) ⟩∎
      ⟦ snoc (reverse y≈z) (map-sym x≈y) ⟧S  ∎

  map-cong : {A B : Set a} {x y : A} (f : A → B) →
             EqS ℓ x y → EqS ℓ (f x) (f y)
  map-cong {ℓ = lower}  f (Cong g x≡y)   = Cong (f ∘ g) x≡y
  map-cong {ℓ = middle} f (No-Sym x≈y)   = No-Sym (map-cong f x≈y)
  map-cong {ℓ = middle} f (Sym    y≈x)   = Sym (map-cong f y≈x)
  map-cong {ℓ = upper}  f Refl           = Refl
  map-cong {ℓ = upper}  f (Cons x≈y y≈z) =
    Cons (map-cong f x≈y) (map-cong f y≈z)

  abstract

    map-cong-correct :
      (f : A → B) (x≈y : EqS ℓ x y) →
      x≡y ≡ ⟦ x≈y ⟧S → cong f x≡y ≡ ⟦ map-cong f x≈y ⟧S
    map-cong-correct {ℓ = lower} {x≡y = gx≡gy} f (Cong g x≡y) h =
      cong f gx≡gy         ≡⟨ cong (cong f) h ⟩
      cong f (cong g x≡y)  ≡⟨ cong-∘ f g _ ⟩∎
      cong (f ∘ g) x≡y     ∎
    map-cong-correct {ℓ = middle} {x≡y = x≡y} f (No-Sym x≈y) h =
      cong f x≡y           ≡⟨ map-cong-correct f x≈y h ⟩∎
      ⟦ map-cong f x≈y ⟧S  ∎
    map-cong-correct {ℓ = middle} {x≡y = x≡y} f (Sym y≈x) h =
      cong f x≡y               ≡⟨ cong (cong f) h ⟩
      cong f (sym ⟦ y≈x ⟧S)    ≡⟨ cong-sym f _ ⟩
      sym (cong f ⟦ y≈x ⟧S)    ≡⟨ cong sym (map-cong-correct f y≈x (refl _)) ⟩∎
      sym ⟦ map-cong f y≈x ⟧S  ∎
    map-cong-correct {ℓ = upper} {x≡y = x≡y} f Refl h =
      cong f x≡y       ≡⟨ cong (cong f) h ⟩
      cong f (refl _)  ≡⟨ cong-refl f ⟩∎
      refl _           ∎
    map-cong-correct {ℓ = upper} {x≡y = x≡y} f (Cons x≈y y≈z) h =
      cong f x≡y                                     ≡⟨ cong (cong f) h ⟩
      cong f (trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S)               ≡⟨ cong-trans f _ _ ⟩
      trans (cong f ⟦ x≈y ⟧S) (cong f ⟦ y≈z ⟧S)      ≡⟨ cong₂ trans (map-cong-correct f x≈y (refl _))
                                                                    (map-cong-correct f y≈z (refl _)) ⟩∎
      trans ⟦ map-cong f x≈y ⟧S ⟦ map-cong f y≈z ⟧S  ∎

-- Equality-preserving simplifier.

simplify : Eq x y → EqS upper x y
simplify (Lift x≡y)      = lift x≡y
simplify Refl            = Refl
simplify (Sym x≡y)       = reverse (simplify x≡y)
simplify (Trans x≡y y≡z) = append (simplify x≡y) (simplify y≡z)
simplify (Cong f x≡y)    = map-cong f (simplify x≡y)

abstract

  simplify-correct :
    (x≈y : Eq x y) → ⟦ x≈y ⟧ ≡ ⟦ simplify x≈y ⟧S
  simplify-correct (Lift x≡y)      = lift-correct x≡y
  simplify-correct Refl            = refl _
  simplify-correct (Sym x≈y)       = reverse-correct (simplify x≈y)
                                       (simplify-correct x≈y)
  simplify-correct (Trans x≈y y≈z) = append-correct (simplify x≈y) _
                                       (simplify-correct x≈y)
                                       (simplify-correct y≈z)
  simplify-correct (Cong f x≈y)    = map-cong-correct f (simplify x≈y)
                                       (simplify-correct x≈y)

------------------------------------------------------------------------
-- Tactic

abstract

  -- Simple tactic for proving equality of equality proofs.

  prove : (x≡y x≡y′ : Eq x y) →
          ⟦ simplify x≡y ⟧S ≡ ⟦ simplify x≡y′ ⟧S →
          ⟦ x≡y ⟧ ≡ ⟦ x≡y′ ⟧
  prove x≡y x≡y′ hyp =
    ⟦ x≡y ⟧             ≡⟨ simplify-correct x≡y ⟩
    ⟦ simplify x≡y  ⟧S  ≡⟨ hyp ⟩
    ⟦ simplify x≡y′ ⟧S  ≡⟨ sym (simplify-correct x≡y′) ⟩∎
    ⟦ x≡y′ ⟧            ∎

------------------------------------------------------------------------
-- Some examples

private
  module Examples (x≡y : x ≡ y) where

    ex₁ : trans (refl x) (sym (sym x≡y)) ≡ x≡y
    ex₁ = prove (Trans Refl (Sym (Sym (Lift x≡y)))) (Lift x≡y) (refl _)

    ex₂ : cong proj₂ (sym (cong (_,_ x) x≡y)) ≡ sym x≡y
    ex₂ = prove (Cong proj₂ (Sym (Cong (_,_ x) (Lift x≡y))))
                (Sym (Lift x≡y))
                (refl _)

-- Non-examples: The tactic cannot prove trans-symˡ or trans-symʳ.
