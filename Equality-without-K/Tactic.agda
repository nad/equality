------------------------------------------------------------------------
-- A simple tactic for proving equality of equality proofs
------------------------------------------------------------------------

module Equality-without-K.Tactic where

open import Data.Product as Prod
open import Function

open import Equality-without-K

------------------------------------------------------------------------
-- Boring lemmas

private

  sym-refl : {A : Set} {x : A} → sym (refl x) ≡ refl x
  sym-refl = elim-refl (λ {z y} _ → y ≡ z) refl

  cong-refl : {A B : Set} (f : A → B) {x : A} →
              cong f (refl x) ≡ refl (f x)
  cong-refl f = elim-refl (λ {u v} _ → f u ≡ f v) (refl ∘ f)

  trans-refl-refl : {A : Set} (x : A) →
                    trans (refl x) (refl x) ≡ refl x
  trans-refl-refl x =
    cong (λ f → f (refl x))
         (trans (refl x)  ≡⟨ elim-refl (λ {u v} _ → v ≡ x → u ≡ x) (λ y y≡x → y≡x) ⟩∎
          id              ∎)

  trans-reflʳ : {A : Set} {x y : A} (x≡y : x ≡ y) →
                trans x≡y (refl y) ≡ x≡y
  trans-reflʳ =
    elim (λ {u v} u≡v → trans u≡v (refl v) ≡ u≡v)
         trans-refl-refl

  trans-reflˡ : {A : Set} {x y : A} (x≡y : x ≡ y) →
                trans (refl x) x≡y ≡ x≡y
  trans-reflˡ =
    elim (λ {u v} u≡v → trans (refl u) u≡v ≡ u≡v)
         trans-refl-refl

  sym-sym : {A : Set} {x y : A} (x≡y : x ≡ y) → sym (sym x≡y) ≡ x≡y
  sym-sym = elim (λ {u v} u≡v → sym (sym u≡v) ≡ u≡v)
                 (λ x → sym (sym (refl x))  ≡⟨ cong sym (sym-refl) ⟩
                        sym (refl x)        ≡⟨ sym-refl ⟩∎
                        refl x              ∎)

  sym-trans : {A : Set} {x y z : A} (x≡y : x ≡ y) (y≡z : y ≡ z) →
              sym (trans x≡y y≡z) ≡ trans (sym y≡z) (sym x≡y)
  sym-trans =
    elim (λ x≡y → ∀ y≡z → sym (trans x≡y y≡z) ≡ trans (sym y≡z) (sym x≡y))
         (λ y y≡z → sym (trans (refl y) y≡z)        ≡⟨ cong sym (trans-reflˡ _) ⟩
                    sym y≡z                         ≡⟨ sym $ trans-reflʳ _ ⟩
                    trans (sym y≡z) (refl y)        ≡⟨ cong (trans _) (sym sym-refl)  ⟩∎
                    trans (sym y≡z) (sym (refl y))  ∎)

  cong-id : {A : Set} {x y : A} (x≡y : x ≡ y) → x≡y ≡ cong id x≡y
  cong-id = elim (λ u≡v → u≡v ≡ cong id u≡v)
                 (λ x → refl x            ≡⟨ sym (cong-refl id) ⟩∎
                        cong id (refl x)  ∎)

  cong-∘ : {A B C : Set} {x y : A}
              (f : B → C) (g : A → B) (x≡y : x ≡ y) →
              cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y
  cong-∘ f g = elim (λ x≡y → cong f (cong g x≡y) ≡ cong (f ∘ g) x≡y)
                    (λ x → cong f (cong g (refl x))  ≡⟨ cong (cong f) (cong-refl g) ⟩
                           cong f (refl (g x))       ≡⟨ cong-refl f ⟩
                           refl (f (g x))            ≡⟨ sym (cong-refl (f ∘ g)) ⟩∎
                           cong (f ∘ g) (refl x)     ∎)

  cong-sym : {A B : Set} {x y : A} (f : A → B) (x≡y : x ≡ y) →
             cong f (sym x≡y) ≡ sym (cong f x≡y)
  cong-sym f = elim (λ x≡y → cong f (sym x≡y) ≡ sym (cong f x≡y))
                    (λ x → cong f (sym (refl x))  ≡⟨ cong (cong f) sym-refl ⟩
                           cong f (refl x)        ≡⟨ cong-refl f ⟩
                           refl (f x)             ≡⟨ sym $ sym-refl ⟩
                           sym (refl (f x))       ≡⟨ cong sym $ sym $ cong-refl f ⟩∎
                           sym (cong f (refl x))  ∎)

  cong-trans : {A B : Set} {x y z : A}
               (f : A → B) (x≡y : x ≡ y) (y≡z : y ≡ z) →
               cong f (trans x≡y y≡z) ≡ trans (cong f x≡y) (cong f y≡z)
  cong-trans f =
    elim (λ x≡y → ∀ y≡z → cong f (trans x≡y y≡z) ≡
                          trans (cong f x≡y) (cong f y≡z))
         (λ y y≡z → cong f (trans (refl y) y≡z)           ≡⟨ cong (cong f) (trans-reflˡ _) ⟩
                    cong f y≡z                            ≡⟨ sym $ trans-reflˡ _ ⟩
                    trans (refl (f y)) (cong f y≡z)       ≡⟨ cong₂ trans (sym $ cong-refl f) (refl _) ⟩∎
                    trans (cong f (refl y)) (cong f y≡z)  ∎)

  trans-assoc : {A : Set} {x y z u : A}
                (x≡y : x ≡ y) (y≡z : y ≡ z) (z≡u : z ≡ u) →
                trans (trans x≡y y≡z) z≡u ≡ trans x≡y (trans y≡z z≡u)
  trans-assoc =
    elim (λ x≡y → ∀ y≡z z≡u → trans (trans x≡y y≡z) z≡u ≡
                              trans x≡y (trans y≡z z≡u))
         (λ y y≡z z≡u →
            trans (trans (refl y) y≡z) z≡u ≡⟨ cong₂ trans (trans-reflˡ _) (refl _) ⟩
            trans y≡z z≡u                  ≡⟨ sym $ trans-reflˡ _ ⟩∎
            trans (refl y) (trans y≡z z≡u) ∎)

------------------------------------------------------------------------
-- Equality expressions

-- Equality expressions.
--
-- Note that the code below pattern matches on expressions of this
-- type, and that this may (implicitly) involve uses of the K rule.
-- However, if the trusted kernel is correct then this should not
-- matter.

data Eq {A : Set} : A → A → Set₁ where
  Lift  : ∀ {x y} (x≡y : x ≡ y) → Eq x y
  Refl  : ∀ {x} → Eq x x
  Sym   : ∀ {x y} (x≈y : Eq x y) → Eq y x
  Trans : ∀ {x y z} (x≈y : Eq x y) (y≈z : Eq y z) → Eq x z
  Cong  : ∀ {B x y} (f : B → A) (x≈y : Eq x y) → Eq (f x) (f y)

-- Semantics.

⟦_⟧ : ∀ {A} {x y : A} → Eq x y → x ≡ y
⟦ Lift x≡y      ⟧ = x≡y
⟦ Refl          ⟧ = refl _
⟦ Sym x≈y       ⟧ = sym ⟦ x≈y ⟧
⟦ Trans x≈y y≈z ⟧ = trans ⟦ x≈y ⟧ ⟦ y≈z ⟧
⟦ Cong f x≈y    ⟧ = cong f ⟦ x≈y ⟧

-- A derived combinator.

Cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        Eq x y → Eq u v → Eq (f x u) (f y v)
Cong₂ f {y = y} {u} x≈y u≈v =
  Trans (Cong (λ g → g u) (Cong f x≈y)) (Cong (f y) u≈v)

private

  Cong₂-correct :
    {A B C : Set} (f : A → B → C) {x y : A} {u v : B}
    (x≈y : Eq x y) (u≈v : Eq u v) →
    ⟦ Cong₂ f x≈y u≈v ⟧ ≡ cong₂ f ⟦ x≈y ⟧ ⟦ u≈v ⟧
  Cong₂-correct f x≈y u≈v = refl _

------------------------------------------------------------------------
-- Simplified expressions

private

  -- The simplified expressions are stratified into three levels.

  data Level : Set where
    upper middle lower : Level

  -- Simplified expressions.

  data EqS {A : Set} : Level → A → A → Set₁ where
    -- Bottom layer: a single use of congruence applied to an actual
    -- equality.

    Cong   : {B : Set} {x y : B} (f : B → A) (x≡y : x ≡ y) →
             EqS lower (f x) (f y)

    -- Middle layer: at most one use of symmetry.

    No-Sym : ∀ {x y} (x≈y : EqS lower x y) → EqS middle x y
    Sym    : ∀ {x y} (x≈y : EqS lower x y) → EqS middle y x

    -- Uppermost layer: a sequence of equalities, combined using
    -- transitivity and a single use of reflexivity.

    Refl   : ∀ {x} → EqS upper x x
    Cons   : ∀ {x y z} (x≈y : EqS middle x y) (y≈z : EqS upper y z) →
             EqS upper x z

  -- Semantics of simplified expressions.

  ⟦_⟧S : ∀ {A ℓ} {x y : A} → EqS ℓ x y → x ≡ y
  ⟦ Cong f x≡y   ⟧S = cong f x≡y
  ⟦ No-Sym x≈y   ⟧S =     ⟦ x≈y ⟧S
  ⟦ Sym  y≈x     ⟧S = sym ⟦ y≈x ⟧S
  ⟦ Refl         ⟧S = refl _
  ⟦ Cons x≈y y≈z ⟧S = trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S

  -- Simplified expressions which are equivalent to a given proof.

  EqS_⟨_⟩ : Level → ∀ {A} {x y : A} → x ≡ y → Set₁
  EqS ℓ ⟨ x≡y ⟩ = ∃ λ (x≈y : EqS ℓ _ _) → x≡y ≡ ⟦ x≈y ⟧S

------------------------------------------------------------------------
-- Manipulation of expressions combined with proofs

private

  lift : ∀ {A} {x y : A} (x≡y : x ≡ y) → EqS upper ⟨ x≡y ⟩
  lift x≡y = Cons (No-Sym (Cong id x≡y)) Refl , (
    x≡y                           ≡⟨ cong-id _ ⟩
    cong id x≡y                   ≡⟨ sym $ trans-reflʳ _ ⟩∎
    trans (cong id x≡y) (refl _)  ∎)

  snoc : ∀ {A} {x y z : A} {x≡y : x ≡ y} {y≡z : y ≡ z} →
         EqS upper ⟨ sym y≡z ⟩ →
         EqS middle ⟨ sym x≡y ⟩        →
         EqS upper ⟨ sym (trans x≡y y≡z) ⟩
  snoc {x≡y = x≡y} {y≡z} (Refl , h₁) (y≈z , h₂) = Cons y≈z Refl , (
    sym (trans x≡y y≡z)        ≡⟨ sym-trans _ _ ⟩
    trans (sym y≡z) (sym x≡y)  ≡⟨ cong₂ trans h₁ h₂ ⟩
    trans (refl _) ⟦ y≈z ⟧S    ≡⟨ trans-reflˡ _ ⟩
    ⟦ y≈z ⟧S                   ≡⟨ sym $ trans-reflʳ _ ⟩∎
    trans ⟦ y≈z ⟧S (refl _)    ∎)
  snoc {x≡y = x≡y} {y≡z} (Cons x≈y y≈z , h₁) (z≈u , h₂)
    with snoc (y≈z , sym-sym _) (z≈u , h₂)
  ... | (y≈u , h₃) = Cons x≈y y≈u , (
    sym (trans x≡y y≡z)                                    ≡⟨ sym-trans _ _ ⟩
    trans (sym y≡z) (sym x≡y)                              ≡⟨ cong₂ trans h₁ (refl _) ⟩
    trans (trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S) (sym x≡y)              ≡⟨ trans-assoc _ _ _ ⟩
    trans ⟦ x≈y ⟧S (trans ⟦ y≈z ⟧S (sym x≡y))              ≡⟨ cong (trans _) $ cong₂ trans (sym $ sym-sym _) (refl _) ⟩
    trans ⟦ x≈y ⟧S (trans (sym (sym ⟦ y≈z ⟧S)) (sym x≡y))  ≡⟨ cong (trans _) $ sym $ sym-trans _ _ ⟩
    trans ⟦ x≈y ⟧S (sym (trans x≡y (sym ⟦ y≈z ⟧S)))        ≡⟨ cong (trans _) h₃ ⟩∎
    trans ⟦ x≈y ⟧S ⟦ y≈u ⟧S                                ∎)

  append : ∀ {A} {x y z : A} {x≡y : x ≡ y} {y≡z : y ≡ z} →
           EqS upper ⟨ x≡y ⟩ →
           EqS upper ⟨ y≡z ⟩ →
           EqS upper ⟨ trans x≡y y≡z ⟩
  append {x≡y = x≡y} {y≡z} (Refl , h) x≈y =
    Prod.map id
             (λ {y≈z} y≡z≡⟦y≈z⟧ →
                trans x≡y y≡z            ≡⟨ cong₂ trans h y≡z≡⟦y≈z⟧ ⟩
                trans (refl _) ⟦ y≈z ⟧S  ≡⟨ trans-reflˡ _ ⟩∎
                ⟦ y≈z ⟧S                 ∎)
             x≈y
  append {x≡y = x≡z} {z≡u} (Cons x≈y y≈z , h) z≈u =
    Prod.map (Cons x≈y)
             (λ {y≈u} trans⟦y≈z⟧z≡u≡⟦y≈u⟧ →
                trans x≡z z≡u                        ≡⟨ cong₂ trans h (refl _) ⟩
                trans (trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S) z≡u  ≡⟨ trans-assoc _ _ _ ⟩
                trans ⟦ x≈y ⟧S (trans ⟦ y≈z ⟧S z≡u)  ≡⟨ cong (trans _) trans⟦y≈z⟧z≡u≡⟦y≈u⟧ ⟩∎
                trans ⟦ x≈y ⟧S ⟦ y≈u ⟧S              ∎)
             (append (y≈z , refl _) z≈u)

  map-sym : ∀ {A} {x y : A} {x≡y : x ≡ y} →
            EqS middle ⟨ x≡y ⟩ → EqS middle ⟨ sym x≡y ⟩
  map-sym {x≡y = x≡y} (No-Sym x≈y , h) = Sym    x≈y , (sym x≡y       ≡⟨ cong sym h ⟩∎
                                                       sym ⟦ x≈y ⟧S  ∎)
  map-sym {x≡y = x≡y} (Sym    x≈y , h) = No-Sym x≈y , (sym x≡y             ≡⟨ cong sym h ⟩
                                                       sym (sym ⟦ x≈y ⟧S)  ≡⟨ sym-sym _ ⟩∎
                                                       ⟦ x≈y ⟧S            ∎)

  reverse : ∀ {A} {x y : A} {x≡y : x ≡ y} →
            EqS upper ⟨ x≡y ⟩ →
            EqS upper ⟨ sym x≡y ⟩
  reverse {x≡y = x≡y} (Refl         , h) = Refl , (sym x≡y       ≡⟨ cong sym h ⟩
                                                   sym (refl _)  ≡⟨ sym-refl ⟩∎
                                                   refl _        ∎)
  reverse {x≡y = x≡y} (Cons x≈y y≈z , h)
    with snoc (reverse (y≈z , refl _)) (map-sym (x≈y , refl _))
  ... | (x≈z , h′) = x≈z , (sym x≡y                        ≡⟨ cong sym h ⟩
                            sym (trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S)  ≡⟨ h′ ⟩∎
                            ⟦ x≈z ⟧S                       ∎)

  map-cong : ∀ {ℓ A B} {x y : A} (f : A → B) {x≡y : x ≡ y} →
             EqS ℓ ⟨ x≡y ⟩ → EqS ℓ ⟨ cong f x≡y ⟩
  map-cong f {gx≡gy} (Cong g x≡y   , h) = Cong (f ∘ g) x≡y , (cong f gx≡gy         ≡⟨ cong (cong f) h ⟩
                                                              cong f (cong g x≡y)  ≡⟨ cong-∘ f g _ ⟩∎
                                                              cong (f ∘ g) x≡y     ∎)
  map-cong f {x≡y}   (No-Sym x≈y   , h) = Prod.map No-Sym id (map-cong f (x≈y , h))
  map-cong f {x≡y}   (Sym    x≈y   , h) = Prod.map Sym (λ {fy≈fx} cong-f-⟦x≈y⟧≡⟦fy≈fx⟧ →
                                                          cong f x≡y             ≡⟨ cong (cong f) h ⟩
                                                          cong f (sym ⟦ x≈y ⟧S)  ≡⟨ cong-sym f _ ⟩
                                                          sym (cong f ⟦ x≈y ⟧S)  ≡⟨ cong sym cong-f-⟦x≈y⟧≡⟦fy≈fx⟧ ⟩∎
                                                          sym ⟦ fy≈fx ⟧S         ∎)
                                                   (map-cong f (x≈y , refl _))
  map-cong f {x≡y}   (Refl         , h) = Refl , (cong f x≡y       ≡⟨ cong (cong f) h ⟩
                                                  cong f (refl _)  ≡⟨ cong-refl f ⟩∎
                                                  refl _           ∎)
  map-cong f {x≡y}   (Cons x≈y y≈z , h)
    with map-cong f (x≈y , refl _) | map-cong f (y≈z , refl _)
  ... | (fx≈fy , h₁) | (fy≈fz , h₂) = Cons fx≈fy fy≈fz , (
    cong f x≡y                                 ≡⟨ cong (cong f) h ⟩
    cong f (trans ⟦ x≈y ⟧S ⟦ y≈z ⟧S)           ≡⟨ cong-trans f _ _ ⟩
    trans (cong f ⟦ x≈y ⟧S) (cong f ⟦ y≈z ⟧S)  ≡⟨ cong₂ trans h₁ h₂ ⟩∎
    trans ⟦ fx≈fy ⟧S ⟦ fy≈fz ⟧S                ∎)

-- Equality-preserving simplifier.

simplify : ∀ {A} {x y : A} (x≡y : Eq x y) → EqS upper ⟨ ⟦ x≡y ⟧ ⟩
simplify (Lift x≡y)      = lift x≡y
simplify Refl            = (Refl , refl _)
simplify (Sym x≡y)       = reverse (simplify x≡y)
simplify (Trans x≡y y≡z) = append (simplify x≡y) (simplify y≡z)
simplify (Cong f x≡y)    = map-cong f (simplify x≡y)

------------------------------------------------------------------------
-- Tactic

-- Simple tactic for proving equality of equality proofs.

prove : ∀ {A} {x y : A} (x≡y x≡y′ : Eq x y) →
        ⟦ proj₁ (simplify x≡y) ⟧S ≡ ⟦ proj₁ (simplify x≡y′) ⟧S →
        ⟦ x≡y ⟧ ≡ ⟦ x≡y′ ⟧
prove x≡y x≡y′ hyp =
  ⟦ x≡y ⟧                     ≡⟨ proj₂ (simplify x≡y) ⟩
  ⟦ proj₁ (simplify x≡y ) ⟧S  ≡⟨ hyp ⟩
  ⟦ proj₁ (simplify x≡y′) ⟧S  ≡⟨ sym (proj₂ (simplify x≡y′)) ⟩∎
  ⟦ x≡y′ ⟧                    ∎

------------------------------------------------------------------------
-- Some examples

private
  module Examples {A : Set} {x y : A} (x≡y : x ≡ y) where

    ex₁ : trans (refl x) (sym (sym x≡y)) ≡ x≡y
    ex₁ = prove (Trans Refl (Sym (Sym (Lift x≡y)))) (Lift x≡y) (refl _)

    ex₂ : cong proj₂ (sym (cong (_,_ x) x≡y)) ≡ sym x≡y
    ex₂ = prove (Cong proj₂ (Sym (Cong (_,_ x) (Lift x≡y))))
                (Sym (Lift x≡y))
                (refl _)

------------------------------------------------------------------------
-- A non-example

-- Note that the tactic does not handle equalities such as the
-- following one.

trans-sym : ∀ {A} {x y : A} (x≡y : x ≡ y) →
            trans x≡y (sym x≡y) ≡ refl x
trans-sym =
  elim (λ {x} x≡y → trans x≡y (sym x≡y) ≡ refl x)
       (λ _ → prove (Trans Refl (Sym Refl)) Refl (refl _))
