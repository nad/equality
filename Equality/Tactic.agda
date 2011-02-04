------------------------------------------------------------------------
-- A tactic for proving equality of equality proofs
------------------------------------------------------------------------

-- I use --type-in-type temporarily while experimenting, because _≡_
-- is not universe-polymorphic.

{-# OPTIONS --without-K --type-in-type #-}

module Equality.Tactic where

open import Equality
open import Prelude hiding (Level; module Level)
open import Variable

------------------------------------------------------------------------
-- Boring lemmas

private

  trans-reflʳ : {A : Set} {x y : A} (x≡y : x ≡ y) →
                trans x≡y (refl y) ≡ x≡y
  trans-reflʳ =
    elim (λ {u v} u≡v → trans u≡v (refl v) ≡ u≡v)
         (λ _ → trans-refl-refl)

  trans-reflˡ : {A : Set} {x y : A} (x≡y : x ≡ y) →
                trans (refl x) x≡y ≡ x≡y
  trans-reflˡ =
    elim (λ {u v} u≡v → trans (refl u) u≡v ≡ u≡v)
         (λ _ → trans-refl-refl)

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
                    trans (sym y≡z) (refl y)        ≡⟨ cong (trans _) (sym sym-refl) ⟩∎
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

-- Equality hypotheses.

infix 6 _⊜_

record Eq : Set₁ where
  constructor _⊜_
  field
    {A} : Set
    x y : A

eq : Eq → Set
eq (x ⊜ y) = x ≡ y

-- Functions.

record Fun : Set₁ where
  constructor fun
  field
    {Domain Codomain} : Set
    function          : Domain → Codomain

-- Equality expressions.

infix 4 _,_⊢_≡_

data _,_⊢_≡_ {m n} (Γ : Ctxt Eq m) (Ρ : Ctxt Fun n)
             {A : Set} : A → A → Set₁ where
  Var   : ∀ {x y} (x≡y : Γ ∋ x ⊜ y) → Γ , Ρ ⊢ x ≡ y
  Refl  : ∀ {x} → Γ , Ρ ⊢ x ≡ x
  Sym   : ∀ {x y} (x≈y : Γ , Ρ ⊢ x ≡ y) → Γ , Ρ ⊢ y ≡ x
  Trans : ∀ {x y z}
          (x≈y : Γ , Ρ ⊢ x ≡ y) (y≈z : Γ , Ρ ⊢ y ≡ z) → Γ , Ρ ⊢ x ≡ z
  Cong  : ∀ {B x y} {f : B → A}
          (f∈Ρ : Ρ ∋ fun f) (x≈y : Γ , Ρ ⊢ x ≡ y) → Γ , Ρ ⊢ f x ≡ f y

-- Semantics.

⟦_⟧ : ∀ {m n} {Γ : Ctxt Eq m} {Ρ : Ctxt Fun n} {A} {x y : A} →
      Γ , Ρ ⊢ x ≡ y → Env eq Γ → x ≡ y
⟦ Var x≡y            ⟧ γ = lookup x≡y γ
⟦ Refl               ⟧ γ = refl _
⟦ Sym x≈y            ⟧ γ = sym (⟦ x≈y ⟧ γ)
⟦ Trans x≈y y≈z      ⟧ γ = trans (⟦ x≈y ⟧ γ) (⟦ y≈z ⟧ γ)
⟦ Cong {f = f} _ x≈y ⟧ γ = cong f (⟦ x≈y ⟧ γ)

------------------------------------------------------------------------
-- Restricted expressions

private
 module Restricted
   {m} {Γ : Ctxt Eq m} (γ : Env eq Γ)
   {n} {Ρ : Ctxt Fun n}
   where

  infix 4 _⟶⋆_ ⊢_≡_[lower] ⊢_≡_[middle] ⊢_≡_[upper] ⊢_≡_[_] ⊢⟨_⟩[_]

  -- A sequence of function variables.

  data _⟶⋆_ : Set → Set → Set₁ where
    [id]  : ∀ {A} → A ⟶⋆ A
    _[∘]_ : ∀ {A B C} {f : B → C}
            (f∈Ρ : Ρ ∋ fun f) (gs : A ⟶⋆ B) → A ⟶⋆ C

  -- Looks up and composes a sequence of function variables.

  compose : ∀ {A B} → A ⟶⋆ B → A → B
  compose [id]                 = id
  compose (_[∘]_ {f = f} _ gs) = f ∘ compose gs

  -- The restricted expressions are stratified into three levels.

  data Level : Set where
    upper middle lower : Level

  -- Bottom layer: a sequence of congruences applied to a variable.

  data ⊢_≡_[lower] {A : Set} : A → A → Set₁ where
    Cong : ∀ {B x y} (fs : B ⟶⋆ A) (x≡y : Γ ∋ x ⊜ y) →
           ⊢ compose fs x ≡ compose fs y [lower]

  -- Middle layer: at most one use of symmetry.

  data ⊢_≡_[middle] {A : Set} : A → A → Set₁ where
    No-sym : ∀ {x y} (x≈y : ⊢ x ≡ y [lower]) → ⊢ x ≡ y [middle]
    Sym    : ∀ {x y} (x≈y : ⊢ x ≡ y [lower]) → ⊢ y ≡ x [middle]

  -- Uppermost layer: a sequence of equalities, combined using
  -- transitivity and a single use of reflexivity.

  data ⊢_≡_[upper] {A : Set} : A → A → Set₁ where
    Refl  : ∀ {x} → ⊢ x ≡ x [upper]
    Trans : ∀ {x y z} (x≈y : ⊢ x ≡ y [middle]) (y≈z : ⊢ y ≡ z [upper]) →
            ⊢ x ≡ z [upper]

  -- Restricted expressions.

  ⊢_≡_[_] : {A : Set} → A → A → Level → Set₁
  ⊢ x ≡ y [ lower  ] = ⊢ x ≡ y [lower]
  ⊢ x ≡ y [ middle ] = ⊢ x ≡ y [middle]
  ⊢ x ≡ y [ upper  ] = ⊢ x ≡ y [upper]

  -- Semantics of restricted expressions.

  ⟦_⟧R : ∀ {ℓ A} {x y : A} → ⊢ x ≡ y [ ℓ ] → x ≡ y
  ⟦_⟧R {lower}  (Cong fs x≡y)   = cong (compose fs) (lookup x≡y γ)
  ⟦_⟧R {middle} (No-sym x≈y)    =     ⟦ x≈y ⟧R
  ⟦_⟧R {middle} (Sym    x≈y)    = sym ⟦ x≈y ⟧R
  ⟦_⟧R {upper}  Refl            = refl _
  ⟦_⟧R {upper}  (Trans x≈y y≈z) = trans ⟦ x≈y ⟧R ⟦ y≈z ⟧R

  -- Restricted expressions which are equivalent to a given proof.

  ⊢⟨_⟩[_] : ∀ {A} {x y : A} → x ≡ y → Level → Set₁
  ⊢⟨ x≡y ⟩[ ℓ ] = ∃ λ (x≈y : ⊢ _ ≡ _ [ ℓ ]) → x≡y ≡ ⟦ x≈y ⟧R

------------------------------------------------------------------------
-- Removal of trans p (sym p) and trans (sym p) p

  -- The following two functions appear to be very hard to define.

  _≟-Exprˡ_ : ∀ {A} {x x′ y : A}
              (e : ⊢ x ≡ y [lower]) (e′ : ⊢ x′ ≡ y [lower]) →
              Maybe (∃ λ (x≡x′ : x ≡ x′) →
                       ⟦ e ⟧R ≡ trans x≡x′ ⟦ e′ ⟧R)
  _≟-Exprˡ_ = {!!}

  _≟-Exprʳ_ : ∀ {A} {x y y′ : A}
              (e : ⊢ x ≡ y [lower]) (e′ : ⊢ x ≡ y′ [lower]) →
              Maybe (∃ λ (y≡y′ : y ≡ y′) →
                       sym ⟦ e ⟧R ≡ trans y≡y′ (sym ⟦ e′ ⟧R))
  _≟-Exprʳ_ = {!!}

  -- Note: The uses of elim below will get in the way of the tactic,
  -- because they do not compute.

  drop-adjacent-inverses :
    ∀ {A} {x y : A} {x≡y : x ≡ y} →
    ⊢⟨ x≡y ⟩[ upper ] → ⊢⟨ x≡y ⟩[ upper ]
  drop-adjacent-inverses (Refl          , h) = (Refl , h)
  drop-adjacent-inverses (Trans x≈y y≈z , h)
    with drop-adjacent-inverses (y≈z , refl _)
  drop-adjacent-inverses {y = z} {x≡y = x≡z}
    (Trans (No-sym x≈y) y≈z , h) | (Trans (Sym u≈y) u≈z , h′)
    with x≈y ≟-Exprˡ u≈y
  ... | just (x≡u , h″) =
    elim (λ {x u} x≡u → {x≡z : x ≡ z} (u≈z : ⊢ u ≡ z [upper]) →
            x≡z ≡ trans x≡u ⟦ u≈z ⟧R → ⊢⟨ x≡z ⟩[ upper ])
         (λ x {x≡z} x≈z hyp → x≈z , (
            x≡z                      ≡⟨ hyp ⟩
            trans (refl x) ⟦ x≈z ⟧R  ≡⟨ trans-reflˡ _ ⟩∎
            ⟦ x≈z ⟧R                 ∎))
         x≡u u≈z
         (x≡z                                                         ≡⟨ h ⟩
          trans ⟦ x≈y ⟧R ⟦ y≈z ⟧R                                     ≡⟨ cong₂ trans h″ h′ ⟩
          trans (trans x≡u ⟦ u≈y ⟧R) (trans (sym ⟦ u≈y ⟧R) ⟦ u≈z ⟧R)  ≡⟨ trans-assoc _ _ _ ⟩
          trans x≡u (trans ⟦ u≈y ⟧R (trans (sym ⟦ u≈y ⟧R) ⟦ u≈z ⟧R))  ≡⟨ cong (trans x≡u) (sym $ trans-assoc _ _ _) ⟩
          trans x≡u (trans (trans ⟦ u≈y ⟧R (sym ⟦ u≈y ⟧R)) ⟦ u≈z ⟧R)  ≡⟨ cong (λ p → trans x≡u (trans p ⟦ u≈z ⟧R)) (trans-symʳ _) ⟩
          trans x≡u (trans (refl _) ⟦ u≈z ⟧R)                         ≡⟨ cong (trans x≡u) (trans-reflˡ _) ⟩∎
          trans x≡u ⟦ u≈z ⟧R                                          ∎)
  ... | nothing = Trans (No-sym x≈y) (Trans (Sym u≈y) u≈z) , (
    x≡z                                             ≡⟨ h ⟩
    trans ⟦ x≈y ⟧R ⟦ y≈z ⟧R                         ≡⟨ cong (trans ⟦ x≈y ⟧R) h′ ⟩∎
    trans ⟦ x≈y ⟧R (trans (sym ⟦ u≈y ⟧R) ⟦ u≈z ⟧R)  ∎)
  drop-adjacent-inverses {y = z} {x≡y = x≡z}
    (Trans (Sym y≈x) y≈z , h) | (Trans (No-sym y≈u) u≈z , h′)
    with y≈x ≟-Exprʳ y≈u
  ... | just (x≡u , h″) =
    elim (λ {x u} x≡u → {x≡z : x ≡ z} (u≈z : ⊢ u ≡ z [upper]) →
            x≡z ≡ trans x≡u ⟦ u≈z ⟧R → ⊢⟨ x≡z ⟩[ upper ])
         (λ x {x≡z} x≈z hyp → x≈z , (
            x≡z                      ≡⟨ hyp ⟩
            trans (refl x) ⟦ x≈z ⟧R  ≡⟨ trans-reflˡ _ ⟩∎
            ⟦ x≈z ⟧R                 ∎))
         x≡u u≈z
         (x≡z                                                         ≡⟨ h ⟩
          trans (sym ⟦ y≈x ⟧R) ⟦ y≈z ⟧R                               ≡⟨ cong₂ trans h″ h′ ⟩
          trans (trans x≡u (sym ⟦ y≈u ⟧R)) (trans ⟦ y≈u ⟧R ⟦ u≈z ⟧R)  ≡⟨ trans-assoc _ _ _ ⟩
          trans x≡u (trans (sym ⟦ y≈u ⟧R) (trans ⟦ y≈u ⟧R ⟦ u≈z ⟧R))  ≡⟨ cong (trans x≡u) (sym $ trans-assoc _ _ _) ⟩
          trans x≡u (trans (trans (sym ⟦ y≈u ⟧R) ⟦ y≈u ⟧R) ⟦ u≈z ⟧R)  ≡⟨ cong (λ p → trans x≡u (trans p ⟦ u≈z ⟧R)) (trans-symˡ _) ⟩
          trans x≡u (trans (refl _) ⟦ u≈z ⟧R)                         ≡⟨ cong (trans x≡u) (trans-reflˡ _) ⟩∎
          trans x≡u ⟦ u≈z ⟧R                                          ∎)
  ... | nothing = Trans (Sym y≈x) (Trans (No-sym y≈u) u≈z) , (
    x≡z                                             ≡⟨ h ⟩
    trans (sym ⟦ y≈x ⟧R) ⟦ y≈z ⟧R                   ≡⟨ cong (trans (sym ⟦ y≈x ⟧R)) h′ ⟩∎
    trans (sym ⟦ y≈x ⟧R) (trans ⟦ y≈u ⟧R ⟦ u≈z ⟧R)  ∎)
  drop-adjacent-inverses {x≡y = x≡z} (Trans x≈y y≈z , h) | (y≈z′ , h′) =
    Trans x≈y y≈z′ , (
      x≡z                       ≡⟨ h ⟩
      trans ⟦ x≈y ⟧R ⟦ y≈z  ⟧R  ≡⟨ cong (trans ⟦ x≈y ⟧R) h′ ⟩∎
      trans ⟦ x≈y ⟧R ⟦ y≈z′ ⟧R  ∎)

------------------------------------------------------------------------
-- Manipulation of restricted expressions

  var : ∀ {A} {x y : A} (x≡y : Γ ∋ x ⊜ y) →
        ⊢⟨ lookup x≡y γ ⟩[ upper ]
  var x≡y = Trans (No-sym (Cong [id] x≡y)) Refl , (
    lookup x≡y γ                             ≡⟨ cong-id _ ⟩
    cong id (lookup x≡y γ)                   ≡⟨ sym $ trans-reflʳ _ ⟩∎
    trans (cong id (lookup x≡y γ)) (refl _)  ∎)

  snoc : ∀ {A} {x y z : A} {x≡y : x ≡ y} {y≡z : y ≡ z} →
         ⊢⟨ sym            y≡z  ⟩[ upper  ] →
         ⊢⟨ sym        x≡y      ⟩[ middle ] →
         ⊢⟨ sym (trans x≡y y≡z) ⟩[ upper  ]
  snoc {x≡y = x≡y} {y≡z} (Refl , h₁) (y≈z , h₂) = Trans y≈z Refl , (
    sym (trans x≡y y≡z)        ≡⟨ sym-trans _ _ ⟩
    trans (sym y≡z) (sym x≡y)  ≡⟨ cong₂ trans h₁ h₂ ⟩
    trans (refl _) ⟦ y≈z ⟧R    ≡⟨ trans-reflˡ _ ⟩
    ⟦ y≈z ⟧R                   ≡⟨ sym $ trans-reflʳ _ ⟩∎
    trans ⟦ y≈z ⟧R (refl _)    ∎)
  snoc {x≡y = x≡y} {y≡z} (Trans x≈y y≈z , h₁) (z≈u , h₂)
    with snoc (y≈z , sym-sym _) (z≈u , h₂)
  ... | (y≈u , h₃) = Trans x≈y y≈u , (
    sym (trans x≡y y≡z)                                    ≡⟨ sym-trans _ _ ⟩
    trans (sym y≡z) (sym x≡y)                              ≡⟨ cong₂ trans h₁ (refl _) ⟩
    trans (trans ⟦ x≈y ⟧R ⟦ y≈z ⟧R) (sym x≡y)              ≡⟨ trans-assoc _ _ _ ⟩
    trans ⟦ x≈y ⟧R (trans ⟦ y≈z ⟧R (sym x≡y))              ≡⟨ cong (trans _) $ cong₂ trans (sym $ sym-sym _) (refl _) ⟩
    trans ⟦ x≈y ⟧R (trans (sym (sym ⟦ y≈z ⟧R)) (sym x≡y))  ≡⟨ cong (trans _) $ sym $ sym-trans _ _ ⟩
    trans ⟦ x≈y ⟧R (sym (trans x≡y (sym ⟦ y≈z ⟧R)))        ≡⟨ cong (trans _) h₃ ⟩∎
    trans ⟦ x≈y ⟧R ⟦ y≈u ⟧R                                ∎)

  append : ∀ {A} {x y z : A} {x≡y : x ≡ y} {y≡z : y ≡ z} →
           ⊢⟨       x≡y     ⟩[ upper ] →
           ⊢⟨           y≡z ⟩[ upper ] →
           ⊢⟨ trans x≡y y≡z ⟩[ upper ]
  append {x≡y = x≡y} {y≡z} (Refl , h) x≈y =
    Σ-map id
          (λ {y≈z} y≡z≡⟦y≈z⟧ →
             trans x≡y y≡z            ≡⟨ cong₂ trans h y≡z≡⟦y≈z⟧ ⟩
             trans (refl _) ⟦ y≈z ⟧R  ≡⟨ trans-reflˡ _ ⟩∎
             ⟦ y≈z ⟧R                 ∎)
          x≈y
  append {x≡y = x≡z} {z≡u} (Trans x≈y y≈z , h) z≈u =
    Σ-map (Trans x≈y)
          (λ {y≈u} trans⟦y≈z⟧z≡u≡⟦y≈u⟧ →
             trans x≡z z≡u                        ≡⟨ cong₂ trans h (refl _) ⟩
             trans (trans ⟦ x≈y ⟧R ⟦ y≈z ⟧R) z≡u  ≡⟨ trans-assoc _ _ _ ⟩
             trans ⟦ x≈y ⟧R (trans ⟦ y≈z ⟧R z≡u)  ≡⟨ cong (trans _) trans⟦y≈z⟧z≡u≡⟦y≈u⟧ ⟩∎
             trans ⟦ x≈y ⟧R ⟦ y≈u ⟧R              ∎)
          (append (y≈z , refl _) z≈u)

  map-sym : ∀ {A} {x y : A} {x≡y : x ≡ y} →
            ⊢⟨     x≡y ⟩[ middle ] →
            ⊢⟨ sym x≡y ⟩[ middle ]
  map-sym {x≡y = x≡y} (No-sym x≈y , h) = Sym    x≈y , (sym x≡y       ≡⟨ cong sym h ⟩∎
                                                       sym ⟦ x≈y ⟧R  ∎)
  map-sym {x≡y = x≡y} (Sym    x≈y , h) = No-sym x≈y , (sym x≡y             ≡⟨ cong sym h ⟩
                                                       sym (sym ⟦ x≈y ⟧R)  ≡⟨ sym-sym _ ⟩∎
                                                       ⟦ x≈y ⟧R            ∎)

  reverse : ∀ {A} {x y : A} {x≡y : x ≡ y} →
            ⊢⟨     x≡y ⟩[ upper ] →
            ⊢⟨ sym x≡y ⟩[ upper ]
  reverse {x≡y = x≡y} (Refl          , h) = Refl , (sym x≡y       ≡⟨ cong sym h ⟩
                                                    sym (refl _)  ≡⟨ sym-refl ⟩∎
                                                    refl _        ∎)
  reverse {x≡y = x≡y} (Trans x≈y y≈z , h)
    with snoc (reverse (y≈z , refl _)) (map-sym (x≈y , refl _))
  ... | (x≈z , h′) = x≈z , (sym x≡y                        ≡⟨ cong sym h ⟩
                            sym (trans ⟦ x≈y ⟧R ⟦ y≈z ⟧R)  ≡⟨ h′ ⟩∎
                            ⟦ x≈z ⟧R                       ∎)

  map-cong : ∀ {A B ℓ} {x y : A} {f : A → B}
             (f∈Ρ : Ρ ∋ fun f) {x≡y : x ≡ y} →
             ⊢⟨        x≡y ⟩[ ℓ ] →
             ⊢⟨ cong f x≡y ⟩[ ℓ ]
  map-cong {A} {f = f} f∈Ρ x≈y = helper _ _ x≈y
    where
    helper : ∀ ℓ {x y : A} (x≡y : x ≡ y) →
             ⊢⟨        x≡y ⟩[ ℓ ] →
             ⊢⟨ cong f x≡y ⟩[ ℓ ]
    helper lower gsx≡gsy (Cong gs x≡y   , h) = Cong (f∈Ρ [∘] gs) x≡y , (cong f gsx≡gsy          ≡⟨ cong (cong f) h ⟩
                                                                        cong f (cong gs′ x≡y′)  ≡⟨ cong-∘ f gs′ _ ⟩∎
                                                                        cong (f ∘ gs′) x≡y′     ∎)
                                               where gs′ = compose gs; x≡y′ = lookup x≡y γ
    helper middle x≡y    (No-sym x≈y    , h) = Σ-map No-sym id (map-cong f∈Ρ (x≈y , h))
    helper middle x≡y    (Sym    x≈y    , h) = Σ-map Sym (λ {fy≈fx} cong-f-⟦x≈y⟧≡⟦fy≈fx⟧ →
                                                            cong f x≡y             ≡⟨ cong (cong f) h ⟩
                                                            cong f (sym ⟦ x≈y ⟧R)  ≡⟨ cong-sym f _ ⟩
                                                            sym (cong f ⟦ x≈y ⟧R)  ≡⟨ cong sym cong-f-⟦x≈y⟧≡⟦fy≈fx⟧ ⟩∎
                                                            sym ⟦ fy≈fx ⟧R         ∎)
                                                     (map-cong f∈Ρ (x≈y , refl _))
    helper upper  x≡y    (Refl          , h) = Refl , (cong f x≡y       ≡⟨ cong (cong f) h ⟩
                                                       cong f (refl _)  ≡⟨ cong-refl f ⟩∎
                                                       refl _           ∎)
    helper upper  x≡y    (Trans x≈y y≈z , h)
      with map-cong f∈Ρ (x≈y , refl _) | map-cong f∈Ρ (y≈z , refl _)
    ... | (fx≈fy , h₁) | (fy≈fz , h₂) = Trans fx≈fy fy≈fz , (
      cong f x≡y                                 ≡⟨ cong (cong f) h ⟩
      cong f (trans ⟦ x≈y ⟧R ⟦ y≈z ⟧R)           ≡⟨ cong-trans f _ _ ⟩
      trans (cong f ⟦ x≈y ⟧R) (cong f ⟦ y≈z ⟧R)  ≡⟨ cong₂ trans h₁ h₂ ⟩∎
      trans ⟦ fx≈fy ⟧R ⟦ fy≈fz ⟧R                ∎)

  -- Equality-preserving restrictifier.

  restrictify : ∀ {A} {x y : A}
                (x≈y : Γ , Ρ ⊢ x ≡ y) → ⊢⟨ ⟦ x≈y ⟧ γ ⟩[ upper ]
  restrictify (Var x≡y)       = var x≡y
  restrictify Refl            = (Refl , refl _)
  restrictify (Sym x≈y)       = reverse (restrictify x≈y)
  restrictify (Trans x≈y y≈z) = append (restrictify x≈y) (restrictify y≈z)
  restrictify (Cong f x≈y)    = map-cong f (restrictify x≈y)

------------------------------------------------------------------------
-- Tactic

-- Applies the function to all possible variables.
--
-- The use of this function makes equality expressions a bit easier to
-- write, because de Bruijn indices can be replaced by Agda variables
-- (see the examples below).

close :
  ∀ {m n} (Γ : Ctxt Eq m) {Ρ : Ctxt Fun n} {A : Set₁} →
  [ (λ eq → Γ , Ρ ⊢ Eq.x eq ≡ Eq.y eq) ] Γ ⇒
    [ (λ f → Ρ ∋ f) ] Ρ ⇒ A →
  A
close Γ {Ρ} f =
  uncurry Ρ (uncurry Γ f (map Var Γ (allVars Γ))) (allVars Ρ)

-- Alternative semantics of expressions.

_⟪_⟫_ : ∀ {m n} (Γ : Ctxt Eq m) {γ : Env eq Γ} {Ρ : Ctxt Fun n}
          {A} {x y : A} {B : Set₁} →
        [ (λ eq → Γ , Ρ ⊢ Eq.x eq ≡ Eq.y eq) ] Γ ⇒
          [ (λ f → Ρ ∋ f) ] Ρ ⇒ B →
        (B → Γ , Ρ ⊢ x ≡ y) → x ≡ y
_⟪_⟫_ Γ {γ} f proj = ⟦ proj₁ (restrictify (proj (close Γ f))) ⟧R
  where open Restricted γ

abstract

  -- The alternative semantics is equivalent to the ordinary one.

  _⟪_⟫-correct_ :
    ∀ {m n} (Γ : Ctxt Eq m) {γ} {Ρ : Ctxt Fun n}
      {A} {x y : A} {B : Set₁}
    (f : [ (λ eq → Γ , Ρ ⊢ Eq.x eq ≡ Eq.y eq) ] Γ ⇒
         [ (λ f → Ρ ∋ f) ] Ρ ⇒ B)
    (proj : B → Γ , Ρ  ⊢ x ≡ y) →
    ⟦ proj (close Γ f) ⟧ γ ≡ Γ ⟪ f ⟫ proj
  Γ ⟪ f ⟫-correct proj = proj₂ (restrictify (proj (close Γ f)))
    where open Restricted _

  -- A tactic for proving equality of equality proofs.

  prove : ∀ m {Γ : Ctxt Eq m} {γ n} (Ρ : Ctxt Fun n) {A} {x y : A}
          (x≈y² : [ (λ eq → Γ , Ρ ⊢ Eq.x eq ≡ Eq.y eq) ] Γ ⇒
                  [ (λ f → Ρ ∋ f) ] Ρ ⇒ (Γ , Ρ ⊢ x ≡ y) ²) →
          Γ ⟪ x≈y² ⟫ proj₁ ≡ Γ ⟪ x≈y² ⟫ proj₂ →
          ⟦ proj₁ (close Γ x≈y²) ⟧ γ ≡ ⟦ proj₂ (close Γ x≈y²) ⟧ γ
  prove _ {Γ} {γ} _ x≈y² hyp =
    ⟦ proj₁ (close Γ x≈y²) ⟧ γ  ≡⟨ Γ ⟪ x≈y² ⟫-correct proj₁ ⟩
    Γ ⟪ x≈y² ⟫ proj₁            ≡⟨ hyp ⟩
    Γ ⟪ x≈y² ⟫ proj₂            ≡⟨ sym (Γ ⟪ x≈y² ⟫-correct proj₂) ⟩∎
    ⟦ proj₂ (close Γ x≈y²) ⟧ γ  ∎

------------------------------------------------------------------------
-- Some examples

private
 module Examples {A B : Set} {x y : A} (x≡y : x ≡ y) (f : A → B) where

  ex₁ : trans (refl x) (sym (sym x≡y)) ≡ x≡y
  ex₁ = prove 1 tt
              (λ x≡y → Trans Refl (Sym (Sym x≡y)) , x≡y)
              (refl _)

  ex₂ : trans (refl (f y)) (sym (cong f x≡y)) ≡ cong f (sym x≡y)
  ex₂ = prove 1 (tt , fun f)
              (λ x≡y f → Trans Refl (Sym (Cong f x≡y)) ,
                         Cong f (Sym x≡y))
              (refl _)

  ex₃ : cong proj₂ (sym (cong (_,_ x) x≡y)) ≡ sym x≡y
  ex₃ = prove 1 ((tt , fun (_,_ x)) , fun proj₂)
              (λ x≡y c p → Cong p (Sym (Cong c x≡y)) , Sym x≡y)
              (refl _)
