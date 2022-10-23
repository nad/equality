------------------------------------------------------------------------
-- Indexed containers
------------------------------------------------------------------------

-- Partly based on "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris, and partly based on "Non-wellfounded trees in
-- Homotopy Type Theory" by Ahrens, Capriotti and Spadotti.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Container.Indexed
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

import Bijection eq as B
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)

private
  variable
    a ℓ p p₁ p₂ pos q r s : Level
    A I O                 : Type a
    P Q R                 : A → Type p
    ext f i k o           : A

------------------------------------------------------------------------
-- _⇾_

-- A kind of function space for indexed types.

infix 4 _⇾_

_⇾_ :
  {A : Type a} →
  (A → Type p) → (A → Type q) → Type (a ⊔ p ⊔ q)
P ⇾ Q = ∀ x → P x → Q x

-- An identity function.

id⇾ : P ⇾ P
id⇾ _ = id

mutual

  infixr 9 _∘⇾_ _∘⇾′_ _∘⇾″_

  -- Composition for _⇾_.

  _∘⇾_ : Q ⇾ R → P ⇾ Q → P ⇾ R
  _∘⇾_ = _∘⇾′_

  -- A generalisation of _∘⇾_.

  _∘⇾′_ :
    {I : Type i} {P : I → Type p} {Q : I → Type q}
    {R : ∀ {i} → Q i → Type r} →
    (∀ i (x : Q i) → R x) →
    (g : P ⇾ Q) →
    ((i : I) (x : P i) → R (g i x))
  f ∘⇾′ g = (λ i _ → f i) ∘⇾″ g

  -- Another generalisation of _∘⇾_.

  _∘⇾″_ :
    {I : Type i} {P : I → Type p} {Q : ∀ {i} → P i → Type q}
    {R : ∀ {i} {x : P i} → Q x → Type r} →
    (∀ i (x : P i) (y : Q x) → R y) →
    (g : ∀ i (x : P i) → Q x) →
    ((i : I) (x : P i) → R (g i x))
  f ∘⇾″ g = λ i → f i _ ∘ g i

-- A variant of cong-post-∘-ext.

cong-post-∘⇾-ext :
  {I : Type i}
  {P : I → Type p} {Q : ∀ {i} → P i → Type q} {R : I → Type r}
  {h : ∀ i (x : P i) → Q x → R i} {f g : ∀ i (x : P i) → Q x}
  {f≡g : ∀ i x → f i x ≡ g i x}
  (ext₁ : Extensionality i (p ⊔ r))
  (ext₂ : Extensionality i (p ⊔ q))
  (ext₃ : Extensionality p r)
  (ext₄ : Extensionality p q) →
  cong (h ∘⇾″_) (apply-ext ext₂ (apply-ext ext₄ ∘ f≡g)) ≡
  apply-ext ext₁ (apply-ext ext₃ ∘ (λ i x → cong (h i x)) ∘⇾″ f≡g)
cong-post-∘⇾-ext {h = h} {f≡g = f≡g} ext₁ ext₂ ext₃ ext₄ =
  cong ((λ {i} → (λ {x} → h i x) ∘_) ∘_)
    (apply-ext ext₂ (apply-ext ext₄ ∘ f≡g))                               ≡⟨ cong-post-∘-ext ext₂ ext₁ ⟩

  (apply-ext ext₁ $
   (λ {i} → cong ((λ {x} → h i x) ∘_)) ∘ apply-ext ext₄ ∘ f≡g)            ≡⟨⟩

  (apply-ext ext₁ λ i →
   cong ((λ {x} → h i x) ∘_) (apply-ext ext₄ (f≡g i)))                    ≡⟨ (cong (apply-ext ext₁) $ apply-ext ext₁ λ _ →
                                                                              cong-post-∘-ext ext₄ ext₃) ⟩∎
  (apply-ext ext₁ λ i → apply-ext ext₃ ((λ {x} → cong (h i x)) ∘ f≡g i))  ∎

-- A variant of cong-pre-∘-ext.

cong-pre-∘⇾-ext :
  {I : Type i}
  {P : I → Type p} {Q : I → Type q} {R : ∀ {i} → Q i → Type r}
  {f g : ∀ i (x : Q i) → R x} {h : P ⇾ Q}
  {f≡g : ∀ i x → f i x ≡ g i x}
  (ext₁ : Extensionality i (p ⊔ r))
  (ext₂ : Extensionality i (q ⊔ r))
  (ext₃ : Extensionality p r)
  (ext₄ : Extensionality q r) →
  cong (_∘⇾′ h) (apply-ext ext₂ (apply-ext ext₄ ∘ f≡g)) ≡
  apply-ext ext₁ (apply-ext ext₃ ∘ f≡g ∘⇾′ h)
cong-pre-∘⇾-ext {h = h} {f≡g = f≡g} ext₁ ext₂ ext₃ ext₄ =
  cong (λ f i → f i ∘ h i) (apply-ext ext₂ (apply-ext ext₄ ∘ f≡g))  ≡⟨ sym $ ext-cong ext₁ ⟩

  (apply-ext ext₁ λ i →
   cong (λ f → f i ∘ h i) (apply-ext ext₂ (apply-ext ext₄ ∘ f≡g)))  ≡⟨ (cong (apply-ext ext₁) $ apply-ext ext₁ λ _ → sym $
                                                                        cong-∘ _ _ _) ⟩
  (apply-ext ext₁ λ i → cong (_∘ h i) $
   cong (_$ i) (apply-ext ext₂ (apply-ext ext₄ ∘ f≡g)))             ≡⟨ (cong (apply-ext ext₁) $ apply-ext ext₁ λ _ → cong (cong _) $
                                                                        cong-ext ext₂) ⟩

  (apply-ext ext₁ λ i → cong (_∘ h i) (apply-ext ext₄ (f≡g i)))     ≡⟨ (cong (apply-ext ext₁) $ apply-ext ext₁ λ _ →
                                                                        cong-pre-∘-ext ext₃ ext₄) ⟩∎
  (apply-ext ext₁ λ i → apply-ext ext₃ (f≡g i ∘ h i))               ∎

------------------------------------------------------------------------
-- Containers

-- Doubly indexed containers.

record Container₂ (I : Type i) (O : Type o) s p :
                  Type (i ⊔ o ⊔ lsuc (s ⊔ p)) where
  field
    Shape    : O → Type s
    Position : ∀ {o} → Shape o → Type p
    index    : ∀ {o} {s : Shape o} → Position s → I

open Container₂ public

-- Singly indexed containers.

Container : Type i → ∀ s p → Type (i ⊔ lsuc (s ⊔ p))
Container I = Container₂ I I

private
  variable
    C : Container₂ I O s p

-- Container₂ can be expressed as a nested Σ-type.

Container≃Σ :
  Container₂ I O s p ≃
  (∃ λ (S : O → Type s) →
   ∃ λ (P : ∀ {o} → S o → Type p) →
     ∀ {o} {s : S o} → P s → I)
Container≃Σ = Eq.↔→≃
  (λ C → C .Shape , C .Position , C .index)
  (λ (S , P , i) → record { Shape = S; Position = P; index = i })
  refl
  refl

------------------------------------------------------------------------
-- Polynomial functors

-- The polynomial functor associated to a container.

⟦_⟧ :
  {I : Type i} {O : Type o} →
  Container₂ I O s p → (I → Type ℓ) → O → Type (ℓ ⊔ s ⊔ p)
⟦ C ⟧ P i = ∃ λ (s : Shape C i) → (p : Position C s) → P (index C p)

-- A map function.

map : (C : Container₂ I O s p) → P ⇾ Q → ⟦ C ⟧ P ⇾ ⟦ C ⟧ Q
map C f _ (s , g) = s , f _ ∘ g

-- Functor laws.

map-id : map C (id⇾ {P = P}) ≡ id⇾
map-id = refl _

map-∘ :
  (f : Q ⇾ R) (g : P ⇾ Q) →
  map C (f ∘⇾ g) ≡ map C f ∘⇾ map C g
map-∘ _ _ = refl _

-- A preservation lemma.

⟦⟧-cong :
  {I : Type i} {P₁ : I → Type p₁} {P₂ : I → Type p₂} →
  Extensionality? k p (p₁ ⊔ p₂) →
  (C : Container₂ I O s p) →
  (∀ i → P₁ i ↝[ k ] P₂ i) →
  (∀ o → ⟦ C ⟧ P₁ o ↝[ k ] ⟦ C ⟧ P₂ o)
⟦⟧-cong {P₁ = P₁} {P₂ = P₂} ext C P₁↝P₂ o =
  (∃ λ (s : Shape C o) → (p : Position C s) → P₁ (index C p))  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → P₁↝P₂ _) ⟩□
  (∃ λ (s : Shape C o) → (p : Position C s) → P₂ (index C p))  □

-- The forward direction of ⟦⟧-cong is an instance of map (at least
-- when k is equivalence).

_ : _≃_.to (⟦⟧-cong ext C f o) ≡ map C (_≃_.to ∘ f) o
_ = refl _

-- The shapes of a container are pointwise equivalent to the
-- polynomial functor of the container applied to the constant
-- function yielding the unit type.
--
-- (This lemma was suggested to me by an anonymous reviewer of a
-- paper.)

Shape≃⟦⟧⊤ :
  (C : Container₂ I O s p) →
  Shape C o ≃ ⟦ C ⟧ (λ _ → ⊤) o
Shape≃⟦⟧⊤ {o = o} C =
  Shape C o                                 ↔⟨ inverse $ drop-⊤-right (λ _ → →-right-zero) ⟩□
  (∃ λ (s : Shape C o) → Position C s → ⊤)  □

-- A rearrangement lemma for cong, map and apply-ext.

cong-map-ext :
  {I : Type i} {O : Type o} {C : Container₂ I O s pos}
  {P : I → Type p} {Q : I → Type q}
  {f g : P ⇾ Q} {f≡g : ∀ i x → f i x ≡ g i x}
  (ext₁ : Extensionality i (p ⊔ q))
  (ext₂ : Extensionality p q)
  (ext₃ : Extensionality o (s ⊔ pos ⊔ p ⊔ q))
  (ext₄ : Extensionality (s ⊔ pos ⊔ p) (s ⊔ pos ⊔ q)) →
  (ext₅ : Extensionality pos q) →
  cong (map C) (apply-ext ext₁ (apply-ext ext₂ ∘ f≡g)) ≡
  (apply-ext ext₃ λ _ → apply-ext ext₄ λ (s , h) →
   cong (s ,_) $ apply-ext ext₅ (f≡g _ ∘ h))
cong-map-ext {C = C} {P = P} {f≡g = f≡g} ext₁ ext₂ ext₃ ext₄ ext₅ =
  cong (λ f _ (s , h) → s , λ p → f (index C p) (h p))
    (apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))             ≡⟨ sym $ ext-cong ext₃ ⟩

  (apply-ext ext₃ λ o →
   cong (λ f ((s , h) : ⟦ C ⟧ P o) →
           s , λ p → f (index C p) (h p)) $
   apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))               ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                            sym $ ext-cong ext₄) ⟩
  (apply-ext ext₃ λ _ → apply-ext ext₄ λ (s , h) →
   cong (λ f → s , λ p → f (index C p) (h p)) $
   apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))               ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                            cong (apply-ext ext₄) $ apply-ext ext₄ λ (s , _) →
                                                            sym $ cong-∘ (s ,_) _ _) ⟩
  (apply-ext ext₃ λ _ →
   apply-ext ext₄ λ (s , h) → cong (s ,_) $
   cong (λ f p → f (index C p) (h p)) $
   apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))               ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                            cong (apply-ext ext₄) $ apply-ext ext₄ λ _ →
                                                            cong (cong _) $
                                                            sym $ ext-cong ext₅) ⟩
  (apply-ext ext₃ λ _ →
   apply-ext ext₄ λ (s , h) → cong (s ,_) $
   apply-ext ext₅ λ p →
   cong (λ f → f (index C p) (h p)) $
   apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))               ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                            cong (apply-ext ext₄) $ apply-ext ext₄ λ _ →
                                                            cong (cong _) $
                                                            cong (apply-ext ext₅) $ apply-ext ext₅ λ _ →
                                                            sym $ cong-∘ _ _ _) ⟩
  (apply-ext ext₃ λ _ →
   apply-ext ext₄ λ (s , h) → cong (s ,_) $
   apply-ext ext₅ λ p → cong (_$ h p) $
   cong (_$ index C p) $
   apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))               ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                            cong (apply-ext ext₄) $ apply-ext ext₄ λ _ →
                                                            cong (cong _) $
                                                            cong (apply-ext ext₅) $ apply-ext ext₅ λ _ →
                                                            cong (cong _) $
                                                            cong-ext ext₁) ⟩
  (apply-ext ext₃ λ _ →
   apply-ext ext₄ λ (s , h) → cong (s ,_) $
   apply-ext ext₅ λ p → cong (_$ h p) $
   apply-ext ext₂ $ f≡g (index C p))                    ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                            cong (apply-ext ext₄) $ apply-ext ext₄ λ _ →
                                                            cong (cong _) $
                                                            cong (apply-ext ext₅) $ apply-ext ext₅ λ _ →
                                                            cong-ext ext₂) ⟩∎
  (apply-ext ext₃ λ _ →
   apply-ext ext₄ λ (s , h) → cong (s ,_) $
   apply-ext ext₅ λ p → f≡g (index C p) (h p))          ∎

------------------------------------------------------------------------
-- Lifting the position type family

-- One can lift the position type family so that it is in a universe
-- that is at least as large as that containing the input indices.

lift-positions :
  {I : Type i} →
  Container₂ I O s p → Container₂ I O s (i ⊔ p)
lift-positions {i = i} C = λ where
  .Shape          → C .Shape
  .Position s     → ↑ i (C .Position s)
  .index (lift p) → C .index p

-- The result of ⟦_⟧ is not affected by lift-positions (up to
-- pointwise equivalence).

⟦⟧≃⟦lift-positions⟧ :
  {I : Type i}
  (C : Container₂ I O s p) (P : I → Type ℓ) →
  ⟦ C ⟧ P o ≃ ⟦ lift-positions C ⟧ P o
⟦⟧≃⟦lift-positions⟧ {o = o} C P =
  ∃-cong λ s →

  ((      p  :      Position C s)  → P (index C p))  ↝⟨ Eq.↔→≃ (_∘ lower) (_∘ lift) refl refl ⟩□
  (((lift p) : ↑ _ (Position C s)) → P (index C p))  □
